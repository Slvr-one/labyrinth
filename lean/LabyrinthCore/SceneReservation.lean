module
public import LabyrinthCore.SceneRouteBudget
public import LabyrinthCore.ScenePreflight

/-! Reservations (S5), part 1: `Scene::admission` and `Scene::reservation`, with the small
equalities they use. Both are total.

`admission(cell)` rejects, in this order: a cell outside the layout (`InvalidIndex`); a suspended,
inactive or layout-pending scene (`InvalidTransition`); a cell some non-idle patch covers
(`Occupied`). Otherwise it succeeds. It never changes the scene.

`reservation(token)` rejects, in this order: a token of another epoch (`StaleEpoch`); a walker
index outside the walker list (`InvalidIndex`); a walker that is not crossing under exactly this
token (`InvalidTransition`). Otherwise it returns the walker's crossing. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-! ### The derived equalities -/

theorem walkerState_ne_ready (s : walker.WalkerState) :
    core.cmp.PartialEq.ne.trait_default
      walker.WalkerState.Insts.CoreCmpPartialEqWalkerState s walker.WalkerState.Ready
      ⦃ b => (b = true ↔ s ≠ walker.WalkerState.Ready) ⦄ := by
  apply core.cmp.PartialEq.ne.trait_default.spec
  cases s <;>
    simp [walker.WalkerState.Insts.CoreCmpPartialEqWalkerState.eq,
      walker.WalkerState.read_discriminant, spec_ok]

theorem stage_ne_idle (s : shatter.Stage) :
    core.cmp.PartialEq.ne.trait_default shatter.Stage.Insts.CoreCmpPartialEqStage s
      shatter.Stage.Idle ⦃ b => (b = true ↔ s ≠ shatter.Stage.Idle) ⦄ := by
  apply core.cmp.PartialEq.ne.trait_default.spec
  cases s <;>
    simp [shatter.Stage.Insts.CoreCmpPartialEqStage.eq, shatter.Stage.read_discriminant,
      spec_ok]

theorem reservation_eq_spec (a b : walker.Reservation) :
    walker.Reservation.Insts.CoreCmpPartialEqReservation.eq a b ⦃ r => (r = true ↔ a = b) ⦄ := by
  unfold walker.Reservation.Insts.CoreCmpPartialEqReservation.eq
  obtain ⟨ae, aw, asr⟩ := a
  obtain ⟨be, bw, bsr⟩ := b
  by_cases h1 : ae = be <;> by_cases h2 : asr = bsr <;> by_cases h3 : aw = bw <;>
    simp_all [spec_ok]

/-! ### `Patch::contains` -/

/-- A non-idle patch covers `cell`. -/
def PatchHas (p : shatter.Patch) (cell : Nat) : Prop :=
  p.stage ≠ shatter.Stage.Idle ∧ cell < p.cells.val.length ∧ p.cells.val[cell]? = some true

theorem patch_contains_spec (p : shatter.Patch) (cell : Std.Usize) :
    shatter.Patch.contains p cell ⦃ b => (b = true ↔ PatchHas p cell.val) ⦄ := by
  unfold shatter.Patch.contains
  apply spec_bind (stage_ne_idle p.stage)
  intro b hb
  by_cases hbt : b = true
  · have hne : p.stage ≠ shatter.Stage.Idle := hb.mp hbt
    simp only [hbt, ↓reduceIte]
    by_cases hlt : cell < alloc.vec.Vec.len p.cells
    · simp only [hlt, ↓reduceIte]
      have hl : cell.val < p.cells.val.length := hlt
      simp only [alloc.vec.Vec.index_slice_index]
      apply spec_mono (alloc.vec.Vec.index_usize_spec p.cells cell hl)
      intro x hx
      rw [hx]
      constructor
      · intro h; exact ⟨hne, hl, by rw [List.getElem?_eq_getElem hl, h]⟩
      · rintro ⟨_, _, h⟩
        rw [List.getElem?_eq_getElem hl] at h
        exact Option.some.inj h
    · simp only [hlt, ↓reduceIte, spec_ok]
      have hl : ¬ cell.val < p.cells.val.length := hlt
      simp only [Bool.false_eq_true, false_iff]
      exact fun ⟨_, h, _⟩ => hl h
  · have hnb : ¬ p.stage ≠ shatter.Stage.Idle := fun h => hbt (hb.mpr h)
    simp only [hbt, Bool.false_eq_true, ↓reduceIte, spec_ok]
    simp only [false_iff]
    exact fun ⟨h, _⟩ => hnb h

/-! ### `Scene::admission` -/

theorem admission_loop_spec (v : alloc.vec.Vec shatter.Patch) (cell : Std.Usize)
    (occ0 : Bool) (i0 : Std.Usize) :
    scene.Scene.admission_loop v cell occ0 i0 ⦃ r =>
      (r = true ↔ occ0 = true ∨ ∃ j, i0.val ≤ j ∧ ∃ p, v.val[j]? = some p ∧ PatchHas p cell.val) ⦄ := by
  unfold scene.Scene.admission_loop
  refine loop.spec_decr_nat (fun x : Bool × Std.Usize => v.length - x.2.val)
    (fun x : Bool × Std.Usize =>
      (x.1 = true ∨ ∃ j, x.2.val ≤ j ∧ ∃ p, v.val[j]? = some p ∧ PatchHas p cell.val) ↔
      (occ0 = true ∨ ∃ j, i0.val ≤ j ∧ ∃ p, v.val[j]? = some p ∧ PatchHas p cell.val))
    (fun r : Bool => (r = true ↔ occ0 = true ∨ ∃ j, i0.val ≤ j ∧ ∃ p, v.val[j]? = some p ∧
      PatchHas p cell.val)) _ _ ?_ Iff.rfl
  rintro ⟨occ, i⟩ hinv
  simp only at hinv
  unfold scene.Scene.admission_loop.body
  by_cases hlt : i < alloc.vec.Vec.len v
  · simp only [hlt, ↓reduceIte]
    have hl : i.val < v.val.length := hlt
    by_cases ho : occ = true
    · simp only [ho, ↓reduceIte, spec_ok]
      exact iff_of_true trivial (hinv.mp (Or.inl ho))
    · simp only [ho, Bool.false_eq_true, ↓reduceIte]
      simp only [alloc.vec.Vec.index_slice_index]
      apply spec_bind (alloc.vec.Vec.index_usize_spec v i hl)
      intro p hp
      apply spec_bind (patch_contains_spec p cell)
      intro c hc
      apply spec_bind (usize_succ_spec i (by have := v.property; scalar_tac))
      intro i2 hi2
      rw [spec_ok]
      have hocc : occ = false := by simpa using ho
      have hvl : v.length = v.val.length := rfl
      have hi2v : i2.val = i.val + 1 := by simpa using hi2
      refine ⟨?_, by show v.length - i2.val < v.length - i.val; omega⟩
      simp only [hi2v]
      rw [← hinv]
      simp only [hocc, Bool.false_eq_true, false_or, hc]
      constructor
      · rintro (h | ⟨j, hj, q, hq, hqp⟩)
        · exact ⟨i.val, le_refl _, p, by rw [List.getElem?_eq_getElem hl, hp], h⟩
        · exact ⟨j, by omega, q, hq, hqp⟩
      · rintro ⟨j, hj, q, hq, hqp⟩
        by_cases hji : j = i.val
        · subst hji
          left
          rw [List.getElem?_eq_getElem hl] at hq
          cases hq; rw [hp]; exact hqp
        · right; exact ⟨j, by omega, q, hq, hqp⟩
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hl : ¬ i.val < v.val.length := hlt
    rw [← hinv]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨j, hj, q, hq, _⟩)
      · exact h
      · exfalso
        have := (List.getElem?_eq_some_iff.mp hq).1
        omega

open Classical in
/-- What `admission` answers for a cell. -/
noncomputable def admissionVerdict (self : scene.Scene) (cell : Nat) :
    core.result.Result Unit topology.Error :=
  if self.layout.cells.val.length ≤ cell then .Err topology.Error.InvalidIndex
  else if self.suspended = true ∨ self.inactive = true ∨ self.pending ≠ none then
    .Err topology.Error.InvalidTransition
  else if ∃ p ∈ self.patches.val, PatchHas p cell then .Err topology.Error.Occupied
  else .Ok ()

theorem admission_spec (self : scene.Scene) (cell : Std.Usize) :
    scene.Scene.admission self cell ⦃ r => r = admissionVerdict self cell.val ⦄ := by
  unfold scene.Scene.admission
  by_cases h1 : cell ≥ alloc.vec.Vec.len self.layout.cells
  · have h1' : self.layout.cells.val.length ≤ cell.val := h1
    simp only [h1, ↓reduceIte, spec_ok, admissionVerdict, h1']
  · have h1' : ¬ self.layout.cells.val.length ≤ cell.val := h1
    simp only [h1, ↓reduceIte]
    by_cases hs : self.suspended = true
    · simp [hs, spec_ok, admissionVerdict, h1']
    · by_cases hi : self.inactive = true
      · simp [hs, hi, spec_ok, admissionVerdict, h1']
      · have hs' : self.suspended = false := by simpa using hs
        have hi' : self.inactive = false := by simpa using hi
        simp only [hs', hi', Bool.false_eq_true, ↓reduceIte]
        by_cases hp : self.pending.isSome = true
        · have : self.pending ≠ none := by
            intro h; simp [h] at hp
          simp [hp, spec_ok, admissionVerdict, h1', this]
        · have hpn : self.pending = none := by
            cases hq : self.pending with
            | none => rfl
            | some x => simp [hq] at hp
          have hp2 : core.option.Option.is_some self.pending = false := by
            simp [core.option.Option.is_some, hpn]
          simp only [hp2, Bool.false_eq_true, ↓reduceIte]
          apply spec_bind (admission_loop_spec self.patches cell false 0#usize)
          intro occ hocc
          by_cases ho : occ = true
          · have hex : ∃ p ∈ self.patches.val, PatchHas p cell.val := by
              obtain ⟨j, _, p, hp, hpp⟩ := (hocc.mp ho).resolve_left (by simp)
              exact ⟨p, List.mem_of_getElem? hp, hpp⟩
            simp [ho, spec_ok, admissionVerdict, h1', hs', hi', hpn, hex]
          · have hex : ¬ ∃ p ∈ self.patches.val, PatchHas p cell.val := by
              rintro ⟨p, hpm, hpp⟩
              apply ho
              apply hocc.mpr
              right
              obtain ⟨j, hj, hjp⟩ := List.getElem_of_mem hpm
              exact ⟨j, by simp, p, by rw [List.getElem?_eq_getElem hj, hjp], hpp⟩
            simp [ho, spec_ok, admissionVerdict, h1', hs', hi', hpn, hex]

/-! ### `Scene::reservation` -/

/-- The walker at `token.walker` is crossing under exactly this token. -/
def HoldsToken (self : scene.Scene) (token : walker.Reservation) (c : walker.Crossing) : Prop :=
  ∃ w, self.walkers.val[token.walker.val]? = some w ∧
    w.state = walker.WalkerState.Crossing c ∧ c.reservation = token

theorem reservation_spec (self : scene.Scene) (token : walker.Reservation) :
    scene.Scene.reservation self token ⦃ r =>
      (token.epoch ≠ self.stamp.epoch → r = .Err topology.Error.StaleEpoch) ∧
      (token.epoch = self.stamp.epoch → self.walkers.val.length ≤ token.walker.val →
        r = .Err topology.Error.InvalidIndex) ∧
      (token.epoch = self.stamp.epoch → token.walker.val < self.walkers.val.length →
        (∀ c, ¬ HoldsToken self token c) → r = .Err topology.Error.InvalidTransition) ∧
      (token.epoch = self.stamp.epoch → ∀ c, HoldsToken self token c → r = .Ok c) ⦄ := by
  unfold scene.Scene.reservation
  by_cases he : token.epoch = self.stamp.epoch
  · have hne : (token.epoch != self.stamp.epoch) = false := by simp [he]
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    have hget : core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice walker.Walker)
        (alloc.vec.Vec.deref self.walkers) token.walker =
        ok (self.walkers.val[token.walker.val]?) := by
      simp [core.slice.Slice.get, alloc.vec.Vec.deref]
    rw [hget, bind_ok]
    cases hw : self.walkers.val[token.walker.val]? with
    | none =>
      have hlen : self.walkers.val.length ≤ token.walker.val := by
        by_contra h
        have := (List.getElem?_eq_getElem (l := self.walkers.val) (by omega : token.walker.val <
          self.walkers.val.length))
        rw [hw] at this; simp at this
      simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, spec_ok, he, hlen, HoldsToken]
    | some w =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have hlt : token.walker.val < self.walkers.val.length := by
        have := (List.getElem?_eq_some_iff.mp hw).1
        exact this
      cases hs : w.state with
      | Crossing c =>
        simp only
        apply spec_bind (reservation_eq_spec c.reservation token)
        intro b hb
        by_cases hbt : b = true
        · have hc : c.reservation = token := hb.mp hbt
          simp only [hbt, ↓reduceIte, spec_ok]
          refine ⟨fun h => absurd he h, fun _ h => by omega, fun _ _ hn => ?_, fun _ c' hc' => ?_⟩
          · exact absurd ⟨w, hw, hs, hc⟩ (hn c)
          · obtain ⟨w', hw', hs', _⟩ := hc'
            rw [hw] at hw'; cases hw'
            rw [hs] at hs'; cases hs'; rfl
        · have hc : ¬ c.reservation = token := fun h => hbt (hb.mpr h)
          simp only [hbt, Bool.false_eq_true, ↓reduceIte, spec_ok]
          refine ⟨fun h => absurd he h, fun _ h => by omega, fun _ _ _ => trivial, fun _ c' hc' => ?_⟩
          obtain ⟨w', hw', hs', hr'⟩ := hc'
          rw [hw] at hw'; cases hw'
          rw [hs] at hs'; cases hs'
          exact absurd hr' hc
      | Ready | Parked | Hidden | Terminated =>
        all_goals
          simp only [spec_ok]
          refine ⟨fun h => absurd he h, fun _ h => by omega, fun _ _ _ => trivial, fun _ c' hc' => ?_⟩
          obtain ⟨w', hw', hs', _⟩ := hc'
          rw [hw] at hw'; cases hw'
          rw [hs] at hs'; cases hs'
  · have hne : (token.epoch != self.stamp.epoch) = true := by simpa using he
    simp only [hne, ↓reduceIte, spec_ok]
    exact ⟨fun _ => trivial, fun h => absurd h he, fun h => absurd h he, fun h => absurd h he⟩

end Labyrinth
