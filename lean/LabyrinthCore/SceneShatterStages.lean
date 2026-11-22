module
public import LabyrinthCore.SceneShatterOps

/-! Shatter (S6), part 3: the walker sweeps that `hide_patch` and the reform step of `tick` run. A
sweep over the walker list sets the state of every walker standing in a patch and leaves the others
alone. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

open Classical in
/-- The walker after a patch sweep to state `s`: standing in the patch means taking the state. -/
noncomputable def stateIf (p : shatter.Patch) (s : walker.WalkerState) (o : walker.Walker) :
    walker.Walker :=
  if PatchHas p o.cell.val then { o with state := s } else o

/-- The sweep of `hide_patch`: every walker standing in the patch is hidden. -/
theorem hide_loop_spec (vw : alloc.vec.Vec walker.Walker) (vp : alloc.vec.Vec shatter.Patch)
    (slot : Std.Usize) (pp : shatter.Patch) (hp : vp.val[slot.val]? = some pp)
    (w0 : Std.Usize) :
    scene.Scene.hide_patch_loop vw vp slot w0 ⦃ r =>
      r.val.length = vw.val.length ∧
      ∀ i, r.val[i]? =
        if w0.val ≤ i then (vw.val[i]?).map (stateIf pp walker.WalkerState.Hidden) else
          vw.val[i]? ⦄ := by
  unfold scene.Scene.hide_patch_loop
  refine loop.spec_decr_nat (fun x : alloc.vec.Vec walker.Walker × Std.Usize =>
      x.1.val.length - x.2.val)
    (fun x => x.1.val.length = vw.val.length ∧ w0.val ≤ x.2.val ∧
      ∀ i, x.1.val[i]? = if w0.val ≤ i ∧ i < x.2.val then
        (vw.val[i]?).map (stateIf pp walker.WalkerState.Hidden) else vw.val[i]?)
    (fun r : alloc.vec.Vec walker.Walker => r.val.length = vw.val.length ∧
      ∀ i, r.val[i]? =
        if w0.val ≤ i then (vw.val[i]?).map (stateIf pp walker.WalkerState.Hidden) else
          vw.val[i]?)
    _ (vw, w0) ?_ ⟨rfl, le_refl _, fun i => by simp⟩
  rintro ⟨y, w⟩ ⟨hl, hw0, hy⟩
  dsimp only at hl hw0 hy
  unfold scene.Scene.hide_patch_loop.body
  by_cases hlt : w < alloc.vec.Vec.len y
  · have hltn : w.val < y.val.length := by simpa using hlt
    simp only [hlt, ↓reduceIte]
    simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
    have hpl : slot.val < vp.val.length := (List.getElem?_eq_some_iff.mp hp).1
    apply spec_bind (alloc.vec.Vec.index_usize_spec vp slot hpl)
    intro p1 hp1
    have hpe : p1 = pp := by
      rw [hp1]
      have := hp
      rw [List.getElem?_eq_getElem hpl] at this
      exact Option.some.inj this
    apply spec_bind (alloc.vec.Vec.index_usize_spec y w hltn)
    intro w1 hw1
    apply spec_bind (patch_contains_spec p1 w1.cell)
    intro b hb
    rw [hpe] at hb
    have hyw : y.val[w.val]? = some w1 := by
      rw [List.getElem?_eq_getElem hltn]; simp [hw1]
    have hoyw : vw.val[w.val]? = some w1 := by
      have := hy w.val
      simp only [show ¬ (w0.val ≤ w.val ∧ w.val < w.val) from by omega, ↓reduceIte] at this
      rw [hyw] at this
      exact this.symm
    by_cases hbt : b = true
    · have hhas : PatchHas pp w1.cell.val := hb.mp hbt
      simp only [hbt, ↓reduceIte, Std.bind_assoc]
      apply spec_bind (alloc.vec.Vec.index_mut_usize_spec y w hltn)
      rintro ⟨w2, back⟩ ⟨hw2, hback⟩
      subst hback
      erw [Std.bind_ok]
      apply spec_bind (Usize.add_spec (x := w) (y := 1#usize) (by scalar_tac))
      intro w3 hw3
      have hw3v : w3.val = w.val + 1 := by simpa using hw3
      rw [spec_ok]; dsimp only
      refine ⟨⟨by simp [hl, alloc.vec.Vec.set_val_eq], by omega, fun i => ?_⟩, by simp only [alloc.vec.Vec.set_val_eq, List.length_set]; omega⟩
      rw [hw3v]
      rw [alloc.vec.Vec.set_val_eq, List.getElem?_set]
      by_cases hiw : w.val = i
      · subst hiw
        have hw2e : w2 = w1 := by rw [hw2] at *; simp [hw1] at hw2 ⊢
        subst hw2e
        simp only [hltn, hoyw, true_and, ↓reduceIte, Option.map_some, stateIf, hhas,
          show w0.val ≤ w.val ∧ w.val < w.val + 1 from ⟨by omega, by omega⟩]
      · simp only [hiw, ↓reduceIte]
        rw [hy i]
        have : (w0.val ≤ i ∧ i < w.val) ↔ (w0.val ≤ i ∧ i < w.val + 1) := by omega
        simp only [this]
    · simp only [hbt, Bool.false_eq_true, ↓reduceIte, Std.bind_ok]
      apply spec_bind (Usize.add_spec (x := w) (y := 1#usize) (by scalar_tac))
      intro w3 hw3
      have hw3v : w3.val = w.val + 1 := by simpa using hw3
      have hnh : ¬ PatchHas pp w1.cell.val := fun h => hbt (hb.mpr h)
      rw [spec_ok]; dsimp only
      refine ⟨⟨hl, by omega, fun i => ?_⟩, by omega⟩
      rw [hw3v]
      rw [hy i]
      by_cases hiw : w.val = i
      · subst hiw
        simp only [hoyw, stateIf, hnh, ↓reduceIte, Option.map_some,
          show w0.val ≤ w.val ∧ w.val < w.val + 1 from ⟨by omega, by omega⟩]
        simp
      · have : (w0.val ≤ i ∧ i < w.val) ↔ (w0.val ≤ i ∧ i < w.val + 1) := by omega
        simp only [this]
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hge : y.val.length ≤ w.val := by simpa using hlt
    refine ⟨hl, fun i => ?_⟩
    rw [hy i]
    by_cases hi : i < y.val.length
    · have : (w0.val ≤ i ∧ i < w.val) ↔ w0.val ≤ i := by omega
      simp only [this]
    · have h1 : vw.val[i]? = none := List.getElem?_eq_none (by omega)
      simp only [h1, Option.map_none, ite_self]


theorem stage_ne_spec (a b : shatter.Stage) :
    core.cmp.PartialEq.ne.trait_default shatter.Stage.Insts.CoreCmpPartialEqStage a b
      ⦃ r => (r = true ↔ a ≠ b) ⦄ := by
  apply core.cmp.PartialEq.ne.trait_default.spec
  exact spec_mono (stage_eq_spec a b) (fun r h => by simp [h])

open Classical in
theorem frozen_ite {α : Type _} (self : scene.Scene) (a b : α) :
    (if self.suspended = true then a else
      if core.option.Option.is_some self.pending = true then a else
        if self.inactive = true then a else b) = if Frozen self then a else b := by
  unfold Frozen
  cases hq : self.pending <;> by_cases h1 : self.suspended = true <;>
    by_cases h3 : self.inactive = true <;> simp [core.option.Option.is_some, h1, h3]

/-! ### `hide_patch` -/

/-- The walkers after `hide_patch`: those standing in the patch are hidden. -/
def SweepOf (p : shatter.Patch) (s : walker.WalkerState) (old new : alloc.vec.Vec walker.Walker) :
    Prop :=
  new.val.length = old.val.length ∧
    ∀ i : Nat, new.val[i]? = (old.val[i]?).map (stateIf p s)

/-- The scene after a successful `hide_patch`. -/
def hiddenScene (self : scene.Scene) (id : shatter.PatchId) (p : shatter.Patch)
    (ws : alloc.vec.Vec walker.Walker) (v : Std.U64) : scene.Scene :=
  { self with
    walkers := ws
    patches := alloc.vec.Vec.set self.patches id.slot { p with stage := shatter.Stage.Hidden }
    stamp := bumped self v }

theorem hide_patch_spec (self : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId) :
    scene.Scene.hide_patch self stamp id ⦃ res =>
      (¬ StampAccepts self stamp ∧ StampRejects self stamp res) ∨
      (StampAccepts self stamp ∧
        ((∃ e, slotVerdict self id = .Err e ∧ res = (.Err e, self)) ∨
         ∃ p, SlotOk self id p ∧
          ((Frozen self ∧ res = (.Err topology.Error.InvalidTransition, self)) ∨
           (¬ Frozen self ∧ p.stage ≠ shatter.Stage.Parked ∧
              res = (.Err topology.Error.Occupied, self)) ∨
           (¬ Frozen self ∧ p.stage = shatter.Stage.Parked ∧
              ∃ (v : Std.U64) (ws : alloc.vec.Vec walker.Walker),
                v.val = self.stamp.revision.val + 1 ∧
                SweepOf p walker.WalkerState.Hidden self.walkers ws ∧
                res = (.Ok (bumped self v), hiddenScene self id p ws v))))) ⦄ := by
  unfold scene.Scene.hide_patch
  apply stamp_gate
  · intro v hv hacc
    simp only []
    apply spec_bind (patch_slot_spec self id)
    intro r1 hr1
    cases r1 with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, spec_ok]
      exact Or.inr ⟨hacc, Or.inl ⟨e, hr1.symm, rfl⟩⟩
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      rcases slotVerdict_cases self id with ⟨e, he⟩ | ⟨p, hp, _⟩
      · rw [he] at hr1; simp at hr1
      · have hu : u = id.slot := by rw [hp.1] at hr1; simpa using hr1.symm.symm
        subst hu
        simp only [frozen_ite]
        split
        · rename_i hF
          rw [spec_ok]
          exact Or.inr ⟨hacc, Or.inr ⟨p, hp, Or.inl ⟨hF, rfl⟩⟩⟩
        · rename_i hF
          have hl : id.slot.val < self.patches.val.length := (List.getElem?_eq_some_iff.mp hp.2).1
          apply spec_bind (alloc.vec.Vec.index_usize_spec self.patches id.slot hl)
          intro p1 hp1
          have hpp : p1 = p := by
            have := hp.2
            rw [List.getElem?_eq_getElem hl] at this
            rw [hp1]; exact Option.some.inj this
          subst hpp
          apply spec_bind (stage_ne_spec p1.stage shatter.Stage.Parked)
          intro b hb
          by_cases hbt : b = true
          · simp only [hbt, ↓reduceIte]
            rw [spec_ok]
            exact Or.inr ⟨hacc, Or.inr ⟨p1, hp, Or.inr (Or.inl ⟨hF, hb.mp hbt, rfl⟩)⟩⟩
          · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
            have hpk : p1.stage = shatter.Stage.Parked := by
              by_contra hne; exact hbt (hb.mpr hne)
            apply spec_bind (hide_loop_spec self.walkers self.patches id.slot p1 hp.2 0#usize)
            intro ws hws
            simp only [alloc.vec.Vec.index_mut_slice_index]
            apply spec_bind (alloc.vec.Vec.index_mut_usize_spec self.patches id.slot hl)
            rintro ⟨p2, back⟩ ⟨hp2, hback⟩
            erw [spec_ok]
            have hp2' : p2 = p1 := by
              have := hp.2
              rw [List.getElem?_eq_getElem hl] at this
              rw [hp2]; exact Option.some.inj this
            subst hp2'
            subst hback
            refine Or.inr ⟨hacc, Or.inr ⟨p2, hp, Or.inr (Or.inr ⟨hF, hpk, v, ws, hv, ⟨hws.1, fun i => ?_⟩, rfl⟩)⟩⟩
            rw [hws.2 i]; simp
  · intro res hn hr
    exact Or.inl ⟨hn, hr⟩

/-! ### `scatter_patch` -/

/-- `U64::checked_add`: a sum within range, or `None` when it overflows. -/
theorem u64_checked_add (x y : Std.U64) :
    (x.val + y.val ≤ U64.max ∧ ∃ z : Std.U64, U64.checked_add x y = some z ∧
      z.val = x.val + y.val) ∨
    (U64.max < x.val + y.val ∧ U64.checked_add x y = none) := by
  have hc := U64.checked_add_bv_spec x y
  cases hco : U64.checked_add x y with
  | none =>
    rw [hco] at hc
    simp at hc
    exact Or.inr ⟨by omega, rfl⟩
  | some z =>
    rw [hco] at hc
    simp at hc
    exact Or.inl ⟨by omega, z, rfl, by omega⟩

/-- The scene after a successful `scatter_patch`. -/
def scatteredScene (self : scene.Scene) (id : shatter.PatchId) (p : shatter.Patch)
    (u : Std.U64) (v : Std.U64) : scene.Scene :=
  { self with
    patches := alloc.vec.Vec.set self.patches id.slot { p with stage := shatter.Stage.Scattered u }
    stamp := bumped self v }

theorem scatter_patch_spec (self : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
    (duration : Std.U64) :
    scene.Scene.scatter_patch self stamp id duration ⦃ res =>
      (¬ StampAccepts self stamp ∧ StampRejects self stamp res) ∨
      (StampAccepts self stamp ∧
        ((∃ e, slotVerdict self id = .Err e ∧ res = (.Err e, self)) ∨
         ∃ p, SlotOk self id p ∧
          ((Frozen self ∧ res = (.Err topology.Error.InvalidTransition, self)) ∨
           (¬ Frozen self ∧ p.stage ≠ shatter.Stage.Hidden ∧
              res = (.Err topology.Error.InvalidTransition, self)) ∨
           (¬ Frozen self ∧ p.stage = shatter.Stage.Hidden ∧ duration.val = 0 ∧
              res = (.Err topology.Error.InvalidTransition, self)) ∨
           (¬ Frozen self ∧ p.stage = shatter.Stage.Hidden ∧ duration.val ≠ 0 ∧
              U64.max < self.clock.val + duration.val ∧
              res = (.Err topology.Error.Overflow, self)) ∨
           (¬ Frozen self ∧ p.stage = shatter.Stage.Hidden ∧ duration.val ≠ 0 ∧
              self.clock.val + duration.val ≤ U64.max ∧
              ∃ (v u : Std.U64), v.val = self.stamp.revision.val + 1 ∧
                u.val = self.clock.val + duration.val ∧
                res = (.Ok (bumped self v), scatteredScene self id p u v))))) ⦄ := by
  unfold scene.Scene.scatter_patch
  apply stamp_gate
  · intro v hv hacc
    apply spec_bind (patch_slot_spec self id)
    intro r1 hr1
    cases r1 with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, spec_ok]
      exact Or.inr ⟨hacc, Or.inl ⟨e, hr1.symm, rfl⟩⟩
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      rcases slotVerdict_cases self id with ⟨e, he⟩ | ⟨p, hp, _⟩
      · rw [he] at hr1; simp at hr1
      · have hu : u = id.slot := by rw [hp.1] at hr1; simpa using hr1.symm.symm
        subst hu
        simp only [frozen_ite]
        split
        · rename_i hF
          rw [spec_ok]
          exact Or.inr ⟨hacc, Or.inr ⟨p, hp, Or.inl ⟨hF, rfl⟩⟩⟩
        · rename_i hF
          have hl : id.slot.val < self.patches.val.length := (List.getElem?_eq_some_iff.mp hp.2).1
          apply spec_bind (alloc.vec.Vec.index_usize_spec self.patches id.slot hl)
          intro p1 hp1
          have hpp : p1 = p := by
            have := hp.2
            rw [List.getElem?_eq_getElem hl] at this
            rw [hp1]; exact Option.some.inj this
          subst hpp
          apply spec_bind (stage_ne_spec p1.stage shatter.Stage.Hidden)
          intro b hb
          by_cases hbt : b = true
          · simp only [hbt, ↓reduceIte]
            rw [spec_ok]
            exact Or.inr ⟨hacc, Or.inr ⟨p1, hp, Or.inr (Or.inl ⟨hF, hb.mp hbt, rfl⟩)⟩⟩
          · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
            have hpk : p1.stage = shatter.Stage.Hidden := by
              by_contra hne; exact hbt (hb.mpr hne)
            by_cases hd : duration = 0#u64
            · simp only [hd, ↓reduceIte]
              rw [spec_ok]
              exact Or.inr ⟨hacc, Or.inr ⟨p1, hp, Or.inr (Or.inr (Or.inl
                ⟨hF, hpk, by simp, rfl⟩))⟩⟩
            · simp only [hd, ↓reduceIte]
              have hd' : duration.val ≠ 0 := fun h => hd (UScalar.eq_of_val_eq (by simpa using h))
              rcases u64_checked_add self.clock duration with ⟨hle, z, hz, hzv⟩ | ⟨hgt, hn⟩
              · simp only [lift, hz, Std.bind_ok, core.option.Option.ok_or]
                simp only [alloc.vec.Vec.index_mut_slice_index]
                apply spec_bind (alloc.vec.Vec.index_mut_usize_spec self.patches id.slot hl)
                rintro ⟨p2, back⟩ ⟨hp2, hback⟩
                erw [spec_ok]
                have hp2' : p2 = p1 := by
                  have := hp.2
                  rw [List.getElem?_eq_getElem hl] at this
                  rw [hp2]; exact Option.some.inj this
                subst hp2'
                subst hback
                exact Or.inr ⟨hacc, Or.inr ⟨p2, hp, Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨hF, hpk, hd', hle, v, z, hv, hzv, rfl⟩)))⟩⟩
              · simp only [lift, hn, Std.bind_ok, core.option.Option.ok_or,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  core.convert.FromSame.from, bind_tc_ok]
                rw [spec_ok]
                exact Or.inr ⟨hacc, Or.inr ⟨p1, hp, Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨hF, hpk, hd', hgt, rfl⟩)))⟩⟩
  · intro res hn hr
    exact Or.inl ⟨hn, hr⟩

end Labyrinth
