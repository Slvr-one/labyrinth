module
public import LabyrinthCore.SceneShatterStages

/-! Shatter (S6), part 4: `Scene::begin_shatter`. After the stamp check it rejects an empty cell
list (`InvalidSize`), a frozen scene (`InvalidTransition`), then walks the cells in order: for cell
`k` it first asks `admission` (`InvalidIndex` outside the layout, `Occupied` inside a live patch),
then rejects a cell equal to an earlier one (`InvalidIndex`). The first failure wins. With every cell
admitted it takes the first idle patch slot (`InsufficientWorkspace` when none), writes the cell
set, serial and stage `Draining`, runs `drain_patches` and publishes revision and trail revision. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

open Classical in
/-- What the duplicate scan for cell `i` leaves, starting from entry `j` with status `st`. -/
noncomputable def dupFinal (cells : List Std.Usize) (i : Nat)
    (st : core.result.Result Unit topology.Error) (j : Nat) :
    core.result.Result Unit topology.Error :=
  match st with
  | .Err e => .Err e
  | .Ok _ =>
    if ∃ j', j ≤ j' ∧ j' < i ∧ cells[j']? = cells[i]? then .Err topology.Error.InvalidIndex
    else .Ok ()

theorem begin_dup_spec (cells : Slice Std.Usize) (i : Std.Usize)
    (hi : i.val < cells.val.length) (status : core.result.Result Unit topology.Error)
    (j0 : Std.Usize) :
    scene.Scene.begin_shatter_loop0_loop0 cells status i j0 ⦃ r =>
      r = dupFinal cells.val i.val status j0.val ⦄ := by
  unfold scene.Scene.begin_shatter_loop0_loop0
  refine loop.spec_decr_nat
    (fun x : (core.result.Result Unit topology.Error) × Std.Usize => i.val - x.2.val)
    (fun x => dupFinal cells.val i.val x.1 x.2.val = dupFinal cells.val i.val status j0.val)
    (fun r => r = dupFinal cells.val i.val status j0.val) _ (status, j0) ?_ rfl
  rintro ⟨st, j⟩ hinv
  dsimp only at hinv
  unfold scene.Scene.begin_shatter_loop0_loop0.body
  by_cases hj : j < i
  · simp only [hj, ↓reduceIte]
    cases st with
    | Err e =>
      simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte, spec_ok]
      simpa [dupFinal] using hinv
    | Ok u =>
      cases u
      simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte]
      have hjl : j.val < cells.val.length := by have : j.val < i.val := hj; omega
      apply spec_bind (Slice.index_usize_spec cells j hjl)
      intro i1 hi1
      apply spec_bind (Slice.index_usize_spec cells i hi)
      intro i2 hi2
      by_cases heq : i1 = i2
      · simp only [heq, ↓reduceIte, Std.bind_ok]
        apply spec_bind (Usize.add_spec (x := j) (y := 1#usize) (by scalar_tac))
        intro j1 hj1
        rw [spec_ok]
        have hj1v : j1.val = j.val + 1 := by simpa using hj1
        have hjv : j.val < i.val := hj
        have hdup : cells.val[j.val]? = cells.val[i.val]? := by
          rw [List.getElem?_eq_getElem hjl, List.getElem?_eq_getElem hi]
          simp [← hi1, ← hi2, heq]
        refine ⟨?_, by simp only [hj1v]; omega⟩
        rw [← hinv]
        have hex : ∃ j', j.val ≤ j' ∧ j' < i.val ∧ cells.val[j']? = cells.val[i.val]? :=
          ⟨j.val, le_refl _, hjv, hdup⟩
        simp [dupFinal, hex]
      · simp only [heq, ↓reduceIte, Std.bind_ok]
        apply spec_bind (Usize.add_spec (x := j) (y := 1#usize) (by scalar_tac))
        intro j1 hj1
        rw [spec_ok]
        have hj1v : j1.val = j.val + 1 := by simpa using hj1
        have hjv : j.val < i.val := hj
        have hnd : cells.val[j.val]? ≠ cells.val[i.val]? := by
          intro h
          rw [List.getElem?_eq_getElem hjl, List.getElem?_eq_getElem hi] at h
          apply heq
          rw [hi1, hi2]
          exact Option.some.inj h
        refine ⟨?_, by simp only [hj1v]; omega⟩
        rw [← hinv]
        have : (∃ j', j1.val ≤ j' ∧ j' < i.val ∧ cells.val[j']? = cells.val[i.val]?) ↔
            (∃ j', j.val ≤ j' ∧ j' < i.val ∧ cells.val[j']? = cells.val[i.val]?) := by
          constructor
          · rintro ⟨j', h1, h2, h3⟩; exact ⟨j', by omega, h2, h3⟩
          · rintro ⟨j', h1, h2, h3⟩
            have : j' ≠ j.val := fun h => hnd (h ▸ h3)
            exact ⟨j', by omega, h2, h3⟩
        simp only [dupFinal]
        by_cases h : ∃ j', j.val ≤ j' ∧ j' < i.val ∧ cells.val[j']? = cells.val[i.val]?
        · simp [h, this.mpr h]
        · have h' : ¬ ∃ j', j1.val ≤ j' ∧ j' < i.val ∧ cells.val[j']? = cells.val[i.val]? :=
            fun x => h (this.mp x)
          simp [h, h']
  · simp only [hj, ↓reduceIte, spec_ok]
    rw [← hinv]
    cases st with
    | Err e => simp [dupFinal]
    | Ok u =>
      cases u
      have : ¬ ∃ j', j.val ≤ j' ∧ j' < i.val ∧ cells.val[j']? = cells.val[i.val]? := by
        rintro ⟨j', h1, h2, _⟩
        have : ¬ j.val < i.val := hj
        omega
      simp [dupFinal, this]

/-- What the scan answers for cell `c` standing at index `k` of the list: its admission verdict,
then (if admitted) the duplicate check against the earlier entries. -/
noncomputable def cellVerdict (self : scene.Scene) (cs : List Std.Usize) (k : Nat) (c : Std.Usize) :
    core.result.Result Unit topology.Error :=
  dupFinal cs k (admissionVerdict self c.val) 0

/-- The scan after the first `n` cells: the first failure, or success. -/
noncomputable def verdictUpTo (self : scene.Scene) (cs : List Std.Usize) :
    Nat → core.result.Result Unit topology.Error
  | 0 => .Ok ()
  | n + 1 =>
    match verdictUpTo self cs n with
    | .Err e => .Err e
    | .Ok _ =>
      match cs[n]? with
      | some c => cellVerdict self cs n c
      | none => .Ok ()

theorem verdictUpTo_err (self : scene.Scene) (cs : List Std.Usize) (n m : Nat) (e : topology.Error)
    (h : verdictUpTo self cs n = .Err e) (hnm : n ≤ m) : verdictUpTo self cs m = .Err e := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => simp [verdictUpTo, ih]

theorem begin_shatter_scan_spec (sc : scene.Scene) (cells : Slice Std.Usize) :
    scene.Scene.begin_shatter_loop0 sc.layout sc.tree sc.work sc.routes sc.required sc.phases
      sc.next_phases sc.holds sc.walkers sc.patches sc.stamp sc.clock sc.wall sc.reanchor
      sc.suspended sc.inactive sc.latest_request sc.pending sc.trail_revision cells
      (core.result.Result.Ok ()) 0#usize ⦃ r => r = verdictUpTo sc cells.val cells.val.length ⦄ := by
  obtain ⟨l, t, w, v, v1, v2, v3, v4, v5, v6, s, i, i1, b, b1, b2, i2, o, i3⟩ := sc
  unfold scene.Scene.begin_shatter_loop0
  refine loop.spec_decr_nat
    (fun x : (core.result.Result Unit topology.Error) × Std.Usize =>
      cells.val.length - x.2.val)
    (fun x => x.2.val ≤ cells.val.length ∧
      x.1 = verdictUpTo ⟨l, t, w, v, v1, v2, v3, v4, v5, v6, s, i, i1, b, b1, b2, i2, o, i3⟩
        cells.val x.2.val)
    (fun r => r = verdictUpTo ⟨l, t, w, v, v1, v2, v3, v4, v5, v6, s, i, i1, b, b1, b2, i2, o, i3⟩
        cells.val cells.val.length) _ (core.result.Result.Ok (), 0#usize) ?_ ⟨by simp, rfl⟩
  rintro ⟨st, k⟩ ⟨hk, hst⟩
  dsimp only at hk hst
  unfold scene.Scene.begin_shatter_loop0.body
  by_cases hlt : k < Slice.len cells
  · have hkl : k.val < cells.val.length := by simpa [Slice.len] using hlt
    simp only [hlt, ↓reduceIte]
    cases st with
    | Err e =>
      simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact (verdictUpTo_err _ _ _ _ e hst.symm hk).symm
    | Ok u =>
      cases u
      simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte]
      apply spec_bind (Slice.index_usize_spec cells k hkl)
      intro c hc
      apply spec_bind (admission_spec _ c)
      intro st1 hst1
      apply spec_bind (begin_dup_spec cells k hkl st1 0#usize)
      intro st2 hst2
      apply spec_bind (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac))
      intro k1 hk1
      rw [spec_ok]
      dsimp only
      have hk1v : k1.val = k.val + 1 := by simpa using hk1
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hk1v]
      simp only [verdictUpTo]
      rw [← hst]
      simp only [List.getElem?_eq_getElem hkl, hc, cellVerdict, hst2, hst1]
      simp
  · simp only [hlt, ↓reduceIte, spec_ok]
    have : k.val = cells.val.length := by
      have : ¬ k.val < cells.val.length := by simpa [Slice.len] using hlt
      omega
    rw [hst, this]

/-- The slot search stops at the first idle patch, or at the end of the list. -/
theorem begin_slot_spec (v : alloc.vec.Vec shatter.Patch) (s0 : Std.Usize)
    (hs0 : s0.val ≤ v.val.length) :
    scene.Scene.begin_shatter_loop1 v s0 ⦃ r =>
      r.val ≤ v.val.length ∧
      (∀ j, s0.val ≤ j → j < r.val → ∃ p, v.val[j]? = some p ∧ p.stage ≠ shatter.Stage.Idle) ∧
      (r.val < v.val.length → ∃ p, v.val[r.val]? = some p ∧ p.stage = shatter.Stage.Idle) ⦄ := by
  unfold scene.Scene.begin_shatter_loop1
  refine loop.spec_decr_nat (fun x : Std.Usize => v.val.length - x.val)
    (fun x => s0.val ≤ x.val ∧ x.val ≤ v.val.length ∧
      ∀ j, s0.val ≤ j → j < x.val → ∃ p, v.val[j]? = some p ∧ p.stage ≠ shatter.Stage.Idle)
    (fun r : Std.Usize => r.val ≤ v.val.length ∧
      (∀ j, s0.val ≤ j → j < r.val → ∃ p, v.val[j]? = some p ∧ p.stage ≠ shatter.Stage.Idle) ∧
      (r.val < v.val.length → ∃ p, v.val[r.val]? = some p ∧ p.stage = shatter.Stage.Idle))
    _ s0 ?_ ⟨le_refl _, hs0, fun j h1 h2 => by omega⟩
  intro s ⟨h1, h2, h3⟩
  unfold scene.Scene.begin_shatter_loop1.body
  by_cases hlt : s < alloc.vec.Vec.len v
  · have hl : s.val < v.val.length := by simpa using hlt
    simp only [hlt, ↓reduceIte, alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec v s hl)
    intro p hp
    apply spec_bind (stage_ne_spec p.stage shatter.Stage.Idle)
    intro b hb
    have hpv : v.val[s.val]? = some p := by rw [List.getElem?_eq_getElem hl, hp]
    by_cases hbt : b = true
    · simp only [hbt, ↓reduceIte]
      apply spec_bind (Usize.add_spec (x := s) (y := 1#usize) (by scalar_tac))
      intro s1 hs1
      rw [spec_ok]
      dsimp only
      have hs1v : s1.val = s.val + 1 := by simpa using hs1
      refine ⟨⟨by omega, by omega, fun j hj1 hj2 => ?_⟩, by omega⟩
      by_cases hjs : j = s.val
      · subst hjs; exact ⟨p, hpv, hb.mp hbt⟩
      · exact h3 j hj1 (by omega)
    · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
      rw [spec_ok]
      refine ⟨h2, h3, fun _ => ⟨p, hpv, ?_⟩⟩
      by_contra hne; exact hbt (hb.mpr hne)
  · simp only [hlt, ↓reduceIte, spec_ok]
    have : v.val.length ≤ s.val := by simpa using hlt
    exact ⟨h2, h3, fun h => by omega⟩

/-- Entry `c` of the patch's cell set is marked: some cell of the list from index `i0` on names it. -/
def Named (cs : List Std.Usize) (i0 : Nat) (c : Nat) : Prop :=
  ∃ i, i0 ≤ i ∧ i < cs.length ∧ (cs[i]?).map (fun x : Std.Usize => x.val) = some c

open Classical in
/-- The cell-writing loop marks every named cell of the patch and changes nothing else. -/
theorem begin_mark_spec (v : alloc.vec.Vec shatter.Patch) (cells : Slice Std.Usize)
    (slot : Std.Usize) (p : shatter.Patch) (hp : v.val[slot.val]? = some p)
    (hc : ∀ i, i < cells.val.length → ∀ c, (cells.val[i]?).map (fun x : Std.Usize => x.val) = some c →
      c < p.cells.val.length) (i0 : Std.Usize) :
    scene.Scene.begin_shatter_loop2 v cells slot i0 ⦃ r =>
      r.val.length = v.val.length ∧ (∀ q, q ≠ slot.val → r.val[q]? = v.val[q]?) ∧
      ∃ p', r.val[slot.val]? = some p' ∧ p'.serial = p.serial ∧ p'.stage = p.stage ∧
        p'.cells.val.length = p.cells.val.length ∧
        ∀ c, p'.cells.val[c]? = if Named cells.val i0.val c then some true else p.cells.val[c]? ⦄ := by
  classical
  unfold scene.Scene.begin_shatter_loop2
  refine loop.spec_decr_nat
    (fun x : alloc.vec.Vec shatter.Patch × Std.Usize => cells.val.length - x.2.val)
    (fun x => i0.val ≤ x.2.val ∧ x.1.val.length = v.val.length ∧ (∀ q, q ≠ slot.val → x.1.val[q]? = v.val[q]?) ∧
      ∃ p', x.1.val[slot.val]? = some p' ∧ p'.serial = p.serial ∧ p'.stage = p.stage ∧
        p'.cells.val.length = p.cells.val.length ∧
        ∀ c, p'.cells.val[c]? =
          if (∃ i, i0.val ≤ i ∧ i < x.2.val ∧ (cells.val[i]?).map (fun x : Std.Usize => x.val) = some c)
            then some true else p.cells.val[c]?)
    (fun r : alloc.vec.Vec shatter.Patch => r.val.length = v.val.length ∧
      (∀ q, q ≠ slot.val → r.val[q]? = v.val[q]?) ∧
      ∃ p', r.val[slot.val]? = some p' ∧ p'.serial = p.serial ∧ p'.stage = p.stage ∧
        p'.cells.val.length = p.cells.val.length ∧
        ∀ c, p'.cells.val[c]? = if Named cells.val i0.val c then some true else p.cells.val[c]?)
    _ (v, i0) ?_ ⟨le_refl _, rfl, fun _ _ => rfl, p, hp, rfl, rfl, rfl, fun c => by
      have : ¬ ∃ i, i0.val ≤ i ∧ i < i0.val ∧ (cells.val[i]?).map (fun x : Std.Usize => x.val) = some c := by
        rintro ⟨i, h1, h2, _⟩; omega
      simp only [this, ↓reduceIte]⟩
  rintro ⟨y, i⟩ ⟨hi0, hl, hq, p', hp', hser, hst, hcl, hcells⟩
  dsimp only at hi0 hl hq hp' hcells
  unfold scene.Scene.begin_shatter_loop2.body
  have hsl : slot.val < y.val.length := (List.getElem?_eq_some_iff.mp hp').1
  by_cases hlt : i < Slice.len cells
  · have hil : i.val < cells.val.length := by simpa [Slice.len] using hlt
    simp only [hlt, ↓reduceIte, alloc.vec.Vec.index_mut_slice_index]
    apply spec_bind (alloc.vec.Vec.index_mut_usize_spec y slot hsl)
    rintro ⟨p1, back⟩ ⟨hp1, hback⟩
    apply spec_bind (Slice.index_usize_spec cells i hil)
    intro i2 hi2
    have hp1e : p1 = p' := by
      rw [hp1, List.getElem?_eq_getElem hsl] at *; exact Option.some.inj hp'
    subst hp1e
    have hi2l : i2.val < p1.cells.val.length := by
      have := hc i.val hil i2.val (by rw [List.getElem?_eq_getElem hil, hi2]; rfl)
      omega
    apply spec_bind (alloc.vec.Vec.index_mut_usize_spec p1.cells i2 hi2l)
    rintro ⟨x, back1⟩ ⟨hx, hback1⟩
    apply spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    intro i3 hi3
    have hi3v : i3.val = i.val + 1 := by simpa using hi3
    rw [spec_ok]
    dsimp only
    subst hback hback1
    have hi2c : (cells.val[i.val]?).map (fun x : Std.Usize => x.val) = some i2.val := by
      rw [List.getElem?_eq_getElem hil, hi2]; rfl
    refine ⟨⟨by omega, ?_, ?_, ?_⟩, by omega⟩
    · simp [hl, alloc.vec.Vec.set_val_eq]
    · intro q hqs
      rw [alloc.vec.Vec.set_val_eq, List.getElem?_set_ne (Ne.symm hqs)]
      exact hq q hqs
    · refine ⟨{ p1 with cells := alloc.vec.Vec.set p1.cells i2 true }, ?_, hser, hst, ?_, ?_⟩
      · rw [alloc.vec.Vec.set_val_eq, List.getElem?_set_self hsl]
      · simp [alloc.vec.Vec.set_val_eq, hcl]
      · intro c
        simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set]
        by_cases hcc : i2.val = c
        · have hex : ∃ j, i0.val ≤ j ∧ j < i3.val ∧
              (cells.val[j]?).map (fun x : Std.Usize => x.val) = some c :=
            ⟨i.val, hi0, by omega, by rw [hi2c, hcc]⟩
          have hcl2 : c < p1.cells.val.length := hcc ▸ hi2l
          simp only [hcc, hcl2, hex, ↓reduceIte]
        · have hiff : (∃ j, i0.val ≤ j ∧ j < i3.val ∧
              (cells.val[j]?).map (fun x : Std.Usize => x.val) = some c) ↔
              (∃ j, i0.val ≤ j ∧ j < i.val ∧
              (cells.val[j]?).map (fun x : Std.Usize => x.val) = some c) := by
            constructor
            · rintro ⟨j, h1, h2, h3⟩
              have : j ≠ i.val := by
                rintro rfl
                rw [hi2c] at h3
                exact hcc (Option.some.inj h3)
              exact ⟨j, h1, by omega, h3⟩
            · rintro ⟨j, h1, h2, h3⟩; exact ⟨j, h1, by omega, h3⟩
          have hcc' : ¬ i2.val = c := hcc
          simp only [hcc', ↓reduceIte]
          rw [hcells c]
          simp only [hiff]
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hge : cells.val.length ≤ i.val := by simpa [Slice.len] using hlt
    refine ⟨hl, hq, p', hp', hser, hst, hcl, fun c => ?_⟩
    rw [hcells c]
    have hiff : (∃ j, i0.val ≤ j ∧ j < i.val ∧
          (cells.val[j]?).map (fun x : Std.Usize => x.val) = some c) ↔ Named cells.val i0.val c := by
      constructor
      · rintro ⟨j, h1, h2, h3⟩
        have : j < cells.val.length := by
          by_contra hj
          rw [List.getElem?_eq_none (by omega)] at h3
          simp at h3
        exact ⟨j, h1, this, h3⟩
      · rintro ⟨j, h1, h2, h3⟩; exact ⟨j, h1, by omega, h3⟩
    simp only [hiff]

/-! ### The whole of `begin_shatter` -/

open Classical in
/-- `begin_shatter` tests suspended, inactive, pending, in that order. -/
theorem frozen_ite2 {α : Type _} (self : scene.Scene) (a b : α) :
    (if self.suspended = true then a else
      if self.inactive = true then a else
        if core.option.Option.is_some self.pending = true then a else b) =
      if Frozen self then a else b := by
  unfold Frozen
  cases hq : self.pending <;> by_cases h1 : self.suspended = true <;>
    by_cases h3 : self.inactive = true <;> simp [core.option.Option.is_some, h1, h3]

theorem cellVerdict_ok {self : scene.Scene} {cs : List Std.Usize} {k : Nat} {c : Std.Usize}
    (h : cellVerdict self cs k c = .Ok ()) :
    admissionVerdict self c.val = .Ok () ∧
      ¬ ∃ j, j < k ∧ cs[j]? = cs[k]? := by
  unfold cellVerdict at h
  cases ha : admissionVerdict self c.val with
  | Err e => rw [ha] at h; simp [dupFinal] at h
  | Ok u =>
    cases u
    rw [ha] at h
    refine ⟨rfl, ?_⟩
    rintro ⟨j, hj, hjc⟩
    simp only [dupFinal] at h
    have : ∃ j', 0 ≤ j' ∧ j' < k ∧ cs[j']? = cs[k]? := ⟨j, Nat.zero_le _, hj, hjc⟩
    simp at h
    exact h j hj hjc

theorem verdictUpTo_ok {self : scene.Scene} {cs : List Std.Usize} {n : Nat}
    (h : verdictUpTo self cs n = .Ok ()) (hn : n ≤ cs.length) :
    ∀ k, k < n → ∃ c, cs[k]? = some c ∧ admissionVerdict self c.val = .Ok () ∧
      ∀ j, j < k → cs[j]? ≠ cs[k]? := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    unfold verdictUpTo at h
    cases hv : verdictUpTo self cs n with
    | Err e => rw [hv] at h; simp at h
    | Ok u =>
      cases u
      rw [hv] at h
      by_cases hkn : k = n
      · subst hkn
        cases hc : cs[k]? with
        | none => exact absurd hc (by rw [List.getElem?_eq_getElem (by omega)]; simp)
        | some c =>
          rw [hc] at h
          simp only at h
          obtain ⟨h1, h2⟩ := cellVerdict_ok h
          exact ⟨c, rfl, h1, fun j hj hjc => h2 ⟨j, hj, hjc.trans hc.symm⟩⟩
      · exact ih hv (by omega) k (by omega)

open Classical in
/-- The patch `begin_shatter` writes into the idle slot: the new serial, stage `Draining`, and a cell
set that holds exactly the named cells (every other entry of the old length is `false`). -/
def FreshPatch (old : shatter.Patch) (cells : Slice Std.Usize) (v : Std.U64) (np : shatter.Patch) :
    Prop :=
  np.serial = v ∧ np.stage = shatter.Stage.Draining ∧
    np.cells.val.length = old.cells.val.length ∧
    ∀ c, np.cells.val[c]? =
      if Named cells.val 0 c then some true else
        if c < old.cells.val.length then some false else none

/-- What `drain_patches` leaves on a scene's walkers and patches (`drain_patches_spec`). -/
def DrainOf (x : scene.Scene) (cw : alloc.vec.Vec walker.Walker)
    (cp : alloc.vec.Vec shatter.Patch) : Prop :=
  cw.val.length = x.walkers.val.length ∧ cp.val.length = x.patches.val.length ∧
  (∀ q, q < x.patches.val.length → ∃ pq, x.patches.val[q]? = some pq ∧
    cp.val[q]? = some (drainP x.walkers.val pq)) ∧
  (∀ i, i < x.walkers.val.length → ∃ o, x.walkers.val[i]? = some o ∧
    cw.val[i]? = some (drainW x.walkers.val x.patches.val x.patches.val.length o))

/-- The scene after a successful `begin_shatter` into `slot`. -/
def shatteredScene (self : scene.Scene) (cw : alloc.vec.Vec walker.Walker)
    (cp : alloc.vec.Vec shatter.Patch) (v : Std.U64) : scene.Scene :=
  { self with walkers := cw, patches := cp, stamp := bumped self v, trail_revision := v }

/-- The patch list `drain_patches` starts from after the new patch went into `slot`. -/
def shatterStart (self : scene.Scene) (slot : Std.Usize) (np : shatter.Patch) : scene.Scene :=
  { self with patches := alloc.vec.Vec.set self.patches slot np }

/-- Patches every cell of the layout carries room for (true of every scene `Scene::new` builds). -/
def PatchRoom (self : scene.Scene) : Prop :=
  ∀ p ∈ self.patches.val, p.cells.val.length = self.layout.cells.val.length

/-- With every cell admitted: no idle slot, or the first idle slot takes the new patch. -/
def BsPlaced (self : scene.Scene) (cells : Slice Std.Usize)
    (res : core.result.Result shatter.PatchId topology.Error × scene.Scene) : Prop :=
  ((∀ p ∈ self.patches.val, p.stage ≠ shatter.Stage.Idle) ∧
    res = (.Err topology.Error.InsufficientWorkspace, self)) ∨
  ∃ (slot : Std.Usize) (old np : shatter.Patch) (v : Std.U64)
    (cw : alloc.vec.Vec walker.Walker) (cp : alloc.vec.Vec shatter.Patch),
    (∀ j, j < slot.val → ∃ p, self.patches.val[j]? = some p ∧ p.stage ≠ shatter.Stage.Idle) ∧
    self.patches.val[slot.val]? = some old ∧ old.stage = shatter.Stage.Idle ∧
    v.val = self.stamp.revision.val + 1 ∧ FreshPatch old cells v np ∧
    DrainOf (shatterStart self slot np) cw cp ∧
    res = (.Ok { epoch := self.stamp.epoch, slot := slot, serial := v },
      shatteredScene self cw cp v)

/-- After the stamp, the empty and frozen checks: the cell scan, then the slot. -/
def BsChecked (self : scene.Scene) (cells : Slice Std.Usize)
    (res : core.result.Result shatter.PatchId topology.Error × scene.Scene) : Prop :=
  (∃ e, verdictUpTo self cells.val cells.val.length = .Err e ∧ res = (.Err e, self)) ∨
  (verdictUpTo self cells.val cells.val.length = .Ok () ∧ BsPlaced self cells res)

/-- `begin_shatter`, error by error. -/
def BsOutcome (self : scene.Scene) (stamp : walker.Stamp) (cells : Slice Std.Usize)
    (res : core.result.Result shatter.PatchId topology.Error × scene.Scene) : Prop :=
  (¬ StampAccepts self stamp ∧ StampRejects self stamp res) ∨
  (StampAccepts self stamp ∧
    ((cells.val = [] ∧ res = (.Err topology.Error.InvalidSize, self)) ∨
     (cells.val ≠ [] ∧ Frozen self ∧ res = (.Err topology.Error.InvalidTransition, self)) ∨
     (cells.val ≠ [] ∧ ¬ Frozen self ∧ BsChecked self cells res)))

theorem begin_shatter_spec (self : scene.Scene) (stamp : walker.Stamp) (cells : Slice Std.Usize)
    (hcs : CrossAtSource self.walkers.val) (hroom : PatchRoom self) :
    scene.Scene.begin_shatter self stamp cells ⦃ res => BsOutcome self stamp cells res ⦄ := by
  classical
  unfold scene.Scene.begin_shatter
  apply stamp_gate
  · intro v hv hacc
    simp only [core.slice.Slice.is_empty, Std.bind_ok]
    have hem' : cells.length = 0 ↔ cells.val = [] := by
      simp [Slice.length]
    by_cases hem : cells.length = 0
    · simp only [hem, decide_true, ↓reduceIte]
      rw [spec_ok]
      exact Or.inr ⟨hacc, Or.inl ⟨hem'.mp hem, rfl⟩⟩
    · simp only [hem, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hne : cells.val ≠ [] := fun h => hem (hem'.mpr h)
      simp only [frozen_ite2]
      split
      · rename_i hF
        rw [spec_ok]
        exact Or.inr ⟨hacc, Or.inr (Or.inl ⟨hne, hF, rfl⟩)⟩
      · rename_i hF
        apply spec_bind (begin_shatter_scan_spec self cells)
        intro status hstat
        cases status with
        | Err e =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok]
          rw [spec_ok]
          exact Or.inr ⟨hacc, Or.inr (Or.inr ⟨hne, hF, Or.inl ⟨e, hstat.symm, rfl⟩⟩)⟩
        | Ok u =>
          cases u
          simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
          apply spec_bind (begin_slot_spec self.patches 0#usize (by simp))
          rintro slot ⟨hle, hnon, hidle⟩
          by_cases hs : slot = alloc.vec.Vec.len self.patches
          · simp only [hs, ↓reduceIte]
            rw [spec_ok]
            have hsv : slot.val = self.patches.val.length := by rw [hs]; simp
            refine Or.inr ⟨hacc, Or.inr (Or.inr ⟨hne, hF, Or.inr ⟨hstat.symm, Or.inl ⟨?_, rfl⟩⟩⟩)⟩
            intro p hp
            obtain ⟨j, hj, hjp⟩ := List.getElem_of_mem hp
            obtain ⟨p', hp', hne'⟩ := hnon j (by simp) (by omega)
            rw [List.getElem?_eq_getElem hj, hjp] at hp'
            cases hp'; exact hne'
          · have hl : slot.val < self.patches.val.length := by
              have : slot.val ≠ self.patches.val.length := fun h => hs (UScalar.eq_of_val_eq (by simpa using h))
              omega
            simp only [hs, ↓reduceIte, alloc.vec.Vec.index_mut_slice_index]
            apply spec_bind (alloc.vec.Vec.index_mut_usize_spec self.patches slot hl)
            rintro ⟨p, back⟩ ⟨hp, hback⟩
            obtain ⟨p0, hp0, hidl⟩ := hidle hl
            have hpp : p = p0 := by
              rw [hp]; rw [List.getElem?_eq_getElem hl] at hp0; exact Option.some.inj hp0
            subst hpp
            subst hback
            simp only [lift, Std.bind_ok, alloc.vec.Vec.deref_mut]
            apply spec_bind (core.slice.Slice.fill.spec core.clone.CloneBool p.cells.slice false
              (by simp [core.clone.impls.CloneBool.clone, spec_ok]))
            intro s1 hs1
            have hroomp : p.cells.val.length = self.layout.cells.val.length :=
              hroom p (List.mem_of_getElem? hp0)
            have hs1l : s1.val.length = p.cells.val.length := by
              exact hs1.1
            have hverd : verdictUpTo self cells.val cells.val.length = .Ok () := hstat.symm
            have hall := verdictUpTo_ok hverd (le_refl _)
            have hpf : (self.patches.set slot
                { serial := p.serial, stage := p.stage, cells := (⟨s1⟩ : alloc.vec.Vec Bool) }).val[slot.val]?
                = some { serial := p.serial, stage := p.stage, cells := (⟨s1⟩ : alloc.vec.Vec Bool) } := by
              rw [alloc.vec.Vec.set_val_eq, List.getElem?_set_self hl]
            apply spec_bind (begin_mark_spec _ cells slot _ hpf ?_ 0#usize)
            · rintro v2 ⟨hl2, hq2, p', hp', hser, hst, hcl, hcells⟩
              have h0 : (0#usize).val = 0 := rfl
              simp only [h0] at hcells
              simp only [alloc.vec.Vec.set_val_eq, List.length_set] at hl2
              have hsl2 : slot.val < v2.val.length := (List.getElem?_eq_some_iff.mp hp').1
              apply spec_bind (alloc.vec.Vec.index_mut_usize_spec v2 slot hsl2)
              rintro ⟨p1, back1⟩ ⟨hp1, hb1⟩
              have hp1e : p1 = p' := by
                rw [hp1, List.getElem?_eq_getElem hsl2] at *; exact Option.some.inj hp'
              subst hp1e
              subst hb1
              have hsl3 : slot.val < (v2.set slot { serial := v, stage := p1.stage, cells := p1.cells }).val.length := by
                simp only [alloc.vec.Vec.set_val_eq, List.length_set]; exact hsl2
              apply spec_bind (alloc.vec.Vec.index_mut_usize_spec _ slot hsl3)
              rintro ⟨p2, back2⟩ ⟨hp2, hb2⟩
              have hp2e : p2 = { serial := v, stage := p1.stage, cells := p1.cells } := by
                have hq : (v2.set slot { serial := v, stage := p1.stage, cells := p1.cells }).val[slot.val]?
                    = some { serial := v, stage := p1.stage, cells := p1.cells } := by
                  rw [alloc.vec.Vec.set_val_eq, List.getElem?_set_self hsl2]
                apply Option.some.inj
                rw [← hq, List.getElem?_eq_getElem hsl3, hp2]
              subst hp2e
              subst hb2
              apply spec_bind (drain_patches_spec ({ self with patches := alloc.vec.Vec.set (alloc.vec.Vec.set v2 slot { serial := v, stage := p1.stage, cells := p1.cells }) slot { serial := v, stage := shatter.Stage.Draining, cells := p1.cells } } : scene.Scene) hcs)
              rintro self1 ⟨cw, cp, hy, hlw, hlp, hdp, hdw⟩
              subst hy
              rw [spec_ok]
              have hP : ((v2.set slot { serial := v, stage := p1.stage, cells := p1.cells }).set slot
                  { serial := v, stage := shatter.Stage.Draining, cells := p1.cells } : alloc.vec.Vec shatter.Patch) =
                  self.patches.set slot { serial := v, stage := shatter.Stage.Draining, cells := p1.cells } := by
                apply alloc.vec.Vec.ext
                apply List.ext_getElem?
                intro q
                simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set]
                by_cases hqs : slot.val = q
                · subst hqs
                  simp [hsl2, hl]
                · simp only [hqs, ↓reduceIte]
                  rw [hq2 q (Ne.symm hqs), alloc.vec.Vec.set_val_eq, List.getElem?_set]
                  simp only [hqs, ↓reduceIte]
              refine Or.inr ⟨hacc, Or.inr (Or.inr ⟨hne, hF, Or.inr ⟨hstat.symm, Or.inr
                ⟨slot, p, { serial := v, stage := shatter.Stage.Draining, cells := p1.cells }, v, cw, cp,
                  fun j hj => hnon j (by simp) hj, hp0, hidl, hv, ?_, ?_, rfl⟩⟩⟩)⟩
              · refine ⟨rfl, rfl, ?_, fun c => ?_⟩
                · exact hcl.trans hs1l
                · have hcells' : ∀ c, p1.cells.val[c]? =
                      if Named cells.val 0 c then some true else s1.val[c]? := hcells
                  rw [hcells' c, hs1.2, List.getElem?_replicate]
                  rfl
              · unfold DrainOf shatterStart
                dsimp only at hlw hlp hdp hdw ⊢
                rw [hP] at hlp hdp hdw
                exact ⟨hlw, hlp, hdp, hdw⟩
            · intro i hi c hc
              obtain ⟨c', hc', hadm, _⟩ := hall i hi
              rw [hc'] at hc
              simp only [Option.map_some, Option.some.injEq] at hc
              subst hc
              have : c'.val < self.layout.cells.val.length := by
                by_contra hge
                unfold admissionVerdict at hadm
                simp [show self.layout.cells.val.length ≤ c'.val by omega] at hadm
              simp only
              show c'.val < s1.val.length
              omega
  · intro res hn hr
    exact Or.inl ⟨hn, hr⟩

end Labyrinth
