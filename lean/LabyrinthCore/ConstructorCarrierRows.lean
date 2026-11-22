module
public import LabyrinthCore.ConstructorRowValidation
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

def constructorEntryAt (offsets neighbors : alloc.vec.Vec Usize) (cell : Usize)
    (index : Nat) : Prop :=
  ∃ value : Usize, neighbors.val[index]? = some value ∧
    value.val < offsets.val.length - 1 ∧ value ≠ cell ∧
    (∀ j, (offsets.val[cell.val]?.getD 0#usize).val ≤ j → j < index →
      neighbors.val[j]? ≠ some value) ∧
    ∃ j, (offsets.val[value.val]?.getD 0#usize).val ≤ j ∧
      j < (offsets.val[value.val + 1]?.getD 0#usize).val ∧ neighbors.val[j]? = some cell

/-- The extracted inner CSR validation loop accepts exactly the valid entries of its entire row. -/
theorem constructor_csr_row_spec
    (offsets neighbors : alloc.vec.Vec Usize) (cell lo hi : Usize)
    (hsize : 2 ≤ offsets.val.length)
    (hrows : constructorRawRows (alloc.vec.Vec.deref offsets) (alloc.vec.Vec.deref neighbors))
    (hcell : cell.val < offsets.val.length - 1)
    (hlo : offsets.val[cell.val]? = some lo)
    (hhi : offsets.val[cell.val + 1]? = some hi)
    (hordered : lo.val ≤ hi.val) (hstorage : hi.val ≤ neighbors.val.length) :
    WP.spec (topology.Carrier.from_csr_loop1_loop0 offsets neighbors cell (.Ok ()) lo)
      (fun status => status = .Ok () ↔
        ∀ j, lo.val ≤ j → j < hi.val → constructorEntryAt offsets neighbors cell j) := by
  let invariant : core.result.Result Unit topology.Error × Usize → Prop := fun state =>
    lo.val ≤ state.2.val ∧ state.2.val ≤ hi.val ∧
    (state.1 = .Ok () ↔ ∀ j, lo.val ≤ j → j < state.2.val →
      constructorEntryAt offsets neighbors cell j)
  unfold topology.Carrier.from_csr_loop1_loop0
  apply loop.spec_decr_nat
    (fun state : core.result.Result Unit topology.Error × Usize => hi.val - state.2.val)
    invariant
  · rintro ⟨status, index⟩ hinv
    obtain ⟨hil, hih, hpref⟩ := hinv
    dsimp only at hil hih hpref
    unfold topology.Carrier.from_csr_loop1_loop0.body
    apply WP.spec_bind (Usize.add_spec (x := cell) (y := 1#usize) (by
      have := offsets.property
      simp only [UScalar.ofNatCore_val_eq]
      omega))
    intro next hn
    have hnext : next.val = cell.val + 1 := by simpa using hn
    simp only [alloc.vec.Vec.index_slice_index]
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec offsets next (by
      change next.val < offsets.val.length
      omega))
    intro rowEnd he
    have hget : offsets.val[next.val]? = some rowEnd := by
      rw [List.getElem?_eq_getElem (show next.val < offsets.val.length by omega), he]
    rw [hnext, hhi] at hget
    have hend : rowEnd = hi := Option.some.inj hget.symm
    rw [hend]
    by_cases hmore : index < hi
    · simp only [hmore, ite_true]
      have hit : index.val < hi.val := by simpa using hmore
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false]
        apply (WP.spec_ok _).mpr
        simp only [reduceCtorEq, false_iff] at hpref ⊢
        intro hall
        exact hpref (fun j hjl hjh => hall j hjl (by omega))
      | Ok resultUnit =>
        cases resultUnit
        simp only [core.result.Result.is_ok, bind_ok, ite_true]
        have hprefix := hpref.mp rfl
        let value := neighbors.val[index.val]'(by omega)
        have hvalue : neighbors.val[index.val]? = some value :=
          List.getElem?_eq_getElem (by omega)
        apply WP.spec_bind (constructor_row_entry_spec
          (alloc.vec.Vec.deref offsets) (alloc.vec.Vec.deref neighbors) cell index value lo hi
          (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using hsize)
          hrows
          (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using hcell)
          (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using hlo)
          (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using hhi)
          ⟨hil, hit⟩
          (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using hstorage)
          (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using hvalue))
        intro status' hs
        simp only [constructorRowEntryValid, alloc.vec.Vec.deref, Slice.from_val] at hs
        have hentry : status' = .Ok () ↔ constructorEntryAt offsets neighbors cell index.val := by
          constructor
          · intro hok
            exact ⟨value, hvalue, hs.mp hok⟩
          · rintro ⟨value', hv', hvalid⟩
            have heq : value' = value := Option.some.inj (hv'.symm.trans hvalue)
            subst value'
            exact hs.mpr hvalid
        apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
          have := neighbors.property
          simp only [UScalar.ofNatCore_val_eq]
          omega))
        intro index' hi'
        have hindex' : index'.val = index.val + 1 := by simpa using hi'
        apply (WP.spec_ok _).mpr
        dsimp only [invariant]
        refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
        constructor
        · intro hok j hjl hjh
          by_cases heq : j = index.val
          · subst j
            exact hentry.mp hok
          · exact hprefix j hjl (by omega)
        · intro hall
          exact hentry.mpr (hall index.val hil (by omega))
    · have heq : index.val = hi.val := by
        have : ¬ index.val < hi.val := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      simpa only [heq] using hpref
  · refine ⟨le_rfl, hordered, ?_⟩
    simp only [true_iff]
    intro j hlo hhi
    omega

def constructorAllRows (offsets neighbors : alloc.vec.Vec Usize) (upto : Nat) : Prop :=
  ∀ cell : Usize, cell.val < upto →
    ∀ j, (offsets.val[cell.val]?.getD 0#usize).val ≤ j →
      j < (offsets.val[cell.val + 1]?.getD 0#usize).val →
      constructorEntryAt offsets neighbors cell j

/-- The entire extracted CSR row-validation phase rejects exactly the invalid row entries. -/
theorem constructor_csr_all_rows_spec
    (offsets neighbors : alloc.vec.Vec Usize) (n : Usize)
    (hsize : 2 ≤ offsets.val.length)
    (hn : n.val = offsets.val.length - 1)
    (hrows : constructorRawRows (alloc.vec.Vec.deref offsets) (alloc.vec.Vec.deref neighbors)) :
    WP.spec (topology.Carrier.from_csr_loop1 offsets neighbors n 0#usize (.Ok ()))
      (fun output => output.1.val ≤ n.val ∧
        (output.2 = .Ok () ↔ constructorAllRows offsets neighbors n.val)) := by
  let invariant : Usize × core.result.Result Unit topology.Error → Prop := fun state =>
    state.1.val ≤ n.val ∧
    (state.2 = .Ok () ↔ constructorAllRows offsets neighbors state.1.val)
  unfold topology.Carrier.from_csr_loop1
  apply loop.spec_decr_nat
    (fun state : Usize × core.result.Result Unit topology.Error => n.val - state.1.val)
    invariant
  · rintro ⟨cell, status⟩ hinv
    obtain ⟨hcell, hpref⟩ := hinv
    dsimp only at hcell hpref
    unfold topology.Carrier.from_csr_loop1.body
    by_cases hmore : cell < n
    · have hc : cell.val < n.val := by simpa using hmore
      simp only [hmore, ite_true]
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false]
        apply (WP.spec_ok _).mpr
        refine ⟨hcell, ?_⟩
        simp only [reduceCtorEq, false_iff] at hpref ⊢
        intro hall
        exact hpref (fun v hv => hall v (by omega))
      | Ok resultUnit =>
        cases resultUnit
        simp only [core.result.Result.is_ok, bind_ok, ite_true,
          alloc.vec.Vec.index_slice_index]
        have hprefix := hpref.mp rfl
        have hraw := hrows
        simp only [constructorRawRows, alloc.vec.Vec.deref, Slice.from_val] at hraw
        obtain ⟨lo, hi, hlo, hhi, hordered, hstorage⟩ := hraw cell.val (by omega)
        apply WP.spec_bind (alloc.vec.Vec.index_usize_spec offsets cell (by
          change cell.val < offsets.val.length
          omega))
        intro start hs
        have he : start = lo := by
          have hg : offsets.val[cell.val]? = some start := by
            rw [List.getElem?_eq_getElem (show cell.val < offsets.val.length by omega), hs]
          exact Option.some.inj (hg.symm.trans hlo)
        rw [he]
        apply WP.spec_bind (constructor_csr_row_spec offsets neighbors cell lo hi
          hsize hrows (by omega) hlo hhi hordered hstorage)
        intro status' hrow
        apply WP.spec_bind (Usize.add_spec (x := cell) (y := 1#usize) (by
          have := offsets.property
          simp only [UScalar.ofNatCore_val_eq]
          omega))
        intro cell' hc'
        have hnext : cell'.val = cell.val + 1 := by simpa using hc'
        apply (WP.spec_ok _).mpr
        dsimp only [invariant]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        constructor
        · intro hok v hv
          by_cases heq : v = cell
          · subst v
            simpa only [hlo, hhi, Option.getD_some] using hrow.mp hok
          · have hne : v.val ≠ cell.val := fun he => heq ((UScalar.eq_equiv _ _).mpr he)
            exact hprefix v (by omega)
        · intro hall
          apply hrow.mpr
          simpa only [hlo, hhi, Option.getD_some] using hall cell (by omega)
    · have he : cell.val = n.val := by
        have : ¬ cell.val < n.val := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      exact ⟨hcell, by simpa only [he] using hpref⟩
  · refine ⟨by simp, ?_⟩
    simp [constructorAllRows]

end Labyrinth
