module
public import LabyrinthCore.Model
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- One actual CSR row boundary is ordered and stays inside adjacency storage. -/
def constructorOffsetOK (offsets : alloc.vec.Vec Usize)
    (neighbors : alloc.vec.Vec Usize) (i : Nat) : Prop :=
  (offsets.val[i]?.getD 0#usize).val ≤ (offsets.val[i + 1]?.getD 0#usize).val ∧
  (offsets.val[i + 1]?.getD 0#usize).val ≤ neighbors.val.length

private theorem constructor_csr_offset_body
    (offsets neighbors : alloc.vec.Vec Usize) (n u : Usize) (valid : Bool)
    (hn : n.val < offsets.val.length) :
    WP.spec (topology.Carrier.from_csr_loop0.body offsets neighbors n u valid)
      (fun r => match r with
      | .done b => b = valid ∧ (n.val ≤ u.val ∨ valid = false)
      | .cont (v, b) => u.val < n.val ∧ v.val = u.val + 1 ∧ valid = true ∧
          (b = true ↔ constructorOffsetOK offsets neighbors u.val)) := by
  unfold topology.Carrier.from_csr_loop0.body
  by_cases hun : u < n
  · simp only [hun, ite_true]
    have hu : u.val < n.val := by simpa using hun
    cases valid with
    | false => simp
    | true =>
      simp only [Bool.true_eq, ite_true, alloc.vec.Vec.index_slice_index]
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec offsets u (by
        change u.val < offsets.val.length
        omega))
      intro x hx
      apply WP.spec_bind (Usize.add_spec (x := u) (y := 1#usize) (by
        have := offsets.property
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro next hnext
      have hnv : next.val = u.val + 1 := by simpa using hnext
      have hnextBound : next.val < offsets.val.length := by omega
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec offsets next hnextBound)
      intro y hy
      have hleft : offsets.val[u.val]? = some x := by
        rw [List.getElem?_eq_getElem (show u.val < offsets.val.length by omega), hx]
      have hright : offsets.val[u.val + 1]? = some y := by
        rw [← hnv, List.getElem?_eq_getElem hnextBound, hy]
      have hrow : constructorOffsetOK offsets neighbors u.val ↔
          x.val ≤ y.val ∧ y.val ≤ neighbors.val.length := by
        simp only [constructorOffsetOK, hleft, hright, Option.getD_some]
      by_cases hxy : x ≤ y
      · simp only [hxy, ite_true]
        rw [Aeneas.Std.bind_assoc]
        apply WP.spec_bind (alloc.vec.Vec.index_usize_spec offsets next hnextBound)
        intro z hz
        have hzy : z = y := hz.trans hy.symm
        simp only [bind_ok, WP.spec_ok, hzy]
        refine ⟨hu, hnv, True.intro, ?_⟩
        have hxyn : x.val ≤ y.val := (UScalar.le_equiv x y).mp hxy
        simp only [decide_eq_true_eq, UScalar.le_equiv, alloc.vec.Vec.len_val,
          hrow, hxyn, true_and]
      · simp only [hxy, ite_false, bind_ok, WP.spec_ok]
        refine ⟨hu, hnv, True.intro, ?_⟩
        simp only [Bool.false_eq_true, false_iff, hrow]
        intro h
        exact hxy ((UScalar.le_equiv x y).mpr h.1)
  · have hnu : n.val ≤ u.val := by simpa using hun
    simp [hun, hnu]

/-- Total offset validation: the extracted loop accepts exactly the ordered bounded CSR rows. -/
theorem constructor_csr_offsets_spec
    (offsets neighbors : alloc.vec.Vec Usize) (n : Usize)
    (hn : n.val < offsets.val.length) :
    WP.spec (topology.Carrier.from_csr_loop0 offsets neighbors n 0#usize true)
      (fun valid => valid = true ↔ ∀ i, i < n.val → constructorOffsetOK offsets neighbors i) := by
  let invariant : Usize × Bool → Prop := fun s =>
    s.1.val ≤ n.val ∧
    (s.2 = true ↔ ∀ i, i < s.1.val → constructorOffsetOK offsets neighbors i)
  unfold topology.Carrier.from_csr_loop0
  apply loop.spec_decr_nat (fun s : Usize × Bool => n.val - s.1.val) invariant
    (fun valid => valid = true ↔ ∀ i, i < n.val → constructorOffsetOK offsets neighbors i)
  · rintro ⟨u, valid⟩ ⟨hub, hpref⟩
    dsimp only at hub hpref
    apply WP.spec_mono (constructor_csr_offset_body offsets neighbors n u valid hn)
    intro r hr
    cases r with
    | done b =>
      obtain ⟨rfl, hdone⟩ := hr
      rcases hdone with hdone | hdone
      · have he : u.val = n.val := by omega
        simpa only [he] using hpref
      · simp only [hdone, Bool.false_eq_true, false_iff] at hpref ⊢
        intro hall
        exact hpref (fun i hi => hall i (by omega))
    | cont state =>
      obtain ⟨next, validNext⟩ := state
      dsimp only [invariant] at hr ⊢
      obtain ⟨hu, hnext, hv, hcurrent⟩ := hr
      have hprefix : ∀ i, i < u.val → constructorOffsetOK offsets neighbors i := hpref.mp hv
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      constructor
      · intro hb i hi
        by_cases he : i = u.val
        · subst i
          exact hcurrent.mp hb
        · exact hprefix i (by omega)
      · intro hall
        exact hcurrent.mpr (hall u.val (by omega))
  · simp [invariant]

end Labyrinth
