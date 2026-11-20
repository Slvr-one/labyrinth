module
public import LabyrinthCore.ConstructorCanonical
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

def constructorCanonicalPairPrefix (cell : Nat) (values : List Usize) (start : Nat) :
    Nat → List (Nat × Nat)
  | 0 => []
  | count + 1 =>
    let emitted := constructorCanonicalPairPrefix cell values start count
    match values[start + count]? with
    | none => emitted
    | some value => if cell < value.val then emitted ++ [(cell, value.val)] else emitted

def constructorCanonicalPairs (offsets neighbors : alloc.vec.Vec Usize) : Nat → List (Nat × Nat)
  | 0 => []
  | cell + 1 =>
    let lo := (offsets.val[cell]?.getD 0#usize).val
    let hi := (offsets.val[cell + 1]?.getD 0#usize).val
    constructorCanonicalPairs offsets neighbors cell ++
      constructorCanonicalPairPrefix cell neighbors.val lo (hi - lo)

theorem constructor_canonical_prefix_pairs (cell : Usize) (values : List Usize) (start count : Nat) :
    (constructorCanonicalPrefix cell values start count).map (fun edge => (edge.u.val, edge.v.val)) =
      constructorCanonicalPairPrefix cell.val values start count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    cases hlookup : values[start + count]? with
    | none =>
      simp only [constructorCanonicalPrefix, constructorCanonicalPairPrefix, hlookup]
      exact ih
    | some value =>
      simp only [constructorCanonicalPrefix, constructorCanonicalPairPrefix, hlookup,
        UScalar.lt_equiv]
      split <;> simp_all

theorem constructor_canonical_rows_length_mono (offsets neighbors : alloc.vec.Vec Usize)
    {a b : Nat} (h : a ≤ b) :
    (constructorCanonicalPairs offsets neighbors a).length ≤
      (constructorCanonicalPairs offsets neighbors b).length := by
  induction h with
  | refl => exact le_rfl
  | @step b h ih =>
    exact le_trans ih (by simp only [constructorCanonicalPairs, List.length_append]; omega)

/-- Exact canonical edge contents of the entire generated extraction phase. The allocation
bound is the mathematical edge count, with no assumption about evaluation or output validity. -/
theorem constructor_canonical_all_rows_spec
    (offsets neighbors : alloc.vec.Vec Usize) (n : Usize)
    (edges : alloc.vec.Vec topology.Edge)
    (hn : n.val = offsets.val.length - 1)
    (hrows : constructorRawRows (alloc.vec.Vec.deref offsets) (alloc.vec.Vec.deref neighbors))
    (hcapacity : edges.val.length = (constructorCanonicalPairs offsets neighbors n.val).length) :
    WP.spec (topology.Carrier.from_csr_loop3 offsets neighbors n 0#usize edges 0#usize)
      (fun output => output.val.map (fun edge => (edge.u.val, edge.v.val)) =
        constructorCanonicalPairs offsets neighbors n.val) := by
  let invariant : Usize × alloc.vec.Vec topology.Edge × Usize → Prop := fun state =>
    state.1.val ≤ n.val ∧ state.2.1.val.length = edges.val.length ∧
    state.2.2.val = (constructorCanonicalPairs offsets neighbors state.1.val).length ∧
    (state.2.1.val.take state.2.2.val).map (fun edge => (edge.u.val, edge.v.val)) =
      constructorCanonicalPairs offsets neighbors state.1.val
  have hraw := hrows
  simp only [constructorRawRows, alloc.vec.Vec.deref, Slice.from_val] at hraw
  unfold topology.Carrier.from_csr_loop3
  apply loop.spec_decr_nat
    (fun state : Usize × alloc.vec.Vec topology.Edge × Usize => n.val - state.1.val) invariant
  · rintro ⟨cell, current, count⟩ hinv
    obtain ⟨hcell, hlen, hcount, hprefix⟩ := hinv
    dsimp only at hcell hlen hcount hprefix
    unfold topology.Carrier.from_csr_loop3.body
    by_cases hmore : cell < n
    · have hc : cell.val < n.val := by simpa using hmore
      simp only [hmore, ite_true, alloc.vec.Vec.index_slice_index]
      obtain ⟨lo, hi, hlo, hhi, hordered, hstorage⟩ := hraw cell.val (by omega)
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec offsets cell (by
        change cell.val < offsets.val.length
        omega))
      intro start hs
      have hlookup : offsets.val[cell.val]? = some start := by
        rw [List.getElem?_eq_getElem (show cell.val < offsets.val.length by omega), hs]
      have hstart : start = lo := Option.some.inj (hlookup.symm.trans hlo)
      rw [hstart]
      have hrowPairs := constructor_canonical_prefix_pairs cell neighbors.val lo.val (hi.val - lo.val)
      have hrowLength := congrArg List.length hrowPairs
      simp only [List.length_map] at hrowLength
      have hfullStep : constructorCanonicalPairs offsets neighbors (cell.val + 1) =
          constructorCanonicalPairs offsets neighbors cell.val ++
            constructorCanonicalPairPrefix cell.val neighbors.val lo.val (hi.val - lo.val) := by
        simp only [constructorCanonicalPairs, hlo, hhi, Option.getD_some]
      have hnextBound := constructor_canonical_rows_length_mono offsets neighbors
        (show cell.val + 1 ≤ n.val by omega)
      rw [hfullStep, List.length_append] at hnextBound
      have hfits : count.val +
          (constructorCanonicalPrefix cell neighbors.val lo.val (hi.val - lo.val)).length ≤
            current.val.length := by omega
      apply WP.spec_bind (constructor_canonical_row_spec offsets neighbors cell lo hi current count
        (by omega) hhi hordered hstorage hfits)
      rintro ⟨written, count'⟩ ⟨hwrittenLength, hcount', hwritten⟩
      dsimp only at hwrittenLength hcount' hwritten
      apply WP.spec_bind (Usize.add_spec (x := cell) (y := 1#usize) (by
        have := offsets.property
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro cell' hc'
      have hcell' : cell'.val = cell.val + 1 := by simpa using hc'
      apply (WP.spec_ok _).mpr
      dsimp only [invariant]
      refine ⟨⟨by omega, hwrittenLength.trans hlen, ?_, ?_⟩, by omega⟩
      · rw [hcell', hfullStep, List.length_append]
        omega
      · rw [hwritten, List.map_append, hprefix, hrowPairs, hcell', hfullStep]
    · have he : cell.val = n.val := by
        have : ¬ cell.val < n.val := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      have hfull : count.val = current.val.length := by rw [hcount, he, hlen, hcapacity]
      simpa only [hfull, List.take_length, he] using hprefix
  · simp [invariant, constructorCanonicalPairs]

end Labyrinth
