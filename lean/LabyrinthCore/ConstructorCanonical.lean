module
public import LabyrinthCore.ConstructorCarrierRows
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- Canonical edges emitted by the first `count` entries starting at the given CSR index. -/
def constructorCanonicalPrefix (cell : Usize) (values : List Usize) (start : Nat) :
    Nat → List topology.Edge
  | 0 => []
  | count + 1 =>
    let emitted := constructorCanonicalPrefix cell values start count
    match values[start + count]? with
    | none => emitted
    | some value => if cell < value then emitted ++ [{ u := cell, v := value }] else emitted

theorem constructor_canonical_prefix_length_mono (cell : Usize) (values : List Usize)
    (start : Nat) {a b : Nat} (h : a ≤ b) :
    (constructorCanonicalPrefix cell values start a).length ≤
      (constructorCanonicalPrefix cell values start b).length := by
  induction h with
  | refl => exact le_rfl
  | @step b h ih =>
    apply le_trans ih
    simp only [constructorCanonicalPrefix]
    split
    · exact le_rfl
    · split <;> simp

/-- A bounded vector append writes exactly one new initialized prefix element. -/
theorem constructor_take_set_append {α : Type*} (values : List α) (index : Nat)
    (value : α) (hbound : index < values.length) :
    (values.set index value).take (index + 1) = values.take index ++ [value] := by
  induction values generalizing index with
  | nil => simp at hbound
  | cons first rest ih =>
    cases index with
    | zero => rfl
    | succ index =>
      have hi : index < rest.length := by simpa using hbound
      simpa using congrArg (List.cons first) (ih index hi)

/-- Exact writes and totality of the generated canonical-edge extraction for one whole row. -/
theorem constructor_canonical_row_spec
    (offsets neighbors : alloc.vec.Vec Usize) (cell lo hi : Usize)
    (edges : alloc.vec.Vec topology.Edge) (count : Usize)
    (hcell : cell.val + 1 < offsets.val.length)
    (hhi : offsets.val[cell.val + 1]? = some hi)
    (hordered : lo.val ≤ hi.val) (hstorage : hi.val ≤ neighbors.val.length)
    (hcapacity : count.val +
      (constructorCanonicalPrefix cell neighbors.val lo.val (hi.val - lo.val)).length ≤
        edges.val.length) :
    WP.spec (topology.Carrier.from_csr_loop3_loop0 offsets neighbors cell edges count lo)
      (fun output => output.1.val.length = edges.val.length ∧
        output.2.val = count.val +
          (constructorCanonicalPrefix cell neighbors.val lo.val (hi.val - lo.val)).length ∧
        output.1.val.take output.2.val = edges.val.take count.val ++
          constructorCanonicalPrefix cell neighbors.val lo.val (hi.val - lo.val)) := by
  let invariant : alloc.vec.Vec topology.Edge × Usize × Usize → Prop := fun state =>
    state.1.val.length = edges.val.length ∧
    lo.val ≤ state.2.2.val ∧ state.2.2.val ≤ hi.val ∧
    state.2.1.val = count.val +
      (constructorCanonicalPrefix cell neighbors.val lo.val (state.2.2.val - lo.val)).length ∧
    state.1.val.take state.2.1.val = edges.val.take count.val ++
      constructorCanonicalPrefix cell neighbors.val lo.val (state.2.2.val - lo.val)
  unfold topology.Carrier.from_csr_loop3_loop0
  apply loop.spec_decr_nat
    (fun state : alloc.vec.Vec topology.Edge × Usize × Usize => hi.val - state.2.2.val)
    invariant
  · rintro ⟨currentEdges, currentCount, index⟩ hinv
    obtain ⟨hlen, hlow, hupp, hcount, hwritten⟩ := hinv
    dsimp only at hlen hlow hupp hcount hwritten
    unfold topology.Carrier.from_csr_loop3_loop0.body
    apply WP.spec_bind (Usize.add_spec (x := cell) (y := 1#usize) (by
      have := offsets.property
      simp only [UScalar.ofNatCore_val_eq]
      omega))
    intro nextCell hnextCell
    have hnext : nextCell.val = cell.val + 1 := by simpa using hnextCell
    simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec offsets nextCell (by
      change nextCell.val < offsets.val.length
      omega))
    intro rowEnd he
    have hget : offsets.val[nextCell.val]? = some rowEnd := by
      rw [List.getElem?_eq_getElem (show nextCell.val < offsets.val.length by omega), he]
    rw [hnext, hhi] at hget
    have hend : rowEnd = hi := Option.some.inj hget.symm
    rw [hend]
    by_cases hmore : index < hi
    · have hiIndex : index.val < hi.val := by simpa using hmore
      have hiBound : index.val < neighbors.val.length := by omega
      simp only [hmore, ite_true]
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec neighbors index hiBound)
      intro value hv
      have hlookup : neighbors.val[index.val]? = some value := by
        rw [List.getElem?_eq_getElem hiBound, hv]
      have hposition : lo.val + (index.val - lo.val) = index.val := by omega
      have hnextOffset : index.val + 1 - lo.val = (index.val - lo.val) + 1 := by omega
      by_cases hcanonical : cell < value
      · simp only [hcanonical, ite_true]
        have hle : cell ≤ value := le_of_lt hcanonical
        simp only [topology.Edge.new, hle, ite_true, bind_ok]
        have hprefixStep :
            constructorCanonicalPrefix cell neighbors.val lo.val ((index.val - lo.val) + 1) =
              constructorCanonicalPrefix cell neighbors.val lo.val (index.val - lo.val) ++
                [{ u := cell, v := value }] := by
          simp only [constructorCanonicalPrefix, hposition, hlookup, hcanonical, ite_true]
        have hlengthBound := constructor_canonical_prefix_length_mono cell neighbors.val lo.val
          (show (index.val - lo.val) + 1 ≤ hi.val - lo.val by omega)
        rw [hprefixStep, List.length_append, List.length_singleton] at hlengthBound
        have hwriteBound : currentCount.val < currentEdges.val.length := by omega
        simp only [Aeneas.Std.bind_assoc]
        apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec currentEdges currentCount hwriteBound)
        rintro ⟨old, back⟩ ⟨_, rfl⟩
        change WP.spec (Std.bind
          (Std.bind (currentCount + 1#usize) (fun nextCount =>
            ok (currentEdges.set currentCount { u := cell, v := value }, nextCount)))
          (fun state => do
            let nextIndex ← index + 1#usize
            ok (cont (state.1, state.2, nextIndex)))) _
        rw [Aeneas.Std.bind_assoc]
        apply WP.spec_bind (Usize.add_spec (x := currentCount) (y := 1#usize) (by
          have := currentEdges.property
          simp only [UScalar.ofNatCore_val_eq]
          omega))
        intro count' hc'
        have hcount' : count'.val = currentCount.val + 1 := by simpa using hc'
        simp only [bind_ok]
        apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
          have := neighbors.property
          simp only [UScalar.ofNatCore_val_eq]
          omega))
        intro index' hi'
        have hindex' : index'.val = index.val + 1 := by simpa using hi'
        apply (WP.spec_ok _).mpr
        dsimp only [invariant]
        refine ⟨⟨by simpa using hlen, by omega, by omega, ?_, ?_⟩, by omega⟩
        · rw [hindex', hnextOffset, hprefixStep, List.length_append, List.length_singleton]
          omega
        · rw [hindex', hnextOffset, hprefixStep, hcount']
          simp only [alloc.vec.Vec.set_val_eq]
          rw [constructor_take_set_append _ _ _ hwriteBound, hwritten, List.append_assoc]
      · simp only [hcanonical, ite_false, bind_ok]
        have hprefixStep :
            constructorCanonicalPrefix cell neighbors.val lo.val ((index.val - lo.val) + 1) =
              constructorCanonicalPrefix cell neighbors.val lo.val (index.val - lo.val) := by
          simp only [constructorCanonicalPrefix, hposition, hlookup, hcanonical, ite_false]
        apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
          have := neighbors.property
          simp only [UScalar.ofNatCore_val_eq]
          omega))
        intro index' hi'
        have hindex' : index'.val = index.val + 1 := by simpa using hi'
        apply (WP.spec_ok _).mpr
        dsimp only [invariant]
        refine ⟨⟨hlen, by omega, by omega, ?_, ?_⟩, by omega⟩
        · simpa only [hindex', hnextOffset, hprefixStep] using hcount
        · simpa only [hindex', hnextOffset, hprefixStep] using hwritten
    · have heq : index.val = hi.val := by
        have : ¬ index.val < hi.val := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      exact ⟨hlen, by simpa only [heq] using hcount, by simpa only [heq] using hwritten⟩
  · simp [invariant, constructorCanonicalPrefix, hordered]

end Labyrinth
