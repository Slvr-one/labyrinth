module
public import LabyrinthCore.Model
public import LabyrinthCore.ConstructorDegree
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core
open scoped BigOperators

namespace Labyrinth

/-- The real edge-list constructor initializes each write cursor to its CSR row start. -/
theorem constructor_cursors_spec (n : Usize) (offsets cursor : alloc.vec.Vec Usize)
    (hsource : n.val ≤ offsets.val.length) (htarget : cursor.val.length = n.val) :
    WP.spec (topology.Carrier.from_edges_loop1 n offsets 0#usize cursor)
      (fun output => output.val = offsets.val.take n.val) := by
  let invariant : Usize × alloc.vec.Vec Usize → Prop := fun state =>
    state.1.val ≤ n.val ∧ state.2.val.length = n.val ∧
    ∀ j, j < state.1.val → state.2.val[j]? = offsets.val[j]?
  unfold topology.Carrier.from_edges_loop1
  apply loop.spec_decr_nat
    (fun state : Usize × alloc.vec.Vec Usize => n.val - state.1.val) invariant
  · rintro ⟨index, current⟩ hinv
    obtain ⟨hindex, hlen, hprefix⟩ := hinv
    dsimp only at hindex hlen hprefix
    unfold topology.Carrier.from_edges_loop1.body
    by_cases hmore : index < n
    · have hi : index.val < n.val := by simpa using hmore
      simp only [hmore, ite_true, alloc.vec.Vec.index_slice_index,
        alloc.vec.Vec.index_mut_slice_index]
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec offsets index (by
        change index.val < offsets.val.length
        omega))
      intro value hv
      have hlookup : offsets.val[index.val]? = some value := by
        rw [List.getElem?_eq_getElem (show index.val < offsets.val.length by omega), hv]
      apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec current index (by
        change index.val < current.val.length
        omega))
      rintro ⟨old, back⟩ ⟨_, rfl⟩
      apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
        have hn : n.val ≤ Usize.max := by scalar_tac
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro next hn
      have hnext : next.val = index.val + 1 := by simpa using hn
      apply (WP.spec_ok _).mpr
      dsimp only [invariant]
      refine ⟨⟨by omega, by simpa using hlen, ?_⟩, by omega⟩
      intro j hj
      by_cases he : j = index.val
      · subst j
        simp [alloc.vec.Vec.set, hlookup, show index.val < current.val.length by omega]
      · simpa [alloc.vec.Vec.set, he, Ne.symm he] using hprefix j (by omega)
    · have he : index.val = n.val := by
        have : ¬ index.val < n.val := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      apply List.ext_getElem
      · simp only [List.length_take, Nat.min_eq_left hsource, hlen]
      · intro j hj hjtake
        have hlook := hprefix j (by omega)
        have hjSource : j < offsets.val.length := by omega
        rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjSource] at hlook
        simpa only [List.getElem_take] using Option.some.inj hlook
  · exact ⟨by simp, htarget, fun _ hj => by simp at hj⟩

/-- Quotient-CSR cursor initialization is the same extracted loop, not a second algorithm. -/
theorem constructor_scene_cursors_spec (n : Usize) (offsets cursor : alloc.vec.Vec Usize)
    (hsource : n.val ≤ offsets.val.length) (htarget : cursor.val.length = n.val) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop4 0#usize n offsets cursor)
      (fun output => output.val = offsets.val.take n.val) := by
  have he : spanning_tree.Tree.scene_dfs_loop4 0#usize n offsets cursor =
      topology.Carrier.from_edges_loop1 n offsets 0#usize cursor := by
    unfold spanning_tree.Tree.scene_dfs_loop4 topology.Carrier.from_edges_loop1
    unfold spanning_tree.Tree.scene_dfs_loop4.body topology.Carrier.from_edges_loop1.body
    rfl
  rw [he]
  exact constructor_cursors_spec n offsets cursor hsource htarget

theorem constructor_degree_zero_slot (edges : List topology.Edge) (count : Nat) :
    constructorDegreeSlot edges 0 count = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [constructorDegreeSlot]
    split
    · exact ih
    · split <;> omega

/-- Exact degree counts and the real prefix operation produce disjoint, exhaustive
CSR rows. The premises are scalar contents, not a successful constructor evaluation. -/
theorem constructor_degree_offsets_layout (n : Nat) (edges : List topology.Edge)
    (counts offsets : List Usize)
    (hcountsLength : counts.length = n + 1)
    (hedges : ∀ edge ∈ edges, edge.u.val < n ∧ edge.v.val < n ∧ edge.u ≠ edge.v)
    (hcounts : ∀ j, j < counts.length →
      (counts[j]?.getD 0#usize).val = constructorDegreeSlot edges j edges.length)
    (hoffsets : ∀ j, j ≤ n →
      (offsets[j]?.getD 0#usize).val = constructorPrefixSum counts (j + 1)) :
    (offsets[0]?.getD 0#usize).val = 0 ∧
    (offsets[n]?.getD 0#usize).val = 2 * edges.length ∧
    (∀ cell, cell < n →
      (offsets[cell]?.getD 0#usize).val +
        constructorDegreeSlot edges (cell + 1) edges.length =
          (offsets[cell + 1]?.getD 0#usize).val) ∧
    (∀ a b, a ≤ b → b ≤ n →
      (offsets[a]?.getD 0#usize).val ≤ (offsets[b]?.getD 0#usize).val) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hoffsets 0 (by omega)]
    simp only [constructorPrefixSum, Nat.zero_add]
    rw [hcounts 0 (by omega), constructor_degree_zero_slot]
  · rw [hoffsets n le_rfl, constructor_prefix_sum_as_sum]
    calc
      (∑ j ∈ Finset.range (n + 1), (counts[j]?.getD 0#usize).val) =
          ∑ j ∈ Finset.range (n + 1), constructorDegreeSlot edges j edges.length := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hcounts j (by rw [hcountsLength]; exact Finset.mem_range.mp hj)
      _ = 2 * edges.length := constructor_degree_sum n edges hedges _ le_rfl
  · intro cell hc
    rw [hoffsets cell (by omega), hoffsets (cell + 1) (by omega)]
    simp only [constructorPrefixSum]
    rw [hcounts (cell + 1) (by omega)]
  · intro a b hab hb
    rw [hoffsets a (by omega), hoffsets b hb]
    exact constructor_prefix_sum_mono counts (by omega)

end Labyrinth
