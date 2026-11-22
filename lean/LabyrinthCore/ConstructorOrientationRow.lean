module
public import LabyrinthCore.ConstructorOrientationModel
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- Row-closure and depth-balance result of loop 10, retaining the ghost discovery order needed
by loop 9. -/
def constructorOrientationRowOutput (carrier : topology.Carrier) (root capacity : Nat)
    (cell : Usize) (before : Finset Nat) (initialDepth : Nat) :
      alloc.vec.Vec Bool × alloc.vec.Vec Usize × Usize × alloc.vec.Vec Usize × Usize → Prop :=
  fun (seen, path, _index, parents, depth) => ∃ visited rank,
    ConstructorOrientationInvariant carrier root capacity seen path parents depth.val
      (some cell.val) visited rank ∧ before ⊆ visited ∧
    depth.val + before.card = initialDepth + visited.card ∧
    ∀ w, carrierEdge carrier cell.val w → w ∈ visited

/-- The actual inner orientation loop terminates, writes each newly discovered neighbor's
carrier parent, and closes the active carrier row (every row neighbour is visited). -/
theorem constructor_scene_orientation_row_spec
    (carrier : topology.Carrier) (root capacity : Nat) (cell : Usize) (rowSlice : Slice Usize)
    (seen : alloc.vec.Vec Bool) (path parents : alloc.vec.Vec Usize) (depth : Usize)
    (visited : Finset Nat) (rank : Nat → Nat)
    (hc : CarrierValid carrier)
    (hcell : cell.val < cellCount carrier)
    (hrow : rowSlice.val.map (·.val) = row carrier cell.val)
    (hstate : ConstructorOrientationInvariant carrier root capacity seen path parents depth.val
      (some cell.val) visited rank)
    (hsource : cell.val ∈ visited) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop9_loop0 seen path 0#usize parents depth cell rowSlice)
      (constructorOrientationRowOutput carrier root capacity cell visited depth.val) := by
  let invariant : alloc.vec.Vec Bool × alloc.vec.Vec Usize × Usize ×
      alloc.vec.Vec Usize × Usize → Prop := fun state => ∃ discovered order,
    ConstructorOrientationInvariant carrier root capacity state.1 state.2.1 state.2.2.2.1
      state.2.2.2.2.val (some cell.val) discovered order ∧
    visited ⊆ discovered ∧
    state.2.2.2.2.val + visited.card = depth.val + discovered.card ∧
    state.2.2.1.val ≤ rowSlice.val.length ∧
    ∀ j, j < state.2.2.1.val → ∀ value : Usize,
      rowSlice.val[j]? = some value → value.val ∈ discovered
  unfold spanning_tree.Tree.scene_dfs_loop9_loop0
  apply loop.spec_decr_nat
    (fun state : alloc.vec.Vec Bool × alloc.vec.Vec Usize × Usize ×
      alloc.vec.Vec Usize × Usize => rowSlice.val.length - state.2.2.1.val) invariant
  · rintro ⟨currentSeen, currentPath, index, currentParents, currentDepth⟩ hinv
    obtain ⟨discovered, order, hs, hsubset, hbalance, hindex, hprefix⟩ := hinv
    dsimp only at hs hsubset hbalance hindex hprefix
    unfold spanning_tree.Tree.scene_dfs_loop9_loop0.body
    by_cases hmore : index < Slice.len rowSlice
    · have hi : index.val < rowSlice.val.length := by simpa using hmore
      simp only [hmore, ite_true, alloc.vec.Vec.index_slice_index,
        alloc.vec.Vec.index_mut_slice_index]
      apply WP.spec_bind (Slice.index_usize_spec rowSlice index hi)
      intro neighbor hn
      have hnlookup : rowSlice.val[index.val]? = some neighbor := by
        rw [List.getElem?_eq_getElem hi, hn]
      have hnmem : neighbor.val ∈ row carrier cell.val := by
        rw [← hrow]
        exact List.mem_map.mpr ⟨neighbor, List.mem_of_getElem? hnlookup, rfl⟩
      have hedge : carrierEdge carrier cell.val neighbor.val := ⟨hcell, hnmem⟩
      have hneighbor : neighbor.val < cellCount carrier :=
        ((hc.2.2.2.2.1 cell.val hcell).2.2 neighbor.val hnmem).1
      have hseenBound : neighbor.val < currentSeen.val.length := by
        rw [hs.seen_length]
        exact lt_of_lt_of_le hneighbor hs.capacity_bound
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec currentSeen neighbor hseenBound)
      intro marked hm
      have hmlookup : currentSeen.val[neighbor.val]? = some marked := by
        rw [List.getElem?_eq_getElem hseenBound, hm]
      by_cases hvisited : neighbor.val ∈ discovered
      · have hmtrue : marked = true := by
          have ht := (hs.seen_iff neighbor.val hneighbor).mpr hvisited
          exact Option.some.inj (hmlookup.symm.trans ht)
        simp only [hmtrue, ite_true, bind_ok]
        apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
          have := rowSlice.property
          simp only [UScalar.ofNatCore_val_eq]
          omega))
        intro next hnext
        have hnval : next.val = index.val + 1 := by simpa using hnext
        apply (WP.spec_ok _).mpr
        dsimp only [invariant]
        refine ⟨⟨discovered, order, hs, hsubset, hbalance, by omega, ?_⟩, by omega⟩
        intro j hj value hv
        by_cases he : j = index.val
        · subst j
          have heq : value = neighbor := Option.some.inj (hv.symm.trans hnlookup)
          simpa only [heq] using hvisited
        · exact hprefix j (by omega) value hv
      · have hmfalse : marked = false := by
          have hf : currentSeen.val[neighbor.val]? ≠ some true := by
            intro ht
            exact hvisited ((hs.seen_iff neighbor.val hneighbor).mp ht)
          cases marked <;> simp_all
        simp only [hmfalse, Bool.false_eq_true, ite_false]
        have hpathBound : currentDepth.val < currentPath.val.length := by
          rw [hs.path_length]
          have hproper : discovered ⊂ Finset.range (cellCount carrier) := by
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨hs.visited_bound, ?_⟩
            intro heq
            exact hvisited (by rw [heq]; exact Finset.mem_range.mpr hneighbor)
          have hcard := Finset.card_lt_card hproper
          simp only [Finset.card_range] at hcard
          have hinitialDepth := hstate.depth_bound
          have hcapa := hs.capacity_bound
          omega
        have hparentBound : neighbor.val < currentParents.val.length := by
          rw [hs.parents_length]
          exact hneighbor
        simp only [Aeneas.Std.bind_assoc]
        apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec currentSeen neighbor hseenBound)
        rintro ⟨oldSeen, backSeen⟩ ⟨_, rfl⟩
        change WP.spec (Std.bind
          (Std.bind (currentParents.index_mut_usize neighbor) (fun parentPair => do
            let (_, pathBack) ← currentPath.index_mut_usize currentDepth
            let nextDepth ← currentDepth + 1#usize
            ok (currentSeen.set neighbor true, pathBack neighbor, parentPair.2 cell, nextDepth)))
          (fun state => do
            let next ← index + 1#usize
            ok (cont (state.1, state.2.1, next, state.2.2.1, state.2.2.2)))) _
        rw [Aeneas.Std.bind_assoc]
        apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec currentParents neighbor hparentBound)
        rintro ⟨oldParent, backParent⟩ ⟨_, rfl⟩
        dsimp only
        rw [Aeneas.Std.bind_assoc]
        apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec currentPath currentDepth hpathBound)
        rintro ⟨oldPath, backPath⟩ ⟨_, rfl⟩
        change WP.spec (Std.bind
          (Std.bind (currentDepth + 1#usize) (fun nextDepth =>
            ok (currentSeen.set neighbor true, (currentPath.set currentDepth) neighbor,
              currentParents.set neighbor cell, nextDepth)))
          (fun state => do
            let next ← index + 1#usize
            ok (cont (state.1, state.2.1, next, state.2.2.1, state.2.2.2)))) _
        rw [Aeneas.Std.bind_assoc]
        apply WP.spec_bind (Usize.add_spec (x := currentDepth) (y := 1#usize) (by
          have := currentPath.property
          simp only [UScalar.ofNatCore_val_eq]
          omega))
        intro nextDepth hdepth
        have hdval : nextDepth.val = currentDepth.val + 1 := by simpa using hdepth
        simp only [bind_ok]
        apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
          have := rowSlice.property
          simp only [UScalar.ofNatCore_val_eq]
          omega))
        intro next hnext
        have hnval : next.val = index.val + 1 := by simpa using hnext
        have hpush := constructor_orientation_push hs hc (hsubset hsource) hedge hvisited
          hseenBound hpathBound hparentBound hdval
        apply (WP.spec_ok _).mpr
        dsimp only [invariant]
        refine ⟨⟨insert neighbor.val discovered,
          (fun v => if v = neighbor.val then discovered.card else order v), hpush,
          fun v hv => Finset.mem_insert_of_mem (hsubset hv), ?_, by omega, ?_⟩, by omega⟩
        · rw [Finset.card_insert_of_notMem hvisited, hdval]
          omega
        · intro j hj value hv
          by_cases he : j = index.val
          · subst j
            have heq : value = neighbor := Option.some.inj (hv.symm.trans hnlookup)
            subst value
            exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hprefix j (by omega) value hv)
    · have he : index.val = rowSlice.val.length := by
        have : ¬ index.val < rowSlice.val.length := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      refine ⟨discovered, order, hs, hsubset, hbalance, ?_⟩
      intro w hedge
      have hmapped : w ∈ rowSlice.val.map (·.val) := by
        rw [hrow]
        exact hedge.2
      obtain ⟨value, hvalue, heq⟩ := List.mem_map.mp hmapped
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hvalue
      have hjb : j < rowSlice.val.length := (List.getElem?_eq_some_iff.mp hj).1
      simpa only [heq] using hprefix j (by rw [he]; exact hjb) value hj
  · exact ⟨visited, rank, hstate, Finset.Subset.refl _, rfl, by simp,
      fun _ h => by simp at h⟩

end Labyrinth
