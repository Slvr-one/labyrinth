module
public import LabyrinthCore.ConstructorOrientationRow
public import LabyrinthCore.MutationValidate
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

abbrev ConstructorOrientationLoopState := alloc.vec.Vec Bool × alloc.vec.Vec Usize × Usize ×
  alloc.vec.Vec Usize × Usize

abbrev ConstructorOrientationLoopResult := alloc.vec.Vec Bool × alloc.vec.Vec Usize ×
  alloc.vec.Vec Usize

def constructorOrientationLoopInvariant (carrier : topology.Carrier) (root capacity : Nat) :
    ConstructorOrientationLoopState → Prop :=
  fun (seen, path, _, parents, depth) => ∃ visited rank,
    ConstructorOrientationInvariant carrier root capacity seen path parents depth.val none
      visited rank

def constructorOrientationLoopMeasure (carrier : topology.Carrier) :
    ConstructorOrientationLoopState → Nat :=
  fun (seen, _, _, _, depth) =>
    (cellCount carrier + 1) *
      (cellCount carrier - constructorOrientationSeenCount seen (cellCount carrier)) + depth.val

def constructorOrientationLoopOutput (carrier : topology.Carrier) (root capacity : Nat) :
    ConstructorOrientationLoopResult → Prop :=
  fun (seen, path, parents) => ∃ visited rank,
    ConstructorOrientationInvariant carrier root capacity seen path parents 0 none visited rank ∧
    visited = Finset.range (cellCount carrier) ∧
    ∀ v, v < cellCount carrier → seen.val[v]? = some true

/-- One actual loop-9 stack iteration either terminates at depth zero or pops one concrete cell,
scans its actual carrier row with loop 10, and strictly decreases undiscovered-plus-stack fuel. -/
theorem constructor_scene_orientation_loop_body_spec
    (carrier : topology.Carrier) (root capacity : Nat)
    (hc : CarrierValid carrier) (hroot : root < cellCount carrier)
    (state : ConstructorOrientationLoopState)
    (hstate : constructorOrientationLoopInvariant carrier root capacity state) :
    WP.spec
      (spanning_tree.Tree.scene_dfs_loop9.body carrier state.1 state.2.1 state.2.2.1
        state.2.2.2.1 state.2.2.2.2)
      (fun output => match output with
        | cont next => constructorOrientationLoopInvariant carrier root capacity next ∧
            constructorOrientationLoopMeasure carrier next <
              constructorOrientationLoopMeasure carrier state
        | done result => constructorOrientationLoopOutput carrier root capacity result) := by
  rcases state with ⟨seen, path, unused, parents, depth⟩
  obtain ⟨visited, rank, hs⟩ := hstate
  dsimp only
  unfold spanning_tree.Tree.scene_dfs_loop9.body
  by_cases hpositive : depth > 0#usize
  · have hd : 0 < depth.val := by simpa using hpositive
    simp only [hpositive, ite_true, alloc.vec.Vec.index_slice_index]
    apply WP.spec_bind (Usize.sub_spec (x := depth) (y := 1#usize) (by
      simp only [UScalar.ofNatCore_val_eq]
      omega))
    intro popped hp
    have hpopped : popped.val = depth.val - 1 := by simpa using hp.1
    have hpathBound : popped.val < path.val.length := by
      rw [hs.path_length]
      have hcard := Finset.card_le_card hs.visited_bound
      simp only [Finset.card_range] at hcard
      have := hs.depth_bound
      have := hs.capacity_bound
      omega
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec path popped hpathBound)
    intro cell hcellLookup
    have hcellAt : path.val[popped.val]? = some cell := by
      rw [List.getElem?_eq_getElem hpathBound, hcellLookup]
    obtain ⟨queued, hqueued, hqueuedMem⟩ := hs.pending popped.val (by omega)
    have hcellEq : queued = cell := Option.some.inj (hqueued.symm.trans hcellAt)
    subst queued
    have hcell : cell.val < cellCount carrier :=
      Finset.mem_range.mp (hs.visited_bound hqueuedMem)
    have hpoppedState : ConstructorOrientationInvariant carrier root capacity seen path parents
        popped.val (some cell.val) visited rank := by
      have hpoppedLt : popped.val < depth.val := by omega
      refine ⟨hs.seen_length, hs.path_length, hs.parents_length, hs.capacity_bound,
        hs.visited_bound, hs.seen_iff, hs.root_mem, hs.root_parent,
        le_trans (Nat.le_of_lt hpoppedLt) hs.depth_bound, ?_, hs.parent,
        hs.rank_bound, hs.rank_decreases, hs.parent_edge, ?_⟩
      · intro i hi
        exact hs.pending i (by omega)
      · intro v hv
        rcases hs.covered v hv with ha | hclosed | ⟨i, hi, queued, hlookup, he⟩
        · cases ha
        · exact Or.inr (Or.inl hclosed)
        · by_cases hstill : i < popped.val
          · exact Or.inr (Or.inr ⟨i, hstill, queued, hlookup, he⟩)
          · have hieq : i = popped.val := by omega
            subst i
            have hqe : queued = cell := Option.some.inj (hlookup.symm.trans hcellAt)
            subst queued
            exact Or.inl (congrArg some he)
    apply WP.spec_bind (mutation_carrier_neighbors_total carrier cell hc hcell)
    intro rowSlice hrow
    apply WP.spec_bind (constructor_scene_orientation_row_spec carrier root capacity cell rowSlice
      seen path parents popped visited rank hc hcell hrow hpoppedState hqueuedMem)
    rintro ⟨seen', path', index', parents', depth'⟩
      ⟨found, order, hfound, hsubset, hbalance, hclosed⟩
    apply (WP.spec_ok _).mpr
    have hfinal := constructor_orientation_finish_row hfound hclosed
    refine ⟨⟨found, order, hfinal⟩, ?_⟩
    have hcard := Finset.card_le_card hsubset
    change (cellCount carrier + 1) *
        (cellCount carrier - constructorOrientationSeenCount seen' (cellCount carrier)) +
          depth'.val <
      (cellCount carrier + 1) *
        (cellCount carrier - constructorOrientationSeenCount seen (cellCount carrier)) +
          depth.val
    rw [constructor_orientation_seen_count hfound, constructor_orientation_seen_count hs]
    have holdBound := Finset.card_le_card hs.visited_bound
    have hnewBound := Finset.card_le_card hfound.visited_bound
    simp only [Finset.card_range] at holdBound hnewBound
    by_cases heq : found.card = visited.card
    · have hdepthEq : depth'.val = popped.val := by omega
      rw [heq, hdepthEq]
      omega
    · have hcardLt : visited.card < found.card := by omega
      have hdepthSmall : depth'.val < cellCount carrier + 1 := by
        have := hfinal.depth_bound
        omega
      have hgap :
          cellCount carrier - found.card + 1 ≤ cellCount carrier - visited.card := by
        omega
      have hmul := Nat.mul_le_mul_left (cellCount carrier + 1) hgap
      calc
        (cellCount carrier + 1) * (cellCount carrier - found.card) + depth'.val
            < (cellCount carrier + 1) * (cellCount carrier - found.card) +
                (cellCount carrier + 1) := Nat.add_lt_add_left hdepthSmall _
        _ = (cellCount carrier + 1) * (cellCount carrier - found.card + 1) := by ring
        _ ≤ (cellCount carrier + 1) * (cellCount carrier - visited.card) := hmul
        _ ≤ (cellCount carrier + 1) * (cellCount carrier - visited.card) + depth.val :=
          Nat.le_add_right _ _
  · have hz : depth.val = 0 := by
      have : ¬ 0 < depth.val := by simpa using hpositive
      omega
    simp only [hpositive, ite_false]
    apply (WP.spec_ok _).mpr
    obtain ⟨hall, hseen⟩ := constructor_orientation_exhausted hc hroot (by simpa only [hz] using hs)
    exact ⟨visited, rank, by simpa only [hz] using hs, hall, hseen⟩

/-- Universal totality and all-cell reachability of the generated orientation loop. -/
theorem constructor_scene_orientation_loop_spec
    (carrier : topology.Carrier) (root capacity : Nat)
    (hc : CarrierValid carrier) (hroot : root < cellCount carrier)
    (seen : alloc.vec.Vec Bool) (path : alloc.vec.Vec Usize) (unused : Usize)
    (parents : alloc.vec.Vec Usize) (depth : Usize) (visited : Finset Nat) (rank : Nat → Nat)
    (hstate : ConstructorOrientationInvariant carrier root capacity seen path parents depth.val none
      visited rank) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop9 seen path unused carrier parents depth)
      (constructorOrientationLoopOutput carrier root capacity) := by
  unfold spanning_tree.Tree.scene_dfs_loop9
  apply loop.spec_decr_nat (constructorOrientationLoopMeasure carrier)
    (constructorOrientationLoopInvariant carrier root capacity)
  · intro state hs
    apply WP.spec_mono
      (constructor_scene_orientation_loop_body_spec carrier root capacity hc hroot state hs)
    intro result hresult
    cases result <;> exact hresult
  · exact ⟨visited, rank, hstate⟩

end Labyrinth
