module
public import LabyrinthCore.ConstructorOrientationLoop
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

/-- The extracted root writes establish the singleton orientation frontier. -/
theorem constructor_orientation_initial
    (carrier : topology.Carrier) (root : Usize) (work : spanning_tree.Workspace)
    (parents : alloc.vec.Vec Usize)
    (hc : CarrierValid carrier) (hroot : root.val < cellCount carrier)
    (hw : WorkspaceValid work) (hcapacity : cellCount carrier ≤ work.path.val.length)
    (hclear : ∀ v, v < cellCount carrier → work.seen.val[v]? = some false)
    (hparents : parents.val = List.replicate (cellCount carrier) root) :
    ConstructorOrientationInvariant carrier root.val work.path.val.length
      (work.seen.set root true) (work.path.set 0#usize root) parents 1 none
      {root.val} (fun _ => 0) := by
  have hrootCapacity : root.val < work.path.val.length := lt_of_lt_of_le hroot hcapacity
  have hzeroCapacity : 0 < work.path.val.length := by have := hc.1; omega
  have hparentLength : parents.val.length = cellCount carrier := by simp [hparents]
  have hrootParent : parents.val[root.val]? = some root := by
    rw [hparents]
    simp [hroot]
  refine {
    seen_length := by simpa [alloc.vec.Vec.set] using hw.1
    path_length := by simp [alloc.vec.Vec.set]
    parents_length := hparentLength
    capacity_bound := hcapacity
    visited_bound := ?_
    seen_iff := ?_
    root_mem := by simp
    root_parent := ⟨root, hrootParent, rfl⟩
    depth_bound := by simp
    pending := ?_
    parent := ?_
    rank_bound := ?_
    rank_decreases := ?_
    parent_edge := ?_
    covered := ?_ }
  · intro v hv
    have he : v = root.val := Finset.mem_singleton.mp hv
    exact Finset.mem_range.mpr (he ▸ hroot)
  · intro v hv
    by_cases he : v = root.val
    · subst v
      simp [alloc.vec.Vec.set, hw.1, hrootCapacity]
    · simp [alloc.vec.Vec.set, he, Ne.symm he, hclear v hv]
  · intro i hi
    have he : i = 0 := by omega
    subst i
    exact ⟨root, by simp [alloc.vec.Vec.set, hzeroCapacity], by simp⟩
  · intro v hv
    have he : v = root.val := Finset.mem_singleton.mp hv
    subst v
    exact ⟨root, hrootParent, by simp⟩
  · intro v hv
    have he : v = root.val := Finset.mem_singleton.mp hv
    subst v
    simp
  · intro v hv hne
    exact False.elim (hne (Finset.mem_singleton.mp hv))
  · intro v hv hne
    exact False.elim (hne (Finset.mem_singleton.mp hv))
  · intro v hv
    have he : v = root.val := Finset.mem_singleton.mp hv
    subst v
    exact Or.inr (Or.inr ⟨0, by simp, root,
      by simp [alloc.vec.Vec.set, hzeroCapacity], rfl⟩)

/-- Replacing only seen/path by equal-length orientation outputs preserves reusable workspace validity. -/
theorem constructor_orientation_workspace_valid
    (before : spanning_tree.Workspace) (seen : alloc.vec.Vec Bool) (path : alloc.vec.Vec Usize)
    (hvalid : WorkspaceValid before)
    (hseen : seen.val.length = before.path.val.length)
    (hpath : path.val.length = before.path.val.length) :
    WorkspaceValid { before with seen := seen, path := path } := by
  unfold WorkspaceValid at hvalid ⊢
  rcases hvalid with ⟨_, hvalid⟩
  refine ⟨by rw [hseen, hpath], ?_⟩
  simpa only [hpath] using hvalid

end Labyrinth
