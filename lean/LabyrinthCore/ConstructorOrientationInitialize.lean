module
public import LabyrinthCore.Model
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- Exact frame of the generated orientation-clear loop. -/
def constructorOrientationCleared (before after : spanning_tree.Workspace) (count : Nat) : Prop :=
  WorkspaceValid after ∧
  after.frames = before.frames ∧ after.path = before.path ∧
  after.parents = before.parents ∧ after.incoming = before.incoming ∧
  after.edit_slots = before.edit_slots ∧ after.edit_nodes = before.edit_nodes ∧
  after.edit_count = before.edit_count ∧ after.edge_capacity = before.edge_capacity ∧
  (∀ j, j < count → after.seen.val[j]? = some false) ∧
  (∀ j, count ≤ j → after.seen.val[j]? = before.seen.val[j]?)

/-- Loop 8 terminates, clears exactly the requested seen prefix, and preserves capacities. -/
theorem constructor_scene_orientation_clear_spec (work : spanning_tree.Workspace) (n : Usize)
    (hvalid : WorkspaceValid work) (hcapacity : n.val ≤ work.path.val.length) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop8 work n 0#usize)
      (fun output => output.2.val = n.val ∧
        constructorOrientationCleared work output.1 n.val) := by
  let invariant : spanning_tree.Workspace × Usize → Prop := fun state =>
    state.2.val ≤ n.val ∧ constructorOrientationCleared work state.1 state.2.val
  unfold spanning_tree.Tree.scene_dfs_loop8
  apply loop.spec_decr_nat
    (fun state : spanning_tree.Workspace × Usize => n.val - state.2.val) invariant
  · rintro ⟨scratch, index⟩ hinv
    obtain ⟨hindex, hsvalid, hframes, hpath, hparents, hincoming, hslots, hnodes,
      hcount, hedges, hprefix, hsuffix⟩ := hinv
    dsimp only at hindex hprefix hsuffix
    unfold spanning_tree.Tree.scene_dfs_loop8.body
    by_cases hmore : index < n
    · have hi : index.val < n.val := by simpa using hmore
      have hseen : index.val < scratch.seen.val.length := by
        rw [hsvalid.1, hpath]
        omega
      simp only [hmore, ite_true, alloc.vec.Vec.index_mut_slice_index]
      apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec scratch.seen index hseen)
      rintro ⟨oldSeen, backSeen⟩ ⟨_, rfl⟩
      apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
        have hn : n.val ≤ Usize.max := by scalar_tac
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro next hn
      have hnext : next.val = index.val + 1 := by simpa using hn
      apply (WP.spec_ok _).mpr
      dsimp only [invariant]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      refine ⟨by simpa [WorkspaceValid] using hsvalid, hframes, hpath, hparents, hincoming,
        hslots, hnodes, hcount, hedges, ?_, ?_⟩
      · intro j hj
        by_cases he : j = index.val
        · subst j
          simp [alloc.vec.Vec.set, hseen]
        · have hjold : j < index.val := by omega
          simpa [alloc.vec.Vec.set, he, Ne.symm he] using hprefix j hjold
      · intro j hj
        have he : j ≠ index.val := by omega
        simpa [alloc.vec.Vec.set, he, Ne.symm he] using hsuffix j (by omega)
    · have he : index.val = n.val := by
        have : ¬ index.val < n.val := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      exact ⟨he, hsvalid, hframes, hpath, hparents, hincoming, hslots, hnodes,
        hcount, hedges, by simpa only [he] using hprefix, by simpa only [he] using hsuffix⟩
  · exact ⟨by simp, hvalid, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ h => by simp at h, fun _ _ => rfl⟩

end Labyrinth
