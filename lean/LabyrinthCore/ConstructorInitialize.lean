module
public import LabyrinthCore.ConstructorDFS
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- The initialization loop changes only the requested prefix of its three scratch arrays. -/
def constructorInitializedPrefix (before after : spanning_tree.Workspace)
    (root : Usize) (count : Nat) : Prop :=
  WorkspaceValid after ∧
  after.path = before.path ∧ after.frames = before.frames ∧
  after.edit_slots = before.edit_slots ∧ after.edit_nodes = before.edit_nodes ∧
  after.edit_count = before.edit_count ∧ after.edge_capacity = before.edge_capacity ∧
  (∀ j, j < count → after.seen.val[j]? = some false ∧
    after.parents.val[j]? = some root ∧ after.incoming.val[j]? = some 0#usize) ∧
  (∀ j, count ≤ j → after.seen.val[j]? = before.seen.val[j]? ∧
    after.parents.val[j]? = before.parents.val[j]? ∧
    after.incoming.val[j]? = before.incoming.val[j]?)

/-- Totality and exact writes of the generated DFS initialization loop, for every capacity. -/
theorem constructor_dfs_initialize_spec (root n : Usize) (work : spanning_tree.Workspace)
    (hvalid : WorkspaceValid work) (hcapacity : n.val ≤ work.path.val.length) :
    WP.spec (spanning_tree.depth_first_loop0 root work n 0#usize)
      (constructorInitializedPrefix work · root n.val) := by
  let invariant : spanning_tree.Workspace × Usize → Prop := fun state =>
    state.2.val ≤ n.val ∧ constructorInitializedPrefix work state.1 root state.2.val
  unfold spanning_tree.depth_first_loop0
  apply loop.spec_decr_nat
    (fun state : spanning_tree.Workspace × Usize => n.val - state.2.val) invariant
  · rintro ⟨scratch, index⟩ hinv
    obtain ⟨hindex, hsvalid, hpath, hframes, hslots, hnodes, hcount, hedges,
      hprefix, hsuffix⟩ := hinv
    dsimp only at hindex hprefix hsuffix
    unfold spanning_tree.depth_first_loop0.body
    by_cases hmore : index < n
    · have hi : index.val < n.val := by simpa using hmore
      have hseen : index.val < scratch.seen.val.length := by
        have h := hsvalid.1
        rw [h, hpath]
        omega
      have hparents : index.val < scratch.parents.val.length := by
        have h := hsvalid.2.2.1
        rw [h, hpath]
        omega
      have hincoming : index.val < scratch.incoming.val.length := by
        have h := hsvalid.2.2.2.1
        rw [h, hpath]
        omega
      simp only [hmore, ite_true, alloc.vec.Vec.index_mut_slice_index]
      apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec scratch.seen index hseen)
      rintro ⟨oldSeen, backSeen⟩ ⟨_, rfl⟩
      apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec scratch.parents index hparents)
      rintro ⟨oldParent, backParent⟩ ⟨_, rfl⟩
      apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec scratch.incoming index hincoming)
      rintro ⟨oldIncoming, backIncoming⟩ ⟨_, rfl⟩
      apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
        have hn : n.val ≤ Usize.max := by scalar_tac
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro next hn
      have hnext : next.val = index.val + 1 := by simpa using hn
      apply (WP.spec_ok _).mpr
      dsimp only [invariant]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      change constructorInitializedPrefix work
        { scratch with
          seen := scratch.seen.set index false
          parents := scratch.parents.set index root
          incoming := scratch.incoming.set index 0#usize } root next.val
      refine And.intro ?_ ?_
      · simpa [WorkspaceValid] using hsvalid
      · refine ⟨hpath, hframes, hslots, hnodes, hcount, hedges, ?_, ?_⟩
        · intro j hj
          by_cases he : j = index.val
          · subst j
            simp [alloc.vec.Vec.set, hseen, hparents, hincoming]
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
      exact ⟨hsvalid, hpath, hframes, hslots, hnodes, hcount, hedges,
        by simpa only [he] using hprefix, by simpa only [he] using hsuffix⟩
  · refine ⟨by simp, hvalid, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro j hj
      simp at hj
    · intro j _
      exact ⟨rfl, rfl, rfl⟩

end Labyrinth
