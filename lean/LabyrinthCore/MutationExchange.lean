module
public import LabyrinthCore.MutationEditEdges

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

/-- The one-edge slice used by the public exchange wrapper. -/
def mutationSingletonEdge (edge : topology.Edge) : Slice topology.Edge :=
  Slice.from [edge] (by scalar_tac)

/-- The exact canonical parent edge removed by `Tree.exchange`. -/
def mutationExchangeCut (t : spanning_tree.Tree) (child : Usize) : topology.Edge :=
  mutationCanonicalEdge {
    u := child
    v := t.parents.val[child.val]?.getD 0#usize
  }

/-- The actual exchange wrapper preserves publication on error and returns a valid tree
with exactly its computed parent edge removed and supplied attachment edge added. -/
theorem mutation_exchange_tree_valid
    (c : topology.Carrier) (t : spanning_tree.Tree) (child : Usize)
    (attach : topology.Edge) (w : spanning_tree.Workspace)
    (hc : CarrierValid c) (ht : TreeValid c t) (hw : WorkspaceValid w)
    (hcapacity : t.parents.val.length ≤ w.path.val.length)
    (hedgeCapacity : c.edges.val.length ≤ w.edge_capacity.val) :
    spanning_tree.Tree.exchange t c child attach w ⦃ out =>
      WorkspaceValid out.2.2 ∧
      (∀ error, out.1 = core.result.Result.Err error → out.2.1 = t) ∧
      (out.1 = core.result.Result.Ok () →
        TreeValid c out.2.1 ∧ out.2.1.root = t.root ∧
        ∀ u v, parentEdge (parents out.2.1) u v ↔
          MutationEditedEdge (parents t)
            (mutationSingletonEdge (mutationExchangeCut t child))
            (mutationSingletonEdge attach) u v) ⦄ := by
  unfold spanning_tree.Tree.exchange
  by_cases hchild : child.val < t.parents.val.length
  · have hguard : ¬ child ≥ alloc.vec.Vec.len t.parents := Nat.not_le.mpr hchild
    simp only [hguard, ite_false]
    by_cases hroot : child = t.root
    · simp [hroot, hw]
    · simp only [hroot, ite_false, alloc.vec.Vec.index_slice_index]
      apply spec_bind (alloc.vec.Vec.index_usize_spec t.parents child hchild)
      intro parent hparent
      apply spec_bind (mutation_edge_new_total child parent)
      intro cut hcut
      have hcutExact : cut = mutationExchangeCut t child := by
        rw [hcut]
        unfold mutationExchangeCut
        have hget : t.parents.val[child.val]? = some parent := by
          simp [hchild, hparent]
        simp [hget]
      have hremoveSlice :
          Array.to_slice (Array.make 1#usize [cut]) = mutationSingletonEdge cut := by
        apply Slice.ext
        simp [Array.to_slice, Array.make, mutationSingletonEdge]
      have hremoveTarget :
          Array.to_slice (Array.make 1#usize [cut]) =
            mutationSingletonEdge (mutationExchangeCut t child) :=
        hremoveSlice.trans (congrArg mutationSingletonEdge hcutExact)
      have haddSlice :
          Array.to_slice (Array.make 1#usize [attach]) = mutationSingletonEdge attach := by
        apply Slice.ext
        simp [Array.to_slice, Array.make, mutationSingletonEdge]
      simp only [lift, bind_ok]
      apply spec_mono (mutation_edit_edges_tree_valid c t
        (Array.to_slice (Array.make 1#usize [cut]))
        (Array.to_slice (Array.make 1#usize [attach])) w
        hc ht hw hcapacity hedgeCapacity)
      intro out hout
      refine ⟨hout.1, hout.2.2.1, ?_⟩
      intro hok
      have hs := hout.2.2.2 hok
      refine ⟨hs.2.2.2.2, hs.1, ?_⟩
      simpa only [hremoveTarget, haddSlice] using hs.2.2.1
  · have hguard : child ≥ alloc.vec.Vec.len t.parents := Nat.le_of_not_gt hchild
    simp [hguard, hw]

end Labyrinth
