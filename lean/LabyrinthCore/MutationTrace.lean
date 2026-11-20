module
public import LabyrinthCore.MutationExchange
public import LabyrinthCore.MutationRerootSpec

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

/-- The three public tree mutations whose accepted finite traces are covered. -/
inductive MutationOperation where
  | reroot (newRoot : Usize)
  | edit (remove add : Slice topology.Edge)
  | exchange (child : Usize) (attach : topology.Edge)

/-- Execute one trace event through the actual generated public operation. -/
def mutationOperationApply (operation : MutationOperation)
    (t : spanning_tree.Tree) (c : topology.Carrier) (w : spanning_tree.Workspace) :
    Result ((core.result.Result Unit topology.Error) × spanning_tree.Tree ×
      spanning_tree.Workspace) :=
  match operation with
  | .reroot newRoot => spanning_tree.Tree.reroot t newRoot w
  | .edit remove add => spanning_tree.Tree.edit_edges t c remove add w
  | .exchange child attach => spanning_tree.Tree.exchange t c child attach w

/-- Capacity preconditions needed by the checked edit and exchange contracts. -/
def MutationOperationReady (c : topology.Carrier) (t : spanning_tree.Tree)
    (w : spanning_tree.Workspace) : MutationOperation → Prop
  | .reroot _ => True
  | .edit _ _ | .exchange _ _ =>
      t.parents.val.length ≤ w.path.val.length ∧
        c.edges.val.length ≤ w.edge_capacity.val

/-- Every actual operation preserves tree/workspace validity, and every returned error
retains the published tree exactly. -/
theorem mutation_operation_preserves
    (c : topology.Carrier) (t : spanning_tree.Tree) (w : spanning_tree.Workspace)
    (operation : MutationOperation) (hc : CarrierValid c) (ht : TreeValid c t)
    (hw : WorkspaceValid w) (hready : MutationOperationReady c t w operation) :
    mutationOperationApply operation t c w ⦃ out =>
      TreeValid c out.2.1 ∧ WorkspaceValid out.2.2 ∧
        ∀ error, out.1 = core.result.Result.Err error → out.2.1 = t ⦄ := by
  cases operation with
  | reroot newRoot =>
      apply spec_mono (mutation_reroot_preserves c t newRoot w hc ht hw)
      intro out hout
      exact ⟨hout.1, hout.2.1, hout.2.2.2.1⟩
  | edit remove add =>
      rcases hready with ⟨hcapacity, hedgeCapacity⟩
      apply spec_mono
        (mutation_edit_edges_tree_valid c t remove add w hc ht hw hcapacity hedgeCapacity)
      intro out hout
      have hvalid : TreeValid c out.2.1 := by
        cases hstatus : out.1 with
        | Ok payload =>
            cases payload
            exact (hout.2.2.2 hstatus).2.2.2.2
        | Err error =>
            rw [hout.2.2.1 error hstatus]
            exact ht
      exact ⟨hvalid, hout.1, hout.2.2.1⟩
  | exchange child attach =>
      rcases hready with ⟨hcapacity, hedgeCapacity⟩
      apply spec_mono
        (mutation_exchange_tree_valid c t child attach w hc ht hw hcapacity hedgeCapacity)
      intro out hout
      have hvalid : TreeValid c out.2.1 := by
        cases hstatus : out.1 with
        | Ok payload =>
            cases payload
            exact (hout.2.2 hstatus).1
        | Err error =>
            rw [hout.2.1 error hstatus]
            exact ht
      exact ⟨hvalid, hout.1, hout.2.1⟩

/-- An accepted trace records only actual successful operation evaluations and each
operation's input readiness. Its state list contains the initial state and every prefix state. -/
inductive MutationAcceptedTrace (c : topology.Carrier) :
    spanning_tree.Tree → spanning_tree.Workspace → List MutationOperation →
      List (spanning_tree.Tree × spanning_tree.Workspace) → Prop where
  | nil (t : spanning_tree.Tree) (w : spanning_tree.Workspace) :
      MutationAcceptedTrace c t w [] [(t, w)]
  | cons {t next : spanning_tree.Tree} {w nextWork : spanning_tree.Workspace}
      {operation : MutationOperation} {operations : List MutationOperation}
      {states : List (spanning_tree.Tree × spanning_tree.Workspace)}
      (ready : MutationOperationReady c t w operation)
      (accepted : mutationOperationApply operation t c w =
        Result.ok (core.result.Result.Ok (), next, nextWork))
      (tail : MutationAcceptedTrace c next nextWork operations states) :
      MutationAcceptedTrace c t w (operation :: operations) ((t, w) :: states)

/-- Every state reached by an accepted finite trace—equivalently, every accepted prefix—
is a valid tree over the same carrier with a valid reusable workspace. -/
theorem mutation_accepted_trace_prefix_valid
    (c : topology.Carrier) (hc : CarrierValid c) :
    ∀ {t : spanning_tree.Tree} {w : spanning_tree.Workspace}
      {operations : List MutationOperation}
      {states : List (spanning_tree.Tree × spanning_tree.Workspace)},
      TreeValid c t → WorkspaceValid w →
      MutationAcceptedTrace c t w operations states →
      ∀ state ∈ states, TreeValid c state.1 ∧ WorkspaceValid state.2 := by
  intro t w operations states ht hw htrace
  induction htrace with
  | nil =>
      intro state hstate
      simp only [List.mem_singleton] at hstate
      subst state
      exact ⟨ht, hw⟩
  | @cons t next w nextWork operation operations states ready accepted tail ih =>
      have hstep := mutation_operation_preserves c t w operation hc ht hw ready
      rw [accepted] at hstep
      have hnext : TreeValid c next ∧ WorkspaceValid nextWork := by
        have hactual := (spec_ok _).mp hstep
        exact ⟨hactual.1, hactual.2.1⟩
      intro state hstate
      simp only [List.mem_cons] at hstate
      rcases hstate with rfl | hstate
      · exact ⟨ht, hw⟩
      · exact ih hnext.1 hnext.2 state hstate

end Labyrinth
