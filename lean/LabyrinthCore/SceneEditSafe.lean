module
public import LabyrinthCore.SceneEditPrepare

/-! Scene edits (S3), part 5: the invariant that edits preserve, and the commit step that
re-establishes it. An edit scene is safe when its carrier, tree and workspace are valid, its scratch
list is well formed, its routes cover every circle and every route edge is a tree edge. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- What every edit preserves. The workspace's edge capacity is a separate precondition of
`Tree::edit_edges` (see `EditCapacity`): its existing specification does not restate it for the
returned workspace. -/
def EditSafe (s : scene.Scene) : Prop :=
  CarrierValid s.layout.carrier ∧ TreeValid s.layout.carrier s.tree ∧ WorkspaceValid s.work ∧
  s.tree.parents.val.length ≤ s.work.path.val.length ∧
  RouteInv s.layout.carrier s.required ∧
  s.phases.val.length ≤ s.next_phases.val.length ∧
  s.routes.val.length = s.layout.circles.val.length ∧
  ∀ e ∈ allEdges s.routes.val, parentEdge (parents s.tree) e.u.val e.v.val

/-- The workspace can hold every carrier edge. -/
def EditCapacity (s : scene.Scene) : Prop :=
  s.layout.carrier.edges.val.length ≤ s.work.edge_capacity.val

theorem allEdges_deref (v : alloc.vec.Vec scene.Route) :
    allEdges (alloc.vec.Vec.deref v).val = allEdges v.val := by
  rw [deref_val]

/-- Committing an edit on a safe tree whose edges contain every route edge leaves a safe scene. -/
theorem edit_commit_safe (self2 : scene.Scene) (t : spanning_tree.Tree)
    (w : spanning_tree.Workspace) (edit : scene.Edit) (val : Std.U64)
    (hc : CarrierValid self2.layout.carrier) (ht : TreeValid self2.layout.carrier t)
    (hw : WorkspaceValid w) (hcap : t.parents.val.length ≤ w.path.val.length)
    (hreq : RouteInv self2.layout.carrier self2.required)
    (hph : self2.phases.val.length ≤ self2.next_phases.val.length)
    (hrl : self2.routes.val.length = self2.layout.circles.val.length)
    (hcirc : ∀ rs, edit.routes = some rs → rs.val.length = self2.layout.circles.val.length)
    (hcert : ∀ e ∈ allEdges (PfRoutes self2 edit).val, parentEdge (parents t) e.u.val e.v.val) :
    scene.Scene.commit_edit { self2 with tree := t, work := w } edit val ⦃ s3 =>
      EditSafe s3 ∧ s3.tree = t ∧ s3.work = w ∧ s3.layout = self2.layout ∧
      s3.required = self2.required ∧ s3.next_phases = self2.next_phases ∧
      s3.stamp = ({ self2.stamp with revision := val } : walker.Stamp) ∧
      s3.phases.val.length = self2.phases.val.length ∧
      (∀ j, j < self2.phases.val.length → s3.phases.val[j]? = self2.next_phases.val[j]?) ∧
      (edit.routes = none → s3.routes = self2.routes) ∧
      (∀ rs, edit.routes = some rs → allEdges s3.routes.val = allEdges rs.val) ⦄ := by
  apply spec_mono (scene_commit_edit_routes { self2 with tree := t, work := w } edit val hph
    (fun rs h => (hcirc rs h).trans hrl.symm))
  rintro s3 ⟨hnone, hsome, htr, hlay, hwk, hrq, _, _, hnp, hrlen, hst, hphl, hphp⟩
  dsimp only at hnone hsome htr hlay hwk hrq hnp hrlen hst hphl hphp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, htr, hwk, hlay, hrq, hnp, hst, hphl, hphp,
    hnone, hsome⟩
  · rw [hlay]; exact hc
  · rw [hlay, htr]; exact ht
  · rw [hwk]; exact hw
  · rw [htr, hwk]; exact hcap
  · rw [hlay, hrq]; exact hreq
  · rw [hnp]; omega
  · rw [hlay, hrlen]; exact hrl
  · intro e he
    rw [htr]
    cases hre : edit.routes with
    | none =>
      have := hnone hre
      rw [this] at he
      apply hcert e
      simp only [PfRoutes, hre, allEdges_deref]
      exact he
    | some rs =>
      rw [hsome rs hre] at he
      apply hcert e
      simpa [PfRoutes, hre] using he

/-- What an accepted edit leaves: a safe scene on the same layout, whose tree has exactly the edited
edge set, whose route cells are the edit's (or unchanged), stamped with the new revision. -/
def CommitPost (self2 : scene.Scene) (edit : scene.Edit) (val : Std.U64) (s3 : scene.Scene) :
    Prop :=
  EditSafe s3 ∧ s3.layout = self2.layout ∧
  (∀ u v, parentEdge (parents s3.tree) u v ↔
    MutationEditedEdge (parents self2.tree) edit.remove edit.add u v) ∧
  (edit.routes = none → s3.routes = self2.routes) ∧
  (∀ rs, edit.routes = some rs → allEdges s3.routes.val = allEdges rs.val) ∧
  s3.stamp = ({ self2.stamp with revision := val } : walker.Stamp) ∧
  s3.required = self2.required ∧ s3.next_phases = self2.next_phases ∧
  s3.phases.val.length = self2.phases.val.length ∧
  (∀ j, j < self2.phases.val.length → s3.phases.val[j]? = self2.next_phases.val[j]?)

/-- Committing on a tree whose edges are the edited edge set, when the preflight certified every
route edge against the edit. -/
theorem edit_commit_post (self2 : scene.Scene) (t : spanning_tree.Tree)
    (w : spanning_tree.Workspace) (edit : scene.Edit) (val : Std.U64)
    (hc : CarrierValid self2.layout.carrier) (ht : TreeValid self2.layout.carrier t)
    (hw : WorkspaceValid w) (hcap : t.parents.val.length ≤ w.path.val.length)
    (hreq : RouteInv self2.layout.carrier self2.required)
    (hph : self2.phases.val.length ≤ self2.next_phases.val.length)
    (hrl : self2.routes.val.length = self2.layout.circles.val.length)
    (hcirc : ∀ rs, edit.routes = some rs → rs.val.length = self2.layout.circles.val.length)
    (hedt : ∀ u v, parentEdge (parents t) u v ↔
      MutationEditedEdge (parents self2.tree) edit.remove edit.add u v)
    (hcert : ∀ e ∈ allEdges (PfRoutes self2 edit).val,
      MutationEditedEdge (parents self2.tree) edit.remove edit.add e.u.val e.v.val) :
    scene.Scene.commit_edit { self2 with tree := t, work := w } edit val ⦃ s3 =>
      CommitPost self2 edit val s3 ∧ s3.tree = t ∧ s3.work = w ⦄ := by
  apply spec_mono (edit_commit_safe self2 t w edit val hc ht hw hcap hreq hph hrl hcirc
    (fun e he => (hedt _ _).mpr (hcert e he)))
  rintro s3 ⟨hsafe, htr, hwk, hlay, hrq, hnp, hst, hphl, hphp, hnone, hsome⟩
  refine ⟨⟨hsafe, hlay, ?_, hnone, hsome, hst, hrq, hnp, hphl, hphp⟩, htr, hwk⟩
  rw [htr]
  exact hedt

theorem edited_edge_empty (before : List Nat) (remove add : Slice topology.Edge)
    (hr : remove.val.length = 0) (ha : add.val.length = 0) (u v : Nat) :
    MutationEditedEdge before remove add u v ↔ parentEdge before u v := by
  have hr' : remove.val = [] := List.length_eq_zero_iff.mp hr
  have ha' : add.val = [] := List.length_eq_zero_iff.mp ha
  simp [MutationEditedEdge, mutationRemoval, mutationAddition, hr', ha']

/-- Combine two `OkPost` facts about one computation. -/
theorem okPost_pair {α : Type _} {m : Result α} {P Q : α → Prop} (h1 : OkPost m P)
    (h2 : OkPost m Q) : OkPost m (fun a => P a ∧ Q a) := fun v hv => ⟨h1 v hv, h2 v hv⟩

end Labyrinth
