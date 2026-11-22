module
public import LabyrinthCore.ScenePreflight

/-! Scene edits (S3), part 2b: what `preflight_edit` leaves behind. A rejected or accepted preflight
changes nothing but the scratch list `required`, which keeps its invariant; an accepted one pairs
removals with additions, certifies every route edge against the edit and leaves exactly the route
edges in `required`. Partial correctness (`OkPost`), as the doorway tests reach the geometry. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- The route check leaves a duplicate-free list inside the carrier's edges, whatever its verdict. -/
theorem pf_route_call_inv (self : scene.Scene) (edit : scene.Edit)
    (req : alloc.vec.Vec topology.Edge) (r : core.result.Result Unit topology.Error)
    (hc : CarrierValid self.layout.carrier) (hinv : RouteInv self.layout.carrier self.required)
    (h : PfRouteCall self edit req r) : RouteInv self.layout.carrier req :=
  (scene_check_routes_required_exact self.layout (PfRoutes self edit)
    (alloc.vec.Vec.deref self.phases) (alloc.vec.Vec.deref self.next_phases) (some self.tree)
    edit self.required hc hinv (r, req) h).1

/-- A passing route check certifies every route edge against the edit. -/
theorem pf_route_call_certificate (self : scene.Scene) (edit : scene.Edit)
    (req : alloc.vec.Vec topology.Edge)
    (hc : CarrierValid self.layout.carrier) (hinv : RouteInv self.layout.carrier self.required)
    (h : PfRouteCall self edit req (core.result.Result.Ok ())) :
    req.val = foldEdges [] (allEdges (PfRoutes self edit).val) ∧
    ∀ e ∈ allEdges (PfRoutes self edit).val,
      MutationEditedEdge (parents self.tree) edit.remove edit.add e.u.val e.v.val :=
  ⟨(scene_check_routes_required_exact self.layout (PfRoutes self edit)
      (alloc.vec.Vec.deref self.phases) (alloc.vec.Vec.deref self.next_phases) (some self.tree)
      edit self.required hc hinv (core.result.Result.Ok (), req) h).2.1 rfl,
   scene_check_routes_route_certificate self.layout (PfRoutes self edit)
      (alloc.vec.Vec.deref self.phases) (alloc.vec.Vec.deref self.next_phases) self.tree edit
      self.required hc hinv (core.result.Result.Ok (), req) h rfl⟩

/-- A rejected or accepted preflight changes nothing but the scratch list `required`, which keeps its
invariant. -/
theorem scene_preflight_edit_frame (self : scene.Scene) (edit : scene.Edit)
    (hc : CarrierValid self.layout.carrier) (hinv : RouteInv self.layout.carrier self.required) :
    OkPost (scene.Scene.preflight_edit self edit) (fun p =>
      ∃ req, p.2 = { self with required := req } ∧ RouteInv self.layout.carrier req) := by
  refine okPost_mono (scene_preflight_edit_spec self edit) ?_
  intro p hp
  have hself : self = { self with required := self.required } := rfl
  rcases hp with ⟨_, rfl⟩ | ⟨_, h | ⟨_, req, h | ⟨hcall, h⟩⟩⟩
  · exact ⟨self.required, hself, hinv⟩
  · obtain ⟨x, k, _, _, _, rfl⟩ := h
    exact ⟨self.required, hself, hinv⟩
  · obtain ⟨x, hcall, rfl⟩ := h
    exact ⟨req, rfl, pf_route_call_inv self edit req _ hc hinv hcall⟩
  · refine ⟨req, ?_, pf_route_call_inv self edit req _ hc hinv hcall⟩
    rcases h with ⟨x, k, _, _, _, rfl⟩ | ⟨_, ⟨x, k, _, _, _, rfl⟩ | ⟨mv, _, _, rfl⟩⟩
    · rfl
    · rfl
    · rfl

/-- A passing route check means the routes cover every circle. -/
theorem pf_route_call_len (self : scene.Scene) (edit : scene.Edit)
    (req : alloc.vec.Vec topology.Edge) (h : PfRouteCall self edit req (core.result.Result.Ok ())) :
    (PfRoutes self edit).val.length = self.layout.circles.val.length := by
  unfold PfRouteCall scene.check_routes at h
  by_cases hne : (Slice.len (PfRoutes self edit) != alloc.vec.Vec.len self.layout.circles) = true
  · simp [hne] at h
  · simpa [Slice.len] using hne

/-- An accepted preflight: the removals and additions pair up, every route edge of the edit's routes
(else the scene's) is either added by the edit or a tree edge the edit does not remove, and
`required` holds exactly the route edges once each. -/
theorem scene_preflight_edit_accepted (self : scene.Scene) (edit : scene.Edit)
    (hc : CarrierValid self.layout.carrier) (hinv : RouteInv self.layout.carrier self.required) :
    OkPost (scene.Scene.preflight_edit self edit) (fun p =>
      ∀ moving, p.1 = core.result.Result.Ok moving →
        edit.remove.val.length = edit.add.val.length ∧
        moving.val ≤ self.tree.parents.val.length ∧
        (∀ j, j < edit.remove.val.length →
          RemovalVerdict self edit.remove j (core.result.Result.Ok ())) ∧
        ∃ req, p.2 = { self with required := req } ∧
          req.val = foldEdges [] (allEdges (PfRoutes self edit).val) ∧
          RouteInv self.layout.carrier req ∧
          (∀ e ∈ allEdges (PfRoutes self edit).val,
            MutationEditedEdge (parents self.tree) edit.remove edit.add e.u.val e.v.val) ∧
          (PfRoutes self edit).val.length = self.layout.circles.val.length) := by
  refine okPost_mono (scene_preflight_edit_spec self edit) ?_
  intro p hp moving hm
  rcases hp with ⟨_, rfl⟩ | ⟨heq, h | ⟨hrem, req, h | ⟨hcall, h⟩⟩⟩
  · simp at hm
  · obtain ⟨x, k, _, _, _, rfl⟩ := h
    simp at hm
  · obtain ⟨x, hcall, rfl⟩ := h
    simp at hm
  · obtain ⟨hfold, hcert⟩ := pf_route_call_certificate self edit req hc hinv hcall
    have hI := pf_route_call_inv self edit req _ hc hinv hcall
    rcases h with ⟨x, k, _, _, _, rfl⟩ | ⟨_, ⟨x, k, _, _, _, rfl⟩ | ⟨mv, hmv, _, rfl⟩⟩
    · simp at hm
    · simp at hm
    · simp only [core.result.Result.Ok.injEq] at hm
      subst hm
      exact ⟨heq, hmv, hrem, req, rfl, hfold, hI, hcert, pf_route_call_len self edit req hcall⟩

end Labyrinth
