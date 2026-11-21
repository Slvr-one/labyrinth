module
public import LabyrinthCore.SceneRouteBudget

/-! Scene construction (S2), part 3a: every edge `check_routes` leaves in `required` was admitted
by `Layout::doorway` under the tables it was called with. The statement is partial correctness
(`OkPost`), because the doorway's geometry is not shown to be total here. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- `Layout::doorway` admits `e` under these tables. -/
def DoorwayAdmits (L : scene.Layout) (phases next : Slice Std.I32) (e : topology.Edge) : Prop :=
  ∃ d, scene.Layout.doorway L e phases next = ok (core.result.Result.Ok d)

/-- Every edge in the scratch list is admitted. -/
def AdmittedList (L : scene.Layout) (phases next : Slice Std.I32)
    (req : alloc.vec.Vec topology.Edge) : Prop :=
  ∀ e ∈ req.val, DoorwayAdmits L phases next e

theorem vec_push_ok {α : Type _} (v : alloc.vec.Vec α) (x : α) (r : alloc.vec.Vec α)
    (h : alloc.vec.Vec.push v x = ok r) : r.val = v.val ++ [x] := by
  unfold alloc.vec.Vec.push at h
  dsimp only at h
  split at h
  · simp only [ok.injEq] at h
    subst h
    simp [alloc.vec.Vec.from_val]
  · simp at h

/-- The admission block keeps the list admitted, provided the edge is. -/
theorem route_admit_admitted (L : scene.Layout) (phases next : Slice Std.I32)
    (edge : topology.Edge) (req : alloc.vec.Vec topology.Edge)
    (hedge : DoorwayAdmits L phases next edge) :
    OkPost (routeAdmit L edge req) (fun p =>
      AdmittedList L phases next req → AdmittedList L phases next p.2) := by
  unfold routeAdmit
  refine okPost_bind (okPost_trivial _) ?_
  intro b _
  by_cases hb : b = true
  · simp only [hb, ↓reduceIte]
    exact okPost_ok (fun h => h)
  · simp only [hb]
    refine okPost_bind (okPost_trivial _) ?_
    intro s1 _
    by_cases hi : alloc.vec.Vec.len req = Slice.len s1
    · simp only [hi, ↓reduceIte]
      exact okPost_ok (fun h => h)
    · simp only [hi, ↓reduceIte]
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro r1 hr1 _
      have hv := vec_push_ok _ _ _ hr1
      refine okPost_ok (fun h x hx => ?_)
      rw [hv] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h x hx
      · rw [List.mem_singleton.mp hx]; exact hedge

/-- One edge check keeps the scratch list admitted. -/
theorem check_route_edge_admitted (L : scene.Layout)
    (edge : core.result.Result (Option topology.Edge) topology.Error)
    (phases next : Slice Std.I32) (pub : scene.RoutePublication)
    (req : alloc.vec.Vec topology.Edge) :
    OkPost (scene.check_route_edge L edge phases next pub req) (fun p =>
      AdmittedList L phases next req → AdmittedList L phases next p.2) := by
  unfold scene.check_route_edge
  cases edge with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    exact okPost_ok (fun h => h)
  | Ok val =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    cases val with
    | none => exact okPost_ok (fun h => h)
    | some e =>
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro r hdoor _
      cases r with
      | Err y =>
        simp only [Std.bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok]
        exact okPost_ok (fun h => h)
      | Ok d =>
        have hadm : DoorwayAdmits L phases next e := ⟨d, hdoor⟩
        simp only [Std.bind_ok]
        have hA := route_admit_admitted L phases next e req hadm
        cases hct : pub.current_tree with
        | none =>
          simp only
          exact hA
        | some current =>
          simp only
          refine okPost_bind (okPost_trivial _) ?_
          intro b _
          by_cases hb : b = true
          · simp only [hb]
            exact hA
          · simp only [hb, Bool.false_eq_true, ↓reduceIte]
            refine okPost_bind (okPost_trivial _) ?_
            intro b1 _
            by_cases hb1 : b1 = true
            · simp only [hb1]
              refine okPost_bind (okPost_trivial _) ?_
              intro b2 _
              by_cases hb2 : b2 = true
              · simp only [hb2]
                exact okPost_ok (fun h => h)
              · simp only [hb2]
                exact hA
            · simp only [hb1, Bool.false_eq_true, ↓reduceIte]
              exact okPost_ok (fun h => h)

theorem check_route_loop_body_admitted (L : scene.Layout) (pub : scene.RoutePublication)
    (phases next : Slice Std.I32) (route : scene.Route)
    (req : alloc.vec.Vec topology.Edge) (st : core.result.Result Unit topology.Error)
    (interior : Bool) (prev i2 : Std.Usize) (hreq : AdmittedList L phases next req) :
    OkPost (scene.check_route_loop.body L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms route.circle route.cells phases next
        pub.current_tree pub.remove pub.add req st interior prev i2)
      (fun y => match y with
        | .cont s => AdmittedList L phases next s.1
        | .done y => AdmittedList L phases next y.1) := by
  unfold scene.check_route_loop.body
  by_cases hlt : i2 < alloc.vec.Vec.len route.cells
  · simp only [hlt, ↓reduceIte]
    refine okPost_bind (okPost_trivial _) ?_
    intro b _
    by_cases hb : b = true
    · simp only [hb, ↓reduceIte]
      refine okPost_bind (okPost_trivial _) ?_
      intro cell _
      refine okPost_bind (okPost_trivial _) ?_
      intro r _
      refine okPost_bind (okPost_trivial _) ?_
      intro e _
      refine okPost_bind (okPost_trivial _) ?_
      rintro ⟨interior1, r1⟩ _
      refine okPost_bind (m := scene.check_route_edge L r1 phases next pub req)
        (check_route_edge_admitted L r1 phases next pub req) ?_
      rintro ⟨st1, req1⟩ hpost
      refine okPost_bind (okPost_trivial _) ?_
      intro i4 _
      exact okPost_ok (hpost hreq)
    · simp only [hb]
      exact okPost_ok hreq
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok hreq

theorem check_route_loop_admitted (L : scene.Layout) (pub : scene.RoutePublication)
    (phases next : Slice Std.I32) (route : scene.Route)
    (req : alloc.vec.Vec topology.Edge) (st : core.result.Result Unit topology.Error)
    (interior : Bool) (prev i2 : Std.Usize) (hreq : AdmittedList L phases next req) :
    OkPost (scene.check_route_loop L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms route.circle route.cells phases next
        pub.current_tree pub.remove pub.add req st interior prev i2)
      (fun y => AdmittedList L phases next y.1) := by
  unfold scene.check_route_loop
  refine okPost_loop (fun s => AdmittedList L phases next s.1)
    (fun y : (alloc.vec.Vec topology.Edge) × (core.result.Result Unit topology.Error) × Bool =>
      AdmittedList L phases next y.1) _ ?_ (req, st, interior, prev, i2) hreq
  rintro ⟨req, st, interior, prev, i2⟩ h
  dsimp only
  refine okPost_mono (check_route_loop_body_admitted L pub phases next route req st interior
    prev i2 h) ?_
  intro y hy
  cases y <;> exact hy

theorem check_route_admitted (L : scene.Layout) (route : scene.Route) (circle : Std.Usize)
    (phases next : Slice Std.I32) (pub : scene.RoutePublication)
    (req : alloc.vec.Vec topology.Edge) (hreq : AdmittedList L phases next req) :
    OkPost (scene.check_route L route circle phases next pub req)
      (fun p => AdmittedList L phases next p.2) := by
  unfold scene.check_route
  by_cases h1 : (route.circle != circle) = true
  · simp only [h1, ↓reduceIte]
    exact okPost_ok hreq
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : alloc.vec.Vec.len route.cells < 7#usize
    · simp only [h2, ↓reduceIte]
      exact okPost_ok hreq
    · simp only [h2, ↓reduceIte]
      by_cases h3 : alloc.vec.Vec.len route.cells > alloc.vec.Vec.len L.cells
      · simp only [h3, ↓reduceIte]
        exact okPost_ok hreq
      · simp only [h3, ↓reduceIte]
        refine okPost_bind (check_route_loop_admitted L pub phases next route req
          (core.result.Result.Ok ()) false 0#usize 0#usize hreq) ?_
        rintro ⟨req1, st1, interior⟩ h1
        refine okPost_bind (okPost_trivial _) ?_
        intro cf _
        cases cf with
        | Continue v =>
          simp only
          by_cases hi : interior = true
          · simp only [hi, ↓reduceIte]
            exact okPost_ok h1
          · simp only [hi]
            exact okPost_ok h1
        | Break v =>
          simp only
          refine okPost_bind (okPost_trivial _) ?_
          intro r _
          exact okPost_ok h1

theorem check_routes_loop_body_admitted (L : scene.Layout) (tree : Option spanning_tree.Tree)
    (rem add : Slice topology.Edge)
    (phases next : Slice Std.I32) (routes : Slice scene.Route)
    (req : alloc.vec.Vec topology.Edge) (st : core.result.Result Unit topology.Error)
    (r : Std.Usize) (hreq : AdmittedList L phases next req) :
    OkPost (scene.check_routes_loop.body L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms routes phases next rem add tree req st r)
      (fun y => match y with
        | .cont s => AdmittedList L phases next s.1
        | .done y => AdmittedList L phases next y.2) := by
  unfold scene.check_routes_loop.body
  by_cases hlt : r < Slice.len routes
  · simp only [hlt, ↓reduceIte]
    refine okPost_bind (okPost_trivial _) ?_
    intro b _
    by_cases hb : b = true
    · simp only [hb, ↓reduceIte]
      refine okPost_bind (okPost_trivial _) ?_
      intro r1 _
      refine okPost_bind (m := scene.check_route L r1 r phases next ⟨tree, rem, add⟩ req)
        (check_route_admitted L r1 r phases next ⟨tree, rem, add⟩ req hreq) ?_
      rintro ⟨st1, req1⟩ h1
      refine okPost_bind (okPost_trivial _) ?_
      intro r2 _
      exact okPost_ok h1
    · simp only [hb]
      exact okPost_ok hreq
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok hreq

theorem check_routes_loop_admitted (L : scene.Layout) (tree : Option spanning_tree.Tree)
    (rem add : Slice topology.Edge)
    (phases next : Slice Std.I32) (routes : Slice scene.Route)
    (req : alloc.vec.Vec topology.Edge) (st : core.result.Result Unit topology.Error)
    (r : Std.Usize) (hreq : AdmittedList L phases next req) :
    OkPost (scene.check_routes_loop L.cell_grid L.cells L.circles L.portals L.bands
        L.geometry L.carrier L.transforms routes phases next rem add req tree st r)
      (fun y => AdmittedList L phases next y.2) := by
  unfold scene.check_routes_loop
  refine okPost_loop (fun s => AdmittedList L phases next s.1)
    (fun y : (core.result.Result Unit topology.Error) × (alloc.vec.Vec topology.Edge) =>
      AdmittedList L phases next y.2) _ ?_ (req, st, r) hreq
  rintro ⟨req, st, r⟩ h
  dsimp only
  refine okPost_mono (check_routes_loop_body_admitted L tree rem add phases next routes req st r
    h) ?_
  intro y hy
  cases y <;> exact hy

/-- Every edge `check_routes` leaves in `required` was admitted by the doorway under the tables
it was called with, whatever the verdict. -/
theorem scene_check_routes_admitted (L : scene.Layout) (routes : Slice scene.Route)
    (phases next : Slice Std.I32) (tree : Option spanning_tree.Tree) (edit : scene.Edit)
    (req : alloc.vec.Vec topology.Edge) (hreq : AdmittedList L phases next req) :
    OkPost (scene.check_routes L routes phases next tree edit req)
      (fun p => AdmittedList L phases next p.2) := by
  unfold scene.check_routes
  by_cases hne : (Slice.len routes != alloc.vec.Vec.len L.circles) = true
  · simp only [hne, ↓reduceIte]
    exact okPost_ok hreq
  · simp only [hne, Bool.false_eq_true, ↓reduceIte]
    refine okPost_bind (okPost_of_spec (vec_clear_spec alloc.alloc.Global req)) ?_
    intro req1 hreq1
    refine okPost_mono (check_routes_loop_admitted L tree edit.remove edit.add phases next routes
      req1 (core.result.Result.Ok ()) 0#usize ?_) ?_
    · intro e he
      simp [hreq1] at he
    · intro y hy; exact hy

end Labyrinth
