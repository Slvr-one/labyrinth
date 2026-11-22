module
public import LabyrinthCore.SceneInvNewTree
public import LabyrinthCore.ConstructorCarrierRowsErrors
public import LabyrinthCore.SceneInvSummary
public import LabyrinthCore.SceneGeometryLayoutTotal

/-! The scene invariant, part 14: no remaining hypothesis.

`scene_new_full_unconditional`: the scene `Scene::new` returns, on a layout `Layout::new` accepted,
satisfies the hold law, the edit capacity and the whole scene invariant, with no hypothesis on its
tree (`scene_new_tree` proves the tree valid on the layout's carrier).

`SceneReachableU` is `SceneReachable` with the tree hypothesis of the construction step removed:
its base case needs only a layout `Layout::new` accepted and a call of `Scene::new` that returned
`Ok`. `sceneReachableU_toReachable` shows every such scene is `SceneReachable`, and
`sceneReachable_inv_unconditional` states the invariant and the hold law for all of them.

`Layout::new` reports one of seven errors (`layout_new_error_set`), the five that `Carrier::from_edges`
leaves possible (`from_edges_error_set`) joining the layout's own. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- **`Scene::new` establishes the hold law, the edit capacity and the scene invariant**, for a
layout whose carrier is valid and has one cell per layout cell, with no hypothesis on the tree. -/
theorem scene_new_full_unconditional {R : Type _} (treeRngInst : tree.Rng R)
    (hrng : constructorLegalRng treeRngInst) (layout : scene.Layout)
    (routes : Slice scene.Route) (occupants : Slice Std.Usize) (patch_capacity : Std.Usize)
    (epoch : Std.U64) (rng : R) (hc : CarrierValid layout.carrier) (hL : LayoutGeom layout)
    (hcells : cellCount layout.carrier = layout.cells.val.length) :
    OkPost (scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng)
      (fun p => ∀ s, p.1 = .Ok s → HoldLaw s ∧ EditCapacity s ∧ SceneInv s) :=
  okPost_mono (okPost_and
    (scene_new_full treeRngInst hrng layout routes occupants patch_capacity epoch rng hc hL)
    (scene_new_tree treeRngInst hrng layout routes occupants patch_capacity epoch rng hc hcells))
    (fun _ hp s hs => ⟨(hp.1 s hs).1, (hp.1 s hs).2.1, (hp.1 s hs).2.2 (hp.2 s hs)⟩)

/-- Scenes built by `Scene::new` on a layout `Layout::new` accepted, and changed by the covered
operations: `SceneReachable` without the tree hypothesis. -/
inductive SceneReachableU : scene.Scene → Prop
  | new {R : Type} (treeRngInst : tree.Rng R) (hrng : constructorLegalRng treeRngInst)
      (grid_spec : grid.GridSpec) (specs : alloc.vec.Vec polar.PolarSpec)
      (ps : Slice polar.PortalSpec) (geometry : grid.Geometry) (layout : scene.Layout)
      (hlayout : scene.Layout.new grid_spec specs ps geometry = ok (.Ok layout))
      (routes : Slice scene.Route) (occupants : Slice Std.Usize) (patch_capacity : Std.Usize)
      (epoch : Std.U64) (rng rng' : R) (s : scene.Scene)
      (h : scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng =
        ok (.Ok s, rng')) : SceneReachableU s
  | suspend (s s' : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64) (hs : SceneReachableU s)
      (h : ∃ r, scene.Scene.suspend s stamp wall = ok (r, s')) : SceneReachableU s'
  | resume (s s' : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64) (hs : SceneReachableU s)
      (h : ∃ r, scene.Scene.resume s stamp wall = ok (r, s')) : SceneReachableU s'
  | request_layout (s s' : scene.Scene) (stamp : walker.Stamp) (hs : SceneReachableU s)
      (h : ∃ r, scene.Scene.request_layout s stamp = ok (r, s')) : SceneReachableU s'
  | reject_layout (s s' : scene.Scene) (request : Std.U64) (viewport : grid.Rect)
      (hs : SceneReachableU s)
      (h : ∃ r, scene.Scene.reject_layout s request viewport = ok (r, s')) : SceneReachableU s'
  | publish_layout (s c s' : scene.Scene) (request : Std.U64) (hs : SceneReachableU s)
      (hc : SceneReachableU c)
      (h : ∃ r, scene.Scene.publish_layout s request c = ok (r, s')) : SceneReachableU s'
  | begin_crossing (s s' : scene.Scene) (stamp : walker.Stamp) (wi target : Std.Usize)
      (duration : Std.U32) (hs : SceneReachableU s)
      (h : ∃ r, scene.Scene.begin_crossing s stamp wi target duration = ok (r, s')) :
      SceneReachableU s'
  | motion (s s' : scene.Scene) (stamp : walker.Stamp) (steps : Slice Std.I32) (edit : scene.Edit)
      (hs : SceneReachableU s)
      (h : ∃ r, scene.Scene.motion s stamp steps edit = ok (r, s')) : SceneReachableU s'
  | carve (s s' : scene.Scene) (stamp : walker.Stamp) (wi target : Std.Usize) (edit : scene.Edit)
      (hs : SceneReachableU s)
      (h : ∃ r, scene.Scene.carve s stamp wi target edit = ok (r, s')) : SceneReachableU s'
  | tick (s s' : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64) (hs : SceneReachableU s)
      (h : ∃ r, scene.Scene.tick s stamp wall = ok (r, s')) : SceneReachableU s'
  | begin_shatter (s s' : scene.Scene) (stamp : walker.Stamp) (cells : Slice Std.Usize)
      (hs : SceneReachableU s)
      (h : ∃ r, scene.Scene.begin_shatter s stamp cells = ok (r, s')) : SceneReachableU s'
  | hide_patch (s s' : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
      (hs : SceneReachableU s)
      (h : ∃ r, scene.Scene.hide_patch s stamp id = ok (r, s')) : SceneReachableU s'
  | scatter_patch (s s' : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
      (duration : Std.U64) (hs : SceneReachableU s)
      (h : ∃ r, scene.Scene.scatter_patch s stamp id duration = ok (r, s')) : SceneReachableU s'
  | reform_patch (s s' : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
      (duration : Std.U64) (edit : scene.Edit) (hs : SceneReachableU s)
      (h : ∃ r, scene.Scene.reform_patch s stamp id duration edit = ok (r, s')) :
      SceneReachableU s'
  | swept_doorway (s s' : scene.Scene) (edge : topology.Edge) (steps : Slice Std.I32)
      (hs : SceneReachableU s)
      (h : ∃ r, scene.Scene.swept_doorway s edge steps = ok (r, s')) : SceneReachableU s'

/-- Every `SceneReachableU` scene is `SceneReachable`: the tree hypothesis always holds. -/
theorem sceneReachableU_toReachable {s : scene.Scene} (h : SceneReachableU s) :
    SceneReachable s := by
  induction h with
  | new treeRngInst hrng grid_spec specs ps geometry layout hlayout routes occupants
      patch_capacity epoch rng rng' s h =>
    obtain ⟨hL, hc⟩ := layout_new_geom grid_spec specs ps geometry _ hlayout layout rfl
    have hcells := layout_new_carrier_cells grid_spec specs ps geometry _ hlayout layout rfl
    exact SceneReachable.new treeRngInst hrng grid_spec specs ps geometry layout hlayout routes
      occupants patch_capacity epoch rng rng' s h
      (scene_new_tree treeRngInst hrng layout routes occupants patch_capacity epoch rng hc hcells
        _ h s rfl)
  | suspend s s' stamp wall _ h ih => exact SceneReachable.suspend s s' stamp wall ih h
  | resume s s' stamp wall _ h ih => exact SceneReachable.resume s s' stamp wall ih h
  | request_layout s s' stamp _ h ih => exact SceneReachable.request_layout s s' stamp ih h
  | reject_layout s s' request viewport _ h ih =>
    exact SceneReachable.reject_layout s s' request viewport ih h
  | publish_layout s c s' request _ _ h ih ihc =>
    exact SceneReachable.publish_layout s c s' request ih ihc h
  | begin_crossing s s' stamp wi target duration _ h ih =>
    exact SceneReachable.begin_crossing s s' stamp wi target duration ih h
  | motion s s' stamp steps edit _ h ih => exact SceneReachable.motion s s' stamp steps edit ih h
  | carve s s' stamp wi target edit _ h ih =>
    exact SceneReachable.carve s s' stamp wi target edit ih h
  | tick s s' stamp wall _ h ih => exact SceneReachable.tick s s' stamp wall ih h
  | begin_shatter s s' stamp cells _ h ih =>
    exact SceneReachable.begin_shatter s s' stamp cells ih h
  | hide_patch s s' stamp id _ h ih => exact SceneReachable.hide_patch s s' stamp id ih h
  | scatter_patch s s' stamp id duration _ h ih =>
    exact SceneReachable.scatter_patch s s' stamp id duration ih h
  | reform_patch s s' stamp id duration edit _ h ih =>
    exact SceneReachable.reform_patch s s' stamp id duration edit ih h
  | swept_doorway s s' edge steps _ h ih => exact SceneReachable.swept_doorway s s' edge steps ih h

/-- **Every scene reachable from `Scene::new` satisfies the scene invariant and the hold law, with
no remaining hypothesis.** The base case needs a layout `Layout::new` accepted and a `Scene::new`
call that returned `Ok`. -/
theorem sceneReachable_inv_unconditional {s : scene.Scene} (h : SceneReachableU s) :
    SceneInvFull s :=
  sceneReachable_inv (sceneReachableU_toReachable h)

/-- Every hold counter of an unconditionally reachable scene is the number of crossing-holds on it. -/
theorem sceneReachableU_hold_exact {s : scene.Scene} (h : SceneReachableU s) :
    ∀ k, k < s.holds.val.length → ∃ a, s.holds.val[k]? = some a ∧
      a.val = crossMult s.walkers.val k :=
  reachable_hold_exact (sceneReachableU_toReachable h)

/-! ### The error sets -/

/-- The seven errors `Layout::new` can return. -/
def LayoutNewErrSet (e : topology.Error) : Prop :=
  e = .InvalidGeometry ∨ e = .InvalidSize ∨ e = .Overflow ∨ e = .InvalidIndex ∨
    e = .InsufficientWorkspace ∨ e = .InvalidCarrier ∨ e = .Disconnected

/-- **`Layout::new`'s error list is a closed set**: the geometry, size, overflow, index and
workspace errors of the layout itself, and the two errors (`InvalidCarrier`, `Disconnected`) that
`Carrier::from_edges` adds to `InvalidSize`, `InvalidIndex` and `Overflow`. -/
theorem layoutNewErr_closed {e : topology.Error} (h : LayoutNewErr e) : LayoutNewErrSet e := by
  unfold LayoutNewErr at h
  unfold LayoutNewErrSet
  rcases h with h | h | h | h | h | ⟨n, es, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · have hs := from_edges_error_set n es _ h e rfl
    unfold FromEdgesErrSet at hs
    rcases hs with hs | hs | hs | hs | hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs)))))
    · exact Or.inr (Or.inr (Or.inl hs))

/-- **`layout_new_total` with a closed error list.** On representable capacities `Layout::new`
returns, and an `Ok` result is a valid layout with a valid carrier of one cell per layout cell; an
`Err` is one of the seven errors in `LayoutNewErrSet`. -/
theorem layout_new_total_closed (grid_spec : grid.GridSpec)
    (specs : alloc.vec.Vec polar.PolarSpec) (ps : Slice polar.PortalSpec)
    (geometry : grid.Geometry) (hcap : LayoutCapacity grid_spec specs ps) :
    ∃ r, scene.Layout.new grid_spec specs ps geometry = ok r ∧
      (∀ L, r = .Ok L → LayoutGeom L ∧ CarrierValid L.carrier ∧ LayoutFloor L ∧
        cellCount L.carrier = L.cells.val.length) ∧
      (∀ e, r = .Err e → LayoutNewErrSet e) := by
  obtain ⟨r, hr, hok, herr⟩ := layout_new_total grid_spec specs ps geometry hcap
  refine ⟨r, hr, fun L hL => ⟨(hok L hL).1, (hok L hL).2.1, (hok L hL).2.2,
    layout_new_carrier_cells grid_spec specs ps geometry r hr L hL⟩,
    fun e he => layoutNewErr_closed (herr e he)⟩

end Labyrinth
