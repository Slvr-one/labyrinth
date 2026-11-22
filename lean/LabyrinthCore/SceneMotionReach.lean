module
public import LabyrinthCore.SceneMotionAdvance

/-! The motion planner (S7), part 2: reachability with `advance_motion`.

`SceneReachableM` is `SceneReachable` with one more operation, `advance_motion` with the motion
planner: scenes built by `Scene::new` and then changed by any sequence of the covered operations,
now including `advance_motion` (with any workspace), each on whatever it returns. Every scene
`SceneReachable` covers is in it (`sceneReachable_motion`), and every scene in it satisfies the
scene invariant and the hold law (`sceneReachableM_inv`), under the same single assumption about
the scene `Scene::new` returns. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- Scenes built by `Scene::new` and changed by the covered operations and `advance_motion`. -/
inductive SceneReachableM : scene.Scene → Prop
  | new {R : Type} (treeRngInst : tree.Rng R) (hrng : constructorLegalRng treeRngInst)
      (grid_spec : grid.GridSpec) (specs : alloc.vec.Vec polar.PolarSpec)
      (ps : Slice polar.PortalSpec) (geometry : grid.Geometry) (layout : scene.Layout)
      (hlayout : scene.Layout.new grid_spec specs ps geometry = ok (.Ok layout))
      (routes : Slice scene.Route) (occupants : Slice Std.Usize) (patch_capacity : Std.Usize)
      (epoch : Std.U64) (rng rng' : R) (s : scene.Scene)
      (h : scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng =
        ok (.Ok s, rng'))
      (htree : TreeValid s.layout.carrier s.tree) : SceneReachableM s
  | suspend (s s' : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64) (hs : SceneReachableM s)
      (h : ∃ r, scene.Scene.suspend s stamp wall = ok (r, s')) : SceneReachableM s'
  | resume (s s' : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64) (hs : SceneReachableM s)
      (h : ∃ r, scene.Scene.resume s stamp wall = ok (r, s')) : SceneReachableM s'
  | request_layout (s s' : scene.Scene) (stamp : walker.Stamp) (hs : SceneReachableM s)
      (h : ∃ r, scene.Scene.request_layout s stamp = ok (r, s')) : SceneReachableM s'
  | reject_layout (s s' : scene.Scene) (request : Std.U64) (viewport : grid.Rect)
      (hs : SceneReachableM s)
      (h : ∃ r, scene.Scene.reject_layout s request viewport = ok (r, s')) : SceneReachableM s'
  | publish_layout (s c s' : scene.Scene) (request : Std.U64) (hs : SceneReachableM s)
      (hc : SceneReachableM c)
      (h : ∃ r, scene.Scene.publish_layout s request c = ok (r, s')) : SceneReachableM s'
  | begin_crossing (s s' : scene.Scene) (stamp : walker.Stamp) (wi target : Std.Usize)
      (duration : Std.U32) (hs : SceneReachableM s)
      (h : ∃ r, scene.Scene.begin_crossing s stamp wi target duration = ok (r, s')) :
      SceneReachableM s'
  | motion (s s' : scene.Scene) (stamp : walker.Stamp) (steps : Slice Std.I32) (edit : scene.Edit)
      (hs : SceneReachableM s)
      (h : ∃ r, scene.Scene.motion s stamp steps edit = ok (r, s')) : SceneReachableM s'
  | carve (s s' : scene.Scene) (stamp : walker.Stamp) (wi target : Std.Usize) (edit : scene.Edit)
      (hs : SceneReachableM s)
      (h : ∃ r, scene.Scene.carve s stamp wi target edit = ok (r, s')) : SceneReachableM s'
  | tick (s s' : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64) (hs : SceneReachableM s)
      (h : ∃ r, scene.Scene.tick s stamp wall = ok (r, s')) : SceneReachableM s'
  | begin_shatter (s s' : scene.Scene) (stamp : walker.Stamp) (cells : Slice Std.Usize)
      (hs : SceneReachableM s)
      (h : ∃ r, scene.Scene.begin_shatter s stamp cells = ok (r, s')) : SceneReachableM s'
  | hide_patch (s s' : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
      (hs : SceneReachableM s)
      (h : ∃ r, scene.Scene.hide_patch s stamp id = ok (r, s')) : SceneReachableM s'
  | scatter_patch (s s' : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
      (duration : Std.U64) (hs : SceneReachableM s)
      (h : ∃ r, scene.Scene.scatter_patch s stamp id duration = ok (r, s')) : SceneReachableM s'
  | reform_patch (s s' : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
      (duration : Std.U64) (edit : scene.Edit) (hs : SceneReachableM s)
      (h : ∃ r, scene.Scene.reform_patch s stamp id duration edit = ok (r, s')) :
      SceneReachableM s'
  | swept_doorway (s s' : scene.Scene) (edge : topology.Edge) (steps : Slice Std.I32)
      (hs : SceneReachableM s)
      (h : ∃ r, scene.Scene.swept_doorway s edge steps = ok (r, s')) : SceneReachableM s'
  | advance_motion (s s' : scene.Scene) (stamp : walker.Stamp) (requested : Slice Std.I32)
      (work : motion.MotionWorkspace) (hs : SceneReachableM s)
      (h : ∃ r w', scene.Scene.advance_motion s stamp requested work = ok (r, s', w')) :
      SceneReachableM s'

/-- Every scene `SceneReachable` covers is reachable with `advance_motion` too. -/
theorem sceneReachable_motion {s : scene.Scene} (h : SceneReachable s) : SceneReachableM s := by
  induction h with
  | new treeRngInst hrng grid_spec specs ps geometry layout hlayout routes occupants
      patch_capacity epoch rng rng' s h htree =>
    exact .new treeRngInst hrng grid_spec specs ps geometry layout hlayout routes occupants
      patch_capacity epoch rng rng' s h htree
  | suspend s s' stamp wall _ h ih => exact .suspend s s' stamp wall ih h
  | resume s s' stamp wall _ h ih => exact .resume s s' stamp wall ih h
  | request_layout s s' stamp _ h ih => exact .request_layout s s' stamp ih h
  | reject_layout s s' request viewport _ h ih => exact .reject_layout s s' request viewport ih h
  | publish_layout s c s' request _ _ h ih ihc => exact .publish_layout s c s' request ih ihc h
  | begin_crossing s s' stamp wi target duration _ h ih =>
    exact .begin_crossing s s' stamp wi target duration ih h
  | motion s s' stamp steps edit _ h ih => exact .motion s s' stamp steps edit ih h
  | carve s s' stamp wi target edit _ h ih => exact .carve s s' stamp wi target edit ih h
  | tick s s' stamp wall _ h ih => exact .tick s s' stamp wall ih h
  | begin_shatter s s' stamp cells _ h ih => exact .begin_shatter s s' stamp cells ih h
  | hide_patch s s' stamp id _ h ih => exact .hide_patch s s' stamp id ih h
  | scatter_patch s s' stamp id duration _ h ih => exact .scatter_patch s s' stamp id duration ih h
  | reform_patch s s' stamp id duration edit _ h ih =>
    exact .reform_patch s s' stamp id duration edit ih h
  | swept_doorway s s' edge steps _ h ih => exact .swept_doorway s s' edge steps ih h

/-- **Every scene reachable with `advance_motion` satisfies the scene invariant and the hold
law.** -/
theorem sceneReachableM_inv {s : scene.Scene} (h : SceneReachableM s) : SceneInvFull s := by
  induction h with
  | new treeRngInst hrng grid_spec specs ps geometry layout hlayout routes occupants
      patch_capacity epoch rng rng' s h htree =>
    exact sceneReachable_inv (.new treeRngInst hrng grid_spec specs ps geometry layout hlayout
      routes occupants patch_capacity epoch rng rng' s h htree)
  | suspend s s' stamp wall _ h ih =>
    obtain ⟨r, hr⟩ := h; exact (sceneInvFull_ops s ih).1 stamp wall _ hr
  | resume s s' stamp wall _ h ih =>
    obtain ⟨r, hr⟩ := h; exact (sceneInvFull_ops s ih).2.1 stamp wall _ hr
  | request_layout s s' stamp _ h ih =>
    obtain ⟨r, hr⟩ := h; exact (sceneInvFull_ops s ih).2.2.1 stamp _ hr
  | reject_layout s s' request viewport _ h ih =>
    obtain ⟨r, hr⟩ := h; exact (sceneInvFull_ops s ih).2.2.2.1 request viewport _ hr
  | publish_layout s c s' request _ _ h ih ihc =>
    obtain ⟨r, hr⟩ := h; exact (sceneInvFull_ops s ih).2.2.2.2.1 request c ihc _ hr
  | begin_crossing s s' stamp wi target duration _ h ih =>
    obtain ⟨r, hr⟩ := h
    exact (sceneInvFull_ops s ih).2.2.2.2.2.1 stamp wi target duration _ hr
  | motion s s' stamp steps edit _ h ih =>
    obtain ⟨r, hr⟩ := h; exact (sceneInvFull_ops s ih).2.2.2.2.2.2.1 stamp steps edit _ hr
  | carve s s' stamp wi target edit _ h ih =>
    obtain ⟨r, hr⟩ := h
    exact (sceneInvFull_ops s ih).2.2.2.2.2.2.2.1 stamp wi target edit _ hr
  | tick s s' stamp wall _ h ih =>
    obtain ⟨r, hr⟩ := h; exact (sceneInvFull_ops s ih).2.2.2.2.2.2.2.2.1 stamp wall _ hr
  | begin_shatter s s' stamp cells _ h ih =>
    obtain ⟨r, hr⟩ := h; exact (sceneInvFull_ops s ih).2.2.2.2.2.2.2.2.2.1 stamp cells _ hr
  | hide_patch s s' stamp id _ h ih =>
    obtain ⟨r, hr⟩ := h; exact (sceneInvFull_ops s ih).2.2.2.2.2.2.2.2.2.2.1 stamp id _ hr
  | scatter_patch s s' stamp id duration _ h ih =>
    obtain ⟨r, hr⟩ := h
    exact (sceneInvFull_ops s ih).2.2.2.2.2.2.2.2.2.2.2.1 stamp id duration _ hr
  | reform_patch s s' stamp id duration edit _ h ih =>
    obtain ⟨r, hr⟩ := h
    exact (sceneInvFull_ops s ih).2.2.2.2.2.2.2.2.2.2.2.2 stamp id duration edit _ hr
  | swept_doorway s s' edge steps _ h ih =>
    obtain ⟨r, hr⟩ := h
    exact swept_doorway_inv s edge steps ih _ hr
  | advance_motion s s' stamp requested work _ h ih =>
    obtain ⟨r, w', hr⟩ := h
    exact advance_motion_inv s stamp requested work ih _ hr

/-- **The counter law with `advance_motion`.** Every hold counter of a reachable scene equals the
number of crossing-holds on it. -/
theorem reachableM_hold_exact {s : scene.Scene} (h : SceneReachableM s) :
    ∀ k, k < s.holds.val.length → ∃ a, s.holds.val[k]? = some a ∧
      a.val = crossMult s.walkers.val k :=
  (sceneReachableM_inv h).2.1

/-- A positive hold counter of a reachable scene is held by a crossing walker. -/
theorem reachableM_no_leaked_hold {s : scene.Scene} (h : SceneReachableM s) (k : Nat)
    (a : Std.Usize) (ha : s.holds.val[k]? = some a) (hpos : 0 < a.val) :
    ∃ wk ∈ s.walkers.val, ∃ c, wk.state = walker.WalkerState.Crossing c ∧
      ∃ x ∈ c.holds.ids.val.take c.holds.count.val, x.val = k := by
  have hk : k < s.holds.val.length := (List.getElem?_eq_some_iff.mp ha).1
  obtain ⟨b, hb, hbe⟩ := reachableM_hold_exact h k hk
  rw [ha] at hb; cases hb
  exact crossMult_pos (by omega)

/-- **Safety of `advance_motion` on every reachable scene.** -/
theorem reachableM_advance_motion_safe {s : scene.Scene} (h : SceneReachableM s)
    (stamp : walker.Stamp) (requested : Slice Std.I32) (w : motion.MotionWorkspace) :
    OkPost (scene.Scene.advance_motion s stamp requested w) (fun p =>
      ∀ a, p.1 = core.result.Result.Ok a →
        (∀ wk ∈ s.walkers.val, ∀ c, wk.state = walker.WalkerState.Crossing c →
          ∀ e1 : topology.Edge, topology.Edge.new c.source c.target = ok e1 →
          parentEdge (parents s.tree) e1.u.val e1.v.val →
          parentEdge (parents p.2.1.tree) e1.u.val e1.v.val) ∧
        (∀ (k : Nat) (n : Std.Usize), s.holds.val[k]? = some n → n.val ≠ 0 →
          p.2.1.phases.val[k]? = s.phases.val[k]?)) :=
  advance_motion_safe s stamp requested w (sceneReachableM_inv h).1

end Labyrinth
