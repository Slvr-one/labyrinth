module
public import LabyrinthCore.SceneInvNew

/-! The scene invariant, part 10: the summary.

`SceneReachable` is the set of scenes built by `Scene::new` and then changed by any sequence of the
covered public operations: `suspend`, `resume`, `request_layout`, `reject_layout`, `publish_layout`
(whose candidate is itself reachable), `begin_crossing`, `motion`, `carve`, `tick`, `begin_shatter`,
`hide_patch`, `scatter_patch` and `reform_patch`, each on whatever it returns (accepted or
rejected). The read-only operations (`stamp`, `layout`, `tree`, `routes`, `phases`, `holds`,
`walkers`, `clock`, `trail_revision`, `is_suspended`, `is_inactive`, `cell_pose`, `walker_pose`,
`doorway_bounds`, `reservation`, `patch_stage`) do not change the scene. Not covered:
`swept_doorway` (writes the scratch phase table) and `advance_motion` with the motion planner.

`sceneReachable_inv`: every reachable scene satisfies the scene invariant and the hold law. The
construction step assumes the edit preconditions `EditSafe` and `EditCapacity` of the scene
`Scene::new` returns (see `scene_new_inv`); everything else the invariant states about that scene is
proved.

The hold law answers the hold-release question: every counter equals the number of crossing-holds on
it (`reachable_hold_exact`), so a positive counter is always held by a crossing walker
(`reachable_no_leaked_hold`), and every path that ends a crossing releases exactly its holds. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- The scene invariant together with the hold law. -/
def SceneInvFull (s : scene.Scene) : Prop := SceneInv s ∧ HoldLaw s

/-- Scenes built by `Scene::new` and changed by the covered operations. -/
inductive SceneReachable : scene.Scene → Prop
  | new {R : Type} (treeRngInst : tree.Rng R) (layout : scene.Layout) (routes : Slice scene.Route)
      (occupants : Slice Std.Usize) (patch_capacity : Std.Usize) (epoch : Std.U64) (rng rng' : R)
      (s : scene.Scene) (hL : LayoutGeom layout)
      (h : scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng =
        ok (.Ok s, rng'))
      (hsafe : EditSafe s) (hcap : EditCapacity s) : SceneReachable s
  | suspend (s s' : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64) (hs : SceneReachable s)
      (h : ∃ r, scene.Scene.suspend s stamp wall = ok (r, s')) : SceneReachable s'
  | resume (s s' : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64) (hs : SceneReachable s)
      (h : ∃ r, scene.Scene.resume s stamp wall = ok (r, s')) : SceneReachable s'
  | request_layout (s s' : scene.Scene) (stamp : walker.Stamp) (hs : SceneReachable s)
      (h : ∃ r, scene.Scene.request_layout s stamp = ok (r, s')) : SceneReachable s'
  | reject_layout (s s' : scene.Scene) (request : Std.U64) (viewport : grid.Rect)
      (hs : SceneReachable s)
      (h : ∃ r, scene.Scene.reject_layout s request viewport = ok (r, s')) : SceneReachable s'
  | publish_layout (s c s' : scene.Scene) (request : Std.U64) (hs : SceneReachable s)
      (hc : SceneReachable c)
      (h : ∃ r, scene.Scene.publish_layout s request c = ok (r, s')) : SceneReachable s'
  | begin_crossing (s s' : scene.Scene) (stamp : walker.Stamp) (wi target : Std.Usize)
      (duration : Std.U32) (hs : SceneReachable s)
      (h : ∃ r, scene.Scene.begin_crossing s stamp wi target duration = ok (r, s')) :
      SceneReachable s'
  | motion (s s' : scene.Scene) (stamp : walker.Stamp) (steps : Slice Std.I32) (edit : scene.Edit)
      (hs : SceneReachable s)
      (h : ∃ r, scene.Scene.motion s stamp steps edit = ok (r, s')) : SceneReachable s'
  | carve (s s' : scene.Scene) (stamp : walker.Stamp) (wi target : Std.Usize) (edit : scene.Edit)
      (hs : SceneReachable s)
      (h : ∃ r, scene.Scene.carve s stamp wi target edit = ok (r, s')) : SceneReachable s'
  | tick (s s' : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64) (hs : SceneReachable s)
      (h : ∃ r, scene.Scene.tick s stamp wall = ok (r, s')) : SceneReachable s'
  | begin_shatter (s s' : scene.Scene) (stamp : walker.Stamp) (cells : Slice Std.Usize)
      (hs : SceneReachable s)
      (h : ∃ r, scene.Scene.begin_shatter s stamp cells = ok (r, s')) : SceneReachable s'
  | hide_patch (s s' : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
      (hs : SceneReachable s)
      (h : ∃ r, scene.Scene.hide_patch s stamp id = ok (r, s')) : SceneReachable s'
  | scatter_patch (s s' : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
      (duration : Std.U64) (hs : SceneReachable s)
      (h : ∃ r, scene.Scene.scatter_patch s stamp id duration = ok (r, s')) : SceneReachable s'
  | reform_patch (s s' : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
      (duration : Std.U64) (edit : scene.Edit) (hs : SceneReachable s)
      (h : ∃ r, scene.Scene.reform_patch s stamp id duration edit = ok (r, s')) :
      SceneReachable s'

/-- Every covered operation keeps the scene invariant and the hold law, on every outcome. -/
theorem sceneInvFull_ops (s : scene.Scene) (h : SceneInvFull s) :
    (∀ stamp wall, OkPost (scene.Scene.suspend s stamp wall) (fun p => SceneInvFull p.2)) ∧
    (∀ stamp wall, OkPost (scene.Scene.resume s stamp wall) (fun p => SceneInvFull p.2)) ∧
    (∀ stamp, OkPost (scene.Scene.request_layout s stamp) (fun p => SceneInvFull p.2)) ∧
    (∀ request viewport,
      OkPost (scene.Scene.reject_layout s request viewport) (fun p => SceneInvFull p.2)) ∧
    (∀ request c, SceneInvFull c →
      OkPost (scene.Scene.publish_layout s request c) (fun p => SceneInvFull p.2)) ∧
    (∀ stamp wi target duration, OkPost (scene.Scene.begin_crossing s stamp wi target duration)
      (fun p => SceneInvFull p.2)) ∧
    (∀ stamp steps edit, OkPost (scene.Scene.motion s stamp steps edit)
      (fun p => SceneInvFull p.2)) ∧
    (∀ stamp wi target edit, OkPost (scene.Scene.carve s stamp wi target edit)
      (fun p => SceneInvFull p.2)) ∧
    (∀ stamp wall, OkPost (scene.Scene.tick s stamp wall) (fun p => SceneInvFull p.2)) ∧
    (∀ stamp cells, OkPost (scene.Scene.begin_shatter s stamp cells)
      (fun p => SceneInvFull p.2)) ∧
    (∀ stamp id, OkPost (scene.Scene.hide_patch s stamp id) (fun p => SceneInvFull p.2)) ∧
    (∀ stamp id duration, OkPost (scene.Scene.scatter_patch s stamp id duration)
      (fun p => SceneInvFull p.2)) ∧
    (∀ stamp id duration edit, OkPost (scene.Scene.reform_patch s stamp id duration edit)
      (fun p => SceneInvFull p.2)) := by
  obtain ⟨hi, hl⟩ := h
  have hs := hi.1
  have hcap := hi.2.1
  have hres := hi.2.2.2.2.2.1
  refine ⟨fun _ _ => okPost_pair (suspend_inv _ _ _ hi) (suspend_holdLaw _ _ _ hl),
    fun _ _ => okPost_pair (resume_inv _ _ _ hi) (resume_holdLaw _ _ _ hl),
    fun _ => okPost_pair (request_layout_inv _ _ hi) (request_layout_holdLaw _ _ hl),
    fun _ _ => okPost_pair (reject_layout_inv _ _ _ hi) (reject_layout_holdLaw _ _ _ hl),
    fun _ _ hc => okPost_pair (publish_layout_inv _ _ _ hi hc.1)
      (publish_layout_holdLaw _ _ _ hl hc.2),
    fun _ _ _ _ => okPost_pair (begin_crossing_inv _ _ _ _ _ hi) (begin_crossing_holdLaw _ _ _ _ _ hl),
    fun _ _ _ => okPost_pair (motion_inv _ _ _ _ hi) (motion_holdLaw _ _ _ _ hs hl),
    fun _ _ _ _ => okPost_pair (carve_inv _ _ _ _ _ hi) (carve_holdLaw _ _ _ _ _ hs hl),
    fun _ _ => okPost_pair (tick_inv _ _ _ hi) (tick_holdLaw _ _ _ hres hl),
    fun _ _ => okPost_pair (begin_shatter_inv _ _ _ hi) (begin_shatter_holdLaw _ _ _ hi hl),
    fun _ _ => okPost_pair (hide_patch_inv _ _ _ hi) (hide_patch_holdLaw _ _ _ hi hl),
    fun _ _ _ => okPost_pair (scatter_patch_inv _ _ _ _ hi) (scatter_patch_holdLaw _ _ _ _ hl),
    fun _ _ _ _ => okPost_pair (reform_patch_inv _ _ _ _ _ hi)
      (reform_patch_holdLaw _ _ _ _ _ hs hcap hl)⟩

/-- **Every reachable scene satisfies the scene invariant and the hold law.** -/
theorem sceneReachable_inv {s : scene.Scene} (h : SceneReachable s) : SceneInvFull s := by
  induction h with
  | new treeRngInst layout routes occupants patch_capacity epoch rng rng' s hL h hsafe hcap =>
    obtain ⟨hlaw, hinv⟩ :=
      scene_new_inv treeRngInst layout routes occupants patch_capacity epoch rng hL _ h s rfl
    exact ⟨hinv hsafe hcap, hlaw⟩
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

/-! ### The hold-release question -/

/-- **The counter law.** In every reachable scene, each hold counter equals the number of
crossing-holds on it (with multiplicity). -/
theorem reachable_hold_exact {s : scene.Scene} (h : SceneReachable s) :
    ∀ k, k < s.holds.val.length → ∃ a, s.holds.val[k]? = some a ∧
      a.val = crossMult s.walkers.val k :=
  (sceneReachable_inv h).2.1

/-- A positive count of crossing-holds on `k` comes from a crossing walker holding `k`. -/
theorem crossMult_pos {l : List walker.Walker} {k : Nat} (h : 0 < crossMult l k) :
    ∃ wk ∈ l, ∃ c, wk.state = walker.WalkerState.Crossing c ∧
      ∃ x ∈ c.holds.ids.val.take c.holds.count.val, x.val = k := by
  unfold crossMult at h
  have hne : (l.map (walkerMult · k)).sum ≠ 0 := by omega
  obtain ⟨m, hm, hpos⟩ := List.exists_mem_ne_zero_of_sum_ne_zero hne
  obtain ⟨wk, hwk, rfl⟩ := List.mem_map.mp hm
  unfold walkerMult at hpos
  split at hpos
  · rename_i c hc
    refine ⟨wk, hwk, c, hc, ?_⟩
    unfold holdMult at hpos
    obtain ⟨x, hx, hxk⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero hpos)
    exact ⟨x, hx, by simpa using hxk⟩
  · exact absurd rfl hpos

/-- **No hold leaks.** In every reachable scene, a positive hold counter is held by a crossing
walker; so once no crossing walker holds a transform, its counter is zero and `prepare_motion`
accepts nonzero steps on it again. -/
theorem reachable_no_leaked_hold {s : scene.Scene} (h : SceneReachable s) (k : Nat)
    (a : Std.Usize) (ha : s.holds.val[k]? = some a) (hpos : 0 < a.val) :
    ∃ wk ∈ s.walkers.val, ∃ c, wk.state = walker.WalkerState.Crossing c ∧
      ∃ x ∈ c.holds.ids.val.take c.holds.count.val, x.val = k := by
  have hk : k < s.holds.val.length := (List.getElem?_eq_some_iff.mp ha).1
  obtain ⟨b, hb, hbe⟩ := reachable_hold_exact h k hk
  rw [ha] at hb; cases hb
  exact crossMult_pos (by omega)

/-- A counter nobody crossing holds is zero. -/
theorem reachable_unheld_zero {s : scene.Scene} (h : SceneReachable s) (k : Nat) (a : Std.Usize)
    (ha : s.holds.val[k]? = some a)
    (hfree : ∀ wk ∈ s.walkers.val, ∀ c, wk.state = walker.WalkerState.Crossing c →
      ∀ x ∈ c.holds.ids.val.take c.holds.count.val, x.val ≠ k) : a.val = 0 := by
  by_contra hne
  obtain ⟨wk, hwk, c, hc, x, hx, hxk⟩ := reachable_no_leaked_hold h k a ha (by omega)
  exact hfree wk hwk c hc x hx hxk

end Labyrinth
