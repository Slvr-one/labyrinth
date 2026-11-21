module
public import LabyrinthCore.SceneInvSummary

/-! The motion planner (S7), part 1: what `advance_motion` does to the scene.

`MotionWorkspace::advance` validates the request with `prepare_motion`, checks that the workspace
belongs to the scene, then searches divisors: for each it writes the divided steps, runs
`prepare_motion` again and lets the planner propose an edit. The planner (`plan`) and the workspace
checks only read the scene; `prepare_motion` writes only the scratch phase table. The one
publication is a final `Scene::motion` call with the proposed steps and edit, and `motion`
re-checks everything it publishes.

`advance_scene` states this frame: every outcome either is an error on a scene that differs from the
input only in the scratch phase table, or is exactly what `motion` returns on such a scene. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- `c` is `s` with another scratch phase table of the same length. -/
def NextOf (s c : scene.Scene) : Prop :=
  ∃ v : alloc.vec.Vec Std.I32, v.val.length = s.next_phases.val.length ∧
    c = { s with next_phases := v }

theorem nextOf_refl (s : scene.Scene) : NextOf s s := ⟨s.next_phases, rfl, rfl⟩

theorem nextOf_trans {s c d : scene.Scene} (h1 : NextOf s c) (h2 : NextOf c d) : NextOf s d := by
  obtain ⟨v, hv, rfl⟩ := h1
  obtain ⟨w, hw, rfl⟩ := h2
  exact ⟨w, by simpa [hv] using hw, rfl⟩

/-- `prepare_motion` moves a scene only along `NextOf`. -/
theorem prepare_motion_next (s c : scene.Scene) (stamp : walker.Stamp) (steps : Slice Std.I32)
    (h : NextOf s c) :
    OkPost (scene.Scene.prepare_motion c stamp steps) (fun p => NextOf s p.2) :=
  okPost_mono (prepare_motion_spec c stamp steps)
    (fun _ ⟨v, hv, hp, _⟩ => nextOf_trans h ⟨v, hv, hp⟩)

/-- The scene invariant does not read the scratch phase table beyond its length. -/
theorem sceneInv_next {s c : scene.Scene} (h : SceneInv s) (hn : NextOf s c) : SceneInv c := by
  obtain ⟨v, hv, rfl⟩ := hn
  obtain ⟨hs, hcap, hL, htr, hpr, hres, hcr, hroom⟩ := h
  exact ⟨editSafe_next hs v hv, hcap, hL, htr, hpr, hres, hcr, hroom⟩

theorem holdLaw_next {s c : scene.Scene} (h : HoldLaw s) (hn : NextOf s c) : HoldLaw c := by
  obtain ⟨v, _, rfl⟩ := hn
  exact holdLaw_of_eq_fields h rfl rfl rfl

theorem sceneInvFull_next {s c : scene.Scene} (h : SceneInvFull s) (hn : NextOf s c) :
    SceneInvFull c :=
  ⟨sceneInv_next h.1 hn, holdLaw_next h.2 hn⟩

/-! ### The divisor search -/

/-- The divisor search moves the scene only along `NextOf`. -/
theorem advance_loop2_next (s : scene.Scene) (expected : walker.Stamp)
    (requested : Slice Std.I32) (maximum : Std.Usize) (w : motion.MotionWorkspace)
    (c : scene.Scene) (divisor : Std.Usize) (planned : Bool) (failure : topology.Error)
    (status : core.result.Result Unit topology.Error) (hc : NextOf s c) :
    OkPost (motion.MotionWorkspace.advance_loop2 w c expected requested maximum divisor planned
      failure status) (fun y => NextOf s y.2.1) := by
  unfold motion.MotionWorkspace.advance_loop2
  refine okPost_loop
    (fun x : motion.MotionWorkspace × scene.Scene × Std.Usize × Bool × topology.Error ×
      core.result.Result Unit topology.Error => NextOf s x.2.1)
    (fun y : motion.MotionWorkspace × scene.Scene × Std.Usize × Bool × topology.Error ×
      core.result.Result Unit topology.Error => NextOf s y.2.1) _ ?_ _ hc
  rintro ⟨self1, current1, divisor1, planned1, failure1, status1⟩ hx
  simp only at hx ⊢
  unfold motion.MotionWorkspace.advance_loop2.body
  split
  · split
    · exact okPost_ok hx
    · refine okPost_bind (okPost_trivial _) (fun b _ => ?_)
      split
      · refine okPost_bind (okPost_trivial _) (fun self2 _ => ?_)
        refine okPost_bind (prepare_motion_next s current1 expected _ hx) ?_
        rintro ⟨r, current2⟩ hc2
        simp only at hc2 ⊢
        refine okPost_bind (okPost_trivial _) (fun status2 _ => ?_)
        refine okPost_bind (okPost_trivial _) (fun b1 _ => ?_)
        refine okPost_bind (okPost_trivial _) ?_
        rintro ⟨self3, planned2, failure2, status3⟩ _
        cases planned2
        · refine okPost_bind (okPost_trivial _) (fun b2 _ => ?_)
          split
          · refine okPost_bind (okPost_trivial _) (fun next _ => ?_)
            refine okPost_bind (okPost_trivial _) ?_
            rintro ⟨self4, next1⟩ _
            exact okPost_ok hc2
          · exact okPost_ok hc2
        · exact okPost_ok hc2
      · exact okPost_ok hx
  · exact okPost_ok hx

/-! ### The frame of `advance` -/

/-- What `advance` leaves on the scene side: an error on the input scene with another scratch phase
table, or exactly what `motion` returns on such a scene (and an accepted advance is an accepted
motion with the same event). -/
def AdvanceScene (s : scene.Scene) (stamp : walker.Stamp)
    (p : (core.result.Result motion.MotionAdvance topology.Error) × motion.MotionWorkspace ×
      scene.Scene) : Prop :=
  ((∃ x, p.1 = core.result.Result.Err x) ∧ NextOf s p.2.2) ∨
  ∃ c steps edit r, NextOf s c ∧ scene.Scene.motion c stamp steps edit = ok (r, p.2.2) ∧
    ∀ a, p.1 = core.result.Result.Ok a → r = core.result.Result.Ok a.event

theorem advance_residual_err (residual : core.result.Result Never topology.Error) :
    ∃ x, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      motion.MotionAdvance (core.convert.FromSame topology.Error) residual =
        ok (core.result.Result.Err x) := by
  cases residual with
  | Ok n => cases n
  | Err x =>
    exact ⟨x, by simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]⟩

/-- An early return on a scene along `NextOf`. -/
theorem advance_early (s c : scene.Scene) (stamp : walker.Stamp) (w : motion.MotionWorkspace)
    (hc : NextOf s c) (residual : core.result.Result Never topology.Error) :
    OkPost (do
      let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        motion.MotionAdvance (core.convert.FromSame topology.Error) residual
      ok (r, w, c) : Result ((core.result.Result motion.MotionAdvance topology.Error) ×
        motion.MotionWorkspace × scene.Scene)) (AdvanceScene s stamp) := by
  obtain ⟨x, hx⟩ := advance_residual_err residual
  rw [hx, Std.bind_ok]
  exact okPost_ok (Or.inl ⟨⟨x, rfl⟩, hc⟩)

/-- The publishing call: `motion` on a scene along `NextOf`, its event returned as is. -/
theorem advance_publish (s c : scene.Scene) (stamp : walker.Stamp) (w : motion.MotionWorkspace)
    (hc : NextOf s c) (steps : Slice Std.I32) (edit : scene.Edit) (divisor : Std.Usize) :
    OkPost (do
      let (r2, current3) ← scene.Scene.motion c stamp steps edit
      let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf3 with
      | core.ops.control_flow.ControlFlow.Continue val =>
        ok (core.result.Result.Ok { event := val, divisor }, w, current3)
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r3 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          motion.MotionAdvance (core.convert.FromSame topology.Error) residual
        ok (r3, w, current3) : Result ((core.result.Result motion.MotionAdvance topology.Error) ×
        motion.MotionWorkspace × scene.Scene)) (AdvanceScene s stamp) := by
  refine okPost_bind_eq (okPost_trivial _) ?_
  intro p hm _
  obtain ⟨r2, current3⟩ := p
  refine okPost_bind_eq (okPost_trivial _) (fun cf hcf _ => ?_)
  cases r2 with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf
    subst hcf
    obtain ⟨y, hy⟩ := advance_residual_err (core.result.Result.Err x)
    refine okPost_bind_eq (okPost_trivial _) (fun r3 hr3 _ => ?_)
    rw [hy, ok.injEq] at hr3
    subst hr3
    exact okPost_ok (Or.inr ⟨c, steps, edit, _, hc, hm, fun a ha => by simp at ha⟩)
  | Ok val =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf
    subst hcf
    refine okPost_ok (Or.inr ⟨c, steps, edit, _, hc, hm, fun a ha => ?_⟩)
    simp only [core.result.Result.Ok.injEq] at ha
    rw [← ha]

/-- **The frame of `advance`.** -/
theorem advance_scene (w : motion.MotionWorkspace) (s : scene.Scene) (stamp : walker.Stamp)
    (requested : Slice Std.I32) :
    OkPost (motion.MotionWorkspace.advance w s stamp requested) (AdvanceScene s stamp) := by
  unfold motion.MotionWorkspace.advance
  refine okPost_bind (prepare_motion_next s s stamp requested (nextOf_refl s)) ?_
  rintro ⟨r, current1⟩ hc1
  simp only at hc1 ⊢
  refine okPost_bind (okPost_trivial _) (fun cf _ => ?_)
  split
  · refine okPost_bind (okPost_trivial _) (fun r1 _ => ?_)
    refine okPost_bind (okPost_trivial _) (fun cf1 _ => ?_)
    split
    · refine okPost_bind (okPost_trivial _) (fun maximum _ => ?_)
      split
      · refine okPost_bind (okPost_trivial _) (fun e _ => ?_)
        exact advance_publish s current1 stamp w hc1 requested e 1#usize
      · refine okPost_bind (okPost_trivial _) ?_
        rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
          a19, a20, a21⟩ _
        refine okPost_bind (advance_loop2_next s stamp requested maximum _ current1 _ _ _ _ hc1) ?_
        rintro ⟨self1, current2, divisor, planned, failure, status⟩ hc2
        simp only at hc2 ⊢
        refine okPost_bind (okPost_trivial _) (fun cf2 _ => ?_)
        split
        · split
          · split
            · exact advance_publish s current2 stamp self1 hc2 _ _ divisor
            · exact advance_publish s current2 stamp self1 hc2 _ _ divisor
          · exact okPost_ok (Or.inl ⟨⟨failure, rfl⟩, hc2⟩)
        · exact advance_early s current2 stamp self1 hc2 _
    · exact advance_early s current1 stamp w hc1 _
  · exact advance_early s current1 stamp w hc1 _

/-! ### `advance_motion`: the invariant and safety -/

/-- `advance_motion` is `advance` with the scene and the workspace swapped in the result. -/
theorem advance_motion_scene (s : scene.Scene) (stamp : walker.Stamp) (requested : Slice Std.I32)
    (w : motion.MotionWorkspace) :
    OkPost (scene.Scene.advance_motion s stamp requested w)
      (fun p => AdvanceScene s stamp (p.1, p.2.2, p.2.1)) := by
  unfold scene.Scene.advance_motion
  refine okPost_bind (advance_scene w s stamp requested) ?_
  rintro ⟨r, w', s'⟩ h
  exact okPost_ok h

/-- **`advance_motion` keeps the scene invariant and the hold law**, whatever it returns. -/
theorem advance_motion_inv (s : scene.Scene) (stamp : walker.Stamp) (requested : Slice Std.I32)
    (w : motion.MotionWorkspace) (h : SceneInvFull s) :
    OkPost (scene.Scene.advance_motion s stamp requested w) (fun p => SceneInvFull p.2.1) := by
  refine okPost_mono (advance_motion_scene s stamp requested w) ?_
  rintro ⟨r, s', w'⟩ hp
  rcases hp with ⟨_, hn⟩ | ⟨c, steps, edit, r', hc, hm, _⟩
  · exact sceneInvFull_next h hn
  · have hc' := sceneInvFull_next h hc
    exact okPost_pair (motion_inv c stamp steps edit hc'.1)
      (motion_holdLaw c stamp steps edit hc'.1.1 hc'.2) _ hm

/-- **Safety for `advance_motion`.** An accepted advance removes no tree edge a crossing walker is
on, and every transform with a nonzero hold counter keeps its published phase. -/
theorem advance_motion_safe (s : scene.Scene) (stamp : walker.Stamp) (requested : Slice Std.I32)
    (w : motion.MotionWorkspace) (h : SceneInv s) :
    OkPost (scene.Scene.advance_motion s stamp requested w) (fun p =>
      ∀ a, p.1 = core.result.Result.Ok a →
        (∀ wk ∈ s.walkers.val, ∀ c, wk.state = walker.WalkerState.Crossing c →
          ∀ e1 : topology.Edge, topology.Edge.new c.source c.target = ok e1 →
          parentEdge (parents s.tree) e1.u.val e1.v.val →
          parentEdge (parents p.2.1.tree) e1.u.val e1.v.val) ∧
        (∀ (k : Nat) (n : Std.Usize), s.holds.val[k]? = some n → n.val ≠ 0 →
          p.2.1.phases.val[k]? = s.phases.val[k]?)) := by
  refine okPost_mono (advance_motion_scene s stamp requested w) ?_
  rintro ⟨r, s', w'⟩ hp a ha
  simp only at ha hp ⊢
  rcases hp with ⟨⟨x, hx⟩, _⟩ | ⟨c, steps, edit, r', hc, hm, hr⟩
  · simp [ha] at hx
  · have hc' := sceneInv_next h hc
    have hr' := hr a ha
    obtain ⟨v, hv, rfl⟩ := hc
    obtain ⟨_, _, hok⟩ := scene_motion_spec _ stamp steps edit hc'.1 hc'.2.1 _ hm
    obtain ⟨_, _, hedt, _, _⟩ := hok a.event hr'
    have hav := motion_safe _ stamp steps edit hc'.1 hc'.2.2.1 hc'.2.2.2.1
      (crossHeld_fresh hc'.2.2.2.2.2.2.1) _ hm ⟨a.event, hr'⟩
    refine ⟨edited_keeps_crossings hedt hav, ?_⟩
    obtain ⟨_, _, _, _, _, hphl, hsh⟩ := motion_shape _ stamp steps edit hc'.1 _ hm
    obtain ⟨np, hacc, hph | hnp, _⟩ := hsh a.event hr'
    · intro k n _ _
      rw [hph]
    · intro k n hk hn
      by_cases hkl : k < s.phases.val.length
      · rw [hnp k hkl]
        exact prepAccepted_held hacc hc'.2.2.2.2.1 k n hk hn hkl
      · simp only at hphl
        rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

end Labyrinth
