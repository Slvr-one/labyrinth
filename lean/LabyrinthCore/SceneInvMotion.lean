module
public import LabyrinthCore.SceneInvCapacity
public import LabyrinthCore.SceneEditMotion

/-! The scene invariant, part 4: what `motion` changes, and that an accepted motion removes no edge
a crossing walker is on.

`motion_shape` adds to `scene_motion_spec` what the invariant needs: the walkers, holds, patches
and layout are untouched, the workspace keeps its edge capacity, the published phases keep their
length, and an accepted motion either keeps them or publishes the scratch table the first loop of
`prepare_motion` wrote; it either removes nothing or passed `preflight_edit` on the scene with that
scratch table. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- What a motion leaves, beyond `MotionPost`. -/
def MotionShape (self : scene.Scene) (steps : Slice Std.I32) (edit : scene.Edit)
    (p : (core.result.Result scene.MotionEvent topology.Error) × scene.Scene) : Prop :=
  p.2.walkers = self.walkers ∧ p.2.holds = self.holds ∧ p.2.patches = self.patches ∧
  p.2.layout = self.layout ∧ p.2.work.edge_capacity = self.work.edge_capacity ∧
  p.2.phases.val.length = self.phases.val.length ∧
  ∀ ev, p.1 = core.result.Result.Ok ev → ∃ np : alloc.vec.Vec Std.I32,
    PrepAccepted self steps np ∧
    (p.2.phases = self.phases ∨ ∀ j, j < self.phases.val.length → p.2.phases.val[j]? = np.val[j]?) ∧
    (edit.remove.val.length = 0 ∨ ∃ m req, PreflightOutcome { self with next_phases := np } edit
      (core.result.Result.Ok m, { self with next_phases := np, required := req }))

/-- A rejection that kept everything but the scratch fields and the workspace (same capacity). -/
theorem motionShape_err (self : scene.Scene) (steps : Slice Std.I32) (edit : scene.Edit)
    (x : topology.Error) (Y : scene.Scene) (h1 : Y.walkers = self.walkers)
    (h2 : Y.holds = self.holds) (h3 : Y.patches = self.patches) (h4 : Y.layout = self.layout)
    (h5 : Y.work.edge_capacity = self.work.edge_capacity) (h6 : Y.phases = self.phases) :
    MotionShape self steps edit (core.result.Result.Err x, Y) :=
  ⟨h1, h2, h3, h4, h5, by rw [h6], fun ev h => by simp at h⟩

theorem motionShape_residual (self : scene.Scene) (steps : Slice Std.I32) (edit : scene.Edit)
    (Y : scene.Scene) (h1 : Y.walkers = self.walkers)
    (h2 : Y.holds = self.holds) (h3 : Y.patches = self.patches) (h4 : Y.layout = self.layout)
    (h5 : Y.work.edge_capacity = self.work.edge_capacity) (h6 : Y.phases = self.phases)
    (residual : core.result.Result Never topology.Error) :
    OkPost (do
      let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        scene.MotionEvent (core.convert.FromSame topology.Error) residual
      ok (r, Y) : Result ((core.result.Result scene.MotionEvent topology.Error) × scene.Scene))
      (MotionShape self steps edit) := by
  cases residual with
  | Ok n => cases n
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, Std.bind_ok]
    exact okPost_ok (motionShape_err self steps edit x Y h1 h2 h3 h4 h5 h6)

/-- `preflight_edit` changes only `required`. -/
theorem preflight_shape (s : scene.Scene) (edit : scene.Edit) :
    OkPost (scene.Scene.preflight_edit s edit) (fun p =>
      PreflightOutcome s edit p ∧ ∃ req, p.2 = { s with required := req }) := by
  refine okPost_mono (scene_preflight_edit_spec s edit) ?_
  intro p hp
  refine ⟨hp, ?_⟩
  have hself : s = { s with required := s.required } := rfl
  rcases hp with ⟨_, rfl⟩ | ⟨_, h | ⟨_, req, h | ⟨_, h⟩⟩⟩
  · exact ⟨s.required, hself⟩
  · obtain ⟨x, k, _, _, _, rfl⟩ := h
    exact ⟨s.required, hself⟩
  · obtain ⟨x, _, rfl⟩ := h
    exact ⟨req, rfl⟩
  · rcases h with ⟨x, k, _, _, _, rfl⟩ | ⟨_, ⟨x, k, _, _, _, rfl⟩ | ⟨mv, _, _, rfl⟩⟩ <;>
      exact ⟨req, rfl⟩

/-- An accepted preflight's routes cover every circle. -/
theorem preflightOutcome_ok_len {s : scene.Scene} {edit : scene.Edit} {m : Std.Usize}
    {s2 : scene.Scene} (h : PreflightOutcome s edit (core.result.Result.Ok m, s2)) :
    (PfRoutes s edit).val.length = s.layout.circles.val.length := by
  rcases h with ⟨_, h⟩ | ⟨_, h | ⟨_, req, h | ⟨hcall, _⟩⟩⟩
  · simp at h
  · obtain ⟨x, k, _, _, _, h⟩ := h; simp at h
  · obtain ⟨x, _, h⟩ := h; simp at h
  · exact pf_route_call_len s edit req hcall

/-- The commit of a motion. -/
theorem motion_commit_shape (self : scene.Scene) (steps : Slice Std.I32) (edit : scene.Edit)
    (np : alloc.vec.Vec Std.I32) (X : scene.Scene) (val : Std.U64)
    (h1 : X.walkers = self.walkers) (h2 : X.holds = self.holds) (h3 : X.patches = self.patches)
    (h4 : X.layout = self.layout) (h5 : X.work.edge_capacity = self.work.edge_capacity)
    (h6 : X.phases = self.phases) (h7 : X.next_phases = np) (h8 : X.routes = self.routes)
    (hph : self.phases.val.length ≤ np.val.length)
    (hrl : self.routes.val.length = self.layout.circles.val.length)
    (hroutes : ∀ rs, edit.routes = some rs → rs.val.length = self.layout.circles.val.length)
    (hacc : PrepAccepted self steps np)
    (hev : edit.remove.val.length = 0 ∨ ∃ m req, PreflightOutcome { self with next_phases := np }
      edit (core.result.Result.Ok m, { self with next_phases := np, required := req })) :
    OkPost (scene.Scene.commit_edit X edit val) (fun s3 =>
      ∀ r, MotionShape self steps edit (r, s3)) := by
  refine okPost_of_spec (spec_mono (scene_commit_edit_spec X edit val (by rw [h6, h7]; exact hph)
    (fun rs hrs => by rw [h8, hroutes rs hrs, hrl])) ?_)
  rintro s3 ⟨ph, hphl, hphv, rt, _, _, rfl⟩ r
  simp only [commitResult]
  refine ⟨h1, h2, h3, h4, h5, by rw [hphl, h6], fun ev _ => ⟨np, hacc, Or.inr ?_, hev⟩⟩
  intro j hj
  rw [hphv j (by rw [h6]; exact hj), h7]

theorem stationary_shape (self : scene.Scene) (steps : Slice Std.I32) (edit : scene.Edit)
    (np : alloc.vec.Vec Std.I32) (st : walker.Stamp) (hacc : PrepAccepted self steps np)
    (h0 : edit.remove.val.length = 0) (ev : core.result.Result scene.MotionEvent topology.Error) :
    MotionShape self steps edit (ev, { self with next_phases := np, stamp := st }) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨np, hacc, Or.inl rfl, Or.inl h0⟩⟩

theorem motion_phase_room {self : scene.Scene} {np : alloc.vec.Vec Std.I32} (hs : EditSafe self)
    (hnp : np.val.length = self.next_phases.val.length) :
    self.phases.val.length ≤ np.val.length := by
  rw [hnp]; exact hs.2.2.2.2.2.1

theorem preflight_routes_len {self : scene.Scene} {np : alloc.vec.Vec Std.I32} {edit : scene.Edit}
    {m : Std.Usize} {s2 : scene.Scene}
    (hpo : PreflightOutcome { self with next_phases := np } edit (core.result.Result.Ok m, s2)) :
    ∀ rs, edit.routes = some rs → rs.val.length = self.layout.circles.val.length := by
  intro rs hrs
  have : (PfRoutes { self with next_phases := np } edit).val.length =
      self.layout.circles.val.length := preflightOutcome_ok_len hpo
  simpa [PfRoutes, hrs] using this

/-- The commit after an accepted preflight. -/
macro "ap_commit" hs:term:max hnp:term:max hacc:term:max hpo:term:max : tactic =>
  `(tactic| (
  refine okPost_bind (motion_commit_shape _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (motion_phase_room $hs $hnp) ($hs).2.2.2.2.2.2.1 (preflight_routes_len $hpo) $hacc
      (Or.inr ⟨_, _, $hpo⟩)) (fun s3 h => okPost_ok (h _)) <;> rfl))

/-- The edge edit and the commit after an accepted preflight. -/
macro "ap_edges" hs:term:max hnp:term:max hacc:term:max hpo:term:max : tactic =>
  `(tactic| (
  refine okPost_bind (edit_edges_capacity _ _ _ _ _) ?_
  rintro ⟨r2, t, w⟩ hw
  simp only at hw
  refine okPost_bind_eq (okPost_trivial _) (fun cf2 hcf2 _ => ?_)
  cases r2 with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf2
    subst hcf2
    refine motionShape_residual _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ _ <;> first | rfl | exact hw
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf2
    subst hcf2
    refine okPost_bind (motion_commit_shape _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (motion_phase_room $hs $hnp) ($hs).2.2.2.2.2.2.1 (preflight_routes_len $hpo) $hacc
      (Or.inr ⟨_, _, $hpo⟩)) (fun s3 h => okPost_ok (h _)) <;> first | rfl | exact hw))

/-- The part of a motion after the preflight accepted, whichever way the removal test is known. -/
macro "after_preflight" hs:term:max hnp:term:max hacc:term:max hpo:term:max : tactic =>
  `(tactic| first
    | ap_commit $hs $hnp $hacc $hpo
    | ap_edges $hs $hnp $hacc $hpo
    | (refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
       split
       · ap_commit $hs $hnp $hacc $hpo
       · ap_edges $hs $hnp $hacc $hpo))

/-- The preflight and what follows, in every branch of `motion` that runs it. -/
macro "motion_tail" hs:term:max hnp:term:max hacc:term:max : tactic => `(tactic| (
  refine okPost_bind (preflight_shape _ _) ?_
  rintro ⟨r1, s2⟩ ⟨hpo, req, hs2⟩
  simp only at hs2 hpo
  subst hs2
  refine okPost_bind_eq (okPost_trivial _) (fun cf1 hcf1 _ => ?_)
  cases r1 with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf1
    subst hcf1
    refine motionShape_residual _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ _ <;> rfl
  | Ok m =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf1
    subst hcf1
    dsimp only
    after_preflight $hs $hnp $hacc hpo))

/-- **What `motion` changes**, beyond `scene_motion_spec`. -/
theorem motion_shape (self : scene.Scene) (stamp : walker.Stamp) (steps : Slice Std.I32)
    (edit : scene.Edit) (hs : EditSafe self) :
    OkPost (scene.Scene.motion self stamp steps edit) (MotionShape self steps edit) := by
  unfold scene.Scene.motion
  refine okPost_bind (prepare_motion_spec self stamp steps) ?_
  rintro ⟨r, s1⟩ ⟨np, hnp, hs1, hacc⟩
  simp only at hs1 hacc
  subst hs1
  refine okPost_bind_eq (okPost_trivial _) (fun cf hcf _ => ?_)
  cases r with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf
    subst hcf
    refine motionShape_residual _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ _ <;> rfl
  | Ok val =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf
    subst hcf
    have hacc' := hacc val rfl
    refine okPost_bind (okPost_trivial _) (fun stationary _ => ?_)
    split
    · refine okPost_bind_eq (okPost_of_spec (core.slice.Slice.is_empty_spec edit.remove)) ?_
      intro b _ hb
      split
      · rename_i hbt
        have h0 : edit.remove.val.length = 0 := by
          have : edit.remove.length = 0 := by rw [← hb]; exact hbt
          simpa using this
        refine okPost_bind (okPost_trivial _) (fun b1 _ => ?_)
        split
        · dsimp only
          split
          · exact okPost_ok (stationary_shape self steps edit np _ hacc' h0 _)
          · motion_tail hs hnp hacc'
        · motion_tail hs hnp hacc'
      · motion_tail hs hnp hacc'
    · motion_tail hs hnp hacc'

/-- **Safety for `motion`.** An accepted motion removes no edge a crossing walker is on. -/
theorem motion_safe (self : scene.Scene) (stamp : walker.Stamp) (steps : Slice Std.I32)
    (edit : scene.Edit) (hs : EditSafe self) (hL : LayoutGeom self.layout)
    (hph : self.layout.transforms.val ≤ self.phases.val.length) (hfresh : CrossFresh self) :
    OkPost (scene.Scene.motion self stamp steps edit) (fun p =>
      (∃ ev, p.1 = core.result.Result.Ok ev) → AvoidsCrossings self edit.remove) := by
  refine okPost_mono (motion_shape self stamp steps edit hs) ?_
  rintro p ⟨_, _, _, _, _, _, hok⟩ ⟨ev, hev⟩
  obtain ⟨np, _, _, h0 | ⟨m, req, hpo⟩⟩ := hok ev hev
  · intro wk _ c _ e1 _ j e hj
    have : j < edit.remove.val.length := (List.getElem?_eq_some_iff.mp hj).1
    omega
  · refine removals_avoid_crossings self edit.remove hL hs.1 hph hfresh ?_
    intro j hj
    exact (removalVerdict_next self np _ edit.remove j _).mp
      (preflightOutcome_removals hpo m rfl j hj)

end Labyrinth
