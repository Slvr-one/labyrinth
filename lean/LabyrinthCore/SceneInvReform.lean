module
public import LabyrinthCore.SceneInvShatter

/-! The scene invariant, part 8: `reform_patch`.

`reform_patch_spec` does not say what workspace capacity a rejected or committed reform edit leaves;
`reform_cap` walks `reform_patch` for it: the edge edit keeps the capacity and the commit keeps the
workspace. With `reform_patch_safe` (an accepted reform edit removes no crossing walker's edge) the
reform keeps the invariant on every outcome, and since it writes only the reformed patch's stage it
keeps the hold law. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- **`reform_patch` keeps the workspace's edge capacity**, whatever it returns. -/
theorem reform_cap (self : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
    (duration : Std.U64) (edit : scene.Edit) (hs : EditSafe self) :
    OkPost (scene.Scene.reform_patch self stamp id duration edit)
      (fun res => res.2.work.edge_capacity = self.work.edge_capacity) := by
  have hph : self.phases.val.length ≤ self.next_phases.val.length := hs.2.2.2.2.2.1
  unfold scene.Scene.reform_patch
  rw [reform_loop2_eq]
  repeat' (first
    | (refine okPost_ok ?_; rfl)
    | (refine okPost_bind (okPost_of_spec (carve_loop_spec _ _ hph 0#usize (by simp))) ?_)
    | (refine okPost_bind (okPost_trivial _) (fun _ _ => ?_))
    | split
    | dsimp only)
  rintro v ⟨hvl, _⟩
  refine okPost_bind (preflight_shape _ _) ?_
  rintro ⟨r3, s1⟩ ⟨hpo, req, hs1⟩
  simp only at hs1 hpo
  subst hs1
  refine okPost_bind_eq (okPost_trivial _) (fun cf3 hcf3 _ => ?_)
  cases r3 with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf3
    subst hcf3
    dsimp only
    exact okPost_bind (okPost_trivial _) (fun _ _ => okPost_ok rfl)
  | Ok m =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf3
    subst hcf3
    dsimp only
    have hroutes := preflight_routes_len hpo
    refine okPost_bind (okPost_trivial _) (fun b1 _ => ?_)
    split
    · refine okPost_bind (commit_frame _ edit _ (by dsimp only; omega) (fun rs hrs => by
        dsimp only; rw [hroutes rs hrs, hs.2.2.2.2.2.2.1])) ?_
      rintro s3 ⟨_, _, _, h4⟩
      refine okPost_bind (okPost_trivial _) (fun _ _ => okPost_ok ?_)
      dsimp only
      rw [h4]
    · refine okPost_bind (edit_edges_capacity _ _ _ _ _) ?_
      rintro ⟨r4, t, w⟩ hw
      simp only at hw
      refine okPost_bind_eq (okPost_trivial _) (fun cf4 hcf4 _ => ?_)
      cases r4 with
      | Err x =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf4
        subst hcf4
        dsimp only
        exact okPost_bind (okPost_trivial _) (fun _ _ => okPost_ok hw)
      | Ok u =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf4
        subst hcf4
        dsimp only
        refine okPost_bind (commit_frame _ edit _ (by dsimp only; omega) (fun rs hrs => by
          dsimp only; rw [hroutes rs hrs, hs.2.2.2.2.2.2.1])) ?_
        rintro s3 ⟨_, _, _, h4⟩
        refine okPost_bind (okPost_trivial _) (fun _ _ => okPost_ok ?_)
        dsimp only
        rw [h4]
        exact hw

/-- **`reform_patch` keeps the scene invariant**, whatever it returns. -/
theorem reform_patch_inv (self : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
    (duration : Std.U64) (edit : scene.Edit) (h : SceneInv self) :
    OkPost (scene.Scene.reform_patch self stamp id duration edit) (fun res => SceneInv res.2) := by
  have h' := h
  obtain ⟨hs, hcap, hL, htr, hpr, hres, hcr, hroom⟩ := h'
  intro res hres'
  have hwc := reform_cap self stamp id duration edit hs res hres'
  have hav := reform_patch_safe self stamp id duration edit hs hcap hL htr (crossHeld_fresh hcr)
    res hres'
  have hout := reform_patch_spec self stamp id duration edit hs hcap res hres'
  rcases hout with ⟨hn, hf⟩ | ⟨_, ⟨_, _, e⟩ | ⟨p, hp, ⟨_, e⟩ | ⟨_, _, _, e⟩ |
      ⟨_, _, _, ⟨_, e⟩ | ⟨_, dl, _, ⟨_, e⟩ | ⟨_, hsafe, hgate⟩⟩⟩⟩⟩
  · rw [stampFail_scene hn hf]; exact h
  all_goals try (rw [e]; exact h)
  rcases hgate with ⟨np, x, pr, req, _, _, rfl, e⟩ | ⟨np, m, req, _, _, ⟨x, wk, _, e⟩ |
      ⟨v, wk, t, ph, rt, _, ⟨_, hedt, _, hph, _⟩, e⟩⟩
  · rw [e] at hsafe ⊢
    exact sceneInv_of_edit h hsafe rfl rfl hroom rfl rfl rfl (same_phases_range hpr rfl)
      (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ hpe => hpe)
  · rw [e] at hsafe hwc ⊢
    exact sceneInv_of_edit h hsafe rfl rfl hroom rfl hwc rfl (same_phases_range hpr rfl)
      (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ hpe => hpe)
  · rw [e] at hsafe hwc hav ⊢
    have hroom' : PatchRoom (reformedScene self id p dl v req np wk t ph rt) := by
      intro q hq
      have hq' : q ∈ (alloc.vec.Vec.set self.patches id.slot
        { p with stage := shatter.Stage.Reforming dl }).val := hq
      rw [alloc.vec.Vec.set_val_eq] at hq'
      exact patchRoom_set_stage hroom p (slotOk_mem hp) _ _ q hq'
    have hph' : (reformedScene self id p dl v req np wk t ph rt).phases = self.phases := hph
    exact sceneInv_of_edit h hsafe rfl rfl hroom' rfl hwc (by rw [hph'])
      (same_phases_range hpr hph') (fun _ _ _ _ _ _ => by rw [hph'])
      (edited_keeps_crossings hedt (hav ⟨_, rfl⟩))

/-- `reform_patch` keeps the hold law: it moves a scattered patch to reforming and writes no walker
or hold. -/
theorem reform_patch_holdLaw (self : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
    (duration : Std.U64) (edit : scene.Edit) (hs : EditSafe self) (hcap : EditCapacity self)
    (h : HoldLaw self) :
    OkPost (scene.Scene.reform_patch self stamp id duration edit) (fun res => HoldLaw res.2) := by
  intro res hres'
  have hout := reform_patch_spec self stamp id duration edit hs hcap res hres'
  rcases hout with ⟨hn, hf⟩ | ⟨_, ⟨_, _, e⟩ | ⟨p, hp, ⟨_, e⟩ | ⟨_, _, _, e⟩ |
      ⟨_, _, ⟨u, hu, _⟩, ⟨_, e⟩ | ⟨_, dl, _, ⟨_, e⟩ | ⟨_, _, hgate⟩⟩⟩⟩⟩
  · rw [stampFail_scene hn hf]; exact h
  all_goals try (rw [e]; exact h)
  rcases hgate with ⟨np, x, pr, req, _, _, rfl, e⟩ | ⟨np, m, req, _, _, ⟨x, wk, _, e⟩ |
      ⟨v, wk, t, ph, rt, _, _, e⟩⟩
  · rw [e]; exact h
  · rw [e]; exact h
  · rw [e]
    refine ⟨h.1, ?_⟩
    show PatchClearL self.walkers.val (alloc.vec.Vec.set self.patches id.slot
      { p with stage := shatter.Stage.Reforming dl }).val
    rw [alloc.vec.Vec.set_val_eq]
    exact patchClear_set_stage h.2 p (slotOk_mem hp) (by rw [hu]; simp) (by rw [hu]; simp) _ _

end Labyrinth
