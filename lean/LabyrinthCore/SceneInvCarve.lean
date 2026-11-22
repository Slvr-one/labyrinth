module
public import LabyrinthCore.SceneHoldTickActive
public import LabyrinthCore.SceneEditCarve
public import LabyrinthCore.SceneGeometryLayoutNew

/-! The scene invariant, part 6: `carve`.

A carve keeps the published phases (it copies them into the scratch table before the preflight) and
always runs `Tree::edit_edges` after an accepted preflight. `carve_shape` records what it leaves
beyond `CarvePost`: the walkers, holds and patches untouched, the workspace's capacity kept, and an
accepted carve passed `preflight_edit` on the scene with the copied scratch table. So an accepted
carve removes no edge a crossing walker is on (`carve_safe`), and every carve keeps the invariant
(`carve_inv`) and the hold law. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- What a carve leaves, beyond `CarvePost`. -/
def CarveShape (self : scene.Scene) (edit : scene.Edit)
    (p : (core.result.Result walker.Stamp topology.Error) × scene.Scene) : Prop :=
  p.2.walkers = self.walkers ∧ p.2.holds = self.holds ∧ p.2.patches = self.patches ∧
  p.2.work.edge_capacity = self.work.edge_capacity ∧
  ∀ st, p.1 = core.result.Result.Ok st → ∃ (np : alloc.vec.Vec Std.I32) (m : Std.Usize)
    (req : alloc.vec.Vec topology.Edge),
    PreflightOutcome { self with next_phases := np } edit
      (core.result.Result.Ok m, { self with next_phases := np, required := req })

/-- `commit_edit` writes only the phases, routes, stamp and trail revision. -/
theorem commit_frame (X : scene.Scene) (edit : scene.Edit) (val : Std.U64)
    (hph : X.phases.val.length ≤ X.next_phases.val.length)
    (hr : ∀ rs, edit.routes = some rs → rs.val.length ≤ X.routes.val.length) :
    OkPost (scene.Scene.commit_edit X edit val) (fun s3 =>
      s3.walkers = X.walkers ∧ s3.holds = X.holds ∧ s3.patches = X.patches ∧ s3.work = X.work) :=
  okPost_mono (okPost_of_spec (scene_commit_edit_spec X edit val hph hr))
    (by rintro s3 ⟨ph, _, _, rt, _, _, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩)

/-- A carve that answers with a forwarded error keeps the scene's frame. -/
theorem carveShape_residual (self : scene.Scene) (edit : scene.Edit) (Y : scene.Scene)
    (h1 : Y.walkers = self.walkers) (h2 : Y.holds = self.holds) (h3 : Y.patches = self.patches)
    (h4 : Y.work.edge_capacity = self.work.edge_capacity)
    (residual : core.result.Result Never topology.Error) :
    OkPost (do
      let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        walker.Stamp (core.convert.FromSame topology.Error) residual
      ok (r, Y) : Result ((core.result.Result walker.Stamp topology.Error) × scene.Scene))
      (CarveShape self edit) := by
  refine okPost_bind (okPost_residual_gen (P := fun r => ∃ e, r = .Err e) residual
    (fun e => ⟨e, rfl⟩)) ?_
  rintro _ ⟨e, rfl⟩
  exact okPost_ok ⟨h1, h2, h3, h4, fun st h => by simp at h⟩

theorem carveShape_err (self : scene.Scene) (edit : scene.Edit) (x : topology.Error) :
    CarveShape self edit (.Err x, self) := ⟨rfl, rfl, rfl, rfl, fun st h => by simp at h⟩

/-- Walk the checks of `carve` before the copy loop. -/
macro "carve_walk" : tactic => `(tactic| repeat (first
  | (refine okPost_ok ?_; exact carveShape_err _ _ _)
  | (refine carveShape_residual _ _ _ ?_ ?_ ?_ ?_ _ <;> rfl)
  | (dsimp only)
  | (refine okPost_bind (okPost_of_spec (carve_loop_spec _ _ (by assumption) 0#usize (by simp))) ?_)
  | (refine okPost_bind (okPost_trivial _) (fun _ _ => ?_))
  | split))

/-- **What `carve` changes**, beyond `scene_carve_spec`. -/
theorem carve_shape (self : scene.Scene) (stamp : walker.Stamp) (walker_index target : Std.Usize)
    (edit : scene.Edit) (hs : EditSafe self) :
    OkPost (scene.Scene.carve self stamp walker_index target edit) (CarveShape self edit) := by
  have hph : self.phases.val.length ≤ self.next_phases.val.length := hs.2.2.2.2.2.1
  unfold scene.Scene.carve
  carve_walk
  all_goals try (first
    | (refine okPost_ok ?_; exact carveShape_err _ _ _)
    | (refine carveShape_residual _ _ _ ?_ ?_ ?_ ?_ _ <;> rfl))
  rintro v ⟨hvl, _⟩
  refine okPost_bind (preflight_shape _ _) ?_
  rintro ⟨r4, s1⟩ ⟨hpo, req, hs1⟩
  simp only at hs1 hpo
  subst hs1
  refine okPost_bind_eq (okPost_trivial _) (fun cf4 hcf4 _ => ?_)
  cases r4 with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf4
    subst hcf4
    dsimp only
    refine carveShape_residual _ _ _ ?_ ?_ ?_ ?_ _ <;> rfl
  | Ok m =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf4
    subst hcf4
    dsimp only
    refine okPost_bind (okPost_trivial _) (fun revision _ => ?_)
    refine okPost_bind (edit_edges_capacity _ _ _ _ _) ?_
    rintro ⟨r5, t, w⟩ hw
    simp only at hw
    refine okPost_bind_eq (okPost_trivial _) (fun cf5 hcf5 _ => ?_)
    cases r5 with
    | Err x =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf5
      subst hcf5
      dsimp only
      refine carveShape_residual _ _ _ ?_ ?_ ?_ ?_ _ <;> first | rfl | exact hw
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf5
      subst hcf5
      dsimp only
      have hroutes := preflight_routes_len hpo
      refine okPost_bind (commit_frame _ edit revision (by dsimp only; omega) (fun rs hrs => by
        dsimp only; rw [hroutes rs hrs, hs.2.2.2.2.2.2.1])) ?_
      rintro s3 ⟨h1, h2, h3, h4⟩
      exact okPost_ok (show CarveShape self edit _ from
        ⟨h1, h2, h3, by rw [h4]; exact hw, fun st _ => ⟨v, m, req, hpo⟩⟩)

/-- **The preflight of an accepted carve.** An accepted carve passed `preflight_edit` on the scene
with the published phases copied into the scratch table. -/
theorem carve_preflight (self : scene.Scene) (stamp : walker.Stamp) (walker_index target : Std.Usize)
    (edit : scene.Edit) (hs : EditSafe self) :
    OkPost (scene.Scene.carve self stamp walker_index target edit) (fun p =>
      ∀ st, p.1 = core.result.Result.Ok st → ∃ (np : alloc.vec.Vec Std.I32) (m : Std.Usize)
        (req : alloc.vec.Vec topology.Edge),
        PreflightOutcome { self with next_phases := np } edit
          (core.result.Result.Ok m, { self with next_phases := np, required := req })) :=
  okPost_mono (carve_shape self stamp walker_index target edit hs) (fun _ h => h.2.2.2.2)

/-- **Safety for `carve`.** An accepted carve removes no edge a crossing walker is on. -/
theorem carve_safe (self : scene.Scene) (stamp : walker.Stamp) (walker_index target : Std.Usize)
    (edit : scene.Edit) (hs : EditSafe self) (hL : LayoutGeom self.layout)
    (hph : self.layout.transforms.val ≤ self.phases.val.length) (hfresh : CrossFresh self) :
    OkPost (scene.Scene.carve self stamp walker_index target edit) (fun p =>
      (∃ st, p.1 = core.result.Result.Ok st) → AvoidsCrossings self edit.remove) := by
  refine okPost_mono (carve_preflight self stamp walker_index target edit hs) ?_
  rintro p hok ⟨st, hst⟩
  obtain ⟨np, m, req, hpo⟩ := hok st hst
  refine removals_avoid_crossings self edit.remove hL hs.1 hph hfresh ?_
  intro j hj
  exact (removalVerdict_next self np _ edit.remove j _).mp
    (preflightOutcome_removals hpo m rfl j hj)

/-- **`carve` keeps the scene invariant**, whatever it returns. -/
theorem carve_inv (self : scene.Scene) (stamp : walker.Stamp) (walker_index target : Std.Usize)
    (edit : scene.Edit) (h : SceneInv self) :
    OkPost (scene.Scene.carve self stamp walker_index target edit) (fun p => SceneInv p.2) := by
  have h' := h
  obtain ⟨hs, hcap, hL, htr, hpr, hres, hcr, hroom⟩ := h'
  intro p hp
  obtain ⟨hs', herr, hok⟩ := scene_carve_spec self stamp walker_index target edit hs hcap p hp
  obtain ⟨hw, hh, hpa, hwc, _⟩ := carve_shape self stamp walker_index target edit hs p hp
  have hav := carve_safe self stamp walker_index target edit hs hL htr (crossHeld_fresh hcr) p hp
  cases hr : p.1 with
  | Err x =>
    obtain ⟨req, np, wk, he⟩ := herr x hr
    have hph : p.2.phases = self.phases := by rw [he]
    have hlay : p.2.layout = self.layout := by rw [he]
    have hroom' : PatchRoom p.2 := by unfold PatchRoom; rw [hpa, hlay]; exact hroom
    exact sceneInv_of_edit h hs' hw hh hroom' hlay hwc (by rw [hph]) (same_phases_range hpr hph)
      (fun _ _ _ _ _ _ => by rw [hph]) (fun _ _ _ _ _ _ hpe => by rw [he]; exact hpe)
  | Ok st =>
    obtain ⟨_, hlay, hedt, _, _, hph⟩ := hok st hr
    have hroom' : PatchRoom p.2 := by unfold PatchRoom; rw [hpa, hlay]; exact hroom
    exact sceneInv_of_edit h hs' hw hh hroom' hlay hwc (by rw [hph]) (same_phases_range hpr hph)
      (fun _ _ _ _ _ _ => by rw [hph]) (edited_keeps_crossings hedt (hav ⟨st, hr⟩))

/-- `carve` keeps the hold law: it writes no walker, hold or patch. -/
theorem carve_holdLaw (self : scene.Scene) (stamp : walker.Stamp) (walker_index target : Std.Usize)
    (edit : scene.Edit) (hs : EditSafe self) (h : HoldLaw self) :
    OkPost (scene.Scene.carve self stamp walker_index target edit) (fun p => HoldLaw p.2) :=
  okPost_mono (carve_shape self stamp walker_index target edit hs)
    (fun _ hp => holdLaw_of_eq_fields h hp.1 hp.2.1 hp.2.2.1)

/-- `motion` keeps the hold law: it writes no walker, hold or patch. -/
theorem motion_holdLaw (self : scene.Scene) (stamp : walker.Stamp) (steps : Slice Std.I32)
    (edit : scene.Edit) (hs : EditSafe self) (h : HoldLaw self) :
    OkPost (scene.Scene.motion self stamp steps edit) (fun p => HoldLaw p.2) :=
  okPost_mono (motion_shape self stamp steps edit hs)
    (fun _ hp => holdLaw_of_eq_fields h hp.1 hp.2.1 hp.2.2.1)

end Labyrinth
