module
public import LabyrinthCore.SceneEditSafe

/-! Scene edits (S3), part 6: `Scene::motion`. An accepted motion publishes the edit's tree and
routes together: the new tree is valid on the carrier, its edge set is the old one edited, and every
route edge of the new routes is one of its edges. A rejected motion changes nothing except the
scratch list `required`, the scratch phase table `next_phases` and the scratch workspace `work`
(still valid, same capacity). The planner's checks and the geometry are not analysed, so these are
partial correctness (`OkPost`). -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

theorem editSafe_next {self : scene.Scene} (hs : EditSafe self) (np : alloc.vec.Vec Std.I32)
    (hnp : np.val.length = self.next_phases.val.length) :
    EditSafe { self with next_phases := np } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
  exact ⟨h1, h2, h3, h4, h5, by simpa [hnp] using h6, h7, h8⟩

theorem editSafe_required {self : scene.Scene} (hs : EditSafe self)
    (req : alloc.vec.Vec topology.Edge) (hr : RouteInv self.layout.carrier req) :
    EditSafe { self with required := req } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
  exact ⟨h1, h2, h3, h4, hr, h6, h7, h8⟩

theorem editSafe_work {self : scene.Scene} (hs : EditSafe self) (w : spanning_tree.Workspace)
    (hw : WorkspaceValid w) (hl : w.path.val.length = self.work.path.val.length) :
    EditSafe { self with work := w } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
  exact ⟨h1, h2, hw, by simpa [hl] using h4, h5, h6, h7, h8⟩

theorem editSafe_stamp {self : scene.Scene} (hs : EditSafe self) (st : walker.Stamp) :
    EditSafe { self with stamp := st } := hs

/-- The outcome of a motion. -/
def MotionPost (self : scene.Scene) (edit : scene.Edit)
    (p : (core.result.Result scene.MotionEvent topology.Error) × scene.Scene) : Prop :=
  EditSafe p.2 ∧
  (∀ x, p.1 = core.result.Result.Err x → ∃ req np wk,
    p.2 = { self with required := req, next_phases := np, work := wk }) ∧
  (∀ ev, p.1 = core.result.Result.Ok ev →
    ev.stamp = p.2.stamp ∧ p.2.layout = self.layout ∧
    (∀ u v, parentEdge (parents p.2.tree) u v ↔
      MutationEditedEdge (parents self.tree) edit.remove edit.add u v) ∧
    (edit.routes = none → p.2.routes = self.routes) ∧
    (∀ rs, edit.routes = some rs → allEdges p.2.routes.val = allEdges rs.val))

theorem pfRoutes_congr (s s' : scene.Scene) (edit : scene.Edit) (h : s.routes = s'.routes) :
    PfRoutes s edit = PfRoutes s' edit := by
  simp [PfRoutes, h]

/-- The tail of a motion, once the preflight accepted and the removal list is empty: commit. -/
theorem motion_commit_leaf (self self2 : scene.Scene) (edit : scene.Edit) (val : Std.U64)
    (val1 : Std.Usize) (hs2 : EditSafe self2) (e1 : self2.layout = self.layout)
    (e2 : self2.tree = self.tree) (e3 : self2.routes = self.routes)
    (h0 : edit.remove.val.length = 0) (hadd : edit.add.val.length = 0)
    (hcirc : (PfRoutes self edit).val.length = self.layout.circles.val.length)
    (hcert : ∀ e ∈ allEdges (PfRoutes self edit).val,
      MutationEditedEdge (parents self.tree) edit.remove edit.add e.u.val e.v.val) :
    OkPost (do
      let self3 ← scene.Scene.commit_edit self2 edit val
      let i := Slice.len edit.remove
      ok (core.result.Result.Ok { stamp := self3.stamp, replaced := i, moving_doorways := val1 },
        self3) : Result ((core.result.Result scene.MotionEvent topology.Error) × scene.Scene))
      (MotionPost self edit) := by
  obtain ⟨c2, t2, w2, cap2, rq2, ph2, rl2, _⟩ := hs2
  have hsr : PfRoutes self2 edit = PfRoutes self edit := pfRoutes_congr _ _ _ e3
  refine okPost_bind (m := scene.Scene.commit_edit self2 edit val) (okPost_of_spec
    (edit_commit_post self2 self2.tree self2.work edit val c2 t2 w2 cap2 rq2 ph2 rl2 ?_ ?_
      ?_)) ?_
  · intro rs hrs
    have := hcirc
    simp only [PfRoutes, hrs] at this
    rw [e1]; exact this
  · intro u v
    exact (edited_edge_empty _ edit.remove edit.add h0 hadd u v).symm
  · intro e he
    rw [hsr] at he
    rw [e2]; exact hcert e he
  · rintro s3 ⟨hcp, htr, hwk⟩
    refine okPost_ok ⟨hcp.1, fun x hx => by simp at hx, fun ev hev => ?_⟩
    simp only [core.result.Result.Ok.injEq] at hev
    subst hev
    refine ⟨rfl, hcp.2.1.trans e1, ?_, fun hn => (hcp.2.2.2.1 hn).trans e3,
      hcp.2.2.2.2.1⟩
    intro u v
    rw [hcp.2.2.1 u v, e2]

/-- The tail of a motion with edges to remove: edit the tree, then commit. -/
theorem motion_edges_leaf (self self2 : scene.Scene) (req : alloc.vec.Vec topology.Edge)
    (np : alloc.vec.Vec Std.I32) (edit : scene.Edit) (val : Std.U64) (val1 : Std.Usize)
    (hform : self2 = { self with required := req, next_phases := np })
    (hs2 : EditSafe self2) (hcap2 : EditCapacity self2)
    (hcirc : (PfRoutes self edit).val.length = self.layout.circles.val.length)
    (hcert : ∀ e ∈ allEdges (PfRoutes self edit).val,
      MutationEditedEdge (parents self.tree) edit.remove edit.add e.u.val e.v.val) :
    OkPost (do
      let (r2, t, w) ← spanning_tree.Tree.edit_edges self2.tree self2.layout.carrier edit.remove
        edit.add self2.work
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue _ => do
        let self3 ← scene.Scene.commit_edit { self2 with tree := t, work := w } edit val
        let i := Slice.len edit.remove
        ok (core.result.Result.Ok { stamp := self3.stamp, replaced := i, moving_doorways := val1 },
          self3)
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r3 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            scene.MotionEvent (core.convert.FromSame topology.Error) residual
        ok (r3, { self2 with tree := t, work := w }) :
          Result ((core.result.Result scene.MotionEvent topology.Error) × scene.Scene))
      (MotionPost self edit) := by
  have e1 : self2.layout = self.layout := by rw [hform]
  have e2 : self2.tree = self.tree := by rw [hform]
  have e3 : self2.routes = self.routes := by rw [hform]
  have hsr : PfRoutes self2 edit = PfRoutes self edit := pfRoutes_congr _ _ _ e3
  obtain ⟨c2, t2, w2, cap2, rq2, ph2, rl2, edges2⟩ := hs2
  refine okPost_bind (okPost_of_spec (mutation_edit_edges_tree_valid self2.layout.carrier
    self2.tree edit.remove edit.add self2.work c2 t2 w2 cap2 hcap2)) ?_
  rintro ⟨r2, t, w⟩ ⟨hwv, hpl, herr, hok⟩
  refine okPost_bind_eq (okPost_trivial _) ?_
  intro cf2 hcf2 _
  cases r2 with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf2
    subst hcf2
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro r3 hr3 _
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hr3
    subst hr3
    have ht : t = self2.tree := herr e rfl
    subst ht
    refine okPost_ok ⟨editSafe_work ⟨c2, t2, w2, cap2, rq2, ph2, rl2, edges2⟩ w hwv hpl,
      fun x _ => ⟨req, np, w, by rw [hform]⟩, fun ev h => by simp at h⟩
  | Ok u =>
    cases u
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf2
    subst hcf2
    obtain ⟨hroot, hlen, hiff, hcar, htv⟩ := hok rfl
    refine okPost_bind (m := scene.Scene.commit_edit { self2 with tree := t, work := w } edit val)
      (okPost_of_spec (edit_commit_post self2 t w edit val c2 htv hwv
        (by dsimp only at hlen hpl ⊢; omega) rq2 ph2 rl2 ?_ hiff ?_)) ?_
    · intro rs hrs
      have := hcirc
      simp only [PfRoutes, hrs] at this
      rw [e1]; exact this
    · intro e he
      rw [hsr] at he
      rw [e2]; exact hcert e he
    · rintro s3 ⟨hcp, htr, hwk⟩
      refine okPost_ok ⟨hcp.1, fun x hx => by simp at hx, fun ev hev => ?_⟩
      simp only [core.result.Result.Ok.injEq] at hev
      subst hev
      refine ⟨rfl, hcp.2.1.trans e1, ?_, fun hn => (hcp.2.2.2.1 hn).trans e3,
        hcp.2.2.2.2.1⟩
      intro u v
      rw [hcp.2.2.1 u v, e2]

theorem scene_motion_spec (self : scene.Scene) (stamp : walker.Stamp) (steps : Slice Std.I32)
    (edit : scene.Edit) (hs : EditSafe self) (hcap : EditCapacity self) :
    OkPost (scene.Scene.motion self stamp steps edit) (MotionPost self edit) := by
  unfold scene.Scene.motion
  refine okPost_bind (prepare_motion_frame self stamp steps) ?_
  rintro ⟨r, self1⟩ ⟨np, hnp, rfl⟩
  have hs1 := editSafe_next hs np hnp
  cases r with
  | Err x =>
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro cf hcf _
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf
    subst hcf
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro r1 hr1 _
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hr1
    subst hr1
    exact okPost_ok ⟨hs1, fun _ _ => ⟨self.required, np, self.work, rfl⟩, fun ev h => by simp at h⟩
  | Ok val =>
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro cf hcf _
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf
    subst hcf
    refine okPost_bind (okPost_trivial _) ?_
    intro stationary _
    by_cases hst : stationary = true
    · simp only [hst, ↓reduceIte]
      refine okPost_bind_eq (okPost_of_spec (core.slice.Slice.is_empty_spec edit.remove)) ?_
      intro b _ hb
      by_cases hbt : b = true
      · simp only [hbt, ↓reduceIte]
        refine okPost_bind_eq (okPost_of_spec (core.slice.Slice.is_empty_spec edit.add)) ?_
        intro b1 _ hb1
        by_cases hb1t : b1 = true
        · simp only [hb1t, ↓reduceIte]
          by_cases hb2 : core.option.Option.is_none edit.routes = true
          · simp only [hb2, ↓reduceIte]
            have h0' : edit.remove.length = 0 := by rw [← hb]; exact hbt
            have h0 : edit.remove.val.length = 0 := by simpa using h0'
            have h1' : edit.add.length = 0 := by rw [← hb1]; exact hb1t
            have h1 : edit.add.val.length = 0 := by simpa using h1'
            have hnone : edit.routes = none := by simpa [core.option.Option.is_none] using hb2
            refine okPost_ok ⟨editSafe_stamp hs1 _, fun x hx => by simp at hx, fun ev hev => ?_⟩
            simp only [core.result.Result.Ok.injEq] at hev
            subst hev
            refine ⟨rfl, rfl, fun u v => ?_, fun _ => rfl, fun rs hrs => by simp [hnone] at hrs⟩
            exact (edited_edge_empty _ edit.remove edit.add h0 h1 u v).symm
          · simp only [hb2, Bool.false_eq_true, ↓reduceIte]
            have hc1 := hs1.1
            have hinv1 := hs1.2.2.2.2.1
            refine okPost_bind (okPost_pair (scene_preflight_edit_frame _ edit hc1 hinv1)
              (scene_preflight_edit_accepted _ edit hc1 hinv1)) ?_
            rintro ⟨r1, self2⟩ ⟨⟨req, hself2, hreq⟩, hacc⟩
            refine okPost_bind_eq (okPost_trivial _) ?_
            intro cf1 hcf1 _
            cases r1 with
            | Err x =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf1
              subst hcf1
              refine okPost_bind_eq (okPost_trivial _) ?_
              intro r3 hr3 _
              simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hr3
              subst hr3
              have hf : self2 = { self with required := req, next_phases := np } := hself2
              refine okPost_ok ⟨?_, fun x' _ => ⟨req, np, self.work, hf⟩, fun ev h => by simp at h⟩
              rw [hf]
              exact editSafe_required (editSafe_next hs np hnp) req hreq
            | Ok val1 =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf1
              subst hcf1
              obtain ⟨hlen, hmv, hrem, req', hself2', hfold, hI, hcert, hcirc⟩ := hacc val1 rfl
              have hf : self2 = { self with required := req', next_phases := np } := hself2'
              have hs2 : EditSafe self2 := by
                rw [hf]
                exact editSafe_required (editSafe_next hs np hnp) req' hI
              have hcert' : ∀ e ∈ allEdges (PfRoutes self edit).val,
                  MutationEditedEdge (parents self.tree) edit.remove edit.add e.u.val e.v.val := hcert
              have hcirc' : (PfRoutes self edit).val.length = self.layout.circles.val.length := hcirc

              have h0' : edit.remove.length = 0 := by rw [← hb]; exact hbt
              have h0 : edit.remove.val.length = 0 := by simpa using h0'
              exact motion_commit_leaf self self2 edit val val1 hs2 (by rw [hf]) (by rw [hf])
                (by rw [hf]) h0 (by omega) hcirc' hcert'
        · simp only [hb1t, Bool.false_eq_true, ↓reduceIte]
          have hc1 := hs1.1
          have hinv1 := hs1.2.2.2.2.1
          refine okPost_bind (okPost_pair (scene_preflight_edit_frame _ edit hc1 hinv1)
            (scene_preflight_edit_accepted _ edit hc1 hinv1)) ?_
          rintro ⟨r1, self2⟩ ⟨⟨req, hself2, hreq⟩, hacc⟩
          refine okPost_bind_eq (okPost_trivial _) ?_
          intro cf1 hcf1 _
          cases r1 with
          | Err x =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf1
            subst hcf1
            refine okPost_bind_eq (okPost_trivial _) ?_
            intro r3 hr3 _
            simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hr3
            subst hr3
            have hf : self2 = { self with required := req, next_phases := np } := hself2
            refine okPost_ok ⟨?_, fun x' _ => ⟨req, np, self.work, hf⟩, fun ev h => by simp at h⟩
            rw [hf]
            exact editSafe_required (editSafe_next hs np hnp) req hreq
          | Ok val1 =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf1
            subst hcf1
            obtain ⟨hlen, hmv, hrem, req', hself2', hfold, hI, hcert, hcirc⟩ := hacc val1 rfl
            have hf : self2 = { self with required := req', next_phases := np } := hself2'
            have hs2 : EditSafe self2 := by
              rw [hf]
              exact editSafe_required (editSafe_next hs np hnp) req' hI
            have hcert' : ∀ e ∈ allEdges (PfRoutes self edit).val,
                MutationEditedEdge (parents self.tree) edit.remove edit.add e.u.val e.v.val := hcert
            have hcirc' : (PfRoutes self edit).val.length = self.layout.circles.val.length := hcirc

            have h0' : edit.remove.length = 0 := by rw [← hb]; exact hbt
            have h0 : edit.remove.val.length = 0 := by simpa using h0'
            exact motion_commit_leaf self self2 edit val val1 hs2 (by rw [hf]) (by rw [hf])
              (by rw [hf]) h0 (by omega) hcirc' hcert'
      · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
        have hc1 := hs1.1
        have hinv1 := hs1.2.2.2.2.1
        refine okPost_bind (okPost_pair (scene_preflight_edit_frame _ edit hc1 hinv1)
          (scene_preflight_edit_accepted _ edit hc1 hinv1)) ?_
        rintro ⟨r1, self2⟩ ⟨⟨req, hself2, hreq⟩, hacc⟩
        refine okPost_bind_eq (okPost_trivial _) ?_
        intro cf1 hcf1 _
        cases r1 with
        | Err x =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf1
          subst hcf1
          refine okPost_bind_eq (okPost_trivial _) ?_
          intro r3 hr3 _
          simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hr3
          subst hr3
          have hf : self2 = { self with required := req, next_phases := np } := hself2
          refine okPost_ok ⟨?_, fun x' _ => ⟨req, np, self.work, hf⟩, fun ev h => by simp at h⟩
          rw [hf]
          exact editSafe_required (editSafe_next hs np hnp) req hreq
        | Ok val1 =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf1
          subst hcf1
          obtain ⟨hlen, hmv, hrem, req', hself2', hfold, hI, hcert, hcirc⟩ := hacc val1 rfl
          have hf : self2 = { self with required := req', next_phases := np } := hself2'
          have hs2 : EditSafe self2 := by
            rw [hf]
            exact editSafe_required (editSafe_next hs np hnp) req' hI
          have hcert' : ∀ e ∈ allEdges (PfRoutes self edit).val,
              MutationEditedEdge (parents self.tree) edit.remove edit.add e.u.val e.v.val := hcert
          have hcirc' : (PfRoutes self edit).val.length = self.layout.circles.val.length := hcirc

          exact motion_edges_leaf self self2 req' np edit val val1 hf hs2 (by rw [hf]; exact hcap)
            hcirc' hcert'
    · simp only [hst, Bool.false_eq_true, ↓reduceIte]
      have hc1 := hs1.1
      have hinv1 := hs1.2.2.2.2.1
      refine okPost_bind (okPost_pair (scene_preflight_edit_frame _ edit hc1 hinv1)
        (scene_preflight_edit_accepted _ edit hc1 hinv1)) ?_
      rintro ⟨r1, self2⟩ ⟨⟨req, hself2, hreq⟩, hacc⟩
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro cf1 hcf1 _
      cases r1 with
      | Err x =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf1
        subst hcf1
        refine okPost_bind_eq (okPost_trivial _) ?_
        intro r3 hr3 _
        simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hr3
        subst hr3
        have hf : self2 = { self with required := req, next_phases := np } := hself2
        refine okPost_ok ⟨?_, fun x' _ => ⟨req, np, self.work, hf⟩, fun ev h => by simp at h⟩
        rw [hf]
        exact editSafe_required (editSafe_next hs np hnp) req hreq
      | Ok val1 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf1
        subst hcf1
        obtain ⟨hlen, hmv, hrem, req', hself2', hfold, hI, hcert, hcirc⟩ := hacc val1 rfl
        have hf : self2 = { self with required := req', next_phases := np } := hself2'
        have hs2 : EditSafe self2 := by
          rw [hf]
          exact editSafe_required (editSafe_next hs np hnp) req' hI
        have hcert' : ∀ e ∈ allEdges (PfRoutes self edit).val,
            MutationEditedEdge (parents self.tree) edit.remove edit.add e.u.val e.v.val := hcert
        have hcirc' : (PfRoutes self edit).val.length = self.layout.circles.val.length := hcirc
        refine okPost_bind_eq (okPost_of_spec (core.slice.Slice.is_empty_spec edit.remove)) ?_
        intro b _ hb
        by_cases hbt : b = true
        · simp only [hbt, ↓reduceIte]
          have h0' : edit.remove.length = 0 := by rw [← hb]; exact hbt
          have h0 : edit.remove.val.length = 0 := by simpa using h0'
          exact motion_commit_leaf self self2 edit val val1 hs2 (by rw [hf]) (by rw [hf])
            (by rw [hf]) h0 (by omega) hcirc' hcert'
        · simp only [hbt, Bool.false_eq_true, ↓reduceIte]
          exact motion_edges_leaf self self2 req' np edit val val1 hf hs2 (by rw [hf]; exact hcap)
            hcirc' hcert'

end Labyrinth
