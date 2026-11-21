module
public import LabyrinthCore.SceneMotionReach

/-! The motion planner (S7), part 3: an accepted advance keeps every doorway of the tree admissible.

`motion_door` adds to `motion_shape` which check an accepted motion passed: either it was
stationary (tree, published phases and routes unchanged), or `preflight_edit` accepted the edit on
the scene with the scratch phase table `np` that the motion then published. An accepted
`preflight_edit` checked the doorway of every kept tree edge and of every added edge for the
transition from the published phases to `np` (`KeptVerdict`, `AddVerdict`).

`advance_motion_connected` is the formal reading of "both motion modes keep admissible doorways
connected": after an accepted `advance_motion`, the tree is valid on the layout's carrier, every
route edge is a tree edge, and either nothing moved or every edge of the new tree has an existing
doorway for the published transition; in particular no old tree edge whose doorway became
inadmissible is still in the tree. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- What an accepted motion checked: stationary, or an accepted preflight for the scratch phase
table it published. -/
def MotionDoor (self : scene.Scene) (steps : Slice Std.I32) (edit : scene.Edit)
    (p : (core.result.Result scene.MotionEvent topology.Error) × scene.Scene) : Prop :=
  ∀ ev, p.1 = core.result.Result.Ok ev →
    (p.2.tree = self.tree ∧ p.2.phases = self.phases ∧ p.2.routes = self.routes) ∨
    ∃ (np : alloc.vec.Vec Std.I32) (m : Std.Usize) (req : alloc.vec.Vec topology.Edge),
      PrepAccepted self steps np ∧
      PreflightOutcome { self with next_phases := np } edit
        (core.result.Result.Ok m, { self with next_phases := np, required := req }) ∧
      ∀ j, j < self.phases.val.length → p.2.phases.val[j]? = np.val[j]?

theorem motionDoor_residual (self : scene.Scene) (steps : Slice Std.I32) (edit : scene.Edit)
    (Y : scene.Scene) (residual : core.result.Result Never topology.Error) :
    OkPost (do
      let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        scene.MotionEvent (core.convert.FromSame topology.Error) residual
      ok (r, Y) : Result ((core.result.Result scene.MotionEvent topology.Error) × scene.Scene))
      (MotionDoor self steps edit) := by
  cases residual with
  | Ok n => cases n
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, Std.bind_ok]
    exact okPost_ok (fun ev h => by simp at h)

/-- The commit after an accepted preflight publishes the scratch table. -/
theorem motion_commit_door (self : scene.Scene) (steps : Slice Std.I32) (edit : scene.Edit)
    (np : alloc.vec.Vec Std.I32) (X : scene.Scene) (val : Std.U64) (m : Std.Usize)
    (req : alloc.vec.Vec topology.Edge)
    (h6 : X.phases = self.phases) (h7 : X.next_phases = np) (h8 : X.routes = self.routes)
    (hph : self.phases.val.length ≤ np.val.length)
    (hrl : self.routes.val.length = self.layout.circles.val.length)
    (hroutes : ∀ rs, edit.routes = some rs → rs.val.length = self.layout.circles.val.length)
    (hacc : PrepAccepted self steps np)
    (hpo : PreflightOutcome { self with next_phases := np } edit
      (core.result.Result.Ok m, { self with next_phases := np, required := req })) :
    OkPost (scene.Scene.commit_edit X edit val) (fun s3 =>
      ∀ r, MotionDoor self steps edit (r, s3)) := by
  refine okPost_of_spec (spec_mono (scene_commit_edit_spec X edit val (by rw [h6, h7]; exact hph)
    (fun rs hrs => by rw [h8, hroutes rs hrs, hrl])) ?_)
  rintro s3 ⟨ph, hphl, hphv, rt, _, _, rfl⟩ r ev _
  refine Or.inr ⟨np, m, req, hacc, hpo, fun j hj => ?_⟩
  simp only [commitResult]
  rw [hphv j (by rw [h6]; exact hj), h7]

/-- The commit after an accepted preflight. -/
macro "door_commit" hs:term:max hnp:term:max hacc:term:max hpo:term:max : tactic =>
  `(tactic| (
  refine okPost_bind (motion_commit_door _ _ _ _ _ _ _ _ ?_ ?_ ?_
      (motion_phase_room $hs $hnp) ($hs).2.2.2.2.2.2.1 (preflight_routes_len $hpo) $hacc
      $hpo) (fun s3 h => okPost_ok (h _)) <;> rfl))

/-- The edge edit and the commit after an accepted preflight. -/
macro "door_edges" hs:term:max hnp:term:max hacc:term:max hpo:term:max : tactic =>
  `(tactic| (
  refine okPost_bind (okPost_trivial _) ?_
  rintro ⟨r2, t, w⟩ _
  refine okPost_bind_eq (okPost_trivial _) (fun cf2 hcf2 _ => ?_)
  cases r2 with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf2
    subst hcf2
    exact motionDoor_residual _ _ _ _ _
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf2
    subst hcf2
    refine okPost_bind (motion_commit_door _ _ _ _ _ _ _ _ ?_ ?_ ?_
      (motion_phase_room $hs $hnp) ($hs).2.2.2.2.2.2.1 (preflight_routes_len $hpo) $hacc
      $hpo) (fun s3 h => okPost_ok (h _)) <;> rfl))

/-- The part of a motion after the preflight accepted, whichever way the removal test is known. -/
macro "door_after" hs:term:max hnp:term:max hacc:term:max hpo:term:max : tactic =>
  `(tactic| first
    | door_commit $hs $hnp $hacc $hpo
    | door_edges $hs $hnp $hacc $hpo
    | (refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
       split
       · door_commit $hs $hnp $hacc $hpo
       · door_edges $hs $hnp $hacc $hpo))

/-- The preflight and what follows, in every branch of `motion` that runs it. -/
macro "door_tail" hs:term:max hnp:term:max hacc:term:max : tactic => `(tactic| (
  refine okPost_bind (preflight_shape _ _) ?_
  rintro ⟨r1, s2⟩ ⟨hpo, req, hs2⟩
  simp only at hs2 hpo
  subst hs2
  refine okPost_bind_eq (okPost_trivial _) (fun cf1 hcf1 _ => ?_)
  cases r1 with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf1
    subst hcf1
    exact motionDoor_residual _ _ _ _ _
  | Ok m =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf1
    subst hcf1
    dsimp only
    door_after $hs $hnp $hacc hpo))

/-- **Which check an accepted motion passed.** -/
theorem motion_door (self : scene.Scene) (stamp : walker.Stamp) (steps : Slice Std.I32)
    (edit : scene.Edit) (hs : EditSafe self) :
    OkPost (scene.Scene.motion self stamp steps edit) (MotionDoor self steps edit) := by
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
    exact motionDoor_residual _ _ _ _ _
  | Ok val =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf
    subst hcf
    have hacc' := hacc val rfl
    refine okPost_bind (okPost_trivial _) (fun stationary _ => ?_)
    split
    · refine okPost_bind (okPost_trivial _) (fun b _ => ?_)
      split
      · refine okPost_bind (okPost_trivial _) (fun b1 _ => ?_)
        split
        · dsimp only
          split
          · exact okPost_ok (fun _ _ => Or.inl ⟨rfl, rfl, rfl⟩)
          · door_tail hs hnp hacc'
        · door_tail hs hnp hacc'
      · door_tail hs hnp hacc'
    · door_tail hs hnp hacc'

/-! ### From the preflight verdicts to the edges of the new tree -/

theorem edge_new_canon (u v : Std.Usize) :
    topology.Edge.new u v = ok (mutationCanonicalEdge { u := u, v := v }) := by
  unfold topology.Edge.new mutationCanonicalEdge
  split <;> simp_all

theorem unitOf_ok {r : core.result.Result scene.Doorway topology.Error}
    (h : core.result.Result.Ok () = unitOf r) : ∃ d, r = core.result.Result.Ok d := by
  cases r with
  | Ok d => exact ⟨d, rfl⟩
  | Err x => simp [unitOf] at h

/-- A removal list containing an edge's canonical form removes the edge. -/
theorem removal_of_contains {remove : Slice topology.Edge} {e : topology.Edge}
    (h : scene.contains remove (mutationCanonicalEdge e) = ok true) :
    mutationRemoval remove e.u.val e.v.val := by
  have hs := scene_contains_spec remove (mutationCanonicalEdge e)
  rw [h] at hs
  obtain ⟨x, hx, hxe⟩ := ((spec_ok _).mp hs).mp rfl
  rw [← mutation_removal_canonical_edge, ← hxe, mutation_removal_canonical_edge]
  exact ⟨x, hx, Or.inl ⟨rfl, rfl⟩⟩

/-- A kept tree edge, seen from its child: its doorway exists for the transition. -/
theorem kept_door_dir (L : scene.Layout) (t : spanning_tree.Tree)
    (phases next : alloc.vec.Vec Std.I32) (remove : Slice topology.Edge)
    (hk : ∀ j, j < t.parents.val.length →
      KeptVerdict L t phases next remove j (core.result.Result.Ok ()))
    (c p : Std.Usize) (hpar : t.parents.val[c.val]? = some p) (hne : p.val ≠ c.val)
    (hnr : ¬ mutationRemoval remove c.val p.val) :
    ∃ d, scene.Layout.doorway L (mutationCanonicalEdge { u := c, v := p })
      (alloc.vec.Vec.deref phases) (alloc.vec.Vec.deref next) = ok (core.result.Result.Ok d) := by
  have hcl : c.val < t.parents.val.length := (List.getElem?_eq_some_iff.mp hpar).1
  obtain ⟨p', hp', hv⟩ := hk c.val hcl
  rw [hpar] at hp'
  cases hp'
  rcases hv with ⟨heq, _⟩ | ⟨_, cu, hcu, e, he, hv⟩
  · exact absurd heq hne
  · have hcu' : cu = c := UScalar.eq_of_val_eq hcu
    subst hcu'
    rw [edge_new_canon] at he
    simp only [ok.injEq] at he
    subst he
    rcases hv with ⟨hc, _⟩ | ⟨_, r, hd, hr⟩
    · exact absurd (removal_of_contains hc) hnr
    · obtain ⟨d, rfl⟩ := unitOf_ok hr
      exact ⟨d, hd⟩

/-- Every kept tree edge has an existing doorway for the transition. -/
theorem kept_door (L : scene.Layout) (t : spanning_tree.Tree) (phases next : alloc.vec.Vec Std.I32)
    (remove : Slice topology.Edge)
    (hk : ∀ j, j < t.parents.val.length →
      KeptVerdict L t phases next remove j (core.result.Result.Ok ()))
    (u v : Std.Usize) (hpe : parentEdge (parents t) u.val v.val)
    (hnr : ¬ mutationRemoval remove u.val v.val) :
    ∃ e d, topology.Edge.new u v = ok e ∧ scene.Layout.doorway L e (alloc.vec.Vec.deref phases)
      (alloc.vec.Vec.deref next) = ok (core.result.Result.Ok d) := by
  obtain ⟨_, _, hne, hp | hp⟩ := hpe
  · simp only [parents, List.getElem?_map, Option.map_eq_some_iff] at hp
    obtain ⟨p, hpar, hpv⟩ := hp
    have : p = v := UScalar.eq_of_val_eq hpv
    subst this
    obtain ⟨d, hd⟩ := kept_door_dir L t phases next remove hk u p hpar (Ne.symm hne) hnr
    exact ⟨_, d, edge_new_canon u p, hd⟩
  · simp only [parents, List.getElem?_map, Option.map_eq_some_iff] at hp
    obtain ⟨p, hpar, hpv⟩ := hp
    have : p = u := UScalar.eq_of_val_eq hpv
    subst this
    obtain ⟨d, hd⟩ := kept_door_dir L t phases next remove hk v p hpar hne
      (fun h => hnr ((mutation_removal_symmetric remove _ _).mp h))
    refine ⟨_, d, edge_new_canon p v, ?_⟩
    rw [mutation_canonical_swap]
    exact hd

/-- Every added edge has an existing doorway for the transition. -/
theorem added_door (L : scene.Layout) (phases next : alloc.vec.Vec Std.I32)
    (add : Slice topology.Edge)
    (ha : ∀ k, k < add.val.length → AddVerdict L phases next add k (core.result.Result.Ok ()))
    (u v : Std.Usize) (hadd : mutationAddition add u.val v.val) :
    ∃ e d, topology.Edge.new u v = ok e ∧ scene.Layout.doorway L e (alloc.vec.Vec.deref phases)
      (alloc.vec.Vec.deref next) = ok (core.result.Result.Ok d) := by
  obtain ⟨x, hx, hxe⟩ := hadd
  obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hx
  obtain ⟨e, he, e1, he1, r, hd, hr⟩ := ha k hk
  rw [List.getElem?_eq_getElem hk, hkx] at he
  cases he
  obtain ⟨d, rfl⟩ := unitOf_ok hr
  refine ⟨e1, d, ?_, hd⟩
  rw [edge_new_canon] at he1 ⊢
  rw [← he1]
  rcases hxe with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [UScalar.eq_of_val_eq h1, UScalar.eq_of_val_eq h2]
  · rw [UScalar.eq_of_val_eq h1, UScalar.eq_of_val_eq h2, mutation_canonical_swap]

/-- An accepted preflight's verdicts, as a doorway for every edge of the edited tree. -/
theorem preflight_doors {self : scene.Scene} {edit : scene.Edit} {m : Std.Usize}
    {s2 : scene.Scene} (hpo : PreflightOutcome self edit (core.result.Result.Ok m, s2))
    (u v : Std.Usize)
    (he : MutationEditedEdge (parents self.tree) edit.remove edit.add u.val v.val) :
    ∃ e d, topology.Edge.new u v = ok e ∧ scene.Layout.doorway self.layout e
      (alloc.vec.Vec.deref self.phases) (alloc.vec.Vec.deref self.next_phases) =
        ok (core.result.Result.Ok d) := by
  rcases hpo with ⟨_, h⟩ | ⟨_, ⟨x, k, _, _, _, h⟩ | ⟨_, req, ⟨x, _, h⟩ | ⟨_, hafter⟩⟩⟩
  · simp at h
  · simp at h
  · simp at h
  · rcases hafter with ⟨x, k, _, _, _, h⟩ | ⟨hkept, ⟨x, k, _, _, _, h⟩ | ⟨_, _, hadd, _⟩⟩
    · simp at h
    · simp at h
    · rcases he with ⟨hpe, hnr⟩ | hadd'
      · exact kept_door _ _ _ _ _ hkept u v hpe hnr
      · exact added_door _ _ _ _ hadd u v hadd'

/-! ### The headline -/

/-- **An accepted `advance_motion` keeps admissible doorways connected.** The new tree is valid on
the layout's carrier (connected and spanning), every route edge is a tree edge, and either nothing
moved (tree, published phases and routes unchanged) or the published phases are a table `np` for
which every edge of the new tree has an existing doorway between the old and the new phases: no
edge whose doorway became inadmissible stays in the tree. -/
theorem advance_motion_connected (s : scene.Scene) (stamp : walker.Stamp)
    (requested : Slice Std.I32) (w : motion.MotionWorkspace) (h : SceneInv s) :
    OkPost (scene.Scene.advance_motion s stamp requested w) (fun p =>
      ∀ a, p.1 = core.result.Result.Ok a →
        p.2.1.layout = s.layout ∧ TreeValid s.layout.carrier p.2.1.tree ∧
        (∀ e ∈ allEdges p.2.1.routes.val, parentEdge (parents p.2.1.tree) e.u.val e.v.val) ∧
        ((p.2.1.tree = s.tree ∧ p.2.1.phases = s.phases ∧ p.2.1.routes = s.routes) ∨
          ∃ np : alloc.vec.Vec Std.I32,
            (∀ j, j < s.phases.val.length → p.2.1.phases.val[j]? = np.val[j]?) ∧
            ∀ u v : Std.Usize, parentEdge (parents p.2.1.tree) u.val v.val →
              ∃ e d, topology.Edge.new u v = ok e ∧
                scene.Layout.doorway s.layout e (alloc.vec.Vec.deref s.phases)
                  (alloc.vec.Vec.deref np) = ok (core.result.Result.Ok d))) := by
  refine okPost_mono (advance_motion_scene s stamp requested w) ?_
  rintro ⟨r, s', w'⟩ hp a ha
  simp only at ha hp ⊢
  rcases hp with ⟨⟨x, hx⟩, _⟩ | ⟨c, steps, edit, r', hc, hm, hr⟩
  · simp [ha] at hx
  · have hc' := sceneInv_next h hc
    have hr' := hr a ha
    obtain ⟨v, hv, rfl⟩ := hc
    have hinv := motion_inv _ stamp steps edit hc' _ hm
    obtain ⟨_, _, hok⟩ := scene_motion_spec _ stamp steps edit hc'.1 hc'.2.1 _ hm
    obtain ⟨_, hlay, hedt, _, _⟩ := hok a.event hr'
    simp only at hlay hedt hinv
    have hs' := hinv.1
    have ht := hs'.2.1
    rw [hlay] at ht
    refine ⟨hlay, ht, hs'.2.2.2.2.2.2.2, ?_⟩
    rcases motion_door _ stamp steps edit hc'.1 _ hm a.event hr' with
      hst | ⟨np, m, req, _, hpo, hph⟩
    · exact Or.inl hst
    · refine Or.inr ⟨np, hph, fun u v hpe => ?_⟩
      exact preflight_doors hpo u v ((hedt u.val v.val).mp hpe)

/-- The same on every scene reachable with `advance_motion`. -/
theorem reachableM_advance_motion_connected {s : scene.Scene} (hs : SceneReachableM s)
    (stamp : walker.Stamp) (requested : Slice Std.I32) (w : motion.MotionWorkspace) :
    OkPost (scene.Scene.advance_motion s stamp requested w) (fun p =>
      ∀ a, p.1 = core.result.Result.Ok a →
        p.2.1.layout = s.layout ∧ TreeValid s.layout.carrier p.2.1.tree ∧
        (∀ e ∈ allEdges p.2.1.routes.val, parentEdge (parents p.2.1.tree) e.u.val e.v.val) ∧
        ((p.2.1.tree = s.tree ∧ p.2.1.phases = s.phases ∧ p.2.1.routes = s.routes) ∨
          ∃ np : alloc.vec.Vec Std.I32,
            (∀ j, j < s.phases.val.length → p.2.1.phases.val[j]? = np.val[j]?) ∧
            ∀ u v : Std.Usize, parentEdge (parents p.2.1.tree) u.val v.val →
              ∃ e d, topology.Edge.new u v = ok e ∧
                scene.Layout.doorway s.layout e (alloc.vec.Vec.deref s.phases)
                  (alloc.vec.Vec.deref np) = ok (core.result.Result.Ok d))) :=
  advance_motion_connected s stamp requested w (sceneReachableM_inv hs).1

end Labyrinth
