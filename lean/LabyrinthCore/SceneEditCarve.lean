module
public import LabyrinthCore.SceneEditMotion

/-! Scene edits (S3), part 7: `Scene::carve`. A carve first copies the published phases into the
scratch table, then preflights, edits the tree and commits. A rejected carve changes nothing except
`required`, `next_phases` and `work`; an accepted one leaves a safe scene with the edited tree and
the published phases unchanged. Partial correctness (`OkPost`): the preflight and the crossing
admissions reach the geometry. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- The carve copy loop writes the published phases over the scratch table from entry `i` on. -/
theorem carve_loop_spec (v v1 : alloc.vec.Vec Std.I32)
    (hn : v.val.length ≤ v1.val.length) (i : Std.Usize) (hi : i.val ≤ v.val.length) :
    scene.Scene.carve_loop v v1 i ⦃ (out : alloc.vec.Vec Std.I32) =>
      out.val.length = v1.val.length ∧
      ∀ j, out.val[j]? = if i.val ≤ j ∧ j < v.val.length then v.val[j]? else v1.val[j]? ⦄ := by
  unfold scene.Scene.carve_loop
  refine loop.spec_decr_nat (fun x : alloc.vec.Vec Std.I32 × Std.Usize => v.val.length - x.2.val)
    (fun x => x.1.val.length = v1.val.length ∧ x.2.val ≤ v.val.length ∧ i.val ≤ x.2.val ∧
      ∀ j, x.1.val[j]? = if i.val ≤ j ∧ j < x.2.val then v.val[j]? else v1.val[j]?)
    (fun (out : alloc.vec.Vec Std.I32) => out.val.length = v1.val.length ∧
      ∀ j, out.val[j]? = if i.val ≤ j ∧ j < v.val.length then v.val[j]? else v1.val[j]?)
    _ (v1, i) ?_ ⟨rfl, hi, le_refl _, fun j => by simp⟩
  rintro ⟨v2, i1⟩ ⟨hlen, hi1, hii, hv2⟩
  dsimp only at hlen hi1 hii hv2
  unfold scene.Scene.carve_loop.body
  simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
  by_cases hlt : i1 < alloc.vec.Vec.len v
  · have hltn : i1.val < v.val.length := by simpa using hlt
    simp only [hlt, ite_true]
    apply spec_bind (alloc.vec.Vec.index_usize_spec v i1 hltn)
    intro i2 hi2
    apply spec_bind (alloc.vec.Vec.index_mut_usize_spec v2 i1 (by simp; omega))
    rintro ⟨x, back⟩ ⟨hx, rfl⟩
    apply spec_bind (Usize.add_spec (x := i1) (y := 1#usize) (by scalar_tac))
    intro i3 hi3
    have hi3v : i3.val = i1.val + 1 := by simpa using hi3
    rw [spec_ok]
    dsimp only
    refine ⟨⟨by simp [hlen], by omega, by omega, ?_⟩, by omega⟩
    intro j
    rw [alloc.vec.Vec.set_val_eq, List.getElem?_set]
    by_cases hji : i1.val = j
    · subst hji
      have hl : i1.val < v2.val.length := by omega
      have hc : i.val ≤ i1.val ∧ i1.val < i3.val := by omega
      simp only [hl, hc, and_self, ↓reduceIte, hi2]
      rw [List.getElem?_eq_getElem hltn]
    · simp only [hji, ↓reduceIte]
      rw [hv2 j]
      have : (i.val ≤ j ∧ j < i1.val) ↔ (i.val ≤ j ∧ j < i3.val) := by omega
      simp only [this]
  · simp only [hlt, ite_false, spec_ok]
    have hge : i1.val = v.val.length := by
      have : ¬ i1.val < v.val.length := by simpa using hlt
      omega
    refine ⟨hlen, fun j => ?_⟩
    rw [hv2 j, hge]

/-- The outcome of a carve. -/
def CarvePost (self : scene.Scene) (edit : scene.Edit)
    (p : (core.result.Result walker.Stamp topology.Error) × scene.Scene) : Prop :=
  EditSafe p.2 ∧
  (∀ x, p.1 = core.result.Result.Err x → ∃ req np wk,
    p.2 = { self with required := req, next_phases := np, work := wk }) ∧
  (∀ st, p.1 = core.result.Result.Ok st →
    st = p.2.stamp ∧ p.2.layout = self.layout ∧
    (∀ u v, parentEdge (parents p.2.tree) u v ↔
      MutationEditedEdge (parents self.tree) edit.remove edit.add u v) ∧
    (edit.routes = none → p.2.routes = self.routes) ∧
    (∀ rs, edit.routes = some rs → allEdges p.2.routes.val = allEdges rs.val) ∧
    p.2.phases = self.phases)

theorem scene_carve_spec (self : scene.Scene) (stamp : walker.Stamp) (walker_index target : Std.Usize)
    (edit : scene.Edit) (hs : EditSafe self) (hcap : EditCapacity self) :
    OkPost (scene.Scene.carve self stamp walker_index target edit) (CarvePost self edit) := by
  unfold scene.Scene.carve
  refine okPost_bind (okPost_trivial _) ?_
  intro r _
  cases r with
  | Err x =>
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro cf hcf _
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf
    subst hcf
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro rr hrr _
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hrr
    subst hrr
    exact okPost_ok ⟨hs, fun _ _ => ⟨self.required, self.next_phases, self.work, rfl⟩,
      fun st h => by simp at h⟩
  | Ok u1 =>
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro cf hcf _
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf
    subst hcf
    refine okPost_bind (okPost_trivial _) ?_
    intro o _
    refine okPost_bind (okPost_trivial _) ?_
    intro r _
    cases r with
    | Err x =>
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro cf hcf _
      simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf
      subst hcf
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro rr hrr _
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hrr
      subst hrr
      exact okPost_ok ⟨hs, fun _ _ => ⟨self.required, self.next_phases, self.work, rfl⟩,
        fun st h => by simp at h⟩
    | Ok val =>
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro cf hcf _
      simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf
      subst hcf
      refine okPost_bind (okPost_trivial _) ?_
      intro b _
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte]
        exact okPost_ok ⟨hs, fun _ _ => ⟨self.required, self.next_phases, self.work, rfl⟩,
          fun st h => by simp at h⟩
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        refine okPost_bind (okPost_trivial _) ?_
        intro r _
        cases r with
        | Err x =>
          refine okPost_bind_eq (okPost_trivial _) ?_
          intro cf hcf _
          simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf
          subst hcf
          refine okPost_bind_eq (okPost_trivial _) ?_
          intro rr hrr _
          simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hrr
          subst hrr
          exact okPost_ok ⟨hs, fun _ _ => ⟨self.required, self.next_phases, self.work, rfl⟩,
            fun st h => by simp at h⟩
        | Ok u2 =>
          refine okPost_bind_eq (okPost_trivial _) ?_
          intro cf hcf _
          simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf
          subst hcf
          refine okPost_bind (okPost_trivial _) ?_
          intro r _
          cases r with
          | Err x =>
            refine okPost_bind_eq (okPost_trivial _) ?_
            intro cf hcf _
            simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf
            subst hcf
            refine okPost_bind_eq (okPost_trivial _) ?_
            intro rr hrr _
            simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hrr
            subst hrr
            exact okPost_ok ⟨hs, fun _ _ => ⟨self.required, self.next_phases, self.work, rfl⟩,
              fun st h => by simp at h⟩
          | Ok u3 =>
            refine okPost_bind_eq (okPost_trivial _) ?_
            intro cf hcf _
            simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf
            subst hcf
            refine okPost_bind (okPost_trivial _) ?_
            intro edge _
            refine okPost_bind (okPost_trivial _) ?_
            intro b1 _
            by_cases hb1 : b1 = true
            · simp only [hb1, ↓reduceIte]
              exact okPost_ok ⟨hs, fun _ _ => ⟨self.required, self.next_phases, self.work, rfl⟩,
                fun st h => by simp at h⟩
            · simp only [hb1, Bool.false_eq_true, ↓reduceIte]
              refine okPost_bind (okPost_trivial _) ?_
              intro b2 _
              by_cases hb2 : b2 = true
              · simp only [hb2, ↓reduceIte]
                refine okPost_bind (P := fun v : alloc.vec.Vec Std.I32 =>
                    v.val.length = self.next_phases.val.length ∧
                    ∀ j, j < self.phases.val.length → v.val[j]? = self.phases.val[j]?)
                  (okPost_mono (okPost_of_spec (carve_loop_spec self.phases self.next_phases
                    hs.2.2.2.2.2.1 0#usize (by simp))) ?_) ?_
                · rintro v ⟨hl, hj⟩
                  exact ⟨hl, fun j hj' => by rw [hj j]; simp [hj']⟩
                intro v ⟨hv, hvj⟩
                have hs1 := editSafe_next hs v hv
                have hc1 := hs1.1
                have hinv1 := hs1.2.2.2.2.1
                refine okPost_bind (okPost_pair (scene_preflight_edit_frame _ edit hc1 hinv1)
                  (scene_preflight_edit_accepted _ edit hc1 hinv1)) ?_
                rintro ⟨r4, self1⟩ ⟨⟨req, hself1, hreq⟩, hacc⟩
                refine okPost_bind_eq (okPost_trivial _) ?_
                intro cf4 hcf4 _
                cases r4 with
                | Err x =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf4
                  subst hcf4
                  refine okPost_bind_eq (okPost_trivial _) ?_
                  intro r6 hr6 _
                  simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                    core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hr6
                  subst hr6
                  have hf : self1 = { self with required := req, next_phases := v } := hself1
                  refine okPost_ok ⟨?_, fun x' _ => ⟨req, v, self.work, hf⟩, fun st h => by simp at h⟩
                  rw [hf]
                  exact editSafe_required hs1 req hreq
                | Ok m =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf4
                  subst hcf4
                  obtain ⟨hlen, hmv, hrem, req', hself1', hfold, hI, hcert, hcirc⟩ := hacc m rfl
                  have hf : self1 = { self with required := req', next_phases := v } := hself1'
                  have hs2 : EditSafe self1 := by
                    rw [hf]
                    exact editSafe_required hs1 req' hI
                  have hcap1 : EditCapacity self1 := by rw [hf]; exact hcap
                  have hcert1 : ∀ e ∈ allEdges (PfRoutes self1 edit).val,
                      MutationEditedEdge (parents self1.tree) edit.remove edit.add e.u.val e.v.val := by
                    rw [hf]; exact hcert
                  have hcirc1 : (PfRoutes self1 edit).val.length = self1.layout.circles.val.length := by
                    rw [hf]; exact hcirc
                  have e1 : self1.layout = self.layout := by rw [hf]
                  have e2 : self1.tree = self.tree := by rw [hf]
                  have e3 : self1.routes = self.routes := by rw [hf]
                  refine okPost_bind (okPost_trivial _) ?_
                  intro revision _
                  obtain ⟨c2, t2, w2, cap2, rq2, ph2, rl2, edges2⟩ := hs2
                  refine okPost_bind (okPost_of_spec (mutation_edit_edges_tree_valid self1.layout.carrier
                    self1.tree edit.remove edit.add self1.work c2 t2 w2 cap2 hcap1)) ?_
                  rintro ⟨r5, t, w⟩ ⟨hwv, hpl, herr, hok⟩
                  refine okPost_bind_eq (okPost_trivial _) ?_
                  intro cf5 hcf5 _
                  cases r5 with
                  | Err e =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf5
                    subst hcf5
                    refine okPost_bind_eq (okPost_trivial _) ?_
                    intro r6 hr6 _
                    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                      core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hr6
                    subst hr6
                    have ht : t = self1.tree := herr e rfl
                    subst ht
                    refine okPost_ok ⟨editSafe_work ⟨c2, t2, w2, cap2, rq2, ph2, rl2, edges2⟩ w hwv hpl,
                      fun x _ => ⟨req', v, w, by rw [hf]⟩, fun st h => by simp at h⟩
                  | Ok u =>
                    cases u
                    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf5
                    subst hcf5
                    obtain ⟨hroot, hlen2, hiff, hcar, htv⟩ := hok rfl
                    refine okPost_bind (m := scene.Scene.commit_edit { self1 with tree := t, work := w } edit
                      revision) (okPost_of_spec (edit_commit_post self1 t w edit revision c2 htv hwv
                        (by dsimp only at hlen2 hpl ⊢; omega) rq2 ph2 rl2 ?_ hiff hcert1)) ?_
                    · intro rs hrs
                      have := hcirc1
                      simp only [PfRoutes, hrs] at this
                      exact this
                    · rintro s3 ⟨hcp, htr, hwk⟩
                      refine okPost_ok ⟨hcp.1, fun x hx => by simp at hx, fun st hst => ?_⟩
                      simp only [core.result.Result.Ok.injEq] at hst
                      subst hst
                      refine ⟨rfl, hcp.2.1.trans e1, ?_, fun hn => (hcp.2.2.2.1 hn).trans e3, hcp.2.2.2.2.1, ?_⟩
                      · intro u v
                        rw [hcp.2.2.1 u v, e2]
                      · obtain ⟨_, _, _, _, _, _, _, _, hphl, hphp⟩ := hcp
                        have hnp : self1.next_phases = v := by rw [hf]
                        have hpn : self1.phases = self.phases := by rw [hf]
                        apply alloc.vec.Vec.ext
                        apply List.ext_getElem?
                        intro j
                        by_cases hj : j < self.phases.val.length
                        · rw [hphp j (by rw [hpn]; exact hj), hnp, hvj j hj]
                        · have h1 : s3.phases.val[j]? = none := List.getElem?_eq_none (by rw [hphl, hpn]; omega)
                          have h2 : self.phases.val[j]? = none := List.getElem?_eq_none (by omega)
                          rw [h1, h2]
              · simp only [hb2, Bool.false_eq_true, ↓reduceIte]
                exact okPost_ok ⟨hs, fun _ _ => ⟨self.required, self.next_phases, self.work, rfl⟩,
                  fun st h => by simp at h⟩

end Labyrinth
