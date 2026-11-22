module
public import LabyrinthCore.SceneShatterBegin
public import LabyrinthCore.SceneEditCarve

/-! Shatter (S6), part 5: `Scene::reform_patch`. After the stamp and the handle it rejects (all with
`InvalidTransition`) a frozen scene or a zero duration, a patch that is not `Scattered` with its
deadline already reached, then (`Overflow`) a deadline that does not fit, then an edit with an edge
outside the patch. Past those it is `carve`'s edit: copy the published phases into the scratch table,
`preflight_edit`, `edit_edges` when something is removed, `commit_edit`; then the patch becomes
`Reforming` with the new deadline and the trail revision becomes the new revision. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

theorem reform_loop1_eq : scene.Scene.reform_patch_loop1 = scene.Scene.reform_patch_loop0 := rfl

/-- Some edge of the list from entry `i0` on has an end outside the patch. -/
def EdgeOutside (p : shatter.Patch) (s : Slice topology.Edge) (i0 : Nat) : Prop :=
  ∃ j, i0 ≤ j ∧ ∃ e, s.val[j]? = some e ∧ ¬ (PatchHas p e.u.val ∧ PatchHas p e.v.val)

theorem edgeOutside_step (p : shatter.Patch) (s : Slice topology.Edge) (i : Nat) (e : topology.Edge)
    (hes : s.val[i]? = some e) :
    EdgeOutside p s i ↔
      (¬ (PatchHas p e.u.val ∧ PatchHas p e.v.val)) ∨ EdgeOutside p s (i + 1) := by
  constructor
  · rintro ⟨j, hj, e', he', hn⟩
    by_cases hji : j = i
    · subst hji; rw [hes] at he'; cases he'; exact Or.inl hn
    · exact Or.inr ⟨j, by omega, e', he', hn⟩
  · rintro (h | ⟨j, hj, e', he', hn⟩)
    · exact ⟨i, le_refl _, e, hes, h⟩
    · exact ⟨j, by omega, e', he', hn⟩

theorem reform_outside_spec (v : alloc.vec.Vec shatter.Patch) (s : Slice topology.Edge)
    (slot : Std.Usize) (p : shatter.Patch) (hp : v.val[slot.val]? = some p)
    (out0 : Bool) (i0 : Std.Usize) :
    scene.Scene.reform_patch_loop0 v s slot out0 i0 ⦃ r =>
      (r = true ↔ out0 = true ∨ EdgeOutside p s i0.val) ⦄ := by
  unfold scene.Scene.reform_patch_loop0
  have hpl : slot.val < v.val.length := (List.getElem?_eq_some_iff.mp hp).1
  refine loop.spec_decr_nat (fun x : Bool × Std.Usize => s.val.length - x.2.val)
    (fun x => (x.1 = true ∨ EdgeOutside p s x.2.val) ↔ (out0 = true ∨ EdgeOutside p s i0.val))
    (fun r : Bool => (r = true ↔ out0 = true ∨ EdgeOutside p s i0.val)) _ (out0, i0) ?_ Iff.rfl
  rintro ⟨o, i⟩ hinv
  dsimp only at hinv
  unfold scene.Scene.reform_patch_loop0.body
  by_cases hlt : i < Slice.len s
  · have hil : i.val < s.val.length := by simpa [Slice.len] using hlt
    simp only [hlt, ↓reduceIte]
    by_cases ho : o = true
    · simp only [ho, ↓reduceIte, spec_ok]
      rw [← hinv]
      simp [ho]
    · simp only [ho, Bool.false_eq_true, ↓reduceIte]
      apply spec_bind (Slice.index_usize_spec s i hil)
      intro e he
      simp only [alloc.vec.Vec.index_slice_index]
      apply spec_bind (alloc.vec.Vec.index_usize_spec v slot hpl)
      intro p1 hp1
      have hpe : p1 = p := by
        rw [hp1]; have := hp; rw [List.getElem?_eq_getElem hpl] at this; exact Option.some.inj this
      subst hpe
      apply spec_bind (patch_contains_spec p1 e.u)
      intro b hb
      have hes : s.val[i.val]? = some e := by rw [List.getElem?_eq_getElem hil, he]
      have hstep := edgeOutside_step p1 s i.val e hes
      have hnext : ∀ (o' : Bool) (i2 : Std.Usize), i2.val = i.val + 1 →
          (o' = true ↔ ¬ (PatchHas p1 e.u.val ∧ PatchHas p1 e.v.val)) →
          ((o' = true ∨ EdgeOutside p1 s i2.val) ↔ (out0 = true ∨ EdgeOutside p1 s i0.val)) ∧
            s.val.length - i2.val < s.val.length - i.val := by
        intro o' i2 hi2 ho'
        refine ⟨?_, by omega⟩
        rw [← hinv, hi2, hstep]
        simp only [ho, ho']
        tauto
      by_cases hb' : b = true
      · simp only [hb', ↓reduceIte, Std.bind_assoc]
        have hu : PatchHas p1 e.u.val := hb.mp hb'
        apply spec_bind (patch_contains_spec p1 e.v)
        intro b1 hb1
        simp only [Std.bind_ok]
        apply spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
        intro i2 hi2
        rw [spec_ok]
        refine hnext _ i2 (by simpa using hi2) ?_
        simp only [decide_eq_true_eq]
        constructor
        · intro h hh; exact h (hb1.mpr hh.2)
        · intro h hv; exact h ⟨hu, hb1.mp hv⟩
      · simp only [hb', Bool.false_eq_true, ↓reduceIte, Std.bind_ok]
        apply spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
        intro i2 hi2
        rw [spec_ok]
        refine hnext _ i2 (by simpa using hi2) ?_
        have hnu : ¬ PatchHas p1 e.u.val := fun h => hb' (hb.mpr h)
        simp [hnu]
  · simp only [hlt, ↓reduceIte, spec_ok]
    rw [← hinv]
    have hge : s.val.length ≤ i.val := by simpa [Slice.len] using hlt
    simp only [EdgeOutside]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨j, hj, e, he, _⟩)
      · exact h
      · exfalso; rw [List.getElem?_eq_none (by omega)] at he; simp at he

/-! ### The whole of `reform_patch` -/

/-- The scratch phase table `reform_patch` hands to `preflight_edit`: the published phases copied
over the front of the old scratch table. -/
def PhaseCopy (self : scene.Scene) (np : alloc.vec.Vec Std.I32) : Prop :=
  np.val.length = self.next_phases.val.length ∧
    ∀ j, j < self.phases.val.length → np.val[j]? = self.phases.val[j]?

/-- Some edit edge has an end outside the patch. -/
def OutsidePatch (p : shatter.Patch) (edit : scene.Edit) : Prop :=
  EdgeOutside p edit.remove 0 ∨ EdgeOutside p edit.add 0

/-- The scene with the edit's fields in place (everything the edit block can write). -/
def editedScene (self : scene.Scene) (req : alloc.vec.Vec topology.Edge)
    (np : alloc.vec.Vec Std.I32) (wk : spanning_tree.Workspace) (t : spanning_tree.Tree)
    (ph : alloc.vec.Vec Std.I32) (rt : alloc.vec.Vec scene.Route) : scene.Scene :=
  { self with
    required := req
    next_phases := np
    work := wk
    tree := t
    phases := ph
    routes := rt }

/-- The scene `reform_patch` leaves on success. -/
def reformedScene (self : scene.Scene) (id : shatter.PatchId) (p : shatter.Patch)
    (dl : Std.U64) (v : Std.U64) (req : alloc.vec.Vec topology.Edge)
    (np : alloc.vec.Vec Std.I32) (wk : spanning_tree.Workspace) (t : spanning_tree.Tree)
    (ph : alloc.vec.Vec Std.I32) (rt : alloc.vec.Vec scene.Route) : scene.Scene :=
  { self with
    required := req
    next_phases := np
    work := wk
    tree := t
    phases := ph
    routes := rt
    patches := alloc.vec.Vec.set self.patches id.slot
      { p with stage := shatter.Stage.Reforming dl }
    stamp := bumped self v
    trail_revision := v }

/-- What a committed reform edit leaves, apart from the patch: a safe scene whose tree has exactly the
edited edge set, the published phases unchanged, the routes the edit's (or unchanged). -/
def ReformKept (self : scene.Scene) (edit : scene.Edit) (req : alloc.vec.Vec topology.Edge)
    (np : alloc.vec.Vec Std.I32) (wk : spanning_tree.Workspace) (t : spanning_tree.Tree)
    (ph : alloc.vec.Vec Std.I32) (rt : alloc.vec.Vec scene.Route) : Prop :=
  EditSafe (editedScene self req np wk t ph rt) ∧
  (∀ u w, parentEdge (parents t) u w ↔
    MutationEditedEdge (parents self.tree) edit.remove edit.add u w) ∧
  (edit.remove.val.length = 0 → t = self.tree ∧ wk = self.work) ∧
  ph = self.phases ∧ PhaseCopy self np ∧
  (edit.routes = none → rt = self.routes) ∧
  (∀ rs, edit.routes = some rs → allEdges rt.val = allEdges rs.val)

/-- The edit part of `reform_patch`, once the patch checks passed: `preflight_edit` on the scratch
table, then the edge edit when something is removed, then the commit. -/
def ReformGate (self : scene.Scene) (id : shatter.PatchId) (p : shatter.Patch)
    (dl : Std.U64) (edit : scene.Edit)
    (res : core.result.Result walker.Stamp topology.Error × scene.Scene) : Prop :=
  EditSafe res.2 ∧
  ((∃ np x pr req, PhaseCopy self np ∧
      PreflightOutcome { self with next_phases := np } edit (.Err x, pr) ∧
      pr = { self with next_phases := np, required := req } ∧ res = (.Err x, pr)) ∨
   (∃ np m req, PhaseCopy self np ∧
      PreflightOutcome { self with next_phases := np } edit (.Ok m,
        { self with next_phases := np, required := req }) ∧
      ((∃ x wk, edit.remove.val.length ≠ 0 ∧
          res = (.Err x, { self with next_phases := np, required := req, work := wk })) ∨
       (∃ v wk t ph rt, v.val = self.stamp.revision.val + 1 ∧ ReformKept self edit req np wk t ph rt ∧
          res = (.Ok (bumped self v), reformedScene self id p dl v req np wk t ph rt)))))

/-- After the deadline fits: the outside-the-patch check, then the edit. -/
def ReformPlaced (self : scene.Scene) (id : shatter.PatchId) (p : shatter.Patch)
    (dl : Std.U64) (edit : scene.Edit)
    (res : core.result.Result walker.Stamp topology.Error × scene.Scene) : Prop :=
  (OutsidePatch p edit ∧ res = (.Err topology.Error.InvalidTransition, self)) ∨
  (¬ OutsidePatch p edit ∧ ReformGate self id p dl edit res)

/-- A `Scattered` patch whose deadline is reached: the new deadline overflows, or is placed. -/
def ReformDue (self : scene.Scene) (id : shatter.PatchId) (p : shatter.Patch) (duration : Std.U64)
    (edit : scene.Edit) (res : core.result.Result walker.Stamp topology.Error × scene.Scene) : Prop :=
  (U64.max < self.clock.val + duration.val ∧ res = (.Err topology.Error.Overflow, self)) ∨
  (self.clock.val + duration.val ≤ U64.max ∧
    ∃ dl : Std.U64, dl.val = self.clock.val + duration.val ∧ ReformPlaced self id p dl edit res)

/-- With a valid handle: the frozen and zero-duration check, the stage check, then the deadline. -/
def ReformAtPatch (self : scene.Scene) (id : shatter.PatchId) (p : shatter.Patch)
    (duration : Std.U64) (edit : scene.Edit)
    (res : core.result.Result walker.Stamp topology.Error × scene.Scene) : Prop :=
  ((Frozen self ∨ duration.val = 0) ∧ res = (.Err topology.Error.InvalidTransition, self)) ∨
  (¬ Frozen self ∧ duration.val ≠ 0 ∧
    (¬ ∃ u : Std.U64, p.stage = shatter.Stage.Scattered u ∧ u.val ≤ self.clock.val) ∧
    res = (.Err topology.Error.InvalidTransition, self)) ∨
  (¬ Frozen self ∧ duration.val ≠ 0 ∧
    (∃ u : Std.U64, p.stage = shatter.Stage.Scattered u ∧ u.val ≤ self.clock.val) ∧
    ReformDue self id p duration edit res)

/-- `reform_patch`, check by check. -/
def ReformOutcome (self : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
    (duration : Std.U64) (edit : scene.Edit)
    (res : core.result.Result walker.Stamp topology.Error × scene.Scene) : Prop :=
  (¬ StampAccepts self stamp ∧ StampRejects self stamp res) ∨
  (StampAccepts self stamp ∧
    ((∃ e, slotVerdict self id = .Err e ∧ res = (.Err e, self)) ∨
     ∃ p, SlotOk self id p ∧ ReformAtPatch self id p duration edit res))

theorem reform_loop2_eq : scene.Scene.reform_patch_loop2 = scene.Scene.carve_loop := rfl

/-- The tail of `reform_patch` after the edge edit: commit, then the patch becomes `Reforming`. -/
theorem reform_finish (self self1 : scene.Scene) (id : shatter.PatchId) (p : shatter.Patch)
    (dl v : Std.U64) (t : spanning_tree.Tree) (w : spanning_tree.Workspace) (edit : scene.Edit)
    (req : alloc.vec.Vec topology.Edge) (np : alloc.vec.Vec Std.I32)
    (hform : self1 = { self with required := req, next_phases := np })
    (hp : self.patches.val[id.slot.val]? = some p) (hs1 : EditSafe self1)
    (htv : TreeValid self1.layout.carrier t) (hwv : WorkspaceValid w)
    (hcap : t.parents.val.length ≤ w.path.val.length)
    (hedt : ∀ u v, parentEdge (parents t) u v ↔
      MutationEditedEdge (parents self1.tree) edit.remove edit.add u v)
    (hcert : ∀ e ∈ allEdges (PfRoutes self1 edit).val,
      MutationEditedEdge (parents self1.tree) edit.remove edit.add e.u.val e.v.val)
    (hcirc : ∀ rs, edit.routes = some rs → rs.val.length = self1.layout.circles.val.length)
    (hempty : edit.remove.val.length = 0 → t = self1.tree ∧ w = self1.work)
    (hnp : PhaseCopy self np) :
    OkPost (do
      let self2 ← scene.Scene.commit_edit { self1 with tree := t, work := w } edit v
      let (p1, index_mut_back) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice shatter.Patch)
          self2.patches id.slot
      ok (core.result.Result.Ok self2.stamp,
        { self2 with
            patches := index_mut_back { p1 with stage := shatter.Stage.Reforming dl }
            trail_revision := v }) :
        Result ((core.result.Result walker.Stamp topology.Error) × scene.Scene))
      (fun res => ∃ ph rt, res = (.Ok (bumped self v),
          reformedScene self id p dl v req np w t ph rt) ∧ ReformKept self edit req np w t ph rt) := by
  obtain ⟨c2, t2, w2, cap2, rq2, ph2, rl2, edges2⟩ := hs1
  refine okPost_bind (okPost_pair (okPost_of_spec (edit_commit_post self1 t w edit v c2 htv hwv hcap
    rq2 ph2 rl2 hcirc hedt hcert))
    (okPost_of_spec (scene_commit_edit_spec { self1 with tree := t, work := w } edit v ph2
      (fun rs h => ((hcirc rs h).trans rl2.symm).le)))) ?_
  rintro s3 ⟨⟨hcp, htr, hwk⟩, ph, hphl, hphp, rt, hrl, hrt, hs3⟩
  simp only [alloc.vec.Vec.index_mut_slice_index]
  have hpat : s3.patches = self.patches := by rw [hs3, hform]; rfl
  have hl : id.slot.val < s3.patches.val.length := by
    rw [hpat]; exact (List.getElem?_eq_some_iff.mp hp).1
  refine okPost_bind (okPost_of_spec (alloc.vec.Vec.index_mut_usize_spec s3.patches id.slot hl)) ?_
  rintro ⟨p1, back⟩ ⟨hp1, hback⟩
  have hp1e : p1 = p := by
    have h1 : s3.patches.val[id.slot.val]? = some p := by rw [hpat]; exact hp
    rw [List.getElem?_eq_getElem hl] at h1
    rw [hp1]; exact Option.some.inj h1
  subst hp1e
  subst hback
  subst hform
  have hs3p : s3.phases = ph := by rw [hs3]; rfl
  have hs3r : s3.routes = rt := by rw [hs3]; rfl
  obtain ⟨hsafe, hlay, hedge, hnone, hsome, hst, hrq, hnpe, hphl2, hphp2⟩ := hcp
  refine okPost_ok ⟨ph, rt, ?_, ?_⟩
  · rw [hs3]; rfl
  · refine ⟨?_, ?_, hempty, ?_, hnp, ?_, ?_⟩
    · rw [hs3] at hsafe; exact hsafe
    · intro u v'
      rw [← htr]; exact hedge u v'
    · rw [← hs3p]
      apply alloc.vec.Vec.ext
      apply List.ext_getElem?
      intro j
      by_cases hj : j < self.phases.val.length
      · rw [hphp2 j hj]
        exact hnp.2 j hj
      · have hphl3 : s3.phases.val.length = self.phases.val.length := hphl2
        have h1 : s3.phases.val[j]? = none := List.getElem?_eq_none (by omega)
        have h2 : self.phases.val[j]? = none := List.getElem?_eq_none (by omega)
        rw [h1, h2]
    · intro hn; rw [← hs3r]; exact hnone hn
    · intro rs hrs; rw [← hs3r]; exact hsome rs hrs

theorem reform_patch_spec (self : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
    (duration : Std.U64) (edit : scene.Edit) (hs : EditSafe self) (hcap : EditCapacity self) :
    OkPost (scene.Scene.reform_patch self stamp id duration edit)
      (ReformOutcome self stamp id duration edit) := by
  classical
  unfold scene.Scene.reform_patch
  apply stamp_gate_ok
  · intro v hv hacc
    refine okPost_mono (P := fun res => (∃ e, slotVerdict self id = .Err e ∧ res = (.Err e, self)) ∨
      ∃ p, SlotOk self id p ∧ ReformAtPatch self id p duration edit res) ?_
      (fun res h => Or.inr ⟨hacc, h⟩)
    refine okPost_bind (okPost_of_spec (patch_slot_spec self id)) ?_
    intro r1 hr1
    cases r1 with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, okPost_ok_iff]
      exact Or.inl ⟨e, hr1.symm, rfl⟩
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      rcases slotVerdict_cases self id with ⟨e, he⟩ | ⟨p, hp, _⟩
      · rw [he] at hr1; simp at hr1
      · have hu : u = id.slot := by rw [hp.1] at hr1; simpa using hr1.symm.symm
        subst hu
        refine okPost_mono (P := fun res => ReformAtPatch self id p duration edit res) ?_
          (fun res h => Or.inr ⟨p, hp, h⟩)
        simp only [frozen_ite]
        split
        · rename_i hF
          rw [okPost_ok_iff]
          exact Or.inl ⟨Or.inl hF, rfl⟩
        · rename_i hF
          by_cases hd : duration = 0#u64
          · simp only [hd, ↓reduceIte]
            rw [okPost_ok_iff]
            exact Or.inl ⟨Or.inr (by simp), rfl⟩
          · simp only [hd, ↓reduceIte]
            have hd' : duration.val ≠ 0 := fun h => hd (UScalar.eq_of_val_eq (by simpa using h))
            have hl : id.slot.val < self.patches.val.length :=
              (List.getElem?_eq_some_iff.mp hp.2).1
            simp only [alloc.vec.Vec.index_slice_index]
            refine okPost_bind (okPost_of_spec (alloc.vec.Vec.index_usize_spec self.patches id.slot hl)) ?_
            intro p1 hp1
            have hpp : p1 = p := by
              have := hp.2
              rw [List.getElem?_eq_getElem hl] at this
              rw [hp1]; exact Option.some.inj this
            subst hpp
            cases hst : p1.stage with
            | Idle =>
              rw [okPost_ok_iff]
              exact Or.inr (Or.inl ⟨hF, hd', (by rintro ⟨u, hu, _⟩; rw [hst] at hu; cases hu), rfl⟩)
            | Draining =>
              rw [okPost_ok_iff]
              exact Or.inr (Or.inl ⟨hF, hd', (by rintro ⟨u, hu, _⟩; rw [hst] at hu; cases hu), rfl⟩)
            | Parked =>
              rw [okPost_ok_iff]
              exact Or.inr (Or.inl ⟨hF, hd', (by rintro ⟨u, hu, _⟩; rw [hst] at hu; cases hu), rfl⟩)
            | Hidden =>
              rw [okPost_ok_iff]
              exact Or.inr (Or.inl ⟨hF, hd', (by rintro ⟨u, hu, _⟩; rw [hst] at hu; cases hu), rfl⟩)
            | Reforming u =>
              rw [okPost_ok_iff]
              exact Or.inr (Or.inl ⟨hF, hd', (by rintro ⟨u, hu, _⟩; rw [hst] at hu; cases hu), rfl⟩)
            | Scattered u =>
              by_cases hge : self.clock ≥ u
              · have hgev : u.val ≤ self.clock.val := by simpa using hge
                simp only [hge, ↓reduceIte]
                refine okPost_mono (P := fun res => ReformDue self id p1 duration edit res) ?_
                  (fun res h => Or.inr (Or.inr ⟨hF, hd', ⟨u, hst, hgev⟩, h⟩))
                rcases u64_checked_add self.clock duration with ⟨hle, z, hz, hzv⟩ | ⟨hgt, hn⟩
                · simp only [lift, hz, Std.bind_ok, core.option.Option.ok_or]
                  refine okPost_mono (P := fun res => ReformPlaced self id p1 z edit res) ?_
                    (fun res h => Or.inr ⟨hle, z, hzv, h⟩)
                  refine okPost_bind (okPost_of_spec (reform_outside_spec self.patches edit.remove
                    id.slot p1 hp.2 false 0#usize)) ?_
                  intro o1 ho1
                  rw [reform_loop1_eq]
                  refine okPost_bind (okPost_of_spec (reform_outside_spec self.patches edit.add
                    id.slot p1 hp.2 o1 0#usize)) ?_
                  intro o2 ho2
                  by_cases hout : o2 = true
                  · simp only [hout, ↓reduceIte]
                    rw [okPost_ok_iff]
                    refine Or.inl ⟨?_, rfl⟩
                    have := ho2.mp hout
                    unfold OutsidePatch
                    rcases this with h | h
                    · rcases ho1.mp h with h' | h'
                      · simp at h'
                      · exact Or.inl h'
                    · exact Or.inr h
                  · simp only [hout, Bool.false_eq_true, ↓reduceIte]
                    have hno : ¬ OutsidePatch p1 edit := by
                      intro h
                      apply hout
                      apply ho2.mpr
                      rcases h with h | h
                      · exact Or.inl (ho1.mpr (Or.inr h))
                      · exact Or.inr h
                    refine okPost_mono (P := fun res => ReformGate self id p1 z edit res) ?_
                      (fun res h => Or.inr ⟨hno, h⟩)
                    rw [reform_loop2_eq]
                    refine okPost_bind (P := fun np : alloc.vec.Vec Std.I32 => PhaseCopy self np)
                      (okPost_mono (okPost_of_spec (carve_loop_spec self.phases self.next_phases
                        hs.2.2.2.2.2.1 0#usize (by simp))) ?_) ?_
                    · rintro np ⟨hl, hj⟩
                      exact ⟨hl, fun j hj' => by rw [hj j]; simp [hj']⟩
                    intro np hnp
                    have hs1 := editSafe_next hs np hnp.1
                    have hc1 := hs1.1
                    have hinv1 := hs1.2.2.2.2.1
                    refine okPost_bind (okPost_pair (okPost_pair
                      (scene_preflight_edit_frame { self with next_phases := np } edit hc1 hinv1)
                      (scene_preflight_edit_accepted { self with next_phases := np } edit hc1 hinv1))
                      (scene_preflight_edit_spec { self with next_phases := np } edit)) ?_
                    rintro ⟨r3, self1⟩ ⟨⟨⟨req, hself1, hreq⟩, hacc⟩, hpre⟩
                    have hf : self1 = { self with next_phases := np, required := req } := hself1
                    refine okPost_bind_eq (okPost_trivial _) ?_
                    intro cf3 hcf3 _
                    cases r3 with
                    | Err x =>
                      simp only [ok.injEq] at hcf3
                      subst hcf3
                      refine okPost_bind_eq (okPost_trivial _) ?_
                      intro r6 hr6 _
                      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                        core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hr6
                      subst hr6
                      refine okPost_ok ⟨?_, Or.inl ⟨np, x, self1, req, hnp, hpre, hf, rfl⟩⟩
                      rw [hf]
                      exact editSafe_required hs1 req hreq
                    | Ok m =>
                      simp only [ok.injEq] at hcf3
                      subst hcf3
                      obtain ⟨hlen, hmv, hrem, req', hself1', hfold, hI, hcert, hcirc⟩ := hacc m rfl
                      have hf' : self1 = { self with next_phases := np, required := req' } := hself1'
                      have hs2 : EditSafe self1 := by
                        rw [hf']
                        exact editSafe_required hs1 req' hI
                      have hpre' : PreflightOutcome { self with next_phases := np } edit
                          (.Ok m, { self with next_phases := np, required := req' }) := by
                        rw [← hf']; exact hpre
                      have hcert1 : ∀ e ∈ allEdges (PfRoutes self1 edit).val,
                          MutationEditedEdge (parents self1.tree) edit.remove edit.add e.u.val e.v.val := by
                        rw [hf']; exact hcert
                      have hcirc1 : ∀ rs, edit.routes = some rs →
                          rs.val.length = self1.layout.circles.val.length := by
                        intro rs hrs
                        have := hcirc
                        simp only [PfRoutes, hrs] at this
                        rw [hf']; exact this
                      refine okPost_bind (okPost_of_spec (core.slice.Slice.is_empty_spec edit.remove)) ?_
                      intro b1 hb1
                      by_cases hb : b1 = true
                      · simp only [hb, ↓reduceIte]
                        have h0 : edit.remove.val.length = 0 := by
                          have h0' : edit.remove.length = 0 := by rw [← hb1]; exact hb
                          simpa [Slice.length] using h0'
                        have hadd : edit.add.val.length = 0 := by omega
                        refine okPost_mono (reform_finish self self1 id p1 z v self1.tree self1.work edit req' np
                          hf' hp.2 hs2 hs2.2.1 hs2.2.2.1 hs2.2.2.2.1
                          (fun u w => (edited_edge_empty _ edit.remove edit.add h0 hadd u w).symm)
                          hcert1 hcirc1 (fun _ => ⟨rfl, rfl⟩) hnp) ?_
                        rintro res ⟨ph, rt, hres, hkept⟩
                        refine ⟨?_, Or.inr ⟨np, m, req', hnp, hpre', Or.inr ⟨v, self1.work, self1.tree, ph, rt,
                          hv, hkept, hres⟩⟩⟩
                        rw [hres]; exact hkept.1
                      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
                        have hne : edit.remove.val.length ≠ 0 := by
                          intro h0; apply hb
                          rw [hb1]; simpa [Slice.length] using h0
                        have hcap2 : self1.layout.carrier.edges.val.length ≤ self1.work.edge_capacity.val := by
                          rw [hf']; exact hcap
                        refine okPost_bind (okPost_of_spec (mutation_edit_edges_tree_valid self1.layout.carrier
                          self1.tree edit.remove edit.add self1.work hs2.1 hs2.2.1 hs2.2.2.1
                          hs2.2.2.2.1 hcap2)) ?_
                        rintro ⟨r5, t, w⟩ ⟨hwv, hpl, herr, hok⟩
                        refine okPost_bind_eq (okPost_trivial _) ?_
                        intro cf5 hcf5 _
                        cases r5 with
                        | Err e =>
                          simp only [ok.injEq] at hcf5
                          subst hcf5
                          refine okPost_bind_eq (okPost_trivial _) ?_
                          intro r6 hr6 _
                          simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                            core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hr6
                          subst hr6
                          have ht : t = self1.tree := herr e rfl
                          subst ht
                          refine okPost_ok ⟨?_, Or.inr ⟨np, m, req', hnp, hpre', Or.inl ⟨e, w, hne, ?_⟩⟩⟩
                          · exact editSafe_work hs2 w hwv hpl
                          · rw [hf']
                        | Ok u =>
                          cases u
                          simp only [ok.injEq] at hcf5
                          subst hcf5
                          obtain ⟨hroot, hlen2, hiff, hcar, htv⟩ := hok rfl
                          dsimp only at hlen2 hpl hiff htv
                          have hcapt : t.parents.val.length ≤ w.path.val.length := by
                            have := hs2.2.2.2.1
                            omega
                          refine okPost_mono (reform_finish self self1 id p1 z v t w edit req' np
                            hf' hp.2 hs2 htv hwv hcapt hiff hcert1 hcirc1
                            (fun h => absurd h hne) hnp) ?_
                          rintro res ⟨ph, rt, hres, hkept⟩
                          refine ⟨?_, Or.inr ⟨np, m, req', hnp, hpre', Or.inr ⟨v, w, t, ph, rt,
                            hv, hkept, hres⟩⟩⟩
                          rw [hres]; exact hkept.1
                · simp only [lift, hn, Std.bind_ok, core.option.Option.ok_or,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                    core.convert.FromSame.from, bind_tc_ok, okPost_ok_iff]
                  exact Or.inl ⟨hgt, rfl⟩
              · have hgev : self.clock.val < u.val := by
                  have : ¬ u.val ≤ self.clock.val := by simpa using hge
                  omega
                simp only [hge, ↓reduceIte]
                rw [okPost_ok_iff]
                exact Or.inr (Or.inl ⟨hF, hd', (by
                  rintro ⟨u', hu', h⟩; rw [hst] at hu'; cases hu'; omega), rfl⟩)
  · intro res hn hr
    exact Or.inl ⟨hn, hr⟩

end Labyrinth
