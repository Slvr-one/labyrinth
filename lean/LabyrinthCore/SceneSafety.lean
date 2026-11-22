module
public import LabyrinthCore.SceneReservationRemoval
public import LabyrinthCore.SceneReservationInv
public import LabyrinthCore.SceneShatterFrame
public import LabyrinthCore.SceneGeometryDoorway

/-! Safety (S5), part 2: an accepted edit removes no edge a crossing walker is on.

`crossing_blocks_own_edge` needed two geometry premises about a crossing walker's reserved
corridor `c.corridor`: that it is the corridor the doorway of the walker's own tree edge has now, and
that it is a valid rectangle. The first is the freshness invariant `CrossFresh`: `begin_crossing`
stores the corridor of the doorway at the published phases, and the corridor depends only on the
phases of the transforms the crossing holds (`prepare_motion` refuses to move a held transform). The second follows from `LayoutGeom`, through the geometry totality theorem:
every doorway that exists has a valid corridor. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- Every crossing walker's reserved corridor is the corridor its own tree edge's doorway has at the
published phases. -/
def CrossFresh (self : scene.Scene) : Prop :=
  ∀ wk ∈ self.walkers.val, ∀ c, wk.state = walker.WalkerState.Crossing c →
    ∃ e1 d, topology.Edge.new c.source c.target = ok e1 ∧
      parentEdge (parents self.tree) e1.u.val e1.v.val ∧
      scene.Layout.doorway self.layout e1 (alloc.vec.Vec.deref self.phases)
        (alloc.vec.Vec.deref self.phases) = ok (core.result.Result.Ok d) ∧
      d.corridor = c.corridor

/-- The corridor of an existing doorway is a valid rectangle. -/
theorem doorway_corridor_valid (L : scene.Layout) (hL : LayoutGeom L) (hc : CarrierValid L.carrier)
    (edge : topology.Edge) (phases : Slice Std.I32) (hph : L.transforms.val ≤ phases.val.length)
    (d : scene.Doorway)
    (hd : scene.Layout.doorway L edge phases phases = ok (core.result.Result.Ok d)) :
    RectValid d.corridor := by
  have h := layout_doorway_spec L hL hc edge phases phases hph hph
  rw [hd] at h
  have := (spec_ok _).mp h
  obtain ⟨hok, _⟩ := this
  obtain ⟨_, hcor, _⟩ := hok d rfl
  obtain ⟨_, _, hx, hy⟩ := hcor.1
  exact ⟨hx.le, hy.le⟩

/-- Both geometry premises of `crossing_blocks_own_edge` hold on a fresh scene of valid geometry. -/
theorem crossing_blocks_fresh (self : scene.Scene) (hL : LayoutGeom self.layout)
    (hc : CarrierValid self.layout.carrier)
    (hph : self.layout.transforms.val ≤ self.phases.val.length) (hfresh : CrossFresh self)
    (wk : walker.Walker) (hw : wk ∈ self.walkers.val) (c : walker.Crossing)
    (hs : wk.state = walker.WalkerState.Crossing c) :
    ∃ e1, topology.Edge.new c.source c.target = ok e1 ∧
      OkPost (scene.Scene.check_removal self e1) (fun r =>
        r = core.result.Result.Err topology.Error.Occupied) := by
  obtain ⟨e1, d, he, htree, hd, hcor⟩ := hfresh wk hw c hs
  refine ⟨e1, he, ?_⟩
  have hvalid : RectValid d.corridor :=
    doorway_corridor_valid self.layout hL hc e1 (alloc.vec.Vec.deref self.phases)
      (by simpa [alloc.vec.Vec.deref] using hph) d hd
  exact crossing_blocks_own_edge self wk c e1 d hw hs he htree hd hcor (hcor ▸ hvalid)

/-- No removal of an edit may be a crossing walker's own edge: the check on that edge answers
`Occupied`, so a removal list that passed `check_removal` entry by entry avoids every crossing edge. -/
def AvoidsCrossings (self : scene.Scene) (remove : Slice topology.Edge) : Prop :=
  ∀ wk ∈ self.walkers.val, ∀ c, wk.state = walker.WalkerState.Crossing c →
    ∀ e1, topology.Edge.new c.source c.target = ok e1 →
      ∀ (j : Nat) (e : topology.Edge), remove.val[j]? = some e → topology.Edge.new e.u e.v ≠ ok e1

theorem removals_avoid_crossings (self : scene.Scene) (remove : Slice topology.Edge)
    (hL : LayoutGeom self.layout) (hc : CarrierValid self.layout.carrier)
    (hph : self.layout.transforms.val ≤ self.phases.val.length) (hfresh : CrossFresh self)
    (hpass : ∀ j, j < remove.val.length →
      RemovalVerdict self remove j (core.result.Result.Ok ())) :
    AvoidsCrossings self remove := by
  intro wk hw c hs e1 he1 j e hje hnew
  obtain ⟨e1', he1', hocc⟩ := crossing_blocks_fresh self hL hc hph hfresh wk hw c hs
  rw [he1] at he1'
  simp only [ok.injEq] at he1'
  subst he1'
  have hjl : j < remove.val.length := (List.getElem?_eq_some_iff.mp hje).1
  obtain ⟨e', hje', e2, he2, hrem⟩ := hpass j hjl
  rw [hje] at hje'
  cases hje'
  rw [hnew] at he2
  simp only [ok.injEq] at he2
  subst he2
  have := hocc _ hrem
  simp at this

/-- An accepted `preflight_edit` ran `check_removal` on every removal and every one passed. -/
theorem preflightOutcome_removals {self : scene.Scene} {edit : scene.Edit}
    {p : (core.result.Result Std.Usize topology.Error) × scene.Scene}
    (h : PreflightOutcome self edit p) (m : Std.Usize) (hm : p.1 = .Ok m) :
    ∀ j, j < edit.remove.val.length → RemovalVerdict self edit.remove j (core.result.Result.Ok ()) := by
  rcases h with ⟨_, rfl⟩ | ⟨_, h | ⟨hrem, _⟩⟩
  · simp at hm
  · obtain ⟨x, k, _, _, _, rfl⟩ := h
    simp at hm
  · exact hrem

/-- `check_removal` reads only the tree, the layout, the published phases and the walkers. -/
theorem removalVerdict_next (self : scene.Scene) (np : alloc.vec.Vec Std.I32)
    (req : alloc.vec.Vec topology.Edge) (remove : Slice topology.Edge) (j : Nat)
    (v : core.result.Result Unit topology.Error) :
    RemovalVerdict { self with next_phases := np, required := req } remove j v ↔
      RemovalVerdict self remove j v := Iff.rfl

/-- **Reservation safety.** In a scene whose layout has valid geometry and whose crossings are
fresh, an accepted `preflight_edit` removes no edge a crossing walker is on. Every edit operation
(`motion`, `carve`, `reform_patch`) commits only after an accepted `preflight_edit`. -/
theorem preflight_edit_safe (self : scene.Scene) (edit : scene.Edit) (hs : EditSafe self)
    (hL : LayoutGeom self.layout) (hph : self.layout.transforms.val ≤ self.phases.val.length)
    (hfresh : CrossFresh self) :
    OkPost (scene.Scene.preflight_edit self edit) (fun p =>
      (∃ m, p.1 = .Ok m) → AvoidsCrossings self edit.remove) := by
  refine okPost_mono (scene_preflight_edit_spec self edit) ?_
  rintro p hp ⟨m, hm⟩
  exact removals_avoid_crossings self edit.remove hL hs.1 hph hfresh
    (preflightOutcome_removals hp m hm)

/-- `reform_patch` removes no crossing walker's edge either: an accepted reform edit passed
`preflight_edit` on the scratch scene, which sees the same tree, walkers and published phases. -/
theorem reform_patch_safe (self : scene.Scene) (stamp : walker.Stamp) (id : shatter.PatchId)
    (duration : Std.U64) (edit : scene.Edit) (hs : EditSafe self) (hcap : EditCapacity self)
    (hL : LayoutGeom self.layout) (hph : self.layout.transforms.val ≤ self.phases.val.length)
    (hfresh : CrossFresh self) :
    OkPost (scene.Scene.reform_patch self stamp id duration edit) (fun res =>
      (∃ st, res.1 = .Ok st) → AvoidsCrossings self edit.remove) := by
  refine okPost_mono (reform_patch_spec self stamp id duration edit hs hcap) ?_
  rintro res h ⟨st, hst⟩
  have key : ∀ (np : alloc.vec.Vec Std.I32) (m : Std.Usize) (req : alloc.vec.Vec topology.Edge),
      PreflightOutcome { self with next_phases := np } edit
        (.Ok m, { self with next_phases := np, required := req }) →
      AvoidsCrossings self edit.remove := by
    intro np m req hpre
    refine removals_avoid_crossings self edit.remove hL hs.1 hph hfresh ?_
    intro j hj
    exact (removalVerdict_next self np req edit.remove j _).mp
      (by
        have := preflightOutcome_removals hpre m rfl j hj
        exact this)
  rcases h with ⟨hn, hf⟩ | ⟨hacc, h⟩
  · obtain ⟨e, he⟩ := stampRejects_err hn hf
    rw [he] at hst; simp at hst
  · rcases h with ⟨e, _, h⟩ | ⟨p, hp, h⟩
    · rw [h] at hst; simp at hst
    · rcases h with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, ⟨u, hu, hule⟩, hdue⟩
      · rw [h] at hst; simp at hst
      · rw [h] at hst; simp at hst
      · rcases hdue with ⟨_, h⟩ | ⟨hfit, dl, hdlv, hpl⟩
        · rw [h] at hst; simp at hst
        · rcases hpl with ⟨_, h⟩ | ⟨hno, hg⟩
          · rw [h] at hst; simp at hst
          · obtain ⟨hsafe, h | ⟨np, m, req, hnp, hpre, h⟩⟩ := hg
            · obtain ⟨np', x, pr, req', _, _, _, h⟩ := h
              rw [h] at hst; simp at hst
            · exact key np m req hpre

/-! ### `begin_crossing` keeps the crossings fresh -/

theorem begin_crossing_fresh (self : scene.Scene) (stamp : walker.Stamp) (wi target : Std.Usize)
    (duration : Std.U32) (hfresh : CrossFresh self) :
    OkPost (scene.Scene.begin_crossing self stamp wi target duration)
      (fun res => CrossFresh res.2) := by
  refine okPost_mono (begin_crossing_outcome self stamp wi target duration) ?_
  rintro ⟨r, s'⟩ h
  simp only at *
  rcases h with ⟨hn, hf⟩ | ⟨_, h⟩
  · have := stampFail_scene hn hf
    simp only at this
    rw [this]; exact hfresh
  · rcases h with ⟨_, h⟩ | ⟨w, _, _, h⟩ | ⟨w, _, e', _, h⟩ | ⟨w, _, _, e', _, h⟩ |
      ⟨w, e1, _, _, _, _, h⟩ | ⟨w, e1, x, _, _, _, _, h⟩ | ⟨w, e1, d, _, _, _, _, _, h⟩ |
      ⟨w, e1, d, path, lp, val, nh, hr, hadm, hedge, hdoor, _, _, _, _, _, h⟩
    all_goals try (simp only [Prod.mk.injEq] at h; rw [h.2]; exact hfresh)
    simp only [Prod.mk.injEq] at h
    rw [h.2]
    obtain ⟨hte, htree⟩ := hedge
    intro wk hwk c hc
    have hmem := List.mem_or_eq_of_mem_set (by simpa [bcAfter, alloc.vec.Vec.set_val_eq] using hwk)
    rcases hmem with hold | hnew
    · exact hfresh wk hold c hc
    · rw [hnew] at hc
      simp only [walker.WalkerState.Crossing.injEq] at hc
      subst hc
      exact ⟨e1, d, by simpa [bcCrossing] using hte, htree, hdoor, rfl⟩

end Labyrinth
