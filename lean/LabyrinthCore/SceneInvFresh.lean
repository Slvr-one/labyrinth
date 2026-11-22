module
public import LabyrinthCore.SceneDoorwayLocal
public import LabyrinthCore.SceneSafetyTick
public import LabyrinthCore.SceneSafety

/-! The scene invariant, part 2: crossings stay fresh.

`CrossHeld` is `CrossFresh` together with the record of what the crossing holds: the hold set a
crossing walker carries is the hold set of its edge's doorway. With it, a change of the published
phases that keeps every held transform's phase keeps every crossing's doorway
(`doorway_phase_local`). `crossHeld_transfer` is the one lemma every operation uses: crossings of the
new walker list come from crossings of the old one, their edges stay tree edges, the layout is the
same, and the phases agree on what the crossings hold. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- Every crossing walker's reserved corridor and hold set are those of its own tree edge's doorway
at the published phases. -/
def CrossHeld (self : scene.Scene) : Prop :=
  ∀ wk ∈ self.walkers.val, ∀ c, wk.state = walker.WalkerState.Crossing c →
    ∃ e1 d, topology.Edge.new c.source c.target = ok e1 ∧
      parentEdge (parents self.tree) e1.u.val e1.v.val ∧
      scene.Layout.doorway self.layout e1 (alloc.vec.Vec.deref self.phases)
        (alloc.vec.Vec.deref self.phases) = ok (core.result.Result.Ok d) ∧
      d.corridor = c.corridor ∧ d.holds = c.holds

theorem crossHeld_fresh {s : scene.Scene} (h : CrossHeld s) : CrossFresh s := by
  intro wk hwk c hc
  obtain ⟨e1, d, he, ht, hd, hcor, _⟩ := h wk hwk c hc
  exact ⟨e1, d, he, ht, hd, hcor⟩

/-- Every crossing of `ws'` is a crossing of `ws` with the same ends, corridor and holds. -/
def CrossSub (ws ws' : List walker.Walker) : Prop :=
  ∀ n ∈ ws', ∀ c', n.state = walker.WalkerState.Crossing c' →
    ∃ o ∈ ws, ∃ c, o.state = walker.WalkerState.Crossing c ∧ c.source = c'.source ∧
      c.target = c'.target ∧ c.corridor = c'.corridor ∧ c.holds = c'.holds

theorem crossSub_refl (ws : List walker.Walker) : CrossSub ws ws :=
  fun n hn c' hc' => ⟨n, hn, c', hc', rfl, rfl, rfl, rfl⟩

theorem crossSub_trans {a b c : List walker.Walker} (h1 : CrossSub a b) (h2 : CrossSub b c) :
    CrossSub a c := by
  intro n hn c' hc'
  obtain ⟨m, hm, cm, hcm, e1, e2, e3, e4⟩ := h2 n hn c' hc'
  obtain ⟨o, ho, co, hco, f1, f2, f3, f4⟩ := h1 m hm cm hcm
  exact ⟨o, ho, co, hco, f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4⟩

theorem relaxed_crossSub {ws ws' : List walker.Walker} (h : RelaxedList ws ws') : CrossSub ws ws' := by
  intro n hn c' hc'
  obtain ⟨i, hi, hni⟩ := List.getElem_of_mem hn
  obtain ⟨o, n', ho, hn', hr⟩ := h.2 i (by rw [← h.1]; exact hi)
  have : n' = n := by
    rw [List.getElem?_eq_getElem hi, hni] at hn'; exact (Option.some.inj hn').symm
  subst this
  rcases hr with rfl | hr
  · exact ⟨n', List.mem_of_getElem? ho, c', hc', rfl, rfl, rfl, rfl⟩
  · exact absurd hc' (hr c')

/-- A walker list whose entries are the old ones or not crossing. -/
theorem crossSub_pointwise (ws ws' : List walker.Walker) (hlen : ws'.length = ws.length)
    (h : ∀ i, i < ws.length → ∃ o n, ws[i]? = some o ∧ ws'[i]? = some n ∧
      (n = o ∨ ∀ c, n.state ≠ walker.WalkerState.Crossing c)) : CrossSub ws ws' :=
  relaxed_crossSub ⟨hlen, h⟩

/-- **Freshness transfers.** -/
theorem crossHeld_transfer (s s' : scene.Scene) (h : CrossHeld s) (hL : LayoutGeom s.layout)
    (hlay : s'.layout = s.layout) (hsub : CrossSub s.walkers.val s'.walkers.val)
    (htree : ∀ wk ∈ s.walkers.val, ∀ c, wk.state = walker.WalkerState.Crossing c →
      ∀ e1 : topology.Edge, topology.Edge.new c.source c.target = ok e1 →
      parentEdge (parents s.tree) e1.u.val e1.v.val →
      parentEdge (parents s'.tree) e1.u.val e1.v.val)
    (hph : ∀ wk ∈ s.walkers.val, ∀ c, wk.state = walker.WalkerState.Crossing c →
      ∀ x ∈ c.holds.ids.val.take c.holds.count.val, s.phases.val[x.val]? = s'.phases.val[x.val]?) :
    CrossHeld s' := by
  intro n hn c' hc'
  obtain ⟨o, ho, c, hoc, h1, h2, h3, h4⟩ := hsub n hn c' hc'
  obtain ⟨e1, d, he, ht, hd, hcor, hh⟩ := h o ho c hoc
  refine ⟨e1, d, by rw [← h1, ← h2]; exact he, htree o ho c hoc e1 he ht, ?_, by rw [hcor, h3],
    by rw [hh, h4]⟩
  rw [hlay]
  apply doorway_phase_local s.layout hL e1 _ _ d hd
  intro x hx
  rw [hh] at hx
  simpa [deref_val] using hph o ho c hoc x hx

/-! ### The invariant -/

/-- **The scene invariant.** Edit safety and the workspace's edge capacity (the preconditions of
every checked edit), the layout's geometry with a phase table covering its transforms, published
phases in `[0, TURN)`, the reservation invariant, fresh crossings with their holds, and patches
sized to the layout's cells. -/
def SceneInv (s : scene.Scene) : Prop :=
  EditSafe s ∧ EditCapacity s ∧ LayoutGeom s.layout ∧
  s.layout.transforms.val ≤ s.phases.val.length ∧ PhaseRange s ∧ ResInv s ∧ CrossHeld s ∧
  PatchRoom s

/-- The scene invariant gives `CrossFresh`: every crossing still matches the doorway it was given. -/
theorem sceneInv_fresh {s : scene.Scene} (h : SceneInv s) : CrossFresh s := crossHeld_fresh h.2.2.2.2.2.2.1

/-! ### Operations that keep everything the invariant reads -/

/-- A scene with the same fields the invariant reads. -/
theorem sceneInv_of_eq_fields {s s' : scene.Scene} (h : SceneInv s)
    (h1 : s'.layout = s.layout) (h2 : s'.tree = s.tree) (h3 : s'.work = s.work)
    (h4 : s'.routes = s.routes) (h5 : s'.required = s.required) (h6 : s'.phases = s.phases)
    (h7 : s'.next_phases = s.next_phases) (h8 : s'.holds = s.holds)
    (h9 : s'.walkers = s.walkers) (h10 : s'.patches = s.patches) : SceneInv s' := by
  obtain ⟨⟨e1, e2, e3, e4, e5, e6, e7, e8⟩, ecap, hL, htr, hpr, hres, hcr, hroom⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [EditCapacity, PhaseRange, ResInv, CrossHeld, PatchRoom, h1, h2, h3, h4, h5, h6, h7,
      h8, h9, h10] <;> assumption

theorem stamp_rejects_self {α : Type _} {self : scene.Scene} {stamp : walker.Stamp}
    {res : core.result.Result α topology.Error × scene.Scene}
    (hn : ¬ StampAccepts self stamp) (hf : StampRejects self stamp res) : res.2 = self := by
  obtain ⟨e, he⟩ := stampRejects_err hn hf
  rw [he]

theorem suspend_inv (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (h : SceneInv self) :
    OkPost (scene.Scene.suspend self stamp wall) (fun res => SceneInv res.2) := by
  refine okPost_mono (okPost_of_spec (suspend_spec self stamp wall)) ?_
  rintro res ⟨hrej, hlt, hge⟩
  by_cases hacc : StampAccepts self stamp
  · by_cases hw : wall.val < self.wall.val
    · rw [hlt hacc hw]; exact h
    · obtain ⟨v, _, hres⟩ := hge hacc (by omega)
      rw [hres]; exact h
  · rw [stamp_rejects_self hacc hrej]; exact h

theorem resume_inv (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (h : SceneInv self) :
    OkPost (scene.Scene.resume self stamp wall) (fun res => SceneInv res.2) := by
  refine okPost_mono (okPost_of_spec (resume_spec self stamp wall)) ?_
  rintro res ⟨hrej, hlt, hge⟩
  by_cases hacc : StampAccepts self stamp
  · by_cases hw : wall.val < self.wall.val
    · rw [hlt hacc hw]; exact h
    · obtain ⟨v, _, hres⟩ := hge hacc (by omega)
      rw [hres]; exact h
  · rw [stamp_rejects_self hacc hrej]; exact h

theorem request_layout_inv (self : scene.Scene) (stamp : walker.Stamp) (h : SceneInv self) :
    OkPost (scene.Scene.request_layout self stamp) (fun res => SceneInv res.2) := by
  refine okPost_mono (okPost_of_spec (request_layout_spec self stamp)) ?_
  rintro res ⟨hrej, hmax, hlt⟩
  by_cases hacc : StampAccepts self stamp
  · by_cases hm : self.latest_request.val = U64.max
    · rw [hmax hacc hm]; exact h
    · obtain ⟨v, req, _, _, hres⟩ := hlt hacc (by have := self.latest_request.hBounds; scalar_tac)
      rw [hres]; exact h
  · rw [stamp_rejects_self hacc hrej]; exact h

/-- `reject_layout` changes only the stamp, the freeze flag and the pending request. -/
theorem reject_layout_frame (self : scene.Scene) (request : Std.U64) (viewport : grid.Rect) :
    OkPost (scene.Scene.reject_layout self request viewport) (fun res =>
      res.2 = self ∨ ∃ st ia pd, res.2 = { self with stamp := st, inactive := ia, pending := pd }) := by
  unfold scene.Scene.reject_layout
  repeat (first
    | exact okPost_ok (Or.inl rfl)
    | exact okPost_ok (Or.inr ⟨_, _, _, rfl⟩)
    | exact okPost_bind (okPost_trivial _) (fun _ _ => okPost_ok (Or.inl rfl))
    | refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
    | split)

theorem reject_layout_inv (self : scene.Scene) (request : Std.U64) (viewport : grid.Rect)
    (h : SceneInv self) :
    OkPost (scene.Scene.reject_layout self request viewport) (fun res => SceneInv res.2) := by
  refine okPost_mono (reject_layout_frame self request viewport) ?_
  rintro res (hres | ⟨st, ia, pd, hres⟩) <;> rw [hres] <;> exact h

/-- `publish_layout` installs the candidate scene (with the old clock reading, the old suspension and
a reanchor), so it keeps the invariant when the candidate satisfies it; every rejection keeps the
scene. The candidate is a `Scene` value, which outside the crate only `Scene::new` and the
operations here produce. -/
theorem publish_layout_inv (self : scene.Scene) (request : Std.U64) (candidate : scene.Scene)
    (h : SceneInv self) (hc : SceneInv candidate) :
    OkPost (scene.Scene.publish_layout self request candidate) (fun res => SceneInv res.2) := by
  refine okPost_mono (okPost_of_spec (publish_layout_spec self request candidate)) ?_
  rintro res ⟨h1, h2, h3, h4, h5⟩
  by_cases hp : self.pending = some request
  · by_cases hl : self.latest_request = request
    · by_cases he : candidate.stamp.epoch = request
      · by_cases hr : candidate.stamp.revision = 0#u64
        · obtain ⟨t, r, _, _, hres⟩ := h5 hp hl he hr
          rw [hres]; exact hc
        · rw [h4 hp hl he hr]; exact h
      · rw [h3 hp hl he]; exact h
    · rw [h2 hp hl]; exact h
  · rw [h1 hp]; exact h

/-! ### `begin_crossing` -/

theorem begin_crossing_held (self : scene.Scene) (stamp : walker.Stamp) (wi target : Std.Usize)
    (duration : Std.U32) (hfresh : CrossHeld self) :
    OkPost (scene.Scene.begin_crossing self stamp wi target duration)
      (fun res => CrossHeld res.2) := by
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
      exact ⟨e1, d, by simpa [bcCrossing] using hte, htree, hdoor, rfl, rfl⟩

end Labyrinth
