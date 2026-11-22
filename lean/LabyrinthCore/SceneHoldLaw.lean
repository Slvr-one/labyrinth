module
public import LabyrinthCore.SceneInvEdit

/-! The hold law, part 1: every hold counter equals the number of crossing-holds on it.

`ResInv` bounds each counter from below by the holds the crossing walkers carry. The exact law
`HoldEq` is the equality: `begin_crossing` adds a crossing's holds, `tick` subtracts them when the
crossing ends, and nothing else ends a crossing. Two operations rewrite walkers standing in a patch
without releasing anything (`hide_patch` hides them, the reform step of `tick` readies them), so the
law needs a companion: `PatchClear`, no crossing walker has its source or target in a patch that has
finished draining. Then the walkers those sweeps rewrite are never crossing (a crossing walker
stands in its source cell), and the counters stay exact. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- Every counter equals the number of crossing-holds on it. -/
def HoldEqL (ws : List walker.Walker) (hs : List Std.Usize) : Prop :=
  ∀ k, k < hs.length → ∃ a, hs[k]? = some a ∧ a.val = crossMult ws k

/-- No patch past draining is touched by a crossing walker. -/
def PatchClearL (ws : List walker.Walker) (ps : List shatter.Patch) : Prop :=
  ∀ p ∈ ps, p.stage ≠ shatter.Stage.Idle → p.stage ≠ shatter.Stage.Draining → ¬ Touches ws p

/-- **The hold law** of a scene: exact counters, and settled patches clear of crossings. -/
def HoldLaw (s : scene.Scene) : Prop :=
  HoldEqL s.walkers.val s.holds.val ∧ PatchClearL s.walkers.val s.patches.val

/-- The exact law gives the lower bound `ResInv` asks for. -/
theorem holdEqL_le {ws : List walker.Walker} {hs : List Std.Usize} (h : HoldEqL ws hs) :
    ∀ k, k < hs.length → ∃ a, hs[k]? = some a ∧ crossMult ws k ≤ a.val := by
  intro k hk
  obtain ⟨a, ha, he⟩ := h k hk
  exact ⟨a, ha, he.ge⟩

/-! ### Walker lists that keep every crossing -/

theorem touches_crossSub {ws ws' : List walker.Walker} (h : CrossSub ws ws') (p : shatter.Patch)
    (ht : Touches ws' p) : Touches ws p := by
  obtain ⟨n, hn, c', hc', hs⟩ := ht
  obtain ⟨o, ho, c, hc, e1, e2, _, _⟩ := h n hn c' hc'
  exact ⟨o, ho, c, hc, by rw [e1, e2]; exact hs⟩

theorem patchClear_crossSub {ws ws' : List walker.Walker} {ps : List shatter.Patch}
    (h : PatchClearL ws ps) (hs : CrossSub ws ws') : PatchClearL ws' ps :=
  fun p hp h1 h2 ht => h p hp h1 h2 (touches_crossSub hs p ht)

/-- Two walker lists that agree except on walkers crossing in neither. -/
def SameCrossings (ws ws' : List walker.Walker) : Prop :=
  ws'.length = ws.length ∧ ∀ i, i < ws.length → ∃ o n, ws[i]? = some o ∧ ws'[i]? = some n ∧
    (n = o ∨ ((∀ c, o.state ≠ walker.WalkerState.Crossing c) ∧
      ∀ c, n.state ≠ walker.WalkerState.Crossing c))

theorem sameCrossings_relaxed {ws ws' : List walker.Walker} (h : SameCrossings ws ws') :
    RelaxedList ws ws' := by
  refine ⟨h.1, fun i hi => ?_⟩
  obtain ⟨o, n, ho, hn, hr⟩ := h.2 i hi
  exact ⟨o, n, ho, hn, hr.imp id (fun h => h.2)⟩

theorem sameCrossings_symm {ws ws' : List walker.Walker} (h : SameCrossings ws ws') :
    SameCrossings ws' ws := by
  refine ⟨h.1.symm, fun i hi => ?_⟩
  obtain ⟨o, n, ho, hn, hr⟩ := h.2 i (by rw [← h.1]; exact hi)
  exact ⟨n, o, hn, ho, hr.imp (fun h => h.symm) (fun h => ⟨h.2, h.1⟩)⟩

theorem crossMult_same {ws ws' : List walker.Walker} (h : SameCrossings ws ws') (k : Nat) :
    crossMult ws' k = crossMult ws k := by
  have h1 := crossMult_relaxed ws ws' h.1 (sameCrossings_relaxed h).2 k
  have hs := sameCrossings_symm h
  have h2 := crossMult_relaxed ws' ws hs.1 (sameCrossings_relaxed hs).2 k
  omega

theorem holdEqL_same {ws ws' : List walker.Walker} {hs : List Std.Usize} (h : HoldEqL ws hs)
    (hsc : SameCrossings ws ws') : HoldEqL ws' hs := by
  intro k hk
  obtain ⟨a, ha, he⟩ := h k hk
  exact ⟨a, ha, by rw [crossMult_same hsc]; exact he⟩

/-- A sweep over walkers standing in a patch no crossing walker touches, to a state that is not a
crossing, rewrites no crossing walker. -/
theorem sweep_sameCrossings (ws : List walker.Walker) (p : shatter.Patch) (s : walker.WalkerState)
    (hs : ∀ c, s ≠ walker.WalkerState.Crossing c) (hcs : CrossAtSource ws) (ht : ¬ Touches ws p) :
    SameCrossings ws (ws.map (stateIf p s)) := by
  refine ⟨by simp, fun i hi => ⟨ws[i], stateIf p s ws[i], List.getElem?_eq_getElem hi,
    by simp [hi], ?_⟩⟩
  unfold stateIf
  split
  · rename_i hin
    right
    refine ⟨fun c hc => ht ⟨ws[i], List.getElem_mem hi, c, hc, Or.inl ?_⟩, fun c => hs c⟩
    rw [← hcs _ (List.getElem_mem hi) c hc]; exact hin
  · left; rfl

theorem crossSub_of_same {ws ws' : List walker.Walker} (h : SameCrossings ws ws') :
    CrossSub ws ws' := relaxed_crossSub (sameCrossings_relaxed h)

/-! ### Operations that keep walkers, holds and patches -/

theorem holdLaw_of_eq_fields {s s' : scene.Scene} (h : HoldLaw s) (hw : s'.walkers = s.walkers)
    (hh : s'.holds = s.holds) (hp : s'.patches = s.patches) : HoldLaw s' := by
  unfold HoldLaw; rw [hw, hh, hp]; exact h

theorem suspend_holdLaw (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (h : HoldLaw self) :
    OkPost (scene.Scene.suspend self stamp wall) (fun res => HoldLaw res.2) := by
  refine okPost_mono (okPost_of_spec (suspend_spec self stamp wall)) ?_
  rintro res ⟨hrej, hlt, hge⟩
  by_cases hacc : StampAccepts self stamp
  · by_cases hw : wall.val < self.wall.val
    · rw [hlt hacc hw]; exact h
    · obtain ⟨v, _, hres⟩ := hge hacc (by omega)
      rw [hres]; exact h
  · rw [stamp_rejects_self hacc hrej]; exact h

theorem resume_holdLaw (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (h : HoldLaw self) :
    OkPost (scene.Scene.resume self stamp wall) (fun res => HoldLaw res.2) := by
  refine okPost_mono (okPost_of_spec (resume_spec self stamp wall)) ?_
  rintro res ⟨hrej, hlt, hge⟩
  by_cases hacc : StampAccepts self stamp
  · by_cases hw : wall.val < self.wall.val
    · rw [hlt hacc hw]; exact h
    · obtain ⟨v, _, hres⟩ := hge hacc (by omega)
      rw [hres]; exact h
  · rw [stamp_rejects_self hacc hrej]; exact h

theorem request_layout_holdLaw (self : scene.Scene) (stamp : walker.Stamp) (h : HoldLaw self) :
    OkPost (scene.Scene.request_layout self stamp) (fun res => HoldLaw res.2) := by
  refine okPost_mono (okPost_of_spec (request_layout_spec self stamp)) ?_
  rintro res ⟨hrej, hmax, hlt⟩
  by_cases hacc : StampAccepts self stamp
  · by_cases hm : self.latest_request.val = U64.max
    · rw [hmax hacc hm]; exact h
    · obtain ⟨v, req, _, _, hres⟩ := hlt hacc (by have := self.latest_request.hBounds; scalar_tac)
      rw [hres]; exact h
  · rw [stamp_rejects_self hacc hrej]; exact h

theorem reject_layout_holdLaw (self : scene.Scene) (request : Std.U64) (viewport : grid.Rect)
    (h : HoldLaw self) :
    OkPost (scene.Scene.reject_layout self request viewport) (fun res => HoldLaw res.2) := by
  refine okPost_mono (reject_layout_frame self request viewport) ?_
  rintro res (hres | ⟨st, ia, pd, hres⟩) <;> rw [hres] <;> exact h

/-- `publish_layout` installs the candidate, or keeps the scene. The old walkers are terminated and
the old counters zeroed with the old scene, which is replaced whole. -/
theorem publish_layout_holdLaw (self : scene.Scene) (request : Std.U64) (candidate : scene.Scene)
    (h : HoldLaw self) (hc : HoldLaw candidate) :
    OkPost (scene.Scene.publish_layout self request candidate) (fun res => HoldLaw res.2) := by
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

/-! ### `begin_crossing` acquires exactly the holds it records -/

theorem admitted_not_patch {self : scene.Scene} {cell : Nat}
    (h : admissionVerdict self cell = .Ok ()) : ∀ p ∈ self.patches.val, ¬ PatchHas p cell := by
  intro p hp hh
  unfold admissionVerdict at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hno
        exact hno ⟨p, hp, hh⟩

theorem holdLaw_begin_crossing_success (self : scene.Scene) (w : walker.Walker)
    (wi target : Std.Usize) (duration : Std.U32) (val : Std.U64) (door : scene.Doorway)
    (path : walker.Path) (lp : walker.LocalPose) (newHolds : alloc.vec.Vec Std.Usize)
    (h : HoldLaw self) (hready : BcReady self wi duration w)
    (hadm : BcAdmitted self w target)
    (hcap : HoldsCapacity door.holds (alloc.vec.Vec.deref self.holds))
    (hadd : AddPref self.holds.val newHolds.val door.holds door.holds.count.val) :
    HoldLaw (bcAfter self w wi (bcCrossing self w wi target duration val door path lp) val
      newHolds) := by
  obtain ⟨hw, hwr, _⟩ := hready
  have hcapIn : HoldsIn door.holds self.holds.val.length := by
    have := hcap.1; simpa [alloc.vec.Vec.deref] using this
  have hcount : door.holds.count.val ≤ 4 := hcapIn.1
  unfold HoldLaw bcAfter
  simp only [alloc.vec.Vec.set_val_eq]
  have hlen : newHolds.val.length = self.holds.val.length := hadd.1
  refine ⟨?_, ?_⟩
  · intro k hk
    rw [hlen] at hk
    obtain ⟨a, b, ha, hb, hab⟩ := hadd.2 k hk
    obtain ⟨b', hb', heq⟩ := h.1 k hk
    rw [hb] at hb'; cases hb'
    refine ⟨a, ha, ?_⟩
    have hws : self.walkers.val[wi.val]? = some w := hw
    have hset := crossMult_set self.walkers.val wi.val
      (crossingWalker w (bcCrossing self w wi target duration val door path lp)) k w hws
    have h0 : walkerMult w k = 0 := by
      unfold walkerMult; rw [hwr]
    have h1 : walkerMult (crossingWalker w
        (bcCrossing self w wi target duration val door path lp)) k = holdMult door.holds k := by
      simp [walkerMult, crossingWalker, bcCrossing]
    rw [h0, h1] at hset
    have h2 := prefMult_full door.holds k hcount
    change a.val = crossMult (self.walkers.val.set wi.val
      (crossingWalker w (bcCrossing self w wi target duration val door path lp))) k
    omega
  · intro p hp h1 h2 ht
    obtain ⟨n, hn, c, hc, hs⟩ := ht
    rcases List.mem_or_eq_of_mem_set hn with hn | rfl
    · exact h.2 p hp h1 h2 ⟨n, hn, c, hc, hs⟩
    · simp only [walker.WalkerState.Crossing.injEq] at hc
      subst hc
      rcases hs with hs | hs
      · exact admitted_not_patch hadm.1 p hp hs
      · exact admitted_not_patch hadm.2 p hp hs

/-- **`begin_crossing` keeps the hold law.** -/
theorem begin_crossing_holdLaw (self : scene.Scene) (stamp : walker.Stamp) (wi target : Std.Usize)
    (duration : Std.U32) (h : HoldLaw self) :
    OkPost (scene.Scene.begin_crossing self stamp wi target duration)
      (fun res => HoldLaw res.2) := by
  refine okPost_mono (begin_crossing_outcome self stamp wi target duration) ?_
  rintro ⟨r, s'⟩ hout
  simp only
  rcases hout with ⟨hn, hf⟩ | ⟨_, hacc⟩
  · have e : s' = self := stampFail_scene hn hf
    rw [e]; exact h
  · rcases hacc with ⟨_, e⟩ | ⟨w, _, _, e⟩ | ⟨w, _, e', _, e⟩ | ⟨w, _, _, e', _, e⟩ |
      ⟨w, e1, _, _, _, _, e⟩ | ⟨w, e1, x, _, _, _, _, e⟩ | ⟨w, e1, d, _, _, _, _, _, e⟩ |
      ⟨w, e1, door, path, lp, v, nh, hr, hadm, _, _, hcap, _, _, _, hadd, e⟩ <;>
      simp only [Prod.mk.injEq] at e
    all_goals first
      | (rw [e.2]; exact h)
      | (rw [e.2]; exact holdLaw_begin_crossing_success self w wi target duration v door path lp nh
          h hr hadm hcap hadd)

/-- **`begin_crossing` keeps the scene invariant.** -/
theorem begin_crossing_inv (self : scene.Scene) (stamp : walker.Stamp) (wi target : Std.Usize)
    (duration : Std.U32) (h : SceneInv self) :
    OkPost (scene.Scene.begin_crossing self stamp wi target duration)
      (fun res => SceneInv res.2) := by
  obtain ⟨hs, hcap, hL, htr, hpr, hres, hcr, hroom⟩ := h
  have hR := begin_crossing_resinv self stamp wi target duration hres
  have hC := begin_crossing_held self stamp wi target duration hcr
  refine okPost_mono (okPost_pair (okPost_pair hR hC)
    (begin_crossing_outcome self stamp wi target duration)) ?_
  rintro ⟨r, s'⟩ ⟨⟨hR', hC'⟩, hout⟩
  simp only at hR' hC' hout ⊢
  have keep : ∀ (nh : alloc.vec.Vec Std.Usize) (ws : alloc.vec.Vec walker.Walker) (st : walker.Stamp),
      s' = { self with holds := nh, walkers := ws, stamp := st } → SceneInv s' := by
    rintro nh ws st rfl
    exact ⟨hs, hcap, hL, htr, hpr, hR', hC', hroom⟩
  rcases hout with ⟨hn, hf⟩ | ⟨_, hacc⟩
  · exact keep self.holds self.walkers self.stamp (stampFail_scene hn hf)
  · rcases hacc with ⟨_, e⟩ | ⟨w, _, _, e⟩ | ⟨w, _, e', _, e⟩ | ⟨w, _, _, e', _, e⟩ |
      ⟨w, e1, _, _, _, _, e⟩ | ⟨w, e1, x, _, _, _, _, e⟩ | ⟨w, e1, d, _, _, _, _, _, e⟩ |
      ⟨w, e1, door, path, lp, v, nh, hr, hadm, _, _, hcap, _, _, _, hadd, e⟩ <;>
      simp only [Prod.mk.injEq] at e
    all_goals first
      | exact keep self.holds self.walkers self.stamp e.2
      | exact keep _ _ _ e.2

end Labyrinth
