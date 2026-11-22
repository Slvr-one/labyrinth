module
public import LabyrinthCore.SceneReservationCrossing
public import LabyrinthCore.SceneShatterDrain
public import LabyrinthCore.SceneEditSafe

/-! Reservations (S5), part 5: the reservation invariant and what keeps it.

`ResInv` says, of the walker list and the holds table:
* every crossing walker has `elapsed ≤ duration`, a well-formed holds record whose ids index the
  holds table, and stands in its source cell;
* every holds counter is at least the number of crossing walkers holding it (with multiplicity).

The first clause makes `duration - elapsed` safe in `tick`; the second makes the decrement of a
held counter safe (it is never `0` for an id a crossing holds). `begin_crossing` keeps it. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- How many times a walker, if crossing, holds counter `k`. -/
def walkerMult (w : walker.Walker) (k : Nat) : Nat :=
  match w.state with
  | walker.WalkerState.Crossing c => holdMult c.holds k
  | _ => 0

/-- How many crossing-holds of counter `k` the walkers carry in total. -/
def crossMult (l : List walker.Walker) (k : Nat) : Nat := (l.map (walkerMult · k)).sum

/-- The reservation invariant, on a walker list and a holds table. -/
def ResInvL (ws : List walker.Walker) (hs : List Std.Usize) : Prop :=
  (∀ w ∈ ws, ∀ c, w.state = walker.WalkerState.Crossing c →
    c.elapsed.val ≤ c.duration.val ∧ HoldsIn c.holds hs.length ∧ w.cell = c.source) ∧
  (∀ k, k < hs.length → ∃ a, hs[k]? = some a ∧ crossMult ws k ≤ a.val)

/-- The reservation invariant of a scene. -/
def ResInv (s : scene.Scene) : Prop := ResInvL s.walkers.val s.holds.val

theorem walkerMult_le_crossMult {l : List walker.Walker} {w : walker.Walker} (h : w ∈ l)
    (k : Nat) : walkerMult w k ≤ crossMult l k := by
  unfold crossMult
  exact List.le_sum_of_mem (List.mem_map_of_mem h)

theorem walkerMult_notCrossing (w : walker.Walker) (k : Nat)
    (h : ∀ c, w.state ≠ walker.WalkerState.Crossing c) : walkerMult w k = 0 := by
  unfold walkerMult
  cases hs : w.state with
  | Crossing c => exact absurd hs (h c)
  | _ => rfl

theorem crossMult_set (l : List walker.Walker) (i : Nat) (w' : walker.Walker) (k : Nat)
    (o : walker.Walker) (ho : l[i]? = some o) :
    crossMult (l.set i w') k + walkerMult o k = crossMult l k + walkerMult w' k := by
  induction l generalizing i with
  | nil => simp at ho
  | cons a t ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ho
      subst ho
      simp only [List.set_cons_zero, crossMult, List.map_cons, List.sum_cons]
      omega
    | succ j =>
      simp only [List.getElem?_cons_succ] at ho
      have := ih j ho
      simp only [List.set_cons_succ, crossMult, List.map_cons, List.sum_cons] at this ⊢
      omega

/-- Replacing walkers by walkers that are equal or not crossing never raises the count. -/
theorem crossMult_relaxed (ws ws' : List walker.Walker) (hlen : ws'.length = ws.length)
    (h : ∀ i, i < ws.length → ∃ o n, ws[i]? = some o ∧ ws'[i]? = some n ∧
      (n = o ∨ ∀ c, n.state ≠ walker.WalkerState.Crossing c)) (k : Nat) :
    crossMult ws' k ≤ crossMult ws k := by
  induction ws generalizing ws' with
  | nil =>
    have : ws' = [] := List.length_eq_zero_iff.mp hlen
    subst this; simp [crossMult]
  | cons a t ih =>
    cases ws' with
    | nil => simp at hlen
    | cons b t' =>
      have hlen' : t'.length = t.length := by simpa using hlen
      obtain ⟨o, n, h0, h1, h2⟩ := h 0 (by simp)
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0 h1
      subst h0 h1
      have ih' := ih t' hlen' (fun i hi => by
        obtain ⟨o, n, h0, h1, h2⟩ := h (i + 1) (by simpa using hi)
        exact ⟨o, n, by simpa using h0, by simpa using h1, h2⟩)
      simp only [crossMult, List.map_cons, List.sum_cons] at ih' ⊢
      have : walkerMult b k ≤ walkerMult a k := by
        rcases h2 with h2 | h2
        · rw [h2]
        · rw [walkerMult_notCrossing b k h2]; exact Nat.zero_le _
      omega

/-- Walkers equal or not crossing, pointwise; the holds table untouched: the invariant survives. -/
theorem resInvL_relaxed (ws ws' : List walker.Walker) (hs : List Std.Usize)
    (hinv : ResInvL ws hs) (hlen : ws'.length = ws.length)
    (h : ∀ i, i < ws.length → ∃ o n, ws[i]? = some o ∧ ws'[i]? = some n ∧
      (n = o ∨ ∀ c, n.state ≠ walker.WalkerState.Crossing c)) : ResInvL ws' hs := by
  refine ⟨?_, ?_⟩
  · intro n hn c hc
    obtain ⟨i, hi, hni⟩ := List.getElem_of_mem hn
    have hiw : i < ws.length := by omega
    obtain ⟨o, n', ho, hn', hr⟩ := h i hiw
    have hn'n : n' = n := by
      rw [List.getElem?_eq_getElem hi, hni] at hn'; exact (Option.some.inj hn').symm
    rw [hn'n] at hr
    rcases hr with hr | hr
    · subst hr
      exact hinv.1 _ (List.mem_of_getElem? ho) c hc
    · exact absurd hc (hr c)
  · intro k hk
    obtain ⟨a, ha, hle⟩ := hinv.2 k hk
    exact ⟨a, ha, le_trans (crossMult_relaxed ws ws' hlen h k) hle⟩

/-- The walker with a crossing installed. -/
def crossingWalker (w : walker.Walker) (c : walker.Crossing) : walker.Walker :=
  { w with state := walker.WalkerState.Crossing c }

/-- A successful `begin_crossing` keeps the invariant. -/
theorem resInv_begin_crossing_success (self : scene.Scene) (w : walker.Walker) (wi target : Std.Usize)
    (duration : Std.U32) (val : Std.U64) (door : scene.Doorway) (path : walker.Path)
    (lp : walker.LocalPose) (newHolds : alloc.vec.Vec Std.Usize) (hinv : ResInv self)
    (hready : BcReady self wi duration w)
    (hcap : HoldsCapacity door.holds (alloc.vec.Vec.deref self.holds))
    (hadd : AddPref self.holds.val newHolds.val door.holds door.holds.count.val) :
    ResInv (bcAfter self w wi (bcCrossing self w wi target duration val door path lp) val
      newHolds) := by
  obtain ⟨hw, hwr, _⟩ := hready
  have hcapIn : HoldsIn door.holds self.holds.val.length := by
    have := hcap.1; simpa [alloc.vec.Vec.deref] using this
  have hcount : door.holds.count.val ≤ 4 := hcapIn.1
  unfold ResInv bcAfter
  simp only [alloc.vec.Vec.set_val_eq]
  have hlen : newHolds.val.length = self.holds.val.length := hadd.1
  refine ⟨?_, ?_⟩
  · intro x hx c hc
    rw [hlen]
    rcases List.mem_or_eq_of_mem_set hx with hx | rfl
    · exact hinv.1 x hx c hc
    · simp only [walker.WalkerState.Crossing.injEq] at hc
      subst hc
      exact ⟨by simp [bcCrossing], hcapIn, rfl⟩
  · intro k hk
    rw [hlen] at hk
    obtain ⟨a, b, ha, hb, hab⟩ := hadd.2 k hk
    obtain ⟨b', hb', hle⟩ := hinv.2 k hk
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
    change crossMult (self.walkers.val.set wi.val
      (crossingWalker w (bcCrossing self w wi target duration val door path lp))) k ≤ a.val
    omega

/-- `begin_crossing` keeps the reservation invariant (every rejection returns the scene itself). -/
theorem begin_crossing_resinv (self : scene.Scene) (stamp : walker.Stamp) (wi target : Std.Usize)
    (duration : Std.U32) (hinv : ResInv self) :
    OkPost (scene.Scene.begin_crossing self stamp wi target duration) (fun res => ResInv res.2) := by
  refine okPost_mono (begin_crossing_outcome self stamp wi target duration) ?_
  rintro ⟨r, s'⟩ hout
  simp only
  rcases hout with ⟨hn, hf⟩ | ⟨_, hacc⟩
  · have h : s' = self := stampFail_scene hn hf
    rw [h]; exact hinv
  · rcases hacc with ⟨_, h⟩ | ⟨w, _, _, h⟩ | ⟨w, _, e', _, h⟩ | ⟨w, _, _, e', _, h⟩ |
      ⟨w, e1, _, _, _, _, h⟩ | ⟨w, e1, x, _, _, _, _, h⟩ | ⟨w, e1, d, _, _, _, _, _, h⟩ |
      ⟨w, e1, door, path, lp, v, nh, hr, _, _, _, hcap, _, _, _, hadd, h⟩ <;>
      simp only [Prod.mk.injEq] at h
    all_goals first
      | (rw [h.2]; exact hinv)
      | (rw [h.2]; exact resInv_begin_crossing_success self w wi target duration v door path lp nh
          hinv hr hcap hadd)

end Labyrinth
