module
public import LabyrinthCore.SceneReservation
public import LabyrinthCore.ScenePreflight

/-! Reservations (S5), part 4: `Scene::check_removal` answers `Occupied` exactly when the corridor
of the doorway being removed meets the corridor some crossing walker reserved. Both corridors are
closed rectangles and `Rect::intersects` is the usual closed-interval overlap test on both axes.

`check_removal` itself returns, in order: `InvalidTransition` for a non-tree edge, the doorway's own
error, `Occupied`, or success. It never changes the scene. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- Two closed rectangles share a point. -/
def RectMeet (a b : grid.Rect) : Prop :=
  a.min.x.val ≤ b.max.x.val ∧ b.min.x.val ≤ a.max.x.val ∧
  a.min.y.val ≤ b.max.y.val ∧ b.min.y.val ≤ a.max.y.val

/-- A rectangle whose corners are ordered. -/
def RectValid (r : grid.Rect) : Prop :=
  r.min.x.val ≤ r.max.x.val ∧ r.min.y.val ≤ r.max.y.val

theorem rectMeet_self {r : grid.Rect} (h : RectValid r) : RectMeet r r :=
  ⟨h.1, h.1, h.2, h.2⟩

theorem rect_intersects_spec (a b : grid.Rect) :
    grid.Rect.intersects a b ⦃ r => (r = true ↔ RectMeet a b) ⦄ := by
  unfold grid.Rect.intersects
  have e1 := IScalar.le_equiv a.min.x b.max.x
  have e2 := IScalar.le_equiv b.min.x a.max.x
  have e3 := IScalar.le_equiv a.min.y b.max.y
  have e4 := IScalar.le_equiv b.min.y a.max.y
  unfold RectMeet
  rw [← e1, ← e2, ← e3, ← e4]
  by_cases h1 : a.min.x ≤ b.max.x <;> by_cases h2 : b.min.x ≤ a.max.x <;>
    by_cases h3 : a.min.y ≤ b.max.y <;> by_cases h4 : b.min.y ≤ a.max.y <;>
    simp [h1, h2, h3, h4, spec_ok]

/-- A crossing walker's corridor meets `corridor`. -/
def OccupiedBy (walkers : List walker.Walker) (corridor : grid.Rect) : Prop :=
  ∃ wk ∈ walkers, ∃ c, wk.state = walker.WalkerState.Crossing c ∧ RectMeet corridor c.corridor

/-- The walker scan reports `true` exactly when it started `true` or some walker from the start
index on is crossing in a corridor that meets the removed one. -/
theorem removal_loop_spec (v : alloc.vec.Vec walker.Walker) (removed : scene.Doorway)
    (occ0 : Bool) (i0 : Std.Usize) :
    scene.Scene.check_removal_loop v removed occ0 i0 ⦃ r =>
      (r = true ↔ occ0 = true ∨ ∃ j, i0.val ≤ j ∧ ∃ wk c, v.val[j]? = some wk ∧
        wk.state = walker.WalkerState.Crossing c ∧ RectMeet removed.corridor c.corridor) ⦄ := by
  unfold scene.Scene.check_removal_loop
  refine loop.spec_decr_nat (fun x : scene.Doorway × Bool × Std.Usize => v.length - x.2.2.val)
    (fun x : scene.Doorway × Bool × Std.Usize =>
      x.1 = removed ∧
      ((x.2.1 = true ∨ ∃ j, x.2.2.val ≤ j ∧ ∃ wk c, v.val[j]? = some wk ∧
        wk.state = walker.WalkerState.Crossing c ∧ RectMeet removed.corridor c.corridor) ↔
      (occ0 = true ∨ ∃ j, i0.val ≤ j ∧ ∃ wk c, v.val[j]? = some wk ∧
        wk.state = walker.WalkerState.Crossing c ∧ RectMeet removed.corridor c.corridor)))
    (fun r : Bool => (r = true ↔ occ0 = true ∨ ∃ j, i0.val ≤ j ∧ ∃ wk c, v.val[j]? = some wk ∧
      wk.state = walker.WalkerState.Crossing c ∧ RectMeet removed.corridor c.corridor))
    _ _ ?_ ⟨rfl, Iff.rfl⟩
  rintro ⟨rem, occ, i⟩ ⟨hrem, hinv⟩
  simp only at hrem hinv
  subst hrem
  unfold scene.Scene.check_removal_loop.body
  by_cases hlt : i < alloc.vec.Vec.len v
  · simp only [hlt, ↓reduceIte]
    have hl : i.val < v.val.length := hlt
    have hvl : v.length = v.val.length := rfl
    by_cases ho : occ = true
    · simp only [ho, ↓reduceIte, spec_ok]
      exact iff_of_true trivial (hinv.mp (Or.inl ho))
    · simp only [ho, Bool.false_eq_true, ↓reduceIte]
      have hocc : occ = false := by simpa using ho
      simp only [alloc.vec.Vec.index_slice_index]
      apply spec_bind (alloc.vec.Vec.index_usize_spec v i hl)
      intro wk hwk
      have hwks : v.val[i.val]? = some wk := by
        rw [List.getElem?_eq_getElem hl, hwk]
      have hm : ∀ st : walker.WalkerState, (match st with
          | walker.WalkerState.Ready => (ok (rem, false) : Result (scene.Doorway × Bool))
          | walker.WalkerState.Crossing crossing => do
            let occupied2 ← grid.Rect.intersects rem.corridor crossing.corridor
            ok (rem, occupied2)
          | walker.WalkerState.Parked => ok (rem, false)
          | walker.WalkerState.Hidden => ok (rem, false)
          | walker.WalkerState.Terminated => ok (rem, false)) ⦃ p =>
            p.1 = rem ∧ (p.2 = true ↔
              ∃ c, st = walker.WalkerState.Crossing c ∧ RectMeet rem.corridor c.corridor) ⦄ := by
        intro st
        cases st with
        | Crossing c =>
          apply spec_bind (rect_intersects_spec rem.corridor c.corridor)
          intro o2 ho2
          rw [spec_ok]
          refine ⟨rfl, ?_⟩
          rw [ho2]
          constructor
          · intro h; exact ⟨c, rfl, h⟩
          · rintro ⟨c', hc', h⟩
            cases hc'; exact h
        | Ready => rw [spec_ok]; exact ⟨rfl, by simp⟩
        | Parked => rw [spec_ok]; exact ⟨rfl, by simp⟩
        | Hidden => rw [spec_ok]; exact ⟨rfl, by simp⟩
        | Terminated => rw [spec_ok]; exact ⟨rfl, by simp⟩
      apply spec_bind (hm wk.state)
      rintro ⟨rem1, occ1⟩ ⟨hrem1, hocc1⟩
      simp only at hrem1 hocc1
      subst hrem1
      apply spec_bind (usize_succ_spec i (by have := v.property; scalar_tac))
      intro i2 hi2
      rw [spec_ok]
      have hi2v : i2.val = i.val + 1 := hi2
      refine ⟨⟨rfl, ?_⟩, by show v.length - i2.val < v.length - i.val; omega⟩
      simp only [hi2v]
      rw [← hinv]
      simp only [hocc, Bool.false_eq_true, false_or, hocc1]
      constructor
      · rintro (⟨c, hc, hm'⟩ | ⟨j, hj, wk', c, hq, hs', hm'⟩)
        · exact ⟨i.val, le_refl _, wk, c, hwks, hc, hm'⟩
        · exact ⟨j, by omega, wk', c, hq, hs', hm'⟩
      · rintro ⟨j, hj, wk', c, hq, hs', hm'⟩
        by_cases hji : j = i.val
        · subst hji
          left
          rw [hwks] at hq
          cases hq
          exact ⟨c, hs', hm'⟩
        · right; exact ⟨j, by omega, wk', c, hq, hs', hm'⟩
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hl : ¬ i.val < v.val.length := hlt
    rw [← hinv]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨j, hj, wk, c, hq, _⟩)
      · exact h
      · exfalso
        have := (List.getElem?_eq_some_iff.mp hq).1
        omega

/-- `check_removal`, exactly: a non-tree edge is `InvalidTransition`; a tree edge gets the doorway's
error, or `Occupied` precisely when a crossing walker's corridor meets the doorway's, else success.
-/
theorem check_removal_exact (self : scene.Scene) (edge : topology.Edge) :
    OkPost (scene.Scene.check_removal self edge) (fun r =>
      (¬ parentEdge (parents self.tree) edge.u.val edge.v.val →
        r = core.result.Result.Err topology.Error.InvalidTransition) ∧
      (parentEdge (parents self.tree) edge.u.val edge.v.val →
        (∃ x, scene.Layout.doorway self.layout edge (alloc.vec.Vec.deref self.phases)
            (alloc.vec.Vec.deref self.phases) = ok (core.result.Result.Err x) ∧
          r = core.result.Result.Err x) ∨
        (∃ d, scene.Layout.doorway self.layout edge (alloc.vec.Vec.deref self.phases)
            (alloc.vec.Vec.deref self.phases) = ok (core.result.Result.Ok d) ∧
          (r = core.result.Result.Err topology.Error.Occupied ↔
            OccupiedBy self.walkers.val d.corridor) ∧
          (r = core.result.Result.Ok () ↔ ¬ OccupiedBy self.walkers.val d.corridor)))) := by
  refine okPost_mono (scene_check_removal_spec self edge) ?_
  intro r ⟨h1, h2⟩
  refine ⟨h1, fun hp => ?_⟩
  rcases h2 hp with h | ⟨d, b, hd, hl, hr⟩
  · exact Or.inl h
  · refine Or.inr ⟨d, hd, ?_⟩
    have hspec := removal_loop_spec self.walkers d false 0#usize
    rw [hl] at hspec
    have hb := (spec_ok b).mp hspec
    have hocc : b = true ↔ OccupiedBy self.walkers.val d.corridor := by
      rw [hb]
      constructor
      · rintro (h | ⟨j, _, wk, c, hq, hs, hm⟩)
        · simp at h
        · exact ⟨wk, List.mem_of_getElem? hq, c, hs, hm⟩
      · rintro ⟨wk, hmem, c, hs, hm⟩
        obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hmem
        exact Or.inr ⟨j, by simp, wk, c, by rw [List.getElem?_eq_getElem hj, hjw], hs, hm⟩
    by_cases hbt : b = true
    · subst hr
      simp only [hbt, ↓reduceIte]
      exact ⟨⟨fun _ => hocc.mp hbt, fun _ => trivial⟩, ⟨fun h => by simp at h, fun h => absurd (hocc.mp hbt) h⟩⟩
    · have hnb : ¬ OccupiedBy self.walkers.val d.corridor := fun h => hbt (hocc.mpr h)
      subst hr
      simp only [hbt, Bool.false_eq_true, ↓reduceIte]
      exact ⟨⟨fun h => by simp at h, fun h => absurd h hnb⟩, ⟨fun _ => hnb, fun _ => trivial⟩⟩

/-- A crossing walker whose corridor meets the doorway being removed blocks the removal. -/
theorem crossing_blocks_removal (self : scene.Scene) (edge : topology.Edge) (wk : walker.Walker)
    (c : walker.Crossing) (d : scene.Doorway)
    (hw : wk ∈ self.walkers.val) (hs : wk.state = walker.WalkerState.Crossing c)
    (htree : parentEdge (parents self.tree) edge.u.val edge.v.val)
    (hd : scene.Layout.doorway self.layout edge (alloc.vec.Vec.deref self.phases)
      (alloc.vec.Vec.deref self.phases) = ok (core.result.Result.Ok d))
    (hm : RectMeet d.corridor c.corridor) :
    OkPost (scene.Scene.check_removal self edge) (fun r =>
      r = core.result.Result.Err topology.Error.Occupied) := by
  refine okPost_mono (check_removal_exact self edge) ?_
  intro r ⟨_, h2⟩
  rcases h2 htree with ⟨x, hx, _⟩ | ⟨d', hd', hocc, _⟩
  · rw [hd] at hx; simp at hx
  · rw [hd] at hd'
    simp only [ok.injEq, core.result.Result.Ok.injEq] at hd'
    subst hd'
    exact hocc.mpr ⟨wk, hw, c, hs, hm⟩

/-- A crossing walker whose reserved corridor is still the (valid) corridor of its own tree edge
blocks the removal of that edge. -/
theorem crossing_blocks_own_edge (self : scene.Scene) (wk : walker.Walker) (c : walker.Crossing)
    (e1 : topology.Edge) (d : scene.Doorway)
    (hw : wk ∈ self.walkers.val) (hs : wk.state = walker.WalkerState.Crossing c)
    (_he : topology.Edge.new c.source c.target = ok e1)
    (htree : parentEdge (parents self.tree) e1.u.val e1.v.val)
    (hd : scene.Layout.doorway self.layout e1 (alloc.vec.Vec.deref self.phases)
      (alloc.vec.Vec.deref self.phases) = ok (core.result.Result.Ok d))
    (hfresh : d.corridor = c.corridor) (hvalid : RectValid c.corridor) :
    OkPost (scene.Scene.check_removal self e1) (fun r =>
      r = core.result.Result.Err topology.Error.Occupied) :=
  crossing_blocks_removal self e1 wk c d hw hs htree hd (by rw [hfresh]; exact rectMeet_self hvalid)

end Labyrinth
