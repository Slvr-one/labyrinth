module
public import LabyrinthCore.SceneGeometryCordic
public import LabyrinthCore.SceneGeometryArc

/-! Geometry totality (S8), arc bounds. `polar::bounds` projects the arc start and every sampled
angle (the sixteen multiples of 256 that lie in the arc, plus the start and the end) at the inner
and outer radius, tracks the running minimum and maximum corner, and expands the result by the
margin. Every projected point stays within its radius of a center inside the coordinate limit, so
all tracked coordinates stay within twice the coordinate limit; the angle arithmetic stays below
`2 * TURN`, so the loops never fail, and the only remaining failures are the expansion's own
(`InvalidGeometry`, and `Overflow` only for a margin or coordinates outside the validated ranges). -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Labyrinth

/-- A point within twice the coordinate limit on both axes: the range of every tracked corner,
which is a projected point (within the radius of a center inside the limit). -/
def BoundsPointOk (p : grid.Point) : Prop :=
  -2000000 ≤ p.x.val ∧ p.x.val ≤ 2000000 ∧ -2000000 ≤ p.y.val ∧ p.y.val ≤ 2000000

/-- A projected point is within twice the coordinate limit on both axes: it is within the radius
(at most the coordinate limit) of a center that is itself within the limit. -/
theorem polar_point_near (center : grid.Point) (radius angle : Std.I32) (hc : PointOk center)
    (hr : -1000000 ≤ radius.val ∧ radius.val ≤ 1000000) :
    polar.point center radius angle ⦃ p => BoundsPointOk p ⦄ := by
  apply spec_mono (polar_point_spec center radius angle hc hr)
  rintro p ⟨hx, hy⟩
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hc
  have hrad : |radius.val| ≤ 1000000 := by rw [abs_le]; omega
  rw [abs_le] at hx hy
  unfold BoundsPointOk
  omega

/-- The inner scan of `bounds` (the two radii of one angle) keeps both corners within twice the
coordinate limit: each projected point is within that range, so the minimum and maximum are too,
and the counter stays at most 2. -/
theorem polar_bounds_loop0_loop0_spec (center : grid.Point) (inner outer angle : Std.I32)
    (first first1 : grid.Point) (r : Std.I32) (hc : PointOk center)
    (hi : 0 ≤ inner.val ∧ inner.val ≤ 1000000) (ho : 0 ≤ outer.val ∧ outer.val ≤ 1000000)
    (hf : BoundsPointOk first) (hf1 : BoundsPointOk first1) (hr : 0 ≤ r.val ∧ r.val ≤ 2) :
    polar.bounds_loop0_loop0 center inner outer first first1 angle r ⦃ p =>
      BoundsPointOk p.1 ∧ BoundsPointOk p.2 ⦄ := by
  unfold polar.bounds_loop0_loop0
  apply loop.spec_decr_nat
    (fun state : grid.Point × grid.Point × Std.I32 => (2 - state.2.2.val).toNat)
    (fun state : grid.Point × grid.Point × Std.I32 =>
      BoundsPointOk state.1 ∧ BoundsPointOk state.2.1 ∧ 0 ≤ state.2.2.val ∧ state.2.2.val ≤ 2)
    _
  · rintro ⟨f, f1, k⟩ ⟨hfk, hf1k, hk1, hk2⟩
    dsimp only at hfk hf1k hk1 hk2 ⊢
    unfold polar.bounds_loop0_loop0.body
    simp only [lift, Std.bind_ok]
    by_cases hk : k < 2#i32
    · simp only [hk, ite_true]
      have hk' : k.val < 2 := by scalar_tac
      have hrad : (if k = 0#i32 then ok inner else ok outer) ⦃ q =>
          0 ≤ q.val ∧ q.val ≤ 1000000 ⦄ := by
        split_ifs
        · simp only [spec_ok]; exact hi
        · simp only [spec_ok]; exact ho
      apply spec_bind hrad
      intro rad hrd
      apply spec_bind (polar_point_near center rad angle hc ⟨by omega, hrd.2⟩)
      intro p hp
      step as ⟨r1, hr1⟩
      unfold BoundsPointOk at hfk hf1k hp ⊢
      dsimp only
      simp only [core.cmp.impls.OrdI32.min_val, core.cmp.impls.OrdI32.max_val]
      omega
    · simp only [hk, ite_false, spec_ok]
      exact ⟨hfk, hf1k⟩
  · exact ⟨hf, hf1, hr.1, hr.2⟩

/-- The outer scan of `bounds` keeps both corners within twice the coordinate limit for an arc
whose start is an angle in `[0, TURN)` and whose length is at most one turn: each sampled angle
(`arc.start`, `normalize(start + length)`, or a multiple of 256 below `TURN`) is a valid argument of
`Arc::contains`, and the inner scan preserves the corners. -/
theorem polar_bounds_loop0_spec (center : grid.Point) (inner outer angle i : Std.I32)
    (first first1 : grid.Point) (i1 : Std.I32) (hc : PointOk center)
    (hi : 0 ≤ inner.val ∧ inner.val ≤ 1000000) (ho : 0 ≤ outer.val ∧ outer.val ≤ 1000000)
    (hang : 0 ≤ angle.val ∧ angle.val < 4096) (hlen : 0 ≤ i.val ∧ i.val ≤ 4096)
    (hf : BoundsPointOk first) (hf1 : BoundsPointOk first1) (hk : 0 ≤ i1.val ∧ i1.val ≤ 18) :
    polar.bounds_loop0 center inner outer angle i first first1 i1 ⦃ p =>
      BoundsPointOk p.1 ∧ BoundsPointOk p.2 ⦄ := by
  unfold polar.bounds_loop0
  apply loop.spec_decr_nat
    (fun state : grid.Point × grid.Point × Std.I32 => (18 - state.2.2.val).toNat)
    (fun state : grid.Point × grid.Point × Std.I32 =>
      BoundsPointOk state.1 ∧ BoundsPointOk state.2.1 ∧ 0 ≤ state.2.2.val ∧ state.2.2.val ≤ 18)
    _
  · rintro ⟨f, f1, k⟩ ⟨hfk, hf1k, hk1, hk2⟩
    dsimp only at hfk hf1k hk1 hk2 ⊢
    unfold polar.bounds_loop0.body
    by_cases hlt : k < 18#i32
    · simp only [hlt, ite_true]
      have hk' : k.val < 18 := by scalar_tac
      have hang1 : (if k = 16#i32 then ok angle
          else if k = 17#i32 then do
            let i2 ← angle + i
            polar.normalize i2
          else k * 256#i32) ⦃ a => 0 ≤ a.val ∧ a.val < 4096 ⦄ := by
        split_ifs with h16 h17
        · simp only [spec_ok]; exact hang
        · step as ⟨i2, hi2⟩
          step as ⟨a, ha1, ha2, ha3⟩
          exact ⟨ha1, ha2⟩
        · have h16' : k.val ≠ 16 := by intro h; apply h16; scalar_tac
          have h17' : k.val ≠ 17 := by intro h; apply h17; scalar_tac
          step as ⟨a, ha⟩
          omega
      apply spec_bind hang1
      intro angle1 ha1
      apply spec_bind (polar_arc_contains_spec { start := angle, length := i } angle1
        (by unfold ArcBnd; dsimp only; omega) (by omega))
      intro b hb
      by_cases hbt : b = true
      · simp only [hbt, ite_true]
        apply spec_bind (polar_bounds_loop0_loop0_spec center inner outer angle1 f f1 0#i32 hc hi ho
          hfk hf1k (by simp))
        rintro ⟨p, p1⟩ ⟨hp, hp1⟩
        step as ⟨i2, hi2⟩
        exact ⟨hp, hp1, by omega, by omega, by omega⟩
      · simp only [hbt, Bool.false_eq_true, ite_false]
        step as ⟨i2, hi2⟩
        exact ⟨hfk, hf1k, by omega, by omega, by omega⟩
    · simp only [hlt, ite_false, spec_ok]
      exact ⟨hfk, hf1k⟩
  · exact ⟨hf, hf1, hk.1, hk.2⟩

/-- `bounds` never fails except through the final expansion: for a center inside the coordinate
limit, inner and outer radii in `[0, 10^6]` and an arc with bounded fields, the tracked corner box
is valid input for `Rect::expand`. The returned rectangle is valid whenever the result is `Ok`, and
every error is `InvalidGeometry` or `Overflow`; for a margin of at most `10^9` (the validators
bound it by the coordinate limit) the corners stay within `10^9`, so only `InvalidGeometry`
remains. -/
@[step]
theorem polar_bounds_spec (center : grid.Point) (inner outer : Std.I32) (arc : polar.Arc)
    (margin : Std.I32) (hc : PointOk center) (hi : 0 ≤ inner.val ∧ inner.val ≤ 1000000)
    (ho : 0 ≤ outer.val ∧ outer.val ≤ 1000000) (ha : ArcBnd arc) :
    polar.bounds center inner outer arc margin ⦃ r =>
      (∀ e, r = .Ok e → RectOk e) ∧
      (∀ e, r = .Err e → e = .InvalidGeometry ∨ e = .Overflow) ∧
      (margin.val ≤ 1000000000 → ∀ e, r = .Err e → e = .InvalidGeometry) ⦄ := by
  unfold polar.bounds
  obtain ⟨hs0, hs1, hl0, hl1⟩ := ha
  apply spec_bind (polar_point_near center inner arc.start hc ⟨by omega, hi.2⟩)
  intro first hfirst
  apply spec_bind (polar_bounds_loop0_spec center inner outer arc.start arc.length first first
    0#i32 hc hi ho ⟨hs0, hs1⟩ ⟨hl0, hl1⟩ hfirst hfirst (by simp))
  rintro ⟨p, p1⟩ ⟨hp, hp1⟩
  dsimp only at hp hp1
  apply spec_mono (grid_rect_expand_spec { min := p, max := p1 } margin)
  rintro x ⟨h1, h2, h3, h4⟩
  refine ⟨fun e he => (h1 e he).2.2.2.2.2, h3, ?_⟩
  intro hm e he
  obtain ⟨a1, a2, a3, a4⟩ := hp
  obtain ⟨b1, b2, b3, b4⟩ := hp1
  exact h4 (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
    (by dsimp only; omega) hm e he

end Labyrinth
