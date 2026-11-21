module
public import LabyrinthCore.SceneGeometryBounds
public import LabyrinthCore.SceneGeometryCircle
import all Aeneas.Std.Scalar.CheckedOps.Add
import all Aeneas.Std.Scalar.CheckedOps.Sub
import all Aeneas.Std.Scalar.EqOrd

/-! Geometry totality (S8), disk tests: `Rect::touches_disk` computes the squared distance from a
center to a rectangle in `i64`. Within the coordinate limit the squares cannot overflow, so the
test returns and decides exactly the distance comparison. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

/-- `i32::clamp` on ordered bounds computes `max lo (min x hi)`. -/
theorem i32_clamp_val (x lo hi : Std.I32) (h : lo.val ≤ hi.val) :
    core.cmp.impls.OrdI32.clamp x lo hi ⦃ r => r.val = max lo.val (min x.val hi.val) ⦄ := by
  unfold core.cmp.impls.OrdI32.clamp IScalar.clamp
  have hm : massert (lo.val ≤ hi.val) = ok () := (massert_ok _).mpr h
  rw [hm]
  split_ifs with h1 h2 <;> simp only [bind_tc_ok, Std.bind_ok, spec_ok] <;> omega

/-- Squared distance from `center` to the rectangle, on the integers. -/
def diskDist2 (r : grid.Rect) (c : grid.Point) : Int :=
  (c.x.val - max r.min.x.val (min c.x.val r.max.x.val)) ^ 2 +
  (c.y.val - max r.min.y.val (min c.y.val r.max.y.val)) ^ 2

/-- Within the coordinate limit (a valid rectangle and a center within twice the limit) the squared
distance is at most `2 * (3 * COORD_LIMIT)^2`, far below `i64::MAX`. -/
theorem diskDist2_bound (r : grid.Rect) (c : grid.Point) (hr : RectOk r) (hc : BoundsPointOk c) :
    0 ≤ diskDist2 r c ∧ diskDist2 r c ≤ 18000000000000 := by
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩, h1, h2⟩ := hr
  obtain ⟨c1, c2, c3, c4⟩ := hc
  unfold diskDist2
  have hx : -3000000 ≤ c.x.val - max r.min.x.val (min c.x.val r.max.x.val) ∧
      c.x.val - max r.min.x.val (min c.x.val r.max.x.val) ≤ 3000000 := by omega
  have hy : -3000000 ≤ c.y.val - max r.min.y.val (min c.y.val r.max.y.val) ∧
      c.y.val - max r.min.y.val (min c.y.val r.max.y.val) ≤ 3000000 := by omega
  constructor
  · positivity
  · nlinarith [hx.1, hx.2, hy.1, hy.2]

theorem grid_rect_touches_disk_spec (r : grid.Rect) (c : grid.Point) (radius : Std.I32)
    (hr : RectOk r) (hc : BoundsPointOk c) :
    grid.Rect.touches_disk r c radius ⦃ b =>
      (b = true ↔ diskDist2 r c ≤ (radius.val : Int) ^ 2) ⦄ := by
  have hord1 : r.min.x.val ≤ r.max.x.val := by have := hr.2.2.1; omega
  have hord2 : r.min.y.val ≤ r.max.y.val := by have := hr.2.2.2; omega
  unfold grid.Rect.touches_disk
  step with i32_clamp_val as ⟨x, hx⟩
  step with i32_clamp_val as ⟨y, hy⟩
  have hb := diskDist2_bound r c hr hc
  have hxv : (c.x.val - x.val) = c.x.val - max r.min.x.val (min c.x.val r.max.x.val) := by rw [hx]
  have hyv : (c.y.val - y.val) = c.y.val - max r.min.y.val (min c.y.val r.max.y.val) := by rw [hy]
  have hxb : -3000000 ≤ c.x.val - x.val ∧ c.x.val - x.val ≤ 3000000 := by
    have := hr.1.1; have := hr.1.2.1; have := hr.2.1.1; have := hr.2.1.2.1; have := hc.1; have := hc.2.1
    rw [hx]; omega
  have hyb : -3000000 ≤ c.y.val - y.val ∧ c.y.val - y.val ≤ 3000000 := by
    have := hr.1.2.2.1; have := hr.1.2.2.2; have := hr.2.1.2.2.1; have := hr.2.1.2.2.2
    have := hc.2.2.1; have := hc.2.2.2
    rw [hy]; omega
  have hI : (I64.max : Int) = 9223372036854775807 ∧ (I64.min : Int) = -9223372036854775808 := by
    simp [I64.max, I64.min, IScalar.max, IScalar.min, IScalarTy.numBits, I64.numBits]
  obtain ⟨hI1, hI2⟩ := hI
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨dx, hdx⟩
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  step as ⟨dy, hdy⟩
  have hdx' : dx.val = c.x.val - max r.min.x.val (min c.x.val r.max.x.val) := by
    rw [hdx, hi, hi1, hx]
  have hdy' : dy.val = c.y.val - max r.min.y.val (min c.y.val r.max.y.val) := by
    rw [hdy, hi2, hi3, hy]
  have hdx2 : dx.val * dx.val = (c.x.val - max r.min.x.val (min c.x.val r.max.x.val)) ^ 2 := by
    rw [hdx']; ring
  have hdy2 : dy.val * dy.val = (c.y.val - max r.min.y.val (min c.y.val r.max.y.val)) ^ 2 := by
    rw [hdy']; ring
  have hsum : dx.val * dx.val + dy.val * dy.val = diskDist2 r c := by
    rw [hdx2, hdy2]; rfl
  have hsq0 : 0 ≤ dx.val * dx.val := mul_self_nonneg _
  have hsq1 : 0 ≤ dy.val * dy.val := mul_self_nonneg _
  have hle : dx.val * dx.val + dy.val * dy.val ≤ 18000000000000 := by rw [hsum]; exact hb.2
  have hrb := radius.hBounds
  have hrr1 : 0 ≤ radius.val * radius.val := mul_self_nonneg _
  have hrr2 : radius.val * radius.val ≤ 4611686018427387904 := by
    simp only [I32.min, I32.max, IScalar.min, IScalar.max, IScalarTy.numBits, I32.numBits] at hrb
    norm_num at hrb
    nlinarith [hrb.1, hrb.2]
  step as ⟨i4, h4⟩
  step as ⟨i5, h5⟩
  step as ⟨i6, h6⟩
  step as ⟨i7, h7⟩
  step as ⟨i8, h8⟩
  step as ⟨i9, h9⟩
  simp only [spec_ok, decide_eq_true_eq]
  have hk6 : i6.val = diskDist2 r c := by rw [h6, h4, h5, hsum]
  have hk9 : i9.val = (radius.val : Int) ^ 2 := by rw [h9, h7, h8]; ring
  generalize diskDist2 r c = D at *
  generalize (radius.val : Int) ^ 2 = R at *
  constructor <;> intro h <;> scalar_tac

/-- `Rect::touches_disk` returns for every valid rectangle and every center within twice the
coordinate limit (so for every circle center the validators accept), and every radius. -/
theorem grid_rect_touches_disk_total (r : grid.Rect) (c : grid.Point) (radius : Std.I32)
    (hr : RectOk r) (hc : BoundsPointOk c) :
    ∃ b, grid.Rect.touches_disk r c radius = ok b ∧ (b = true ↔ diskDist2 r c ≤ (radius.val : Int) ^ 2) :=
  spec_exists_ok (grid_rect_touches_disk_spec r c radius hr hc)

end Labyrinth
