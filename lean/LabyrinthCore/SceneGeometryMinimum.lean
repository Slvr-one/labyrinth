module
public import LabyrinthCore.SceneGeometryDisk
public import LabyrinthCore.SceneGeometryDoorway
import all Aeneas.Std.Scalar.CheckedOps.Add
import all Aeneas.Std.Scalar.CheckedOps.Sub
import all Aeneas.Std.Scalar.EqOrd

/-! Geometry totality (S8), the doorway's angular minimum: `Layout::doorway` computes
`minimum = ceil(2 * margin * TURN / radius)` in `i64` and narrows it with `as i32`, which wraps
instead of failing. When the radius is at least `4 * margin` (`Circle::new` enforces
`center_radius >= 4 * margin`) the quotient lies in `[1, 2048]`, so the narrowing is exact. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

/-- The quotient in `[1, 2048]` once the radius is at least four margins. -/
theorem doorway_minimum_arith (m r : Int) (hm : 0 < m) (hr : 4 * m ≤ r) :
    1 ≤ (2 * m * 4096 + r - 1) / r ∧ (2 * m * 4096 + r - 1) / r ≤ 2048 := by
  have hr0 : 0 < r := by omega
  constructor
  · rw [Int.le_ediv_iff_mul_le hr0]; nlinarith
  · have : (2 * m * 4096 + r - 1) / r < 2049 := by
      rw [Int.ediv_lt_iff_lt_mul hr0]; nlinarith
    omega

/-- The narrowing in `Layout::doorway`: for two in-range pose radii and a center radius of at
least four margins, `minimum` is the exact quotient, between 1 and 2048. -/
theorem doorway_minimum_exact (margin from_radius to_radius center_radius : Std.I32)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000) (hfloor : 4 * margin.val ≤ center_radius.val)
    (hcr : center_radius.val ≤ 1000000) (hf : 0 ≤ from_radius.val ∧ from_radius.val ≤ 1000000)
    (ht : 0 ≤ to_radius.val ∧ to_radius.val ≤ 1000000) :
    (do
      let i2 ← lift (core.cmp.impls.OrdI32.min from_radius to_radius)
      let radius ← lift (core.cmp.impls.OrdI32.max i2 center_radius)
      let i3 ← lift (core.convert.num.FromI64I32.from margin)
      let i4 ← i3 * 2#i64
      let i5 ← lift (core.convert.num.FromI64I32.from polar.TURN)
      let i6 ← i4 * i5
      let i7 ← lift (core.convert.num.FromI64I32.from radius)
      let i8 ← i6 + i7
      let i9 ← i8 - 1#i64
      let i10 ← lift (core.convert.num.FromI64I32.from radius)
      let i11 ← i9 / i10
      lift (IScalar.cast .I32 i11)) ⦃ minimum =>
      ∃ radius : Int, 4 * margin.val ≤ radius ∧ radius ≤ 1000000 ∧
        minimum.val = (2 * margin.val * 4096 + radius - 1) / radius ∧
        1 ≤ minimum.val ∧ minimum.val ≤ 2048 ⦄ := by
  have ht4 := turn_val
  step as ⟨i2, hi2⟩
  step as ⟨radius, hrad⟩
  have hrad' : 4 * margin.val ≤ radius.val ∧ radius.val ≤ 1000000 := by
    rw [hrad, core.cmp.impls.OrdI32.max_val, hi2, core.cmp.impls.OrdI32.min_val]
    constructor <;> omega
  step as ⟨i3, hi3⟩
  step as ⟨i4, hi4⟩
  step as ⟨i5, hi5⟩
  step as ⟨i6, hi6⟩
  step as ⟨i7, hi7⟩
  step as ⟨i8, hi8⟩
  step as ⟨i9, hi9⟩
  step as ⟨i10, hi10⟩
  step as ⟨i11, hi11⟩
  have hnum := doorway_minimum_arith margin.val radius.val hm.1 hrad'.1
  have hq : i11.val = (2 * margin.val * 4096 + radius.val - 1) / radius.val := by
    have hr0 : 0 < radius.val := by omega
    rw [hi11, hi9, hi8, hi6, hi4, hi3, hi5, hi7, hi10, ht4, Int.tdiv_eq_ediv_of_nonneg (by nlinarith)]
    congr 1; ring
  step as ⟨mn, hmn⟩
  exact ⟨radius.val, hrad'.1, hrad'.2, by rw [hmn, hq], by rw [hmn, hq]; exact hnum.1,
    by rw [hmn, hq]; exact hnum.2⟩

end Labyrinth
