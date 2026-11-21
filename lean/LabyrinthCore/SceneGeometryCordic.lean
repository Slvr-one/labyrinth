module
public import LabyrinthCore.SceneGeometryBase
import all Aeneas.Std.Scalar.EqOrd

/-! Geometry totality (S8), unit vectors. `polar::unit_vector` runs a 31-step CORDIC rotation in
Q30 fixed point on `i64`. The rotation starts from a vector of magnitude below `2^30`, and every
iteration replaces each coordinate by a sum of two coordinates of the previous iteration (one of
them shifted right), so after `i` iterations both coordinates are bounded by `2^30 * 2^i`; with at
most 31 iterations they stay below `2^61`, far from the `i64` limit. The residual angle starts
below `2^30` (a local angle below one quadrant, shifted by 20) and moves by one table entry (at
most `2^29`) per iteration. The final clamp to `±SCALE` makes the returned unit vector bounded by
`2^30` for every `i32` angle, and `polar::point` then scales it by a radius bounded by the
coordinate limit, so the displacement of the projected point never exceeds the radius. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Labyrinth

/-! ### Constants and the arctangent table -/

/-- `SCALE = 1 << 30` is the Q30 representation of one. -/
@[step]
theorem polar_scale_spec : polar.SCALE ⦃ r => r.val = 1073741824 ⦄ := by
  unfold polar.SCALE
  apply spec_mono (I64.ShiftLeft_IScalar_spec 1#i64 30#i32 (by simp) (by simp))
  intro r hr
  rw [hr.1]
  simp [Int.bmod, I64.size, I64.numBits, Int.shiftLeft_eq]

/-- The gain constant that seeds `x` for a nonzero local angle. -/
theorem cordic_gain_val : polar.CORDIC_GAIN.val = 652032874 := by
  simp [polar.CORDIC_GAIN]

/-- Every entry of the arctangent table is at most `2^29` in magnitude. -/
theorem cordic_atan_mem (a : Std.I64) (h : a ∈ polar.ATAN.val) :
    -536870912 ≤ a.val ∧ a.val ≤ 536870912 := by
  unfold polar.ATAN at h
  simp [Array.make] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> simp

/-- The arctangent table has 31 entries. -/
theorem cordic_atan_len : polar.ATAN.length = 31 := by
  simp [polar.ATAN]

/-- The slice view of the arctangent table has length 31. -/
theorem cordic_atan_slice_len : (Slice.len (Array.to_slice polar.ATAN)).val = 31 := by
  simp [Array.to_slice, cordic_atan_len]

/-- Indexing the arctangent table below 31 succeeds and returns an entry of magnitude at most
`2^29`. -/
@[step]
theorem polar_atan_index_spec (i : Std.Usize) (hi : i.val < 31) :
    polar.ATAN.index_usize i ⦃ a => -536870912 ≤ a.val ∧ a.val ≤ 536870912 ⦄ := by
  apply spec_mono (Array.index_usize_spec polar.ATAN i (by rw [cordic_atan_len]; exact hi))
  intro a ha
  rw [ha]
  exact cordic_atan_mem _ (List.getElem_mem _)

/-! ### Arithmetic helpers -/

/-- Powers of two up to `2^31` are at most `2^31`. -/
theorem cordic_pow_le (k : Nat) (h : k ≤ 31) : (2 : Int) ^ k ≤ 2147483648 := by
  have : (2 : Int) ^ k ≤ 2 ^ 31 := pow_le_pow_right₀ (by norm_num) h
  simpa using this

/-- An arithmetic right shift never increases the magnitude: it is a floor division by `2^k`. -/
theorem cordic_shift_abs (m : Int) (k : Nat) (B : Int) (h : |m| ≤ B) :
    -B ≤ m >>> k ∧ m >>> k ≤ B := by
  rw [Int.shiftRight_eq_div_pow]
  push_cast
  have hd : (0 : Int) < 2 ^ k := by positivity
  have h1 : (1 : Int) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  rcases abs_le.mp h with ⟨hl, hu⟩
  by_cases hm : 0 ≤ m
  · have h2 : 0 ≤ m / 2 ^ k := Int.ediv_nonneg hm (le_of_lt hd)
    have h3 : m / 2 ^ k ≤ m := Int.ediv_le_self _ hm
    omega
  · have hm' : m ≤ 0 := by omega
    have h2 : m / 2 ^ k ≤ 0 := by
      have := Int.ediv_le_ediv hd hm'
      simpa using this
    have h3 : m ≤ m / 2 ^ k := by
      apply (Int.le_ediv_iff_mul_le hd).mpr
      nlinarith
    omega

/-- Truncating division by `2^30` of a product with a factor of magnitude at most `2^30` does not
exceed the other factor in magnitude. -/
theorem cordic_tdiv_abs (r u : Int) (hu : |u| ≤ 1073741824) :
    |Int.tdiv (r * u) 1073741824| ≤ |r| := by
  have hu' : u.natAbs ≤ 1073741824 := by
    have := Int.abs_eq_natAbs u
    omega
  have h1 : (Int.tdiv (r * u) 1073741824).natAbs ≤ r.natAbs := by
    rw [Int.natAbs_tdiv, Int.natAbs_mul]
    show (r.natAbs * u.natAbs) / (1073741824 : Int).natAbs ≤ r.natAbs
    have hn : (1073741824 : Int).natAbs = 1073741824 := rfl
    rw [hn]
    apply Nat.div_le_of_le_mul
    have := Nat.mul_le_mul_left r.natAbs hu'
    linarith
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  exact_mod_cast h1

/-- The product of a radius with a factor of magnitude at most `2^30` is bounded by the radius
times `2^30`. -/
theorem cordic_mul_abs (r u : Int) (hu : |u| ≤ 1073741824) :
    -(|r| * 1073741824) ≤ r * u ∧ r * u ≤ |r| * 1073741824 := by
  have h := abs_mul r u
  have h2 : |r| * |u| ≤ |r| * 1073741824 := mul_le_mul_of_nonneg_left hu (abs_nonneg r)
  have h3 := abs_le.mp (show |r * u| ≤ |r| * 1073741824 by rw [h]; exact h2)
  exact h3

/-- The quotient `(radius * unit) / SCALE` computed by `point` is at most the radius in
magnitude. -/
theorem cordic_quot_bound (r u i1 i3 sc : Int) (hi1 : i1 = r * u) (hsc : sc = 1073741824)
    (hi3 : i3 = i1.tdiv sc) (hu : |u| ≤ 1073741824) : |i3| ≤ |r| := by
  rw [hi3, hi1, hsc]; exact cordic_tdiv_abs _ _ hu

/-- `i64::clamp` returns exactly when the bounds are ordered, and then lands in them. -/
@[step]
theorem cordic_i64_clamp_spec (x lo hi : Std.I64) (h : lo.val ≤ hi.val) :
    core.cmp.impls.OrdI64.clamp x lo hi ⦃ r => lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
      (lo.val ≤ x.val → x.val ≤ hi.val → r = x) ⦄ := by
  unfold core.cmp.impls.OrdI64.clamp IScalar.clamp
  have hm : massert (lo.val ≤ hi.val) = ok () := (massert_ok _).mpr h
  rw [hm]
  split_ifs with h1 h2 <;> simp only [bind_tc_ok, Std.bind_ok, spec_ok] <;>
    refine ⟨?_, ?_, ?_⟩ <;> intros <;> first | omega | rfl | trivial

/-! ### The rotation loop -/

/-- The loop invariant after `i` iterations: both coordinates are within `2^30 * 2^i`, the residual
within `2^30 * (i + 1)`, and `i ≤ 31`. -/
def cordic_inv (x y r : Std.I64) (i : Std.Usize) : Prop :=
  |x.val| ≤ 1073741824 * 2 ^ i.val ∧ |y.val| ≤ 1073741824 * 2 ^ i.val ∧
    |r.val| ≤ 1073741824 * (i.val + 1) ∧ i.val ≤ 31

/-- One iteration (or the exit test) preserves the invariant, strictly decreases the number of
remaining iterations, and every exit leaves coordinates of magnitude at most `2^61`. -/
theorem polar_unit_vector_loop_body_spec (l : Std.I32) (x y r : Std.I64) (i : Std.Usize)
    (h : cordic_inv x y r i) :
    polar.unit_vector_loop.body l x y r i ⦃ res =>
      match res with
      | .done p => |p.1.val| ≤ 2305843009213693952 ∧ |p.2.val| ≤ 2305843009213693952
      | .cont s => cordic_inv s.1 s.2.1 s.2.2.1 s.2.2.2 ∧ 31 - s.2.2.2.val < 31 - i.val ⦄ := by
  unfold polar.unit_vector_loop.body
  obtain ⟨hx, hy, hr, hi⟩ := h
  have hp := cordic_pow_le i.val hi
  have hp1 : (0:Int) < 2 ^ i.val := by positivity
  by_cases hl : (l != 0#i32) = true
  · simp only [hl, ite_true, lift, Std.bind_ok]
    by_cases hlt : i < Slice.len (Array.to_slice polar.ATAN)
    · have hlt' : i.val < 31 := by
        have := cordic_atan_slice_len
        have h2 : i.val < (Slice.len (Array.to_slice polar.ATAN)).val := by scalar_tac
        omega
      simp only [hlt, ite_true]
      have hpow : (2:Int) ^ (i.val + 1) = 2 * 2 ^ i.val := by ring
      have hp2 := cordic_pow_le (i.val + 1) (by omega)
      obtain ⟨hs1, hs2⟩ := cordic_shift_abs x.val i.val _ hx
      obtain ⟨hs3, hs4⟩ := cordic_shift_abs y.val i.val _ hy
      have hxb := abs_le.mp hx
      have hyb := abs_le.mp hy
      have hrb := abs_le.mp hr
      have hfin : ∀ (x1 y1 r1 : Std.I64) (i2 : Std.Usize), i2.val = i.val + 1 →
          -(2 * (1073741824 * 2 ^ i.val)) ≤ x1.val → x1.val ≤ 2 * (1073741824 * 2 ^ i.val) →
          -(2 * (1073741824 * 2 ^ i.val)) ≤ y1.val → y1.val ≤ 2 * (1073741824 * 2 ^ i.val) →
          -(1073741824 * (i.val + 2)) ≤ r1.val → r1.val ≤ 1073741824 * (i.val + 2) →
          cordic_inv x1 y1 r1 i2 ∧ 31 - i2.val < 31 - i.val := by
        intro x1 y1 r1 i2 h2 a1 a2 a3 a4 a5 a6
        unfold cordic_inv
        rw [h2, hpow]
        simp only [abs_le]
        omega
      by_cases hr0 : r ≥ 0#i64
      · have hr0' : 0 ≤ r.val := by scalar_tac
        simp only [hr0, ite_true]
        step*
      · have hr0' : r.val < 0 := by scalar_tac
        simp only [hr0, ite_false]
        step*
    · simp only [hlt, ite_false, spec_ok]
      have hlt' : ¬ i.val < 31 := by
        intro hc
        apply hlt
        have := cordic_atan_slice_len
        scalar_tac
      have hxb := abs_le.mp hx
      have hyb := abs_le.mp hy
      constructor <;> rw [abs_le] <;> omega
  · have hl' : (l != 0#i32) = false := Bool.eq_false_iff.mpr hl
    simp only [hl', Bool.false_eq_true, ↓reduceIte, spec_ok]
    have hxb := abs_le.mp hx
    have hyb := abs_le.mp hy
    constructor <;> rw [abs_le] <;> omega

/-- The rotation loop returns, for every state satisfying the invariant: coordinates within
`2^30 * 2^i`, residual within `2^30 * (i + 1)` and `i ≤ 31`. Each iteration at most doubles the
larger coordinate (a coordinate plus a right-shifted copy of the other), the residual moves by one
table entry of magnitude at most `2^29`, and the loop ends once `i` reaches the 31 table entries,
so the loop never overflows an `i64` shift, addition or subtraction, never indexes past the table,
and returns coordinates of magnitude at most `2^61`. -/
theorem polar_unit_vector_loop_spec (l : Std.I32) (x y r : Std.I64) (i : Std.Usize)
    (hx : |x.val| ≤ 1073741824 * 2 ^ i.val) (hy : |y.val| ≤ 1073741824 * 2 ^ i.val)
    (hr : |r.val| ≤ 1073741824 * (i.val + 1)) (hi : i.val ≤ 31) :
    polar.unit_vector_loop l x y r i ⦃ p =>
      |p.1.val| ≤ 2305843009213693952 ∧ |p.2.val| ≤ 2305843009213693952 ⦄ := by
  unfold polar.unit_vector_loop
  apply loop.spec_decr_nat
    (fun state : Std.I64 × Std.I64 × Std.I64 × Std.Usize => 31 - state.2.2.2.val)
    (fun state : Std.I64 × Std.I64 × Std.I64 × Std.Usize =>
      cordic_inv state.1 state.2.1 state.2.2.1 state.2.2.2)
    _
  · rintro ⟨x1, y1, r1, i1⟩ hinv
    dsimp only at hinv ⊢
    refine spec_mono (polar_unit_vector_loop_body_spec l x1 y1 r1 i1 hinv) ?_
    intro res hres
    cases res <;> exact hres
  · exact ⟨hx, hy, hr, hi⟩

/-! ### `unit_vector` and `point` -/

/-- Multiplying a local angle below one quadrant by `2^20` is exact in `i64`. -/
theorem cordic_shl20 (v : Std.I64) (h0 : 0 ≤ v.val) (h1 : v.val < 1024) :
    (v <<< 20#i32) ⦃ z => z.val = v.val * 1048576 ⦄ := by
  apply spec_mono (I64.ShiftLeft_IScalar_spec v 20#i32 (by simp) (by simp))
  intro z hz
  rw [hz.1]
  simp only [Int.shiftLeft_eq, I64.size, I64.numBits]
  have : (20#i32).toNat = 20 := by simp [IScalar.toNat]
  rw [this]
  rw [Int.bmod_eq_of_le] <;> simp <;> omega

/-- `unit_vector` is total on every `i32` angle (`normalize` reduces it modulo `TURN`, the quadrant
`angle / 1024` and the local angle `angle % 1024` use the positive constant divisor `1024`, and the
rotation loop stays within `i64` as shown above), and its clamped components are bounded by `SCALE`
in magnitude; the quadrant negations are therefore safe because no component is `i64::MIN`. -/
@[step]
theorem polar_unit_vector_spec (angle : Std.I32) :
    polar.unit_vector angle ⦃ p => -1073741824 ≤ p.1.val ∧ p.1.val ≤ 1073741824 ∧
      -1073741824 ≤ p.2.val ∧ p.2.val ≤ 1073741824 ⦄ := by
  unfold polar.unit_vector
  step as ⟨angle1, h0, h1, h2⟩
  step as ⟨i, hi⟩
  have hi' : i.val = 1024 := by rw [hi, turn_val]; decide
  step as ⟨quadrant, hq⟩
  step as ⟨loc, hloc⟩
  have hloc' : loc.val = angle1.val % 1024 := by
    rw [hloc, hi', Int.tmod_eq_emod_of_nonneg h0]
  have hlr : 0 ≤ loc.val ∧ loc.val < 1024 := by omega
  have hxs : (if loc = 0#i32 then polar.SCALE else ok polar.CORDIC_GAIN)
      ⦃ x => x.val = 1073741824 ∨ x.val = 652032874 ⦄ := by
    split_ifs
    · apply spec_mono polar_scale_spec
      intro r hr; omega
    · simp only [spec_ok]; right; exact cordic_gain_val
  apply spec_bind hxs
  intro x hx
  simp only [lift, Std.bind_ok]
  have hfrom := core.convert.num.FromI64I32.from_val_eq loc
  apply spec_bind (cordic_shl20 (core.convert.num.FromI64I32.from loc) (by rw [hfrom]; omega)
    (by rw [hfrom]; omega))
  intro residual hres
  rw [hfrom] at hres
  have h0u : (0#usize).val = 0 := by simp
  have h0y : (0#i64).val = 0 := by simp
  have hx0 : |x.val| ≤ 1073741824 * 2 ^ (0#usize).val := by
    rw [h0u, abs_le]; simp only [pow_zero]; omega
  have hy0 : |(0#i64).val| ≤ 1073741824 * 2 ^ (0#usize).val := by
    rw [h0u, h0y]; simp
  have hr0 : |residual.val| ≤ 1073741824 * ((0#usize).val + 1) := by
    rw [h0u, abs_le]; omega
  apply spec_bind (polar_unit_vector_loop_spec loc x 0#i64 residual 0#usize hx0 hy0 hr0
    (by rw [h0u]; omega))
  rintro ⟨x1, y⟩ ⟨hx1, hy1⟩
  step as ⟨sc, hsc⟩
  step as ⟨nsc, hnsc⟩
  step as ⟨x2, hx2⟩
  step as ⟨nsc2, hnsc2⟩
  step as ⟨y1, hy1'⟩
  have hbx : -1073741824 ≤ x2.val ∧ x2.val ≤ 1073741824 := by omega
  have hby : -1073741824 ≤ y1.val ∧ y1.val ≤ 1073741824 := by omega
  split
  · simp only [spec_ok]; omega
  · step as ⟨i5, hi5⟩
    omega
  · step as ⟨i5, hi5⟩
    step as ⟨i6, hi6⟩
    omega
  · step as ⟨i5, hi5⟩
    omega

/-- `point` is total for a center inside the coordinate limit and a radius within the coordinate
limit (the validator rejects every other radius): `radius * x` is at most `10^6 * 2^30` in
magnitude, so the `i64` product and the division by `SCALE` do not fail, the truncated quotient is
at most the radius in magnitude, the narrowing cast to `i32` is exact, and the coordinate addition
stays within `i32`. The projected point lies within the radius of the center on both axes. -/
@[step]
theorem polar_point_spec (center : grid.Point) (radius angle : Std.I32)
    (hc : PointOk center) (hr : -1000000 ≤ radius.val ∧ radius.val ≤ 1000000) :
    polar.point center radius angle ⦃ p =>
      |p.x.val - center.x.val| ≤ |radius.val| ∧ |p.y.val - center.y.val| ≤ |radius.val| ⦄ := by
  unfold polar.point
  apply spec_bind (polar_unit_vector_spec angle)
  rintro ⟨ux, uy⟩ ⟨hux1, hux2, huy1, huy2⟩
  dsimp only at hux1 hux2 huy1 huy2
  simp only [lift, Std.bind_ok]
  obtain ⟨hcx1, hcx2, hcy1, hcy2⟩ := hc
  have hux : |ux.val| ≤ 1073741824 := by rw [abs_le]; omega
  have huy : |uy.val| ≤ 1073741824 := by rw [abs_le]; omega
  have hrad : |radius.val| ≤ 1000000 := by rw [abs_le]; omega
  have hfrom := core.convert.num.FromI64I32.from_val_eq radius
  have hmx := cordic_mul_abs radius.val ux.val hux
  have hmy := cordic_mul_abs radius.val uy.val huy
  have hrb : |radius.val| * 1073741824 ≤ 1000000 * 1073741824 := by
    exact mul_le_mul_of_nonneg_right hrad (by norm_num)
  step as ⟨i1, hi1⟩
  rw [hfrom] at hi1
  step as ⟨sc, hsc⟩
  step as ⟨i3, hi3⟩
  have hi3r : -1000000 ≤ i3.val ∧ i3.val ≤ 1000000 := by
    have hb := cordic_quot_bound radius.val ux.val i1.val i3.val sc.val hi1 hsc hi3 hux
    rw [abs_le] at hb hrad
    omega
  have hcast3 : (IScalar.cast .I32 i3).val = i3.val := by
    apply IScalar.val_mod_pow_inBounds <;> (simp [IScalarTy.numBits]; omega)
  step as ⟨i5, hi5⟩
  step as ⟨i7, hi7⟩
  rw [hfrom] at hi7
  step as ⟨i8, hi8⟩
  have hi8r : -1000000 ≤ i8.val ∧ i8.val ≤ 1000000 := by
    have hb := cordic_quot_bound radius.val uy.val i7.val i8.val sc.val hi7 hsc hi8 huy
    rw [abs_le] at hb hrad
    omega
  have hcast8 : (IScalar.cast .I32 i8).val = i8.val := by
    apply IScalar.val_mod_pow_inBounds <;> (simp [IScalarTy.numBits]; omega)
  step as ⟨i10, hi10⟩
  have hb3 := cordic_quot_bound radius.val ux.val i1.val i3.val sc.val hi1 hsc hi3 hux
  have hb8 := cordic_quot_bound radius.val uy.val i7.val i8.val sc.val hi7 hsc hi8 huy
  constructor
  · rw [hi5, hcast3]; simpa using hb3
  · rw [hi10, hcast8]; simpa using hb8

end Labyrinth
