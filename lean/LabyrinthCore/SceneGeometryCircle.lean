module
public import LabyrinthCore.SceneGeometryCordic
public import LabyrinthCore.SceneGeometryArc

/-! Geometry totality (S8), circle layer: `Circle::arc`, `radius`, `offset` and `offset_at_valid`
return for every circle that satisfies `CircleOk`. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Labyrinth

/-- The facts about one circle of a validated layout that the i32 geometry needs, as
`Circle::new` and `check_circle_extent` establish them: the centre is a valid point, the radii are
positive, at least one ring with `2..=TURN/2` sectors each, `outer = center_radius + rings *
ring_width` within the coordinate limit, the ring transforms fit in the layout's transform count,
and a twisting amplitude of at most `TURN/8`. -/
structure CircleOk (c : polar.Circle) (transforms : Nat) : Prop where
  center : PointOk c.spec.center
  center_radius : 1 ≤ c.spec.center_radius.val
  ring_width : 1 ≤ c.spec.ring_width.val
  rings : 1 ≤ c.spec.sectors.val.length
  directions : c.spec.directions.val.length = c.spec.sectors.val.length
  sectors : ∀ i, ∀ h : i < c.spec.sectors.val.length,
    2 ≤ c.spec.sectors.val[i].val ∧ c.spec.sectors.val[i].val ≤ 2048
  outer : c.outer.val = c.spec.center_radius.val + c.spec.sectors.val.length * c.spec.ring_width.val
  outer_le : c.outer.val ≤ 1000000
  transform : c.transform_start.val + c.spec.sectors.val.length ≤ transforms
  twist : ∀ a m, c.spec.mode = .Twisting a m → 0 ≤ a.val ∧ a.val ≤ 512

theorem CircleOk.outer_pos {c : polar.Circle} {n : Nat} (hc : CircleOk c n) : 1 ≤ c.outer.val := by
  have h1 := hc.outer; have h2 := hc.rings; have h3 := hc.ring_width; have h4 := hc.center_radius
  have : 0 ≤ (c.spec.sectors.val.length : ℤ) * c.spec.ring_width.val := by positivity
  omega

theorem sector_arc_arith (s c : ℤ) (hs : 0 ≤ s) (hc : 2 ≤ c) (hcc : c ≤ 2048) (hsc : s < c) :
    0 ≤ s * 4096 / c ∧ s * 4096 / c < 4096 ∧ 1 ≤ (s + 1) * 4096 / c - s * 4096 / c ∧
      (s + 1) * 4096 / c - s * 4096 / c ≤ 2048 := by
  have hcpos : 0 < c := by omega
  have h1 := Int.ediv_mul_le (s * 4096) hcpos.ne'
  have h2 := Int.lt_ediv_add_one_mul_self (s * 4096) hcpos
  have h3 := Int.ediv_mul_le ((s + 1) * 4096) hcpos.ne'
  have h4 := Int.lt_ediv_add_one_mul_self ((s + 1) * 4096) hcpos
  refine ⟨Int.ediv_nonneg (by nlinarith) hcpos.le, ?_, ?_, ?_⟩
  · rw [Int.ediv_lt_iff_lt_mul hcpos]; nlinarith
  · by_contra hcon
    have : (s + 1) * 4096 / c ≤ s * 4096 / c := by omega
    nlinarith
  · by_contra hcon
    have : (s + 1) * 4096 / c ≥ s * 4096 / c + 2049 := by omega
    nlinarith

/-- A `usize` below `2^31` casts to the same `i32` value. -/
@[step]
theorem usize_hcast_i32_spec (x : Std.Usize) (h : x.val ≤ 2147483647) :
    lift (UScalar.hcast .I32 x) ⦃ y => y.val = x.val ⦄ :=
  UScalar.hcast_inBounds_spec .I32 x (by simp [I32.max, IScalar.max, IScalarTy.numBits, I32.numBits]; omega)

/-- Widening `i32` to `i64`. -/
@[step]
theorem i64_from_i32_spec (x : Std.I32) :
    lift (core.convert.num.FromI64I32.from x) ⦃ y => y.val = x.val ⦄ := by
  simp only [lift, spec_ok]
  exact core.convert.num.FromI64I32.from_val_eq x

/-- Narrowing an `i64` that is within `i32` range. -/
@[step]
theorem i64_cast_i32_spec (x : Std.I64) (h1 : -2147483648 ≤ x.val) (h2 : x.val ≤ 2147483647) :
    lift (IScalar.cast .I32 x) ⦃ y => y.val = x.val ⦄ :=
  IScalar.cast_inBounds_spec .I32 x (by simp [I32.min, I32.max, IScalar.min, IScalar.max, IScalarTy.numBits, I32.numBits]; omega)

@[step]
theorem circle_arc_spec (c : polar.Circle) (ring sector : Std.Usize) (n : Nat) (hc : CircleOk c n)
    (hr : ring.val < c.spec.sectors.val.length)
    (hs : sector.val < c.spec.sectors.val[ring.val].val) :
    polar.Circle.arc c ring sector ⦃ a => ArcOk a ∧ a.length.val ≤ 2048 ⦄ := by
  unfold polar.Circle.arc
  simp only [alloc.vec.Vec.index_slice_index]
  have hsec := hc.sectors ring.val hr
  have h4096 := turn_val
  step as ⟨i, hi⟩
  rw [hi] at *
  step as ⟨count, hcount⟩
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  step as ⟨start, hstart⟩
  step as ⟨i3, hi3⟩
  step as ⟨i4, hi4⟩
  step as ⟨i5, hi5⟩
  step as ⟨e, he⟩
  have hcnt2 : 2 ≤ count.val ∧ count.val ≤ 2048 := by omega
  have hsv : (0:ℤ) ≤ sector.val ∧ (sector.val : ℤ) < count.val := by omega
  have key := sector_arc_arith sector.val count.val (by omega) (by omega) (by omega) (by omega)
  have hs4 : start.val = sector.val * 4096 / count.val := by
    rw [hstart, Int.tdiv_eq_ediv_of_nonneg (by rw [hi2, hi1]; nlinarith)]
    rw [hi2, hi1, h4096]
  have he4 : e.val = (sector.val + 1) * 4096 / count.val := by
    rw [he, Int.tdiv_eq_ediv_of_nonneg (by rw [hi5, hi4, hi3]; nlinarith)]
    rw [hi5, hi4, hi3, h4096]
  step as ⟨i6, hi6⟩
  unfold ArcOk
  dsimp only
  omega

theorem circle_rings_le (c : polar.Circle) (n : Nat) (hc : CircleOk c n) :
    c.spec.sectors.val.length ≤ 1000000 := by
  have h1 := hc.outer; have h2 := hc.outer_le; have h3 := hc.ring_width; have h4 := hc.center_radius
  nlinarith

@[step]
theorem circle_ring_count_spec (c : polar.Circle) :
    polar.Circle.ring_count c ⦃ r => r.val = c.spec.sectors.val.length ⦄ := by
  unfold polar.Circle.ring_count
  simp [spec_ok, alloc.vec.Vec.len]

@[step]
theorem circle_mode_spec (c : polar.Circle) :
    polar.Circle.mode c ⦃ r => r = c.spec.mode ⦄ := by
  unfold polar.Circle.mode; simp [spec_ok]

@[step]
theorem circle_center_spec (c : polar.Circle) :
    polar.Circle.center c ⦃ r => r = c.spec.center ⦄ := by
  unfold polar.Circle.center; simp [spec_ok]

@[step]
theorem circle_radius_spec (c : polar.Circle) (ring : Std.Usize) (n : Nat) (hc : CircleOk c n)
    (hr : ring.val < c.spec.sectors.val.length) :
    polar.Circle.radius c ring ⦃ r => r.val = c.spec.center_radius.val + ring.val * c.spec.ring_width.val
      + c.spec.ring_width.val / 2 ∧ 1 ≤ r.val ∧ r.val < c.outer.val ⦄ := by
  unfold polar.Circle.radius
  have hn := circle_rings_le c n hc
  have ho := hc.outer
  have hw := hc.ring_width
  have hcr := hc.center_radius
  have hol := hc.outer_le
  have hmul : ((ring.val : ℤ) + 1) * c.spec.ring_width.val ≤
      (c.spec.sectors.val.length : ℤ) * c.spec.ring_width.val :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  have hprod : ((ring.val : ℤ)) * c.spec.ring_width.val ≤ 1000000 := by nlinarith
  have hprod0 : 0 ≤ ((ring.val : ℤ)) * c.spec.ring_width.val := by positivity
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  have hp1 : i.val * c.spec.ring_width.val ≤ 1000000 := by rw [hi]; exact hprod
  have hp2 : 0 ≤ i.val * c.spec.ring_width.val := by rw [hi]; exact hprod0
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  step as ⟨i4, hi4⟩
  have ht : (c.spec.ring_width.val).tdiv 2 = c.spec.ring_width.val / 2 :=
    Int.tdiv_eq_ediv_of_nonneg (by omega)
  rw [hi] at hi1
  have hmul' : (ring.val : ℤ) * c.spec.ring_width.val + c.spec.ring_width.val ≤ (c.spec.sectors.val.length : ℤ) * c.spec.ring_width.val := by nlinarith
  rw [ht] at hi3
  refine ⟨by omega, by omega, by omega⟩


@[step]
theorem direction_sign_spec (d : polar.Direction) :
    polar.Direction.sign d ⦃ r => r.val = 1 ∨ r.val = -1 ⦄ := by
  cases d <;> simp [polar.Direction.sign, spec_ok]

@[step]
theorem circle_offset_spec (c : polar.Circle) (ring : Std.Usize) (phases : Slice Std.I32) (n : Nat)
    (hc : CircleOk c n) (hr : ring.val < c.spec.sectors.val.length)
    (hph : c.transform_start.val + ring.val < phases.val.length) :
    polar.Circle.offset c ring phases ⦃ r => 0 ≤ r.val ∧ r.val < 4096 ⦄ := by
  unfold polar.Circle.offset
  have hd := hc.directions
  have hlen := phases.property
  step as ⟨i, hi⟩
  step as ⟨phase, hphase⟩
  cases hmode : c.spec.mode with
  | Spinning =>
    simp only [alloc.vec.Vec.index_slice_index]
    step as ⟨i1, hi1⟩
    step as ⟨d, hd'⟩
    cases d <;> simp only [polar.Direction.sign, Std.bind_ok] <;> step as ⟨i2, hi2⟩ <;> step as ⟨i3, hi3⟩ <;> omega
  | Twisting a m =>
    simp only [alloc.vec.Vec.index_slice_index]
    have ha := hc.twist a m hmode
    have hp0 : PointOk { x := 0#i32, y := 0#i32 } := by simp [PointOk]
    step as ⟨p, hp⟩
    step as ⟨d, hd'⟩
    cases d <;> simp only [polar.Direction.sign, Std.bind_ok] <;> step as ⟨i2, hi2⟩ <;> step as ⟨i3, hi3⟩ <;> omega

theorem tdiv_mul_small (a b c : Int) (hc : 0 < c) (hb0 : 0 ≤ b) (hb : b ≤ c) :
    -|a| ≤ Int.tdiv (a * b) c ∧ Int.tdiv (a * b) c ≤ |a| := by
  have key : ∀ x : Int, 0 ≤ x → 0 ≤ Int.tdiv (x * b) c ∧ Int.tdiv (x * b) c ≤ x := by
    intro x hx
    have hp : 0 ≤ x * b := by positivity
    rw [Int.tdiv_eq_ediv_of_nonneg hp]
    refine ⟨Int.ediv_nonneg hp hc.le, ?_⟩
    have h1 := Int.ediv_mul_le (x * b) hc.ne'
    by_contra hcon
    have hcon := lt_of_not_ge hcon
    nlinarith
  rcases le_or_gt 0 a with ha | ha
  · rw [abs_of_nonneg ha]
    have := key a ha
    omega
  · rw [abs_of_neg ha]
    have := key (-a) (by omega)
    have h2 : Int.tdiv (a * b) c = - Int.tdiv ((-a) * b) c := by
      rw [← Int.neg_tdiv]; congr 1; ring
    omega

theorem tdiv_mul_small_bound (a b c A : Int) (hc : 0 < c) (hb0 : 0 ≤ b) (hb : b ≤ c)
    (ha : -A ≤ a ∧ a ≤ A) : -A ≤ Int.tdiv (a * b) c ∧ Int.tdiv (a * b) c ≤ A := by
  have h1 := tdiv_mul_small a b c hc hb0 hb
  have h2 : |a| ≤ A := abs_le.mpr ha
  constructor <;> linarith [h1.1, h1.2]

/-- Radius of the centre line of ring `ring`. -/
def ringRadius (c : polar.Circle) (ring : Nat) : Int :=
  c.spec.center_radius.val + ring * c.spec.ring_width.val + c.spec.ring_width.val / 2

theorem circle_offset_at_valid_loop_spec (c : polar.Circle) (radius : Std.I32) (n : Nat)
    (hc : CircleOk c n) (ring : Std.Usize) (hr : ring.val < c.spec.sectors.val.length)
    (hrad : ringRadius c ring.val ≤ radius.val) :
    polar.Circle.offset_at_valid_loop c radius ring ⦃ r =>
      r.val < c.spec.sectors.val.length ∧ ringRadius c r.val ≤ radius.val ∧
      (r.val + 1 < c.spec.sectors.val.length → radius.val < ringRadius c (r.val + 1)) ⦄ := by
  unfold polar.Circle.offset_at_valid_loop
  apply loop.spec_decr_nat
    (fun ring : Std.Usize => c.spec.sectors.val.length - ring.val)
    (fun ring : Std.Usize => ring.val < c.spec.sectors.val.length ∧ ringRadius c ring.val ≤ radius.val)
    _
  · intro ring ⟨hr, hrad⟩
    unfold polar.Circle.offset_at_valid_loop.body
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    by_cases hlt : i < i1
    · simp only [hlt, ite_true]
      have hlt' : ring.val + 1 < c.spec.sectors.val.length := by scalar_tac
      step as ⟨i2, hi2, hi2', hi2''⟩
      have hiv : i.val = ring.val + 1 := by scalar_tac
      have hf : ringRadius c (ring.val + 1) = i2.val := by
        unfold ringRadius; rw [hi2, hiv]
      by_cases hge : radius ≥ i2
      · simp only [hge, ite_true, spec_ok]
        have : radius.val ≥ i2.val := by scalar_tac
        rw [hiv]
        omega
      · have hge' : radius.val < i2.val := by scalar_tac
        have hge2 : ¬ radius ≥ i2 := hge
        simp only [hge2, ite_false, spec_ok]
        refine ⟨hr, hrad, fun _ => by omega⟩
    · have hlt2 : ¬ i < i1 := hlt
      simp only [hlt2, ite_false, spec_ok]
      refine ⟨hr, hrad, fun h => ?_⟩
      exfalso; apply hlt2; scalar_tac
  · exact ⟨hr, hrad⟩


theorem int_mul_bounds (a b A B : Int) (ha : -A ≤ a ∧ a ≤ A) (hb : -B ≤ b ∧ b ≤ B) :
    -(A * B) ≤ a * b ∧ a * b ≤ A * B := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hA : 0 ≤ A := by omega
  have hB : 0 ≤ B := by omega
  constructor <;> nlinarith

theorem ringRadius_succ (c : polar.Circle) (ring : Nat) :
    ringRadius c (ring + 1) = ringRadius c ring + c.spec.ring_width.val := by
  unfold ringRadius; push_cast; ring

theorem circle_offset_at_valid_tail (c : polar.Circle) (radius : Std.I32) (phases : Slice Std.I32)
    (n : Nat) (hc : CircleOk c n) (ring i : Std.Usize) (low high : Std.I32)
    (hr : ring.val < c.spec.sectors.val.length) (hi : i.val = ring.val + 1)
    (hph : c.transform_start.val + c.spec.sectors.val.length ≤ phases.val.length)
    (hlow : low.val ≤ radius.val) (hrad : radius.val ≤ 1000000) (hl0 : 0 ≤ low.val)
    (hpos : low.val < high.val) (hhigh : high.val ≤ 2000000) :
    (if radius ≥ high then ok 0#i32 else do
      let «from» ← polar.Circle.offset c ring phases
      let i2 ← polar.Circle.ring_count c
      let «to» ← if i < i2 then polar.Circle.offset c i phases else ok 0#i32
      let i3 ← polar.angle_delta «from» «to»
      let i4 ← lift (core.convert.num.FromI64I32.from i3)
      let i5 ← radius - low
      let i6 ← lift (core.convert.num.FromI64I32.from i5)
      let i7 ← i4 * i6
      let i8 ← high - low
      let i9 ← lift (core.convert.num.FromI64I32.from i8)
      let i10 ← i7 / i9
      let i11 ← lift (IScalar.cast .I32 i10)
      let i12 ← «from» + i11
      polar.normalize i12) ⦃ r => 0 ≤ r.val ∧ r.val < 4096 ⦄ := by
  have htv : c.transform_start.val + ring.val < phases.val.length := by omega
  have h0 : (0#i32).val = 0 := rfl
  by_cases hge : radius ≥ high
  · simp only [hge, ite_true, spec_ok]; omega
  · have hge' : radius.val < high.val := by scalar_tac
    have hge2 : ¬ radius ≥ high := hge
    simp only [hge2, ite_false]
    step as ⟨fr, hfr⟩
    step as ⟨i2, hi2⟩
    have hfr' : -1000000000 ≤ fr.val ∧ fr.val ≤ 1000000000 := by omega
    have hto : (if i < i2 then polar.Circle.offset c i phases else ok 0#i32) ⦃ t => 0 ≤ t.val ∧ t.val < 4096 ⦄ := by
      by_cases hlt : i < i2
      · simp only [hlt, ite_true]
        have : i.val < c.spec.sectors.val.length := by scalar_tac
        apply circle_offset_spec c i phases n hc this (by omega)
      · have hlt2 : ¬ i < i2 := hlt
        simp only [hlt2, ite_false, spec_ok]; omega
    apply spec_bind hto
    intro t ht
    have ht' : -1000000000 ≤ t.val ∧ t.val ≤ 1000000000 := by omega
    step as ⟨i3, hi3⟩
    step as ⟨i4, hi4⟩
    step as ⟨i5, hi5⟩
    step as ⟨i6, hi6⟩
    have hbd := int_mul_bounds i4.val i6.val 2048 2000000 (by omega) (by omega)
    step as ⟨i7, hi7⟩
    step as ⟨i8, hi8⟩
    step as ⟨i9, hi9⟩
    have hts := tdiv_mul_small_bound i4.val i6.val i9.val 2048 (by omega) (by omega) (by omega) (by omega)
    step as ⟨i10, hi10⟩
    rw [hi7] at hi10
    step as ⟨i11, hi11⟩
    step as ⟨i12, hi12⟩
    step as ⟨r, hr'⟩
    omega
theorem circle_offset_at_valid_spec (c : polar.Circle) (radius band : Std.I32)
    (phases : Slice Std.I32) (n : Nat) (hc : CircleOk c n)
    (hband : 0 ≤ band.val ∧ c.outer.val + band.val ≤ 1000000)
    (hrad : 0 ≤ radius.val ∧ radius.val ≤ 1000000)
    (hph : c.transform_start.val + c.spec.sectors.val.length ≤ phases.val.length) :
    polar.Circle.offset_at_valid c radius band phases ⦃ r => 0 ≤ r.val ∧ r.val < 4096 ⦄ := by
  unfold polar.Circle.offset_at_valid
  have hn1 := hc.rings
  have hw := hc.ring_width
  have hcr := hc.center_radius
  have hol := hc.outer_le
  have h0 : (0#usize).val = 0 := rfl
  have hn0 : (0#usize).val < c.spec.sectors.val.length := by omega
  step as ⟨first, hfirst, hfirst1, hfirst2⟩
  by_cases hle : radius ≤ first
  · simp only [hle, ite_true]
    apply circle_offset_spec c 0#usize phases n hc hn0 (by omega)
  · have hle2 : ¬ radius ≤ first := hle
    simp only [hle2, ite_false]
    have hfr : ringRadius c (0#usize).val ≤ radius.val := by
      have : first.val < radius.val := by scalar_tac
      unfold ringRadius; rw [h0]; push_cast; simp only [zero_mul, add_zero]; omega
    apply spec_bind (circle_offset_at_valid_loop_spec c radius n hc 0#usize hn0 hfr)
    rintro ring ⟨hr1, hr2, hr3⟩
    step as ⟨low, hlow, hlow1, hlow2⟩
    step as ⟨i, hi⟩
    step as ⟨i1, hi1⟩
    have hlow' : low.val = ringRadius c ring.val := by unfold ringRadius; exact hlow
    have hiv : i.val = ring.val + 1 := by scalar_tac
    by_cases hlt : i < i1
    · simp only [hlt, ite_true]
      have hlt' : i.val < c.spec.sectors.val.length := by scalar_tac
      step as ⟨high, hhigh, hhigh1, hhigh2⟩
      have hh : high.val = ringRadius c (ring.val + 1) := by
        unfold ringRadius; rw [hhigh, hiv]
      have hs := ringRadius_succ c ring.val
      exact circle_offset_at_valid_tail c radius phases n hc ring i low high hr1 hiv hph
        (by omega) hrad.2 (by omega) (by omega) (by omega)
    · have hlt2 : ¬ i < i1 := hlt
      simp only [hlt2, ite_false]
      step as ⟨high, hhigh⟩
      exact circle_offset_at_valid_tail c radius phases n hc ring i low high hr1 hiv hph
        (by omega) hrad.2 (by omega) (by omega) (by omega)

end Labyrinth
