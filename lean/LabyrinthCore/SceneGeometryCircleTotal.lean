module
public import LabyrinthCore.SceneGeometryLayoutNew
public import LabyrinthCore.SceneGeometryBounds
public import LabyrinthCore.SceneGeometryCircle

/-! Geometry totality (S8), `Circle::new`: for every `PolarSpec` and every margin in
`(0, 10^6]` the constructor returns, and every error it returns is `InvalidGeometry`,
`InvalidSize` or `Overflow`. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

/-- The errors `Circle::new` raises itself. -/
def CircleErr (e : topology.Error) : Prop :=
  e = .InvalidGeometry ∨ e = .InvalidSize ∨ e = .Overflow

/-- A status that is `Ok` or one of the circle errors. -/
def CircleStatus (s : core.result.Result Unit topology.Error) : Prop :=
  ∀ e, s = .Err e → CircleErr e

theorem circle_status_ok : CircleStatus (.Ok ()) := fun e h => by cases h

theorem circle_status_err (e : topology.Error) (h : CircleErr e) :
    CircleStatus (.Err e) := fun e' h' => by cases h'; exact h

@[step]
theorem usize_hcast_turn_spec :
    lift (IScalar.hcast .Usize polar.TURN) ⦃ y => y.val = 4096 ⦄ := by
  have h := turn_val
  apply spec_mono (IScalar.hcast_inBounds_spec .Usize polar.TURN (by scalar_tac))
  intro y hy; omega

theorem circle_loop0_total (cr rw : Std.I32) (v : alloc.vec.Vec Std.Usize) (margin : Std.I32)
    (rs : alloc.vec.Vec Std.Usize) (next : Std.Usize)
    (status : core.result.Result Unit topology.Error) (ring : Std.Usize)
    (hn : v.val.length ≤ 2147483647) (hcr : 1 ≤ cr.val) (hrw : 1 ≤ rw.val)
    (hout : cr.val + v.val.length * rw.val ≤ 1000000)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000)
    (hrs : rs.val.length ≤ ring.val) (hring : ring.val ≤ v.val.length)
    (hinv : status = .Ok () → SectorsUpTo v ring.val) (hst : CircleStatus status) :
    polar.Circle.new_loop0 cr rw v margin rs next status ring ⦃ r =>
      (r.2 = .Ok () → SectorsUpTo v v.val.length) ∧ CircleStatus r.2 ⦄ := by
  unfold polar.Circle.new_loop0
  apply loop.spec_decr_nat
    (fun st : alloc.vec.Vec Std.Usize × Std.Usize × core.result.Result Unit topology.Error ×
      Std.Usize => v.val.length - st.2.2.2.val)
    (fun st : alloc.vec.Vec Std.Usize × Std.Usize × core.result.Result Unit topology.Error ×
      Std.Usize => st.1.val.length ≤ st.2.2.2.val ∧ st.2.2.2.val ≤ v.val.length ∧
        (st.2.2.1 = .Ok () → SectorsUpTo v st.2.2.2.val) ∧ CircleStatus st.2.2.1)
    _
  · rintro ⟨rs, nx, st, rg⟩ ⟨hrs, hrg, hi, hs⟩
    dsimp only at hrs hrg hi hs ⊢
    unfold polar.Circle.new_loop0.body
    by_cases hlt : rg < alloc.vec.Vec.len v
    swap
    · simp only [hlt, ↓reduceIte, spec_ok]
      refine ⟨fun h j hj _ => hi h j hj (by scalar_tac), hs⟩
    simp only [hlt, ↓reduceIte]
    cases st with
    | Err e =>
      simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte, spec_ok]
      and_intros
      all_goals first | exact hs | (intro h; cases h)
    | Ok u =>
      simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte, alloc.vec.Vec.index_slice_index]
      have hrgv : rg.val < v.val.length := by scalar_tac
      step as ⟨count, hcount⟩
      step as ⟨i3, hi3⟩
      have hmul1 : (rg.val : ℤ) * rw.val ≤ (v.val.length : ℤ) * rw.val :=
        Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hrgv.le) (by omega)
      have hmul0 : (0 : ℤ) ≤ (rg.val : ℤ) * rw.val := by positivity
      step as ⟨i4, hi4⟩
      step as ⟨inner, hinner⟩
      have hcv : 0 ≤ count.val := by scalar_tac
      by_cases hc2 : count < 2#usize
      · simp only [hc2, ↓reduceIte, Std.bind_ok]
        step as ⟨rg1, hrg1⟩
        and_intros
        all_goals first | omega | exact circle_status_err _ (by simp [CircleErr]) | (intro h; cases h)
      simp only [hc2, ↓reduceIte, Std.bind_assoc]
      have ht := turn_val
      have hc2' : 2 ≤ count.val := by scalar_tac
      step as ⟨i5, hi5⟩
      step as ⟨i6, hi6⟩
      by_cases hc3 : count > i6
      · simp only [hc3, ↓reduceIte, Std.bind_ok]
        step as ⟨rg1, hrg1⟩
        and_intros
        all_goals first | omega | exact circle_status_err _ (by simp [CircleErr]) | (intro h; cases h)
      simp only [hc3, ↓reduceIte, Std.bind_assoc]
      have hc3' : count.val ≤ 2048 := by scalar_tac
      step as ⟨i7, hi7⟩
      step as ⟨i8, hi8⟩
      step as ⟨i9, hi9⟩
      step as ⟨i10, hi10⟩
      have hinn : 0 ≤ inner.val ∧ inner.val ≤ 1000000 := by
        have := Int.mul_le_mul_of_nonneg_right (show (rg.val : ℤ) ≤ v.val.length by omega)
          (show (0 : ℤ) ≤ rw.val by omega)
        have h3 : (i3.val : ℤ) * rw.val = rg.val * rw.val := by rw [hi3]
        have h4 : (0 : ℤ) ≤ rg.val * rw.val := by positivity
        omega
      have hi9b : 0 ≤ i9.val ∧ i9.val ≤ 2048 := by
        rw [hi9, ht, hi8]
        simp only [Int.tdiv_eq_ediv_of_nonneg (show (0:ℤ) ≤ 4096 by omega)]
        have hc0 : (0:ℤ) < count.val := by omega
        constructor
        · exact Int.ediv_nonneg (by omega) hc0.le
        · rw [Int.ediv_le_iff_le_mul hc0]; push_cast; omega
      have hprod : i7.val * i10.val ≤ 1000000 * 2048 :=
        Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
      have hprod0 : 0 ≤ i7.val * i10.val := Int.mul_nonneg (by omega) (by omega)
      step as ⟨x, hx⟩
      step as ⟨x1, hx1⟩
      step as ⟨x2, hx2⟩
      step as ⟨x3, hx3⟩
      step as ⟨x4, hx4⟩
      by_cases hlt2 : x < x4
      · simp only [hlt2, ↓reduceIte, Std.bind_ok]
        step as ⟨rg1, hrg1⟩
        and_intros
        all_goals first | omega | exact circle_status_err _ (by simp [CircleErr]) | (intro h; cases h)
      simp only [hlt2, ↓reduceIte, Std.bind_assoc]
      have hpl : rs.val.length < Usize.max := by scalar_tac
      step as ⟨rs2, hrs2⟩
      have hl2 : rs2.val.length = rs.val.length + 1 := by rw [hrs2]; simp
      rcases hadd : Usize.checked_add nx count with _ | val
      · simp only [lift, hadd, Std.bind_ok]
        step as ⟨rg1, hrg1⟩
        and_intros
        all_goals first | omega | exact circle_status_err _ (by simp [CircleErr]) | (intro h; cases h)
      · simp only [lift, hadd, Std.bind_ok]
        step as ⟨rg1, hrg1⟩
        refine ⟨by omega, by omega, fun _ j hj hjr => ?_, hs, by omega⟩
        have hh := hi (by cases u; rfl)
        by_cases hjr' : j < rg.val
        · exact hh j hj hjr'
        · have : j = rg.val := by omega
          subst this
          rw [← hcount] at *
          omega
  · exact ⟨hrs, hring, hinv, hst⟩

/-- A `usize` below `2^63` casts to the same `i64` value. -/
@[step]
theorem usize_hcast_i64_spec (x : Std.Usize) (h : x.val ≤ 9223372036854775807) :
    lift (UScalar.hcast .I64 x) ⦃ y => y.val = x.val ⦄ :=
  UScalar.hcast_inBounds_spec .I64 x
    (by simp [I64.max, IScalar.max, IScalarTy.numBits, I64.numBits]; omega)

theorem tdiv_bounds (a b : Int) (ha : 0 ≤ a) (hb : 1 ≤ b) :
    0 ≤ a.tdiv b ∧ a.tdiv b ≤ a := by
  rw [Int.tdiv_eq_ediv_of_nonneg ha]
  exact ⟨Int.ediv_nonneg ha (by omega), Int.ediv_le_self _ ha⟩

theorem circle_loop1_total (cr rw : Std.I32) (v : alloc.vec.Vec Std.Usize)
    (status : core.result.Result Unit topology.Error) (clearance : Std.I64) (ring : Std.Usize)
    (hn : v.val.length ≤ 2147483647) (hcr : 1 ≤ cr.val) (hrw : 1 ≤ rw.val)
    (hout : cr.val + v.val.length * rw.val ≤ 1000000)
    (hcl : 0 ≤ clearance.val ∧ clearance.val ≤ 8192000000)
    (hring : 1 ≤ ring.val)
    (hinv : status = .Ok () → SectorsUpTo v v.val.length) (hst : CircleStatus status) :
    polar.Circle.new_loop1 cr rw v status clearance ring ⦃ r => CircleStatus r ⦄ := by
  unfold polar.Circle.new_loop1
  apply loop.spec_decr_nat
    (fun st : core.result.Result Unit topology.Error × Std.Usize => v.val.length - st.2.val)
    (fun st : core.result.Result Unit topology.Error × Std.Usize =>
      1 ≤ st.2.val ∧ CircleStatus st.1 ∧ (st.1 = .Ok () → SectorsUpTo v v.val.length))
    _
  · rintro ⟨st, rg⟩ ⟨hrg, hs, hinv⟩
    dsimp only at hrg hs hinv ⊢
    unfold polar.Circle.new_loop1.body
    by_cases hlt : rg < alloc.vec.Vec.len v
    swap
    · simp only [hlt, ↓reduceIte, spec_ok]
      exact hs
    simp only [hlt, ↓reduceIte]
    cases st with
    | Err e =>
      simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact hs
    | Ok u =>
      simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte, alloc.vec.Vec.index_slice_index]
      have hrgv : rg.val < v.val.length := by scalar_tac
      have hsec := hinv (by cases u; rfl)
      have hmul1 : ((rg.val - 1 : Nat) : ℤ) * rw.val ≤ (v.val.length : ℤ) * rw.val :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      have hmul0 : (0 : ℤ) ≤ ((rg.val - 1 : Nat) : ℤ) * rw.val := by positivity
      have hb1 : (rw.val : ℤ) ≤ (v.val.length : ℤ) * rw.val := by
        have : (1 : ℤ) ≤ v.val.length := by omega
        nlinarith
      generalize hP : ((rg.val - 1 : Nat) : ℤ) * rw.val = P at hmul1 hmul0
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      step as ⟨i5, hi5⟩
      step as ⟨i6, hi6⟩
      step as ⟨i7, hi7⟩
      step as ⟨i8, hi8⟩
      step as ⟨i9, hi9⟩
      step as ⟨i10, hi10⟩
      step as ⟨radius, hrad⟩
      have h10 : 0 ≤ i10.val ∧ i10.val ≤ rw.val := by
        rw [hi10, hi9]; have := tdiv_bounds rw.val 2 (by omega) (by omega); omega
      have hrad1 : 1 ≤ radius.val ∧ radius.val ≤ 2000000 := by
        have h7 : i7.val = P := by rw [hi7, hi5, hi6, hi4]; exact hP
        omega
      step as ⟨i11, hi11⟩
      step as ⟨i12, hi12⟩
      step as ⟨minimum, hmin⟩
      have hmin' := tdiv_bounds i12.val radius.val (by omega) (by omega)
      have h4 : i4.val < v.val.length := by omega
      step as ⟨i13, hi13⟩
      have h13 : 2 ≤ i13.val ∧ i13.val ≤ 2048 := by rw [hi13]; exact hsec _ h4 h4
      step as ⟨i14, hi14⟩
      step as ⟨i15, hi15⟩
      step as ⟨inner_width, hiw⟩
      step as ⟨i16, hi16⟩
      have h16 : 2 ≤ i16.val ∧ i16.val ≤ 2048 := by rw [hi16]; exact hsec _ hrgv hrgv
      step as ⟨i17, hi17⟩
      step as ⟨i18, hi18⟩
      step as ⟨outer_width, how⟩
      step as ⟨i19, hi19⟩
      step as ⟨i20, hi20⟩
      by_cases hiw2 : inner_width < i20
      · simp only [hiw2, ↓reduceIte, Std.bind_ok]
        step as ⟨rg1, hrg1⟩
        and_intros
        all_goals first | omega | exact circle_status_err _ (by simp [CircleErr]) | (intro h; cases h)
      simp only [hiw2, ↓reduceIte, Std.bind_assoc]
      step as ⟨i21, hi21⟩
      by_cases how2 : outer_width < i21
      · simp only [how2, ↓reduceIte, Std.bind_ok]
        step as ⟨rg1, hrg1⟩
        and_intros
        all_goals first | omega | exact circle_status_err _ (by simp [CircleErr]) | (intro h; cases h)
      simp only [how2, ↓reduceIte, Std.bind_ok]
      step as ⟨rg1, hrg1⟩
      exact ⟨by omega, hs, fun _ => hsec, by omega⟩
  · exact ⟨hring, hst, hinv⟩

@[step]
theorem direction_ne_total (d d1 : polar.Direction) :
    core.cmp.PartialEq.ne.trait_default polar.Direction.Insts.CoreCmpPartialEqDirection d d1
      ⦃ b => True ⦄ := by
  apply spec_mono (core.cmp.PartialEq.ne.trait_default.spec _ d d1 ?_)
  · intro b _; trivial
  · show polar.Direction.Insts.CoreCmpPartialEqDirection.eq d d1 ⦃ b => b ↔ d = d1 ⦄
    unfold polar.Direction.Insts.CoreCmpPartialEqDirection.eq
    simp only [spec_ok]
    cases d <;> cases d1 <;> simp [read_discriminant, polar.Direction.read_discriminant] <;> decide

/-- The status update of one ring of the twisting scan returns. -/
theorem circle_twist_status_total (rw margin outer relative max_relative : Std.I32)
    (st : core.result.Result Unit topology.Error)
    (hrw : 1 ≤ rw.val) (hm : 0 < margin.val ∧ margin.val ≤ 1000000)
    (hout : 0 ≤ outer.val ∧ outer.val ≤ 1000000) (hr : 0 ≤ relative.val ∧ relative.val ≤ 1024)
    (hst : CircleStatus st) :
    (if relative > max_relative then ok (core.result.Result.Err topology.Error.InvalidGeometry)
      else do
        let i4 ← lift (core.convert.num.FromI64I32.from outer)
        let i5 ← lift (core.convert.num.FromI64I32.from relative)
        let i6 ← i4 * i5
        let i7 ← i6 * 8#i64
        let i8 ← margin * 2#i32
        let i9 ← rw - i8
        let i10 ← lift (core.convert.num.FromI64I32.from i9)
        let i11 ← lift (core.convert.num.FromI64I32.from polar.TURN)
        let i12 ← i10 * i11
        if i7 > i12 then ok (core.result.Result.Err topology.Error.InvalidGeometry)
          else ok st) ⦃ s => CircleStatus s ⦄ := by
  by_cases h1 : relative > max_relative
  · simp only [h1, ↓reduceIte, spec_ok]
    exact circle_status_err _ (by simp [CircleErr])
  simp only [h1, ↓reduceIte]
  have ht := turn_val
  have hp : outer.val * relative.val ≤ 1000000 * 1024 :=
    Int.mul_le_mul hout.2 hr.2 hr.1 (by omega)
  have hp0 : 0 ≤ outer.val * relative.val := Int.mul_nonneg hout.1 hr.1
  step as ⟨i4, hi4⟩
  step as ⟨i5, hi5⟩
  step as ⟨i6, hi6⟩
  step as ⟨i7, hi7⟩
  step as ⟨i8, hi8⟩
  step as ⟨i9, hi9⟩
  step as ⟨i10, hi10⟩
  step as ⟨i11, hi11⟩
  have hq : |i10.val * i11.val| ≤ 2147483648 * 4096 := by
    rw [abs_mul, hi11, ht]
    have : |i10.val| ≤ 2147483648 := by rw [abs_le]; have := i32_val_bounds i9; omega
    have h4096 : |(4096 : ℤ)| = 4096 := by norm_num
    rw [h4096]; nlinarith [abs_nonneg i10.val]
  rw [abs_le] at hq
  step as ⟨i12, hi12⟩
  by_cases h2 : i7 > i12
  · simp only [h2, ↓reduceIte, spec_ok]
    exact circle_status_err _ (by simp [CircleErr])
  · simp only [h2, ↓reduceIte, spec_ok]
    exact hst

/-- The twist amplitude of one ring (`amplitude`, doubled when the next ring turns the other way)
is at most `1024`. -/
theorem circle_relative_total (v : alloc.vec.Vec Std.Usize) (v1 : alloc.vec.Vec polar.Direction)
    (amplitude : Std.I32) (rg i2 : Std.Usize) (hd : v1.val.length = v.val.length)
    (hrg : rg.val < v.val.length) (ha : 0 ≤ amplitude.val ∧ amplitude.val ≤ 512)
    (hi2 : i2.val = rg.val + 1) :
    (if i2 < alloc.vec.Vec.len v then do
        let d ← alloc.vec.Vec.index_usize v1 rg
        let d1 ← alloc.vec.Vec.index_usize v1 i2
        let b1 ← core.cmp.PartialEq.ne.trait_default
          polar.Direction.Insts.CoreCmpPartialEqDirection d d1
        if b1 = true then amplitude * 2#i32 else ok amplitude
      else ok amplitude) ⦃ r => 0 ≤ r.val ∧ r.val ≤ 1024 ⦄ := by
  by_cases h1 : i2 < alloc.vec.Vec.len v
  · simp only [h1, ↓reduceIte]
    have h1' : i2.val < v.val.length := by scalar_tac
    step as ⟨d, hdd⟩
    step as ⟨d1, hd1⟩
    step as ⟨b1⟩
    by_cases hb : b1 = true
    · simp only [hb, ↓reduceIte]
      step as ⟨r, hr⟩
      omega
    · have hb' : b1 = false := by simpa using hb
      simp only [hb', Bool.false_eq_true, ↓reduceIte, spec_ok]
      omega
  · simp only [h1, ↓reduceIte, spec_ok]
    omega

theorem circle_loop2_total (rw : Std.I32) (v : alloc.vec.Vec Std.Usize)
    (v1 : alloc.vec.Vec polar.Direction) (margin outer : Std.I32)
    (status : core.result.Result Unit topology.Error) (amplitude max_relative : Std.I32)
    (ring : Std.Usize) (hn : v.val.length ≤ 2147483647) (hd : v1.val.length = v.val.length)
    (hrw : 1 ≤ rw.val) (hm : 0 < margin.val ∧ margin.val ≤ 1000000)
    (hout : 0 ≤ outer.val ∧ outer.val ≤ 1000000) (ha : 0 ≤ amplitude.val ∧ amplitude.val ≤ 512)
    (hmr : 0 ≤ max_relative.val ∧ max_relative.val ≤ 1024) (hst : CircleStatus status) :
    polar.Circle.new_loop2 rw v v1 margin outer status amplitude max_relative ring ⦃ r =>
      CircleStatus r ⦄ := by
  unfold polar.Circle.new_loop2
  apply loop.spec_decr_nat
    (fun st : core.result.Result Unit topology.Error × Std.Usize => v.val.length - st.2.val)
    (fun st : core.result.Result Unit topology.Error × Std.Usize => CircleStatus st.1)
    _
  · rintro ⟨st, rg⟩ hs
    dsimp only at hs ⊢
    unfold polar.Circle.new_loop2.body
    by_cases hlt : rg < alloc.vec.Vec.len v
    swap
    · simp only [hlt, ↓reduceIte, spec_ok]
      exact hs
    simp only [hlt, ↓reduceIte]
    cases st with
    | Err e =>
      simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact hs
    | Ok u =>
      simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte,
        alloc.vec.Vec.index_slice_index]
      have hrgv : rg.val < v.val.length := by scalar_tac
      step as ⟨i2, hi2⟩
      refine spec_bind (circle_relative_total v v1 amplitude rg i2 hd hrgv ha hi2) ?_
      intro relative hrel
      refine spec_bind (circle_twist_status_total rw margin outer relative max_relative _ hrw hm
        hout hrel hs) ?_
      intro s hs'
      simp only [spec_ok]
      exact ⟨hs', by omega⟩
  · exact hst

theorem circle_loop3_total (rw : Std.I32) (v : alloc.vec.Vec Std.Usize)
    (v1 : alloc.vec.Vec polar.Direction) (margin outer : Std.I32)
    (status : core.result.Result Unit topology.Error) (amplitude max_relative : Std.I32)
    (ring : Std.Usize) (hn : v.val.length ≤ 2147483647) (hd : v1.val.length = v.val.length)
    (hrw : 1 ≤ rw.val) (hm : 0 < margin.val ∧ margin.val ≤ 1000000)
    (hout : 0 ≤ outer.val ∧ outer.val ≤ 1000000) (ha : 0 ≤ amplitude.val ∧ amplitude.val ≤ 512)
    (hmr : 0 ≤ max_relative.val ∧ max_relative.val ≤ 1024) (hst : CircleStatus status) :
    polar.Circle.new_loop3 rw v v1 margin outer status amplitude max_relative ring ⦃ r =>
      CircleStatus r ⦄ := by
  unfold polar.Circle.new_loop3
  apply loop.spec_decr_nat
    (fun st : core.result.Result Unit topology.Error × Std.Usize => v.val.length - st.2.val)
    (fun st : core.result.Result Unit topology.Error × Std.Usize => CircleStatus st.1)
    _
  · rintro ⟨st, rg⟩ hs
    dsimp only at hs ⊢
    unfold polar.Circle.new_loop3.body
    by_cases hlt : rg < alloc.vec.Vec.len v
    swap
    · simp only [hlt, ↓reduceIte, spec_ok]
      exact hs
    simp only [hlt, ↓reduceIte]
    cases st with
    | Err e =>
      simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact hs
    | Ok u =>
      simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte,
        alloc.vec.Vec.index_slice_index]
      have hrgv : rg.val < v.val.length := by scalar_tac
      step as ⟨i2, hi2⟩
      refine spec_bind (circle_relative_total v v1 amplitude rg i2 hd hrgv ha hi2) ?_
      intro relative hrel
      refine spec_bind (circle_twist_status_total rw margin outer relative max_relative _ hrw hm
        hout hrel hs) ?_
      intro s hs'
      simp only [spec_ok]
      exact ⟨hs', by omega⟩
  · exact hst

theorem motion_eq_spinning :
    polar.MotionMode.Insts.CoreCmpPartialEqMotionMode.eq .Spinning .Spinning = ok true := by
  simp [polar.MotionMode.Insts.CoreCmpPartialEqMotionMode.eq]

theorem motion_eq_twisting (a m : Std.I32) :
    polar.MotionMode.Insts.CoreCmpPartialEqMotionMode.eq (.Twisting a m) .Spinning = ok false := by
  simp [polar.MotionMode.Insts.CoreCmpPartialEqMotionMode.eq, read_discriminant,
    polar.MotionMode.read_discriminant]

/-- Returning an error that the constructor raises. -/
theorem circle_residual_spec (e : topology.Error) (h : CircleErr e) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual polar.Circle
      (core.convert.FromSame topology.Error) (.Err e) ⦃ r => ∀ e', r = .Err e' → CircleErr e' ⦄ := by
  simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, core.convert.FromSame.from, Std.bind_ok, bind_tc_ok, spec_ok]
  intro e' h'; cases h'; exact h

theorem circle_new_spec (spec : polar.PolarSpec) (cc ts : Std.Usize) (margin : Std.I32)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000) :
    polar.Circle.new spec cc ts margin ⦃ r => ∀ e, r = .Err e → CircleErr e ⦄ := by
  have hErr : ∀ e, CircleErr e → ∀ {T : Type},
      (core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual polar.Circle
        (core.convert.FromSame topology.Error) (.Err e)) ⦃ r => ∀ e', r = .Err e' → CircleErr e' ⦄ :=
    fun e h _ => circle_residual_spec e h
  unfold polar.Circle.new
  refine spec_bind (grid_point_validate_spec spec.center) ?_
  rintro r ⟨hr1, hr2⟩
  cases r with
  | Err e =>
    simp only [branch_err_eq, Std.bind_ok]
    exact circle_residual_spec e (by have := hr2 (by simp); simp at this; simp [this, CircleErr])
  | Ok u =>
  have hpt := hr1.mp (by cases u; rfl)
  simp only [branch_ok_eq, Std.bind_ok, alloc.vec.Vec.is_empty]
  by_cases he : alloc.vec.Vec.length spec.sectors = 0
  · simp only [he, decide_true, ↓reduceIte, spec_ok]; intro e h; cases h; simp [CircleErr]
  simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte]
  by_cases hd : (alloc.vec.Vec.len spec.sectors != alloc.vec.Vec.len spec.directions) = true
  · simp only [hd, ↓reduceIte, spec_ok]; intro e h; cases h; simp [CircleErr]
  have hd' : (alloc.vec.Vec.len spec.sectors != alloc.vec.Vec.len spec.directions) = false :=
    Bool.eq_false_iff.mpr hd
  simp only [hd', Bool.false_eq_true, ↓reduceIte]
  have hdl : spec.sectors.val.length = spec.directions.val.length := by
    simp at hd'; scalar_tac
  have hne : 1 ≤ spec.sectors.val.length := by
    have : ¬ spec.sectors.val.length = 0 := he
    omega
  step as ⟨i2, hi2⟩
  by_cases hc1 : spec.center_radius < i2
  · simp only [hc1, ↓reduceIte, spec_ok]; intro e h; cases h; simp [CircleErr]
  simp only [hc1, ↓reduceIte]
  by_cases hc2 : spec.ring_width < i2
  · simp only [hc2, ↓reduceIte, spec_ok]; intro e h; cases h; simp [CircleErr]
  simp only [hc2, ↓reduceIte]
  have hmax : core.num.I32.MAX.val = 2147483647 := rfl
  apply spec_bind (IScalar.hcast_inBounds_spec .Usize core.num.I32.MAX
    (by rw [hmax]; constructor; omega; scalar_tac))
  intro i4 hi4
  by_cases hc3 : alloc.vec.Vec.len spec.sectors > i4
  · simp only [hc3, ↓reduceIte, spec_ok]; intro e h; cases h; simp [CircleErr]
  simp only [hc3, ↓reduceIte]
  have hlen : spec.sectors.val.length ≤ 2147483647 := by scalar_tac
  apply spec_bind (usize_hcast_i32_spec (alloc.vec.Vec.len spec.sectors) (by scalar_tac))
  intro rc hrc
  simp only [lift, Std.bind_ok]
  rcases i32_checked_mul_cases rc spec.ring_width with hn | ⟨val, hv, hvv⟩
  · simp only [hn, core.option.Option.ok_or, Std.bind_ok, branch_err_eq]
    exact circle_residual_spec _ (by simp [CircleErr])
  simp only [hv, core.option.Option.ok_or, Std.bind_ok, branch_ok_eq]
  rcases i32_checked_add_cases val spec.center_radius with ⟨hn, _⟩ | ⟨val1, hv1, hvv1⟩
  · simp only [hn, core.option.Option.ok_or, Std.bind_ok, branch_err_eq]
    exact circle_residual_spec _ (by simp [CircleErr])
  simp only [hv1, core.option.Option.ok_or, Std.bind_ok, branch_ok_eq]
  have hcl := coord_limit_val
  by_cases hc4 : val1 > grid.COORD_LIMIT
  · simp only [hc4, ↓reduceIte, spec_ok]; intro e h; cases h; simp [CircleErr]
  simp only [hc4, ↓reduceIte]
  have hc4' : val1.val ≤ 1000000 := by scalar_tac
  have hcr : 4 ≤ spec.center_radius.val := by scalar_tac
  have hrw : 4 ≤ spec.ring_width.val := by scalar_tac
  have hvpos : 0 ≤ val.val := by
    rw [hvv, hrc]; exact Int.mul_nonneg (by omega) (by omega)
  have hout : spec.center_radius.val + spec.sectors.val.length * spec.ring_width.val ≤ 1000000 := by
    have : val1.val = spec.sectors.val.length * spec.ring_width.val + spec.center_radius.val := by
      rw [hvv1, hvv, hrc]; simp
    omega
  apply spec_bind (polar_bounds_spec spec.center 0#i32 val1
    { start := 0#i32, length := polar.TURN } margin hpt (by simp) (by constructor <;> omega)
    (by unfold ArcBnd; have := turn_val; dsimp only; scalar_tac))
  intro r3 ⟨_, h3, _⟩
  cases r3 with
  | Err e =>
    simp only [branch_err_eq, Std.bind_ok]
    exact circle_residual_spec e (by rcases h3 e rfl with h | h <;> simp [CircleErr, h])
  | Ok u3 =>
  simp only [branch_ok_eq, Std.bind_ok]
  rcases hopt : Usize.checked_add cc 1#usize with _ | val2
  · simp only [hopt, core.option.Option.ok_or, Std.bind_ok, branch_err_eq]
    exact circle_residual_spec _ (by simp [CircleErr])
  simp only [hopt, core.option.Option.ok_or, Std.bind_ok, branch_ok_eq]
  refine spec_bind (circle_loop0_total spec.center_radius spec.ring_width spec.sectors margin _ _ _ _
    hlen (by omega) (by omega) hout hm (by simp [alloc.vec.Vec.with_capacity]) (by simp)
    (fun _ j hj hj0 => by simp at hj0) circle_status_ok) ?_
  rintro ⟨rs1, st⟩ ⟨hsec, hst⟩
  cases st with
  | Err e =>
    refine spec_bind (core.result.Result.Insts.CoreOpsTry.branch_Err.spec (T := Unit) e) ?_
    intro cf hcf; subst hcf
    exact circle_residual_spec e (hst e rfl)
  | Ok u5 =>
  have hsec' := hsec rfl
  refine spec_bind (core.result.Result.Insts.CoreOpsTry.branch_Ok.spec (E := topology.Error) u5) ?_
  intro cf hcf; subst hcf
  have ht := turn_val
  cases hmode : spec.mode with
  | Spinning =>
    simp only [hmode, motion_eq_spinning, Std.bind_ok, ↓reduceIte]
    have hfT : (core.convert.num.FromI64I32.from polar.TURN).val = 4096 := by
      rw [core.convert.num.FromI64I32.from_val_eq]; exact ht
    have hfc : (core.convert.num.FromI64I32.from spec.center_radius).val = spec.center_radius.val :=
      core.convert.num.FromI64I32.from_val_eq _
    have hfm : (core.convert.num.FromI64I32.from margin).val = margin.val :=
      core.convert.num.FromI64I32.from_val_eq _
    step as ⟨i7, hi7⟩
    step as ⟨i8, hi8⟩
    rw [hfT] at hi8
    step as ⟨i9, hi9⟩
    step as ⟨clearance, hclr⟩
    have hclr' : 0 ≤ i8.val ∧ i8.val ≤ 8192000000 := by omega
    step as ⟨cm, hcm⟩
    have hq := tdiv_bounds clearance.val (core.convert.num.FromI64I32.from spec.center_radius).val
      (by omega) (by omega)
    have h0 : 0 < spec.sectors.val.length := by omega
    step as ⟨i12, hi12⟩
    have h12 : 2 ≤ i12.val ∧ i12.val ≤ 2048 := by rw [hi12]; exact hsec' 0 h0 h0
    have hh12 : (UScalar.hcast IScalarTy.I32 i12).val = i12.val := by
      have := usize_hcast_i32_spec i12 (by omega)
      simpa [lift, spec_ok] using this
    step as ⟨i14, hi14⟩
    step as ⟨i16, hi16⟩
    by_cases hlt : (core.convert.num.FromI64I32.from i14) < i16
    · simp only [hlt, ↓reduceIte, spec_ok]; intro e h; cases h; simp [CircleErr]
    simp only [hlt, ↓reduceIte, Std.bind_assoc]
    refine spec_bind (circle_loop1_total spec.center_radius spec.ring_width spec.sectors _ i8 1#usize
      hlen (by omega) (by omega) hout hclr' (by simp) (fun _ => hsec') circle_status_ok) ?_
    intro st1 hst1
    cases st1 with
    | Err e =>
      refine spec_bind (core.result.Result.Insts.CoreOpsTry.branch_Err.spec (T := Unit) e) ?_
      intro cf hcf; subst hcf
      exact circle_residual_spec e (hst1 e rfl)
    | Ok u6 =>
      refine spec_bind (core.result.Result.Insts.CoreOpsTry.branch_Ok.spec (E := topology.Error) u6) ?_
      intro cf hcf; subst hcf
      simp only [spec_ok]; intro e h; cases h
  | Twisting amp mr =>
    simp only [hmode, motion_eq_twisting, Std.bind_ok, Bool.false_eq_true, ↓reduceIte]
    have hamp := hmode
    have h8 : ¬ (8#i32 = 0#i32) := by decide
    have h4 : ¬ (4#i32 = 0#i32) := by decide
    simp only [massert, h8, h4, ↓reduceIte, Std.bind_ok, range_inclusive_new_eq, not_false_eq_true,
      decide_true, Bool.or_true, Bool.true_or]
    step as ⟨i7, hi7⟩
    step as ⟨b2, hb2⟩
    have hi7' : i7.val = 512 := by rw [hi7, ht]; rfl
    by_cases hb2t : b2 = true
    swap
    · have : b2 = false := by simpa using hb2t
      simp only [this, Bool.false_eq_true, ↓reduceIte, spec_ok]; intro e h; cases h; simp [CircleErr]
    simp only [hb2t, ↓reduceIte, Std.bind_assoc]
    have hamp' : 0 ≤ amp.val ∧ amp.val ≤ 512 := by
      have := hb2.mp hb2t; simp at this; omega
    step as ⟨i8, hi8⟩
    have hi8' : i8.val = 1024 := by rw [hi8, ht]; rfl
    step as ⟨b3, hb3⟩
    by_cases hb3t : b3 = true
    swap
    · have : b3 = false := by simpa using hb3t
      simp only [this, Bool.false_eq_true, ↓reduceIte, spec_ok]; intro e h; cases h; simp [CircleErr]
    simp only [hb3t, ↓reduceIte, Std.bind_assoc]
    have hmr' : 0 ≤ mr.val ∧ mr.val ≤ 1024 := by
      have := hb3.mp hb3t; simp at this; omega
    refine spec_bind (circle_loop3_total spec.ring_width spec.sectors spec.directions margin val1 _ amp mr 0#usize
      hlen hdl.symm (by omega) hm (by omega) hamp' hmr' circle_status_ok) ?_
    intro st1 hst1
    cases st1 with
    | Err e =>
      refine spec_bind (core.result.Result.Insts.CoreOpsTry.branch_Err.spec (T := Unit) e) ?_
      intro cf hcf; subst hcf
      exact circle_residual_spec e (hst1 e rfl)
    | Ok u6 =>
      refine spec_bind (core.result.Result.Insts.CoreOpsTry.branch_Ok.spec (E := topology.Error) u6) ?_
      intro cf hcf; subst hcf
      simp only [spec_ok]; intro e h; cases h

/-- `Circle::new` returns for every spec and every margin in `(0, 10^6]`; an `Err` is
`InvalidGeometry`, `InvalidSize` or `Overflow`, and an `Ok` circle satisfies `CircleOk`. -/
theorem circle_new_total (spec : polar.PolarSpec) (cc ts : Std.Usize) (margin : Std.I32)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000) :
    ∃ r, polar.Circle.new spec cc ts margin = ok r ∧
      (∀ e, r = .Err e → e = .InvalidGeometry ∨ e = .InvalidSize ∨ e = .Overflow) ∧
      (∀ c, r = .Ok c →
        CircleOk c (ts.val + spec.sectors.val.length) ∧ c.transform_start = ts ∧ c.spec = spec) := by
  obtain ⟨r, hr, hq⟩ := spec_exists_ok (circle_new_spec spec cc ts margin hm)
  exact ⟨r, hr, hq, circle_new_ok spec cc ts margin hm r hr⟩

end Labyrinth
