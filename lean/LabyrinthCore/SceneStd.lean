module
public import LabyrinthCore.Funs

/-! Step specifications for the repo-owned standard-library models in `FunsExternal.lean` and for
the library operations the scene code reaches through them (`Slice.contains`, `Option.ok_or`,
`Result::is_err`). `Result::is_ok` and `Result::branch` already carry `@[step]` specs in Aeneas
(`core.result.Result.is_ok.step_spec`, `core.result.Result.Insts.CoreOpsTry.branch.step_spec`). -/

public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-! ### `i32::abs` -/

/-- `abs` is the mathematical absolute value away from `MIN`. -/
@[step]
theorem i32_abs_spec (x : Std.I32) (hx : IScalar.min .I32 < x.val) :
    core.num.I32.abs x ⦃ r => r.val = |x.val| ⦄ := by
  unfold core.num.I32.abs
  split
  · rename_i hneg
    have hne : x ≠ IScalar.min .I32 := by
      intro h; rw [h] at hx; exact absurd hx (lt_irrefl _)
    apply spec_mono (IScalar.neg_step x hne)
    intro r hr
    rw [hr, abs_of_neg hneg]
  · rename_i hnn
    simp only [spec_ok]
    exact (abs_of_nonneg (not_lt.mp hnn)).symm

/-! ### `i32::rem_euclid` -/

/-- For a positive modulus the result is the Euclidean remainder: in `[0, y)` and congruent to `x`
modulo `y`. (The model's `MIN % -1` limit needs `y < 0`, so it is outside this statement.) -/
@[step]
theorem i32_rem_euclid_spec (x y : Std.I32) (hy : 0 < y.val) :
    core.num.I32.rem_euclid x y ⦃ r =>
      r.val = x.val % y.val ∧ 0 ≤ r.val ∧ r.val < y.val ∧ y.val ∣ x.val - r.val ⦄ := by
  unfold core.num.I32.rem_euclid
  have hne : y.val ≠ 0 := by omega
  apply spec_bind (IScalar.rem_spec x hne)
  intro r0 hr0
  have hlow : x.val % y.val < y.val := Int.emod_lt_of_pos _ hy
  have hnn : 0 ≤ x.val % y.val := Int.emod_nonneg _ hne
  have hdef := @Int.tmod_eq_emod x.val y.val
  have hdiv : y.val ∣ x.val - x.val % y.val := by
    have := Int.emod_add_mul_ediv x.val y.val
    exact Dvd.intro (x.val / y.val) (by linarith)
  have hc1 : (0 ≤ x.val ∨ y.val ∣ x.val) → r0.val = x.val % y.val := by
    intro hc; rw [hr0, hdef]; simp [hc]
  have hc2 : ¬ (0 ≤ x.val ∨ y.val ∣ x.val) → r0.val = x.val % y.val - y.val := by
    intro hc; rw [hr0, hdef]; simp [hc, Int.natAbs_of_nonneg (le_of_lt hy)]
  have hy2 := y.hBounds
  split
  · rename_i hneg
    have hcase : r0.val = x.val % y.val - y.val := by
      by_cases hc : (0 ≤ x.val ∨ y.val ∣ x.val)
      · have := hc1 hc; omega
      · exact hc2 hc
    have hb : IScalar.inBounds .I32 (r0.val + (y.val.natAbs : Int)) := by
      rw [Int.natAbs_of_nonneg (le_of_lt hy)]
      have := r0.hBounds
      unfold IScalar.inBounds
      simp only [IScalarTy.numBits] at *
      omega
    have h := IScalar.tryMkOpt_eq .I32 (r0.val + (y.val.natAbs : Int))
    cases hm : IScalar.tryMkOpt .I32 (r0.val + (y.val.natAbs : Int)) with
    | none => rw [hm] at h; exact absurd hb h
    | some z =>
      rw [hm] at h
      have hz := h.1
      rw [Int.natAbs_of_nonneg (le_of_lt hy)] at hz
      have hmk : IScalar.tryMk .I32 (r0.val + (y.val.natAbs : Int)) = ok z := by
        unfold IScalar.tryMk Result.ofOption
        rw [hm]
      rw [hmk, spec_ok]
      refine ⟨by omega, by omega, by omega, ?_⟩
      have : x.val - z.val = x.val - x.val % y.val := by omega
      rw [this]; exact hdiv
  · rename_i hnneg
    rw [spec_ok]
    have hcase : r0.val = x.val % y.val := by
      by_cases hc : (0 ≤ x.val ∨ y.val ∣ x.val)
      · exact hc1 hc
      · have := hc2 hc; omega
    refine ⟨by omega, by omega, by omega, ?_⟩
    have : x.val - r0.val = x.val - x.val % y.val := by omega
    rw [this]; exact hdiv

/-! ### `RangeInclusive::contains` -/

/-- At `i32`, `contains` is `start ≤ item` and then `item < end` once exhausted, else `item ≤ end`. -/
@[step]
theorem range_inclusive_contains_i32_spec
    (self : core.ops.range.RangeInclusive Std.I32) (item : Std.I32) :
    core.ops.range.RangeInclusive.contains core.cmp.PartialOrdI32 core.cmp.PartialOrdI32
      core.cmp.PartialOrdI32 self item ⦃ b =>
      (b = true ↔ self.start.val ≤ item.val ∧
        (if self.exhausted then item.val < self.end.val else item.val ≤ self.end.val)) ⦄ := by
  unfold core.ops.range.RangeInclusive.contains
  simp only [core.cmp.impls.PartialOrdI32.le,
    core.cmp.impls.PartialOrdI32.lt, liftFun2]
  cases hex : self.exhausted <;>
    by_cases h1 : self.start.val ≤ item.val <;> simp [h1, spec_ok]

/-- For a range that is not exhausted (e.g. straight from `RangeInclusive::new`), `contains` is
`start ≤ item ≤ end`. -/
theorem range_inclusive_contains_i32_new (lo hi item : Std.I32) :
    (do
      let r ← core.ops.range.RangeInclusive.new lo hi
      core.ops.range.RangeInclusive.contains core.cmp.PartialOrdI32 core.cmp.PartialOrdI32
        core.cmp.PartialOrdI32 r item) ⦃ b => (b = true ↔ lo.val ≤ item.val ∧ item.val ≤ hi.val) ⦄ := by
  have h : core.ops.range.RangeInclusive.new lo hi = ok ⟨lo, hi, false⟩ := rfl
  rw [h]
  rw [bind_ok]
  refine spec_mono (range_inclusive_contains_i32_spec ⟨lo, hi, false⟩ item) ?_
  intro b hb
  simpa using hb

/-! ### `Option` helpers at `i32`, `u64`, `usize` -/

/-- `Option<&T>::copied` is the identity in the value model. -/
@[simp]
theorem option_copied (T : Type _) (c : core.marker.Copy T) (x : Option T) :
    core.option.OptionShared0T.copied c x = ok x := rfl

/-- `Option::clone` at `i32`. -/
@[simp]
theorem option_clone_i32 (x : Option Std.I32) :
    core.option.Option.Insts.CoreCloneClone.clone core.clone.CloneI32 x = ok x := by
  cases x <;> simp [core.option.Option.Insts.CoreCloneClone.clone, liftFun1]

/-- `Option::clone` at `u64`. -/
@[simp]
theorem option_clone_u64 (x : Option Std.U64) :
    core.option.Option.Insts.CoreCloneClone.clone core.clone.CloneU64 x = ok x := by
  cases x <;> simp [core.option.Option.Insts.CoreCloneClone.clone, liftFun1]

/-- `Option::clone` at `usize`. -/
@[simp]
theorem option_clone_usize (x : Option Std.Usize) :
    core.option.Option.Insts.CoreCloneClone.clone core.clone.CloneUsize x = ok x := by
  cases x <;> simp [core.option.Option.Insts.CoreCloneClone.clone, liftFun1]

/-- `Option::eq` is equality whenever the payload `eq` is (its spec is `b ↔ a = b`). -/
theorem option_eq_spec {T : Type _} (inst : core.cmp.PartialEq T T)
    (heq : ∀ a b : T, inst.eq a b ⦃ r => (r = true ↔ a = b) ⦄) (x y : Option T) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq inst x y ⦃ r => (r = true ↔ x = y) ⦄ := by
  unfold core.option.Option.Insts.CoreCmpPartialEqOption.eq
  cases x <;> cases y <;> simp_all [spec_ok]

/-- `Option::eq` at `i32`. -/
@[step]
theorem option_eq_i32_spec (x y : Option Std.I32) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq core.cmp.PartialEqI32 x y
      ⦃ r => (r = true ↔ x = y) ⦄ :=
  option_eq_spec _ (fun a b => by
    simp only [core.cmp.impls.PartialEqI32.eq, liftFun2, spec_ok]
    simp) x y

/-- `Option::eq` at `u64`. -/
@[step]
theorem option_eq_u64_spec (x y : Option Std.U64) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq core.cmp.PartialEqU64 x y
      ⦃ r => (r = true ↔ x = y) ⦄ :=
  option_eq_spec _ (fun a b => by
    simp only [core.cmp.impls.PartialEqU64.eq, liftFun2, spec_ok]
    simp) x y

/-- `Option::eq` at `usize`. -/
@[step]
theorem option_eq_usize_spec (x y : Option Std.Usize) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq core.cmp.PartialEqUsize x y
      ⦃ r => (r = true ↔ x = y) ⦄ :=
  option_eq_spec _ (fun a b => by
    simp only [core.cmp.impls.PartialEqUsize.eq, liftFun2, spec_ok]
    simp) x y

/-! ### `Vec::clear` -/

/-- `clear` returns the empty vector. -/
@[step]
theorem vec_clear_spec {T : Type _} (A : Type _) (v : alloc.vec.Vec T) :
    alloc.vec.Vec.clear A v ⦃ r => r.val = [] ⦄ := by
  unfold alloc.vec.Vec.clear
  simp [spec_ok, alloc.vec.Vec.new]

/-! ### `i32` division -/

/-- Signed division truncates toward zero; it fails exactly on `0` and on `MIN / -1`. -/
@[step]
theorem i32_div_spec (x y : Std.I32) (hy : y.val ≠ 0)
    (hov : ¬ (x.val = IScalar.min .I32 ∧ y.val = -1)) :
    Std.I32.div x y ⦃ r => r.val = Int.tdiv x.val y.val ⦄ := by
  unfold Std.I32.div
  obtain ⟨z, hz, hv⟩ := IScalar.div_spec (x := x) (y := y) hy hov
  simp only [HDiv.hDiv] at hz
  rw [hz, spec_ok]; exact hv

/-- The two divisions of the turn constant that the arc code performs. -/
theorem i32_div_turn_eight : Std.I32.div polar.TURN 8#i32 ⦃ r => r.val = 512 ⦄ := by
  apply spec_mono (i32_div_spec polar.TURN 8#i32 (by simp) (by simp [polar.TURN]))
  intro r hr
  rw [hr]; simp [polar.TURN]

theorem i32_div_turn_four : Std.I32.div polar.TURN 4#i32 ⦃ r => r.val = 1024 ⦄ := by
  apply spec_mono (i32_div_spec polar.TURN 4#i32 (by simp) (by simp [polar.TURN]))
  intro r hr
  rw [hr]; simp [polar.TURN]

/-! ### `Option` `Debug::fmt` -/

/-- `None` forwards to writing the name `None`. -/
@[simp]
theorem option_debug_fmt_none {T : Type _} (d : core.fmt.Debug T) (f : core.fmt.Formatter) :
    core.option.Option.Insts.CoreFmtDebug.fmt d none f =
      core.fmt.Formatter.write_str f
        (Slice.from (α := U8) [⟨78⟩, ⟨111⟩, ⟨110⟩, ⟨101⟩] (by scalar_tac)) := rfl

/-- `Some p` forwards to a one-field tuple named `Some` holding `p`. -/
@[simp]
theorem option_debug_fmt_some {T : Type _} (d : core.fmt.Debug T) (p : T)
    (f : core.fmt.Formatter) :
    core.option.Option.Insts.CoreFmtDebug.fmt d (some p) f =
      core.fmt.Formatter.debug_tuple_field1_finish f
        (Slice.from (α := U8) [⟨83⟩, ⟨111⟩, ⟨109⟩, ⟨101⟩] (by scalar_tac))
        (Dyn.mk T d p) := rfl

/-! ### `Slice::contains` -/

/-- `contains` finds `x` exactly when some element is `eq`-equal to it; with an `eq` that decides
equality this is list membership. -/
theorem slice_contains_spec {T : Type _} (inst : core.cmp.PartialEq T T)
    (heq : ∀ a b : T, inst.eq a b ⦃ r => (r = true ↔ a = b) ⦄) (s : Slice T) (x : T) :
    core.slice.Slice.contains inst s x ⦃ b => (b = true ↔ x ∈ s.val) ⦄ := by
  unfold core.slice.Slice.contains
  have hp : ∀ b : Bool, (pure b : Result Bool) = ok b := fun _ => rfl
  generalize s.val = l
  induction l with
  | nil =>
    rw [List.anyM_nil, hp]
    simp [spec_ok]
  | cons a l ih =>
    rw [List.anyM_cons]
    apply spec_bind (heq x a)
    intro r hr
    cases r
    · simp only [Bool.false_eq_true, false_iff] at hr
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply spec_mono ih
      intro b hb
      simp only [hb]
      refine ⟨fun h => List.mem_cons_of_mem a h, fun h => ?_⟩
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd rfl hr
      · exact h
    · simp only [true_iff] at hr
      simp only [↓reduceIte, hp]
      simp [spec_ok, hr]

/-- `Edge` equality is componentwise equality. -/
theorem edge_eq_spec (a b : topology.Edge) :
    topology.Edge.Insts.CoreCmpPartialEqEdge.eq a b ⦃ r => (r = true ↔ a = b) ⦄ := by
  unfold topology.Edge.Insts.CoreCmpPartialEqEdge.eq
  obtain ⟨au, av⟩ := a
  obtain ⟨bu, bv⟩ := b
  by_cases hu : au = bu <;> by_cases hv : av = bv <;> simp_all [spec_ok]

/-- `Slice<Edge>::contains` is membership of the edge in the slice's list. -/
@[step]
theorem slice_contains_edge_spec (s : Slice topology.Edge) (x : topology.Edge) :
    core.slice.Slice.contains topology.Edge.Insts.CoreCmpPartialEqEdge s x
      ⦃ b => (b = true ↔ x ∈ s.val) ⦄ :=
  slice_contains_spec _ edge_eq_spec s x

/-! ### `Option::ok_or` and `Result::is_err` -/

/-- `ok_or` maps `Some v` to `Ok v` and `None` to `Err e`. -/
@[step]
theorem option_ok_or_spec {T E : Type _} (x : Option T) (e : E) :
    core.option.Option.ok_or x e ⦃ r =>
      (∀ v, x = some v → r = .Ok v) ∧ (x = none → r = .Err e) ⦄ := by
  cases x <;> simp [spec_ok]

/-- `ok_or` produces an `Ok` exactly when the option is `Some`. -/
theorem option_ok_or_is_ok {T E : Type _} (x : Option T) (e : E) :
    core.option.Option.ok_or x e ⦃ r => r.ok? = x.isSome ⦄ := by
  cases x <;> simp [spec_ok]

/-- `is_err` is the negation of `is_ok`. -/
@[step]
theorem result_is_err_spec {T E : Type _} (r : core.result.Result T E) :
    core.result.Result.is_err r ⦃ b => b = !r.ok? ⦄ := by
  unfold core.result.Result.is_err
  apply spec_bind (core.result.Result.is_ok.step_spec r)
  intro b hb
  simp [spec_ok, hb]

end Labyrinth
