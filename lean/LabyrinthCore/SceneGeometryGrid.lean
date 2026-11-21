module
public import LabyrinthCore.SceneStd
import all Aeneas.Std.Scalar.CheckedOps.Add
import all Aeneas.Std.Scalar.CheckedOps.Sub
import all Aeneas.Std.Scalar.EqOrd

/-! Geometry totality (S8), grid layer. Every `grid.*` function the scene geometry reaches returns
(`ok`) under the stated precondition; the preconditions are the checks the Rust validators
(`Point::validate`, `Rect::validate`, `Geometry::validate`/`margin`) establish: coordinates in
`[-COORD_LIMIT, COORD_LIMIT]`, strictly ordered rectangle corners, and a margin
`walker_radius + clearance + 2 ≤ COORD_LIMIT`. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Labyrinth

theorem coord_limit_val : grid.COORD_LIMIT.val = 1000000 := by
  simp [grid.COORD_LIMIT]

def PointOk (p : grid.Point) : Prop :=
  -1000000 ≤ p.x.val ∧ p.x.val ≤ 1000000 ∧ -1000000 ≤ p.y.val ∧ p.y.val ≤ 1000000

/-- `RectOk` on bare coordinates. -/
def RectOkV (x0 y0 x1 y1 : Int) : Prop :=
  (-1000000 ≤ x0 ∧ x0 ≤ 1000000 ∧ -1000000 ≤ y0 ∧ y0 ≤ 1000000) ∧
  (-1000000 ≤ x1 ∧ x1 ≤ 1000000 ∧ -1000000 ≤ y1 ∧ y1 ≤ 1000000) ∧ x0 < x1 ∧ y0 < y1

/-- A rectangle is valid when both corners are valid points and `min < max` on both axes
(`Rect::validate`). -/
def RectOk (r : grid.Rect) : Prop :=
  PointOk r.min ∧ PointOk r.max ∧ r.min.x.val < r.max.x.val ∧ r.min.y.val < r.max.y.val

theorem rectOk_iff (r : grid.Rect) :
    RectOk r ↔ RectOkV r.min.x.val r.min.y.val r.max.x.val r.max.y.val := by
  simp only [RectOk, RectOkV, PointOk]

/-- Truncating division by two, as linear facts for the arithmetic tactics. -/
@[scalar_tac Int.tdiv x 2]
theorem int_tdiv_two_facts (x : Int) :
    (0 ≤ x → 2 * x.tdiv 2 ≤ x ∧ x ≤ 2 * x.tdiv 2 + 1) ∧
    (x ≤ 0 → x ≤ 2 * x.tdiv 2 ∧ 2 * x.tdiv 2 ≤ x + 1) := by
  have h2 := @Int.tdiv_eq_ediv x 2
  constructor <;> intro h
  · rw [Int.tdiv_eq_ediv_of_nonneg h]; omega
  · by_cases hd : (2:Int) ∣ x
    · have h0 : (if (0 ≤ x ∨ (2:Int) ∣ x) then (0:Int) else Int.sign 2) = 0 := by simp [hd]
      rw [h2, h0]; omega
    · have hs : Int.sign 2 = 1 := by decide
      have hx : x < 0 := by
        have : x ≠ 0 := fun hx0 => hd (hx0 ▸ dvd_zero 2)
        omega
      have hn : ¬ (0 ≤ x ∨ (2:Int) ∣ x) := by
        rintro (hh | hh)
        · omega
        · exact hd hh
      have h0 : (if (0 ≤ x ∨ (2:Int) ∣ x) then (0:Int) else Int.sign 2) = 1 := by
        simp only [hn, ↓reduceIte, hs]
      rw [h2, h0]; omega

@[step]
theorem grid_point_validate_spec (p : grid.Point) :
    grid.Point.validate p ⦃ r =>
      (r = .Ok () ↔ PointOk p) ∧ (r ≠ .Ok () → r = .Err topology.Error.InvalidGeometry) ⦄ := by
  unfold grid.Point.validate
  step as ⟨i, hi⟩
  · have := coord_limit_val; scalar_tac
  have hc := coord_limit_val
  unfold PointOk
  split_ifs <;> simp only [spec_ok] <;> simp <;> scalar_tac

theorem spec_exists_ok {α : Type _} {m : Result α} {P : α → Prop} (h : spec m P) :
    ∃ v, m = ok v ∧ P v := by
  cases m using Result.cases with
  | ret r => exact ⟨r, rfl, (spec_ok r).mp h⟩
  | vis i k => exact absurd h (by rw [spec_vis]; exact id)
  | div => exact absurd h (by simp)

theorem grid_rect_validate_spec (r : grid.Rect) :
    grid.Rect.validate r ⦃ x =>
      (x = .Ok () ↔ RectOk r) ∧ (x ≠ .Ok () → x = .Err topology.Error.InvalidGeometry) ⦄ := by
  unfold grid.Rect.validate
  obtain ⟨r1, hr1, h1, h1'⟩ := spec_exists_ok (grid_point_validate_spec r.min)
  obtain ⟨r2, hr2, h2, h2'⟩ := spec_exists_ok (grid_point_validate_spec r.max)
  rw [hr1]
  cases r1 with
  | Err e =>
    have := h1' (by simp)
    simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, spec_ok, RectOk]
  | Ok u =>
    rw [hr2]
    cases r2 with
    | Err e =>
      have := h2' (by simp)
      simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, spec_ok, RectOk]
    | Ok u2 =>
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      unfold RectOk
      split_ifs <;> simp only [spec_ok] <;> simp_all

theorem i32_checked_add_cases (x y : Std.I32) :
    (I32.checked_add x y = none ∧ ¬ (-2147483648 ≤ x.val + y.val ∧ x.val + y.val ≤ 2147483647)) ∨
    ∃ z, I32.checked_add x y = some z ∧ z.val = x.val + y.val := by
  have h := I32.checked_add_bv_spec x y
  cases hc : I32.checked_add x y with
  | none => 
    left; refine ⟨rfl, ?_⟩
    have hc' : core.num.checked_add_IScalar x y = none := hc
    rw [hc'] at h
    simp [I32.min, I32.max, IScalar.min, IScalar.max, IScalarTy.numBits, I32.numBits] at h
    omega
  | some z =>
    right; refine ⟨z, rfl, ?_⟩
    have hc' : core.num.checked_add_IScalar x y = some z := hc
    rw [hc'] at h
    exact h.2.2.1

theorem i32_checked_sub_cases (x y : Std.I32) :
    (I32.checked_sub x y = none ∧ ¬ (-2147483648 ≤ x.val - y.val ∧ x.val - y.val ≤ 2147483647)) ∨
    ∃ z, I32.checked_sub x y = some z ∧ z.val = x.val - y.val := by
  have h := I32.checked_sub_bv_spec x y
  cases hc : I32.checked_sub x y with
  | none => 
    left; refine ⟨rfl, ?_⟩
    have hc' : core.num.checked_sub_IScalar x y = none := hc
    rw [hc'] at h
    simp [I32.min, I32.max, IScalar.min, IScalar.max, IScalarTy.numBits, I32.numBits] at h
    omega
  | some z =>
    right; refine ⟨z, rfl, ?_⟩
    have hc' : core.num.checked_sub_IScalar x y = some z := hc
    rw [hc'] at h
    exact h.2.2.1

/-- The margin is defined exactly when the radius is positive, the clearance is not negative and
`walker_radius + clearance + 2` stays within the coordinate limit. -/
def MarginOk (g : grid.Geometry) : Prop :=
  0 < g.walker_radius.val ∧ 0 ≤ g.clearance.val ∧
    g.walker_radius.val + g.clearance.val + 2 ≤ 1000000

theorem grid_geometry_margin_spec (g : grid.Geometry) :
    grid.Geometry.margin g ⦃ r =>
      (∀ m, r = .Ok m → MarginOk g ∧ m.val = g.walker_radius.val + g.clearance.val + 2) ∧
      (MarginOk g → ∃ m, r = .Ok m) ∧
      (∀ e, r = .Err e → e = .InvalidGeometry ∨ e = .Overflow) ⦄ := by
  unfold grid.Geometry.margin
  have hc := coord_limit_val
  have hw := g.walker_radius.hBounds
  have hl := g.clearance.hBounds
  unfold MarginOk
  split_ifs with h1 h2
  · simp; intro a b; scalar_tac
  · simp; intro a b; scalar_tac
  · simp only [lift, Std.bind_ok]
    rcases i32_checked_add_cases g.walker_radius g.clearance with ⟨hn, hr⟩ | ⟨z, hz, hzv⟩
    · rw [hn]
      simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, spec_ok]
      scalar_tac
    · rw [hz]
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      rcases i32_checked_add_cases z 2#i32 with ⟨hn2, hr2⟩ | ⟨z2, hz2, hz2v⟩
      · rw [hn2]
        simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, spec_ok]
        scalar_tac
      · rw [hz2]
        simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
        split_ifs with h3 <;> simp [spec_ok] <;> scalar_tac

theorem grid_rect_contains_spec (a b : grid.Rect) :
    grid.Rect.contains a b ⦃ r => (r = true ↔ a.min.x.val ≤ b.min.x.val ∧ a.min.y.val ≤ b.min.y.val ∧
      b.max.x.val ≤ a.max.x.val ∧ b.max.y.val ≤ a.max.y.val) ⦄ := by
  unfold grid.Rect.contains
  split_ifs <;> simp [spec_ok] <;> scalar_tac

@[step]
theorem grid_rect_union_spec (a b : grid.Rect) :
    grid.Rect.union a b ⦃ r =>
      r.min.x.val = min a.min.x.val b.min.x.val ∧ r.min.y.val = min a.min.y.val b.min.y.val ∧
      r.max.x.val = max a.max.x.val b.max.x.val ∧ r.max.y.val = max a.max.y.val b.max.y.val ⦄ := by
  unfold grid.Rect.union
  step*

theorem grid_rect_intersects_spec (a b : grid.Rect) :
    grid.Rect.intersects a b ⦃ r => (r = true ↔ a.min.x.val ≤ b.max.x.val ∧ b.min.x.val ≤ a.max.x.val ∧
      a.min.y.val ≤ b.max.y.val ∧ b.min.y.val ≤ a.max.y.val) ⦄ := by
  unfold grid.Rect.intersects
  split_ifs <;> simp [spec_ok] <;> scalar_tac

theorem i32_val_bounds (x : Std.I32) : -2147483648 ≤ x.val ∧ x.val ≤ 2147483647 := by
  have := x.hBounds
  simp [IScalarTy.numBits, I32.numBits] at this
  omega

theorem grid_rect_expand_spec (r : grid.Rect) (m : Std.I32) :
    grid.Rect.expand r m ⦃ x =>
      (∀ e, x = .Ok e → 0 ≤ m.val ∧ e.min.x.val = r.min.x.val - m.val ∧
        e.min.y.val = r.min.y.val - m.val ∧ e.max.x.val = r.max.x.val + m.val ∧
        e.max.y.val = r.max.y.val + m.val ∧ RectOk e) ∧
      (0 ≤ m.val → RectOkV (r.min.x.val - m.val) (r.min.y.val - m.val) (r.max.x.val + m.val)
        (r.max.y.val + m.val) → ∃ e, x = .Ok e) ∧
      (∀ e, x = .Err e → e = .InvalidGeometry ∨ e = .Overflow) ∧
      (-1000000000 ≤ r.min.x.val → r.max.x.val ≤ 1000000000 → -1000000000 ≤ r.min.y.val →
        r.max.y.val ≤ 1000000000 → m.val ≤ 1000000000 →
        ∀ e, x = .Err e → e = .InvalidGeometry) ⦄ := by
  unfold grid.Rect.expand
  have h1 := i32_val_bounds r.min.x
  have h2 := i32_val_bounds r.min.y
  have h3 := i32_val_bounds r.max.x
  have h4 := i32_val_bounds r.max.y
  have h5 := i32_val_bounds m
  split_ifs with hm
  · simp [spec_ok]; scalar_tac
  · have hm0 : 0 ≤ m.val := by scalar_tac
    simp only [lift, Std.bind_ok]
    rcases i32_checked_sub_cases r.min.x m with ⟨hn, hr⟩ | ⟨z1, hz1, hz1v⟩
    · rw [hn]
      simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, spec_ok]
      unfold RectOkV; scalar_tac
    simp only [hz1, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    rcases i32_checked_sub_cases r.min.y m with ⟨hn, hr⟩ | ⟨z2, hz2, hz2v⟩
    · rw [hn]
      simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, spec_ok]
      unfold RectOkV; scalar_tac
    simp only [hz2, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    rcases i32_checked_add_cases r.max.x m with ⟨hn, hr⟩ | ⟨z3, hz3, hz3v⟩
    · rw [hn]
      simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, spec_ok]
      unfold RectOkV; scalar_tac
    simp only [hz3, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    rcases i32_checked_add_cases r.max.y m with ⟨hn, hr⟩ | ⟨z4, hz4, hz4v⟩
    · rw [hn]
      simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, spec_ok]
      unfold RectOkV; scalar_tac
    simp only [hz4, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    obtain ⟨v, hv, hv1, hv2⟩ := spec_exists_ok (grid_rect_validate_spec
      { min := { x := z1, y := z2 }, max := { x := z3, y := z4 } })
    rw [hv]
    cases v with
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, spec_ok]
      have hok := hv1.mp rfl
      rw [rectOk_iff] at hok
      unfold RectOkV at hok
      simp only at hok
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro e he
        cases he
        refine ⟨hm0, ?_, ?_, ?_, ?_, hv1.mp rfl⟩ <;> simp only <;> omega
      · intro _ _; exact ⟨_, rfl⟩
      · intro e he; cases he
      · intro _ _ _ _ _ e he; cases he
    | Err e =>
      have he : e = topology.Error.InvalidGeometry := by
        have := hv2 (by simp)
        injection this
      subst he
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, spec_ok]
      have hnot : ¬ RectOk { min := { x := z1, y := z2 }, max := { x := z3, y := z4 } } := by
        intro h; exact absurd (hv1.mpr h) (by simp)
      rw [rectOk_iff] at hnot
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro e he; cases he
      · intro hm0 hv; exfalso; apply hnot; simp only; scalar_tac
      · intro e he; cases he; simp
      · intro _ _ _ _ _ e he; cases he; rfl

theorem grid_rect_between_spec (a b : grid.Point) (m : Std.I32) :
    grid.Rect.between a b m ⦃ x =>
      (∀ e, x = .Ok e → 0 < m.val ∧ RectOk e ∧ e.min.x.val = min a.x.val b.x.val - m.val ∧
        e.min.y.val = min a.y.val b.y.val - m.val ∧ e.max.x.val = max a.x.val b.x.val + m.val ∧
        e.max.y.val = max a.y.val b.y.val + m.val) ∧
      (∀ e, x = .Err e → e = .InvalidGeometry ∨ e = .Overflow) ∧
      (PointOk a → PointOk b → m.val ≤ 1000000000 → ∀ e, x = .Err e → e = .InvalidGeometry) ⦄ := by
  unfold grid.Rect.between
  split_ifs with hm
  · simp [spec_ok]
  · simp only [lift, Std.bind_ok]
    have h := grid_rect_expand_spec
      { min := { x := core.cmp.impls.OrdI32.min a.x b.x, y := core.cmp.impls.OrdI32.min a.y b.y },
        max := { x := core.cmp.impls.OrdI32.max a.x b.x, y := core.cmp.impls.OrdI32.max a.y b.y } } m
    apply spec_mono h
    rintro x ⟨h1, h2, h3, h4⟩
    refine ⟨?_, h3, ?_⟩
    · intro e he
      obtain ⟨hm0, e1, e2, e3, e4, e5⟩ := h1 e he
      refine ⟨by scalar_tac, e5, ?_, ?_, ?_, ?_⟩ <;> simp_all
    · intro ha hb hm2 e he
      apply h4 _ _ _ _ _ e he <;> simp [PointOk] at * <;> omega

/-- Rectangle intersection (closed) as a proposition. -/
def RectMeets (a b : grid.Rect) : Prop :=
  a.min.x.val ≤ b.max.x.val ∧ b.min.x.val ≤ a.max.x.val ∧
    a.min.y.val ≤ b.max.y.val ∧ b.min.y.val ≤ a.max.y.val

/-- Closed rectangle containment as a proposition. -/
def RectHolds (a b : grid.Rect) : Prop :=
  a.min.x.val ≤ b.min.x.val ∧ a.min.y.val ≤ b.min.y.val ∧
    b.max.x.val ≤ a.max.x.val ∧ b.max.y.val ≤ a.max.y.val

theorem grid_geometry_check_loop_spec (v : alloc.vec.Vec grid.Rect) (swept : grid.Rect)
    (blocked : Bool) (i : Std.Usize) :
    grid.Geometry.check_loop v swept blocked i ⦃ r =>
      (r = true ↔ blocked = true ∨ ∃ j, i.val ≤ j ∧ ∃ h : j < v.val.length,
        RectMeets swept v.val[j]) ⦄ := by
  unfold grid.Geometry.check_loop
  apply loop.spec_decr_nat
    (fun state : Bool × Std.Usize => v.val.length - state.2.val)
    (fun state : Bool × Std.Usize => 
      (blocked = true ∨ ∃ j, i.val ≤ j ∧ ∃ h : j < v.val.length, RectMeets swept v.val[j]) ↔
      (state.1 = true ∨ ∃ j, state.2.val ≤ j ∧ ∃ h : j < v.val.length, RectMeets swept v.val[j]))
    _
  · rintro ⟨bl, j⟩ hinv
    dsimp only at hinv ⊢
    unfold grid.Geometry.check_loop.body
    by_cases hlt : j.val < v.val.length
    · have hlt' : j < alloc.vec.Vec.len v := by simpa [alloc.vec.Vec.len] using hlt
      simp only [hlt', ite_true]
      by_cases hb : bl = true
      · simp only [hb, ite_true, spec_ok]
        simpa [hb] using hinv
      · simp only [hb, ite_false]
        apply spec_bind (alloc.vec.Vec.index_usize_spec v j hlt)
        intro r hr
        apply spec_bind (grid_rect_intersects_spec swept r)
        intro b hb2
        apply spec_bind (Usize.add_spec (x := j) (y := 1#usize) (by scalar_tac))
        intro n hn
        simp only [spec_ok]
        have hnv : n.val = j.val + 1 := by simpa using hn
        refine ⟨?_, by omega⟩
        have hb' : bl = false := by simpa using hb
        subst hb'
        have hmeets : b = true ↔ RectMeets swept v.val[j.val] := by
          rw [hb2, hr]; exact Iff.rfl
        rw [hinv]
        simp only [Bool.false_eq_true, false_or, hnv]
        constructor
        · rintro ⟨k, hk, hkl, hm⟩
          by_cases hkj : k = j.val
          · subst hkj; left; exact hmeets.mpr hm
          · right; exact ⟨k, by omega, hkl, hm⟩
        · rintro (hbt | ⟨k, hk, hkl, hm⟩)
          · exact ⟨j.val, le_refl _, hlt, hmeets.mp hbt⟩
          · exact ⟨k, by omega, hkl, hm⟩
    · have hlt' : ¬ j < alloc.vec.Vec.len v := by simpa [alloc.vec.Vec.len] using hlt
      simp only [hlt', ite_false, spec_ok]
      rw [hinv]
      constructor
      · intro h; exact Or.inl h
      · intro h
        rcases h with h | ⟨k, hk, hkl, _⟩
        · exact h
        · exact absurd (lt_of_le_of_lt (by omega) hkl) (by omega)
  · exact Iff.rfl

theorem grid_geometry_check_spec (g : grid.Geometry) (swept : grid.Rect) :
    grid.Geometry.check g swept ⦃ x =>
      (x = .Ok () ↔ RectOk swept ∧ RectHolds g.viewport swept ∧
        ∀ k, ∀ h : k < g.obstacles.val.length, ¬ RectMeets swept g.obstacles.val[k]) ∧
      (x ≠ .Ok () → x = .Err topology.Error.InvalidGeometry) ⦄ := by
  unfold grid.Geometry.check
  obtain ⟨v, hv, hv1, hv2⟩ := spec_exists_ok (grid_rect_validate_spec swept)
  rw [hv]
  cases v with
  | Err e =>
    have he : e = topology.Error.InvalidGeometry := by
      have := hv2 (by simp)
      injection this
    subst he
    have hnot : ¬ RectOk swept := fun h => by simpa using hv1.mpr h
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, spec_ok, hnot]
  | Ok u =>
    have hok := hv1.mp rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    apply spec_bind (grid_rect_contains_spec g.viewport swept)
    intro b hb
    split_ifs with hbt
    · apply spec_bind (grid_geometry_check_loop_spec g.obstacles swept false 0#usize)
      intro bl hbl
      split_ifs with hbl'
      · simp only [spec_ok]
        refine ⟨?_, by simp⟩
        simp only [reduceCtorEq, false_iff, not_and]
        intro _ _ hall
        have := hbl.mp hbl'
        simp at this
        obtain ⟨k, hk, hm⟩ := this
        exact hall k hk hm
      · simp only [spec_ok]
        refine ⟨?_, by simp⟩
        simp only [true_iff]
        refine ⟨hok, hb.mp hbt, ?_⟩
        intro k hk hm
        apply hbl'
        apply hbl.mpr
        right; exact ⟨k, by simp, hk, hm⟩
    · simp only [spec_ok]
      refine ⟨?_, by simp⟩
      simp only [reduceCtorEq, false_iff, not_and]
      intro _ hh; exact absurd (hb.mpr hh) hbt

theorem grid_geometry_validate_loop_spec (v : alloc.vec.Vec grid.Rect)
    (status : core.result.Result Unit topology.Error) (i : Std.Usize)
    (hs : status = .Ok () ∨ status = .Err topology.Error.InvalidGeometry) :
    grid.Geometry.validate_loop v status i ⦃ x =>
      (x = .Ok () ↔ status = .Ok () ∧ ∀ k, i.val ≤ k → ∀ h : k < v.val.length, RectOk v.val[k]) ∧
      (x ≠ .Ok () → x = .Err topology.Error.InvalidGeometry) ⦄ := by
  unfold grid.Geometry.validate_loop
  apply loop.spec_decr_nat
    (fun state : core.result.Result Unit topology.Error × Std.Usize => v.val.length - state.2.val)
    (fun state : core.result.Result Unit topology.Error × Std.Usize =>
      (state.1 = .Ok () ∨ state.1 = .Err topology.Error.InvalidGeometry) ∧
      ((status = .Ok () ∧ ∀ k, i.val ≤ k → ∀ h : k < v.val.length, RectOk v.val[k]) ↔
        (state.1 = .Ok () ∧ ∀ k, state.2.val ≤ k → ∀ h : k < v.val.length, RectOk v.val[k])))
    _
  · rintro ⟨st, j⟩ ⟨hst, hinv⟩
    dsimp only at hst hinv ⊢
    unfold grid.Geometry.validate_loop.body
    by_cases hlt : j.val < v.val.length
    · have hlt' : j < alloc.vec.Vec.len v := by simpa [alloc.vec.Vec.len] using hlt
      simp only [hlt', ite_true]
      apply spec_bind (core.result.Result.is_ok.step_spec st)
      intro b hb
      by_cases hbt : b = true
      · simp only [hbt, ite_true]
        apply spec_bind (alloc.vec.Vec.index_usize_spec v j hlt)
        intro r hr
        apply spec_bind (grid_rect_validate_spec r)
        intro st2 ⟨hst2, hst2'⟩
        apply spec_bind (Usize.add_spec (x := j) (y := 1#usize) (by scalar_tac))
        intro n hn
        simp only [spec_ok]
        have hnv : n.val = j.val + 1 := by simpa using hn
        have hstok : st = .Ok () := by
          cases st with
          | Ok u => rfl
          | Err e => simp [hbt] at hb
        refine ⟨⟨?_, ?_⟩, by omega⟩
        · by_cases h : st2 = .Ok ()
          · exact Or.inl h
          · exact Or.inr (hst2' h)
        · rw [hinv, hstok]
          simp only [true_and, hnv]
          constructor
          · intro hall
            refine ⟨hst2.mpr (by rw [hr]; exact hall j.val (le_refl _) hlt), ?_⟩
            intro k hk hkl
            exact hall k (by omega) hkl
          · rintro ⟨h1, hall⟩ k hk hkl
            by_cases hkj : k = j.val
            · subst hkj
              have := hst2.mp h1
              rw [hr] at this
              exact this
            · exact hall k (by omega) hkl
      · have hbf : b = false := by simpa using hbt
        simp only [hbf, Bool.false_eq_true, ↓reduceIte, spec_ok]
        have hstok : st = .Err topology.Error.InvalidGeometry := by
          cases st with
          | Ok u => simp at hb; exact absurd hb hbt
          | Err e => rcases hst with h | h <;> simp_all
        subst hstok
        refine ⟨?_, by simp⟩
        simp only [reduceCtorEq, false_and, iff_false] at hinv
        constructor
        · intro h; cases h
        · intro h; exact absurd h hinv
    · have hlt' : ¬ j < alloc.vec.Vec.len v := by simpa [alloc.vec.Vec.len] using hlt
      simp only [hlt', ite_false, spec_ok]
      refine ⟨?_, ?_⟩
      · rw [hinv]
        constructor
        · intro h; exact ⟨h, fun k hk hkl => absurd hkl (by omega)⟩
        · exact fun h => h.1
      · intro h
        rcases hst with h' | h'
        · exact absurd h' h
        · exact h'
  · exact ⟨hs, Iff.rfl⟩

theorem grid_geometry_validate_spec (g : grid.Geometry) :
    grid.Geometry.validate g ⦃ x =>
      (x = .Ok () ↔ RectOk g.viewport ∧ MarginOk g ∧
        ∀ k, ∀ h : k < g.obstacles.val.length, RectOk g.obstacles.val[k]) ∧
      (x ≠ .Ok () → x = .Err topology.Error.InvalidGeometry ∨ x = .Err topology.Error.Overflow) ⦄ := by
  unfold grid.Geometry.validate
  obtain ⟨v, hv, hv1, hv2⟩ := spec_exists_ok (grid_rect_validate_spec g.viewport)
  rw [hv]
  cases v with
  | Err e =>
    have he : e = topology.Error.InvalidGeometry := by
      have := hv2 (by simp)
      injection this
    subst he
    have hnot : ¬ RectOk g.viewport := fun h => by simpa using hv1.mpr h
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, spec_ok, hnot]
  | Ok u =>
    have hok := hv1.mp rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    by_cases hw : g.walker_radius ≤ 0#i32
    · simp only [hw, ite_true, spec_ok]
      refine ⟨?_, by simp⟩
      simp only [reduceCtorEq, false_iff, not_and]
      intro _ hm; unfold MarginOk at hm; scalar_tac
    · simp only [hw, ite_false]
      by_cases hc : g.clearance < 0#i32
      · simp only [hc, ite_true, spec_ok]
        refine ⟨?_, by simp⟩
        simp only [reduceCtorEq, false_iff, not_and]
        intro _ hm; unfold MarginOk at hm; scalar_tac
      · simp only [hc, ite_false]
        obtain ⟨r, hr, hr1, hr2, hr3⟩ := spec_exists_ok (grid_geometry_margin_spec g)
        rw [hr]
        cases r with
        | Err e =>
          have hnot : ¬ MarginOk g := fun h => by
            obtain ⟨m, hm⟩ := hr2 h
            cases hm
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, Std.bind_ok, spec_ok]
          have := hr3 e rfl
          refine ⟨?_, ?_⟩
          · simp [hnot]
          · intro _; rcases this with h | h <;> simp [h]
        | Ok m =>
          have hm := (hr1 m rfl).1
          simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
          apply spec_mono (grid_geometry_validate_loop_spec g.obstacles (.Ok ()) 0#usize (Or.inl rfl))
          rintro x ⟨h1, h2⟩
          refine ⟨?_, fun h => Or.inl (h2 h)⟩
          rw [h1]
          simp only [true_and, zero_le, forall_const, hok, hm]
          simp

/-- `Rect::center` on a valid rectangle returns a valid point inside it. -/
theorem grid_rect_center_spec (r : grid.Rect) (h : RectOk r) :
    grid.Rect.center r ⦃ p => PointOk p ∧ r.min.x.val ≤ p.x.val ∧ p.x.val ≤ r.max.x.val ∧
      r.min.y.val ≤ p.y.val ∧ p.y.val ≤ r.max.y.val ⦄ := by
  rw [rectOk_iff] at h
  unfold RectOkV at h
  unfold grid.Rect.center
  step*
  all_goals (try simp only [PointOk])
  all_goals scalar_tac

/-- `i32::clamp` returns exactly when the bounds are ordered, and then lands in them. -/
@[step]
theorem i32_clamp_spec (x lo hi : Std.I32) (h : lo.val ≤ hi.val) :
    core.cmp.impls.OrdI32.clamp x lo hi ⦃ r => lo.val ≤ r.val ∧ r.val ≤ hi.val ∧
      (lo.val ≤ x.val → x.val ≤ hi.val → r = x) ⦄ := by
  unfold core.cmp.impls.OrdI32.clamp IScalar.clamp
  have hm : massert (lo.val ≤ hi.val) = ok () := (massert_ok _).mpr h
  rw [hm]
  split_ifs with h1 h2 <;> simp only [bind_tc_ok, Std.bind_ok, spec_ok] <;> refine ⟨?_, ?_, ?_⟩ <;> intros <;> first | omega | rfl | trivial

end Labyrinth
