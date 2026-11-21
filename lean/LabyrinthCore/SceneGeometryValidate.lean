module
public import LabyrinthCore.SceneGeometryDoorway
import all Aeneas.Std.Scalar.CheckedOps.Mul

/-! Geometry totality (S8), the validator link: a layout accepted by `Layout::new` satisfies
`LayoutGeom`. The statements are partial correctness (`OkPost`): they describe every layout
`Layout::new` returns, which is what makes `LayoutGeom` a consequence of validation rather than an
assumption. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

/-! ### Partial-correctness helpers -/

theorem okPost_spec {α β : Type _} {m : Result α} {k : α → Result β} {P : α → Prop}
    {Q : β → Prop} (hm : m ⦃ P ⦄) (hk : ∀ a, P a → OkPost (k a) Q) :
    OkPost (Std.bind m k) Q := okPost_bind (okPost_of_spec hm) hk

theorem okPost_any {α β : Type _} {m : Result α} {k : α → Result β} {Q : β → Prop}
    (hk : ∀ a, OkPost (k a) Q) : OkPost (Std.bind m k) Q :=
  okPost_bind (okPost_trivial m) (fun a _ => hk a)

theorem okPost_const {α : Type _} {m : Result α} {P : α → Prop} (h : ∀ a, P a) : OkPost m P :=
  fun v _ => h v

theorem okPost_residual {T : Type _} {P : core.result.Result T topology.Error → Prop}
    (e : topology.Error) (h : P (.Err e)) :
    OkPost (core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
      (core.convert.FromSame topology.Error) (.Err e)) P := by
  simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, core.convert.FromSame.from, Std.bind_ok, bind_tc_ok]
  exact okPost_ok h

/-! ### `Arc::validate`, `check_portal_spec`, `check_circle_extent` -/

theorem polar_arc_validate_spec (a : polar.Arc) :
    polar.Arc.validate a ⦃ r => r = .Ok () → ArcOk a ⦄ := by
  unfold polar.Arc.validate
  have ht := turn_val
  split_ifs <;> simp only [spec_ok, ArcOk] <;> intro h <;> first | scalar_tac | cases h

/-- What `check_portal_spec` establishes about an accepted portal. -/
def PortalSpecOk (n : Nat) (p : polar.PortalSpec) : Prop :=
  p.circle.val < n ∧ ArcOk p.mouth ∧ 0 ≤ p.band.val

theorem check_portal_spec_ok (p : polar.PortalSpec) (circles : Slice polar.Circle)
    (margin : Std.I32) (hm : 0 < margin.val ∧ margin.val ≤ 1000000) :
    OkPost (scene.check_portal_spec p circles margin)
      (fun r => r = .Ok () → PortalSpecOk circles.val.length p) := by
  unfold scene.check_portal_spec
  by_cases h1 : p.circle ≥ Slice.len circles
  · simp only [h1, ↓reduceIte]; exact okPost_ok (by simp)
  simp only [h1, ↓reduceIte]
  refine okPost_spec (I32.mul_spec (x := margin) (y := 4#i32) (by scalar_tac) (by scalar_tac)) ?_
  intro i1 hi1
  by_cases h2 : p.band < i1
  · simp only [h2, ↓reduceIte]; exact okPost_ok (by simp)
  simp only [h2, ↓reduceIte]
  refine okPost_spec (polar_arc_validate_spec p.mouth) ?_
  intro r hr
  cases r with
  | Err e =>
    simp only [branch_err_eq, Std.bind_ok]
    exact okPost_residual e (by simp)
  | Ok u =>
    simp only [branch_ok_eq, Std.bind_ok]
    exact okPost_const (fun _ _ => ⟨by scalar_tac, hr rfl, by scalar_tac⟩)

theorem check_circle_extent_ok (index : Std.Usize) (circles : Slice polar.Circle)
    (bands : Slice Std.I32) (counts : Slice Std.Usize) (margin : Std.I32)
    (hc : index.val < circles.val.length) (hb : index.val < bands.val.length) :
    OkPost (scene.check_circle_extent index circles bands counts margin)
      (fun r => r = .Ok () →
        (circles.val[index.val]'hc).outer.val + (bands.val[index.val]'hb).val ≤ 1000000) := by
  unfold scene.check_circle_extent
  refine okPost_any (fun i => ?_)
  by_cases h1 : i < 2#usize
  · simp only [h1, ↓reduceIte]; exact okPost_ok (by simp)
  simp only [h1, ↓reduceIte]
  refine okPost_spec (Slice.index_usize_spec circles index (by scalar_tac)) ?_
  intro c hc'
  refine okPost_spec (Slice.index_usize_spec bands index (by scalar_tac)) ?_
  intro b hb'
  simp only [lift, Std.bind_ok]
  rcases i32_checked_add_cases c.outer b with ⟨hn, _⟩ | ⟨z, hz, hzv⟩
  · simp only [hn, core.option.Option.ok_or, Std.bind_ok, branch_err_eq]
    exact okPost_residual _ (by simp)
  · simp only [hz, core.option.Option.ok_or, Std.bind_ok, branch_ok_eq]
    have hcl := coord_limit_val
    by_cases h2 : z > grid.COORD_LIMIT
    · simp only [h2, ↓reduceIte]; exact okPost_ok (by simp)
    simp only [h2, ↓reduceIte]
    refine okPost_const (fun _ _ => ?_)
    have hc2 : c = circles.val[index.val]'hc := by simpa using hc'
    have hb2 : b = bands.val[index.val]'hb := by simpa using hb'
    subst hc2 hb2
    scalar_tac

/-! ### `Circle::new` -/

/-- Sector counts seen so far by the ring loop of `Circle::new` are in `2..=TURN/2`. -/
def SectorsUpTo (v : alloc.vec.Vec Std.Usize) (n : Nat) : Prop :=
  ∀ j (h : j < v.val.length), j < n → 2 ≤ (v.val[j]'h).val ∧ (v.val[j]'h).val ≤ 2048

theorem circle_new_loop0_ok (cr rw : Std.I32) (v : alloc.vec.Vec Std.Usize) (margin : Std.I32)
    (rs : alloc.vec.Vec Std.Usize) (next : Std.Usize) (status : core.result.Result Unit topology.Error)
    (ring : Std.Usize) (hinv : status = .Ok () → SectorsUpTo v ring.val) :
    OkPost (polar.Circle.new_loop0 cr rw v margin rs next status ring)
      (fun r => r.2 = .Ok () → SectorsUpTo v v.val.length) := by
  unfold polar.Circle.new_loop0
  refine okPost_loop
    (fun st : alloc.vec.Vec Std.Usize × Std.Usize × core.result.Result Unit topology.Error ×
      Std.Usize => st.2.2.1 = .Ok () → SectorsUpTo v st.2.2.2.val) _ _ ?_ (rs, next, status, ring) hinv
  rintro ⟨rs, nx, st, rg⟩ hst
  unfold polar.Circle.new_loop0.body
  by_cases hlt : rg < alloc.vec.Vec.len v
  swap
  · simp only [hlt, ↓reduceIte]
    refine okPost_ok (fun hs j hj _ => hst hs j hj (by scalar_tac))
  simp only [hlt, ↓reduceIte]
  cases st with
  | Err e =>
    simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact okPost_ok (fun h => by cases h)
  | Ok u =>
    simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte, alloc.vec.Vec.index_slice_index]
    have hst' := hst (by cases u; rfl)
    refine okPost_spec (alloc.vec.Vec.index_usize_spec v rg (by scalar_tac)) ?_
    intro count hcount
    refine okPost_any (fun i3 => okPost_any (fun i4 => okPost_any (fun inner => ?_)))
    refine okPost_bind (P := fun t : alloc.vec.Vec Std.Usize × Std.Usize ×
        core.result.Result Unit topology.Error =>
        t.2.2 = .Ok () → 2 ≤ count.val ∧ count.val ≤ 2048) ?_ ?_
    · by_cases hc2 : count < 2#usize
      · simp only [hc2, ↓reduceIte]; exact okPost_ok (fun h => by cases h)
      simp only [hc2, ↓reduceIte]
      have ht := turn_val
      refine okPost_spec (IScalar.hcast_inBounds_spec .Usize polar.TURN (by scalar_tac)) ?_
      intro i5 hi5
      refine okPost_spec (Usize.div_spec i5 (y := 2#usize) (by simp)) ?_
      intro i6 hi6
      by_cases hc3 : count > i6
      · simp only [hc3, ↓reduceIte]; exact okPost_ok (fun h => by cases h)
      simp only [hc3, ↓reduceIte]
      exact okPost_const (fun _ _ => ⟨by scalar_tac, by scalar_tac⟩)
    · rintro ⟨rs1, nx1, st1⟩ hP
      refine okPost_spec (Usize.add_spec (x := rg) (y := 1#usize) (by scalar_tac)) ?_
      intro rg1 hrg1
      refine okPost_ok (fun hs1 j hj hjr => ?_)
      have hc := hP hs1
      by_cases hjr' : j < rg.val
      · exact hst' j hj hjr'
      · have : j = rg.val := by scalar_tac
        subst this
        rw [← hcount]; exact hc

theorem i32_checked_mul_cases (x y : Std.I32) :
    I32.checked_mul x y = none ∨ ∃ z, I32.checked_mul x y = some z ∧ z.val = x.val * y.val := by
  have h := I32.checked_mul_bv_spec x y
  cases hc : I32.checked_mul x y with
  | none => left; rfl
  | some z =>
    right; refine ⟨z, rfl, ?_⟩
    have hc' : core.num.checked_mul_IScalar x y = some z := hc
    rw [hc'] at h
    exact h.2.2.1

theorem range_inclusive_new_eq (lo hi : Std.I32) :
    core.ops.range.RangeInclusive.new lo hi = ok ⟨lo, hi, false⟩ := rfl

theorem okPost_residual_gen {T : Type _} {P : core.result.Result T topology.Error → Prop}
    (residual : core.result.Result Never topology.Error) (h : ∀ e, P (.Err e)) :
    OkPost (core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
      (core.convert.FromSame topology.Error) residual) P := by
  cases residual with
  | Ok x => cases x
  | Err e => exact okPost_residual e (h e)

/-- A circle accepted by `Circle::new` with transform start `ts` satisfies `CircleOk` for any
transform count covering its rings. -/
theorem circle_new_ok (spec : polar.PolarSpec) (cc ts : Std.Usize) (margin : Std.I32)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000) :
    OkPost (polar.Circle.new spec cc ts margin) (fun r => ∀ c, r = .Ok c →
      CircleOk c (ts.val + spec.sectors.val.length) ∧ c.transform_start = ts ∧ c.spec = spec) := by
  unfold polar.Circle.new
  refine okPost_spec (grid_point_validate_spec spec.center) ?_
  rintro r ⟨hr1, hr2⟩
  cases r with
  | Err e => simp only [branch_err_eq, Std.bind_ok]; exact okPost_residual e (fun c hc => by cases hc)
  | Ok u =>
  have hpt := hr1.mp (by cases u; rfl)
  simp only [branch_ok_eq, Std.bind_ok, alloc.vec.Vec.is_empty]
  by_cases he : alloc.vec.Vec.length spec.sectors = 0
  · simp only [he, decide_true, ↓reduceIte]; exact okPost_ok (fun c hc => by cases hc)
  simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte]
  by_cases hd : (alloc.vec.Vec.len spec.sectors != alloc.vec.Vec.len spec.directions) = true
  · simp only [hd, ↓reduceIte]; exact okPost_ok (fun c hc => by cases hc)
  have hd' : (alloc.vec.Vec.len spec.sectors != alloc.vec.Vec.len spec.directions) = false :=
    Bool.eq_false_iff.mpr hd
  simp only [hd', Bool.false_eq_true, ↓reduceIte]
  have hdl : spec.sectors.val.length = spec.directions.val.length := by
    simp at hd'; scalar_tac
  refine okPost_spec (I32.mul_spec (x := margin) (y := 4#i32) (by scalar_tac) (by scalar_tac)) ?_
  intro i2 hi2
  by_cases hc1 : spec.center_radius < i2
  · simp only [hc1, ↓reduceIte]; exact okPost_ok (fun c hc => by cases hc)
  simp only [hc1, ↓reduceIte]
  by_cases hc2 : spec.ring_width < i2
  · simp only [hc2, ↓reduceIte]; exact okPost_ok (fun c hc => by cases hc)
  simp only [hc2, ↓reduceIte]
  have hmax : core.num.I32.MAX.val = 2147483647 := rfl
  refine okPost_spec (IScalar.hcast_inBounds_spec .Usize core.num.I32.MAX
    (by rw [hmax]; constructor; omega; scalar_tac)) ?_
  intro i4 hi4
  by_cases hc3 : alloc.vec.Vec.len spec.sectors > i4
  · simp only [hc3, ↓reduceIte]; exact okPost_ok (fun c hc => by cases hc)
  simp only [hc3, ↓reduceIte]
  have hlen : spec.sectors.val.length ≤ 2147483647 := by scalar_tac
  refine okPost_spec (usize_hcast_i32_spec (alloc.vec.Vec.len spec.sectors) (by scalar_tac)) ?_
  intro rc hrc
  simp only [lift, Std.bind_ok]
  rcases i32_checked_mul_cases rc spec.ring_width with hn | ⟨val, hv, hvv⟩
  · simp only [hn, core.option.Option.ok_or, Std.bind_ok, branch_err_eq]
    exact okPost_residual _ (fun c hc => by cases hc)
  simp only [hv, core.option.Option.ok_or, Std.bind_ok, branch_ok_eq]
  rcases i32_checked_add_cases val spec.center_radius with ⟨hn, _⟩ | ⟨val1, hv1, hvv1⟩
  · simp only [hn, core.option.Option.ok_or, Std.bind_ok, branch_err_eq]
    exact okPost_residual _ (fun c hc => by cases hc)
  simp only [hv1, core.option.Option.ok_or, Std.bind_ok, branch_ok_eq]
  have hcl := coord_limit_val
  by_cases hc4 : val1 > grid.COORD_LIMIT
  · simp only [hc4, ↓reduceIte]; exact okPost_ok (fun c hc => by cases hc)
  simp only [hc4, ↓reduceIte]
  refine okPost_any (fun r3 => ?_)
  cases r3 with
  | Err e => simp only [branch_err_eq, Std.bind_ok]; exact okPost_residual e (fun c hc => by cases hc)
  | Ok u3 =>
  simp only [branch_ok_eq, Std.bind_ok]
  rcases hopt : Usize.checked_add cc 1#usize with _ | val2
  · simp only [hopt, core.option.Option.ok_or, Std.bind_ok, branch_err_eq]
    exact okPost_residual _ (fun c hc => by cases hc)
  simp only [hopt, core.option.Option.ok_or, Std.bind_ok, branch_ok_eq]
  refine okPost_bind (circle_new_loop0_ok _ _ _ _ _ _ _ _ (fun _ j hj hj0 => by simp at hj0)) ?_
  rintro ⟨rs1, st⟩ hsec
  cases st with
  | Err e =>
    refine okPost_spec (core.result.Result.Insts.CoreOpsTry.branch_Err.spec (T := Unit) e) ?_
    intro cf hcf; subst hcf
    exact okPost_residual_gen _ (fun e c hc => by cases hc)
  | Ok u5 =>
  have hsec' := hsec (by cases u5; rfl)
  refine okPost_spec (core.result.Result.Insts.CoreOpsTry.branch_Ok.spec (E := topology.Error) u5) ?_
  intro cf hcf; subst hcf
  have hQ : ∀ (rs : alloc.vec.Vec Std.Usize),
      (∀ a m, spec.mode = .Twisting a m → 0 ≤ a.val ∧ a.val ≤ 512) →
      CircleOk ({ spec := spec, center_cell := cc, ring_starts := rs, transform_start := ts, outer := val1 } : polar.Circle)
        (ts.val + spec.sectors.val.length) ∧ ts = ts ∧ spec = spec := by
    intro rs htw
    refine ⟨⟨hpt, by scalar_tac, by scalar_tac, by scalar_tac, hdl.symm ▸ rfl, ?_, ?_, by scalar_tac,
      by simp, htw⟩, rfl, rfl⟩
    · intro i hi; exact hsec' i hi hi
    · simp only []; rw [hvv1, hvv, hrc]; simp; ring
  cases hmode : spec.mode with
  | Spinning =>
    repeat' (first
      | contradiction
      | (refine okPost_residual_gen _ ?_; intro e c hc; cases hc; done)
      | (refine okPost_ok ?_; intro c hc; cases hc; done)
      | (refine okPost_any (fun _ => ?_))
      | split)
    all_goals exact okPost_ok (fun c hc => by
      cases hc; exact hQ _ (fun a m h => by rw [hmode] at h; cases h))
  | Twisting amp mr =>
    repeat' (first
      | contradiction
      | (refine okPost_residual_gen _ ?_; intro e c hc; cases hc; done)
      | (refine okPost_ok ?_; intro c hc; cases hc; done)
      | (refine okPost_spec (range_inclusive_contains_i32_spec _ _) (fun b2 hb2 => ?_))
      | (refine okPost_spec i32_div_turn_eight (fun i17 hi17 => ?_))
      | (rw [range_inclusive_new_eq, Std.bind_ok])
      | (refine okPost_any (fun _ => ?_))
      | split)
    all_goals exact okPost_ok (fun c hc => by
      cases hc; exact hQ _ (fun a m h => by rw [hmode] at h; cases h; simp_all; try omega))


end Labyrinth
