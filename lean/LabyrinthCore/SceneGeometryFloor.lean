module
public import LabyrinthCore.SceneGeometryLayoutNew
public import LabyrinthCore.SceneGeometryMinimum

/-! Geometry totality (S8), the center-radius floor: `Circle::new` rejects a circle whose
`center_radius` is below `4 * margin`, so every circle `Layout::new` keeps satisfies the floor. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

theorem okPost_and {α : Type _} {m : Result α} {P Q : α → Prop} (hp : OkPost m P)
    (hq : OkPost m Q) : OkPost m (fun a => P a ∧ Q a) := fun v h => ⟨hp v h, hq v h⟩

/-- Every circle `Circle::new` accepts has a center radius of at least four margins. -/
theorem circle_new_floor (spec : polar.PolarSpec) (cc ts : Std.Usize) (margin : Std.I32)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000) :
    OkPost (polar.Circle.new spec cc ts margin) (fun r => ∀ c, r = .Ok c →
      4 * margin.val ≤ spec.center_radius.val) := by
  unfold polar.Circle.new
  refine okPost_spec (grid_point_validate_spec spec.center) ?_
  rintro r ⟨hr1, hr2⟩
  cases r with
  | Err e => simp only [branch_err_eq, Std.bind_ok]; exact okPost_residual e (fun c hc => by cases hc)
  | Ok u =>
  simp only [branch_ok_eq, Std.bind_ok, alloc.vec.Vec.is_empty]
  by_cases he : alloc.vec.Vec.length spec.sectors = 0
  · simp only [he, decide_true, ↓reduceIte]; exact okPost_ok (fun c hc => by cases hc)
  simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte]
  by_cases hd : (alloc.vec.Vec.len spec.sectors != alloc.vec.Vec.len spec.directions) = true
  · simp only [hd, ↓reduceIte]; exact okPost_ok (fun c hc => by cases hc)
  have hd' : (alloc.vec.Vec.len spec.sectors != alloc.vec.Vec.len spec.directions) = false :=
    Bool.eq_false_iff.mpr hd
  simp only [hd', Bool.false_eq_true, ↓reduceIte]
  refine okPost_spec (I32.mul_spec (x := margin) (y := 4#i32) (by scalar_tac) (by scalar_tac)) ?_
  intro i2 hi2
  by_cases hc1 : spec.center_radius < i2
  · simp only [hc1, ↓reduceIte]; exact okPost_ok (fun c hc => by cases hc)
  simp only [hc1, ↓reduceIte]
  have hfl : 4 * margin.val ≤ spec.center_radius.val := by scalar_tac
  exact okPost_const (fun _ _ _ => hfl)

/-- Every circle built so far has the center-radius floor. -/
def CirclesFloor (cs : List polar.Circle) (margin : Int) : Prop :=
  ∀ c ∈ cs, 4 * margin ≤ c.spec.center_radius.val

theorem layout_new_loop0_floor (iter : alloc.vec.into_iter.IntoIter polar.PolarSpec)
    (margin : Std.I32) (circles : alloc.vec.Vec polar.Circle) (transforms : Std.Usize)
    (status : core.result.Result Unit topology.Error)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000)
    (hinv : CirclesFloor circles.val margin.val) :
    OkPost (scene.Layout.new_loop0 iter margin circles transforms status)
      (fun r => CirclesFloor r.1.val margin.val) := by
  unfold scene.Layout.new_loop0
  refine okPost_loop
    (fun st : alloc.vec.into_iter.IntoIter polar.PolarSpec × alloc.vec.Vec polar.Circle ×
      Std.Usize × core.result.Result Unit topology.Error => CirclesFloor st.2.1.val margin.val)
    _ _ ?_ (iter, circles, transforms, status) hinv
  rintro ⟨it, cs, tr, st⟩ hcs
  unfold scene.Layout.new_loop0.body
  refine okPost_any (fun p => ?_)
  obtain ⟨o, it1⟩ := p
  cases o with
  | none => exact okPost_ok hcs
  | some spec =>
  refine okPost_spec (core.result.Result.is_ok.step_spec st) ?_
  intro b hb
  cases b with
  | false => exact okPost_ok hcs
  | true =>
  refine okPost_bind (okPost_and (circle_new_ok spec 0#usize tr margin hm)
    (circle_new_floor spec 0#usize tr margin hm)) ?_
  intro r hr
  cases r with
  | Err e => exact okPost_ok hcs
  | Ok circle =>
  obtain ⟨⟨hco, hts, hsp⟩, hfl⟩ : (CircleOk circle (tr.val + spec.sectors.val.length) ∧
      circle.transform_start = tr ∧ circle.spec = spec) ∧ 4 * margin.val ≤ spec.center_radius.val :=
    ⟨hr.1 circle rfl, hr.2 circle rfl⟩
  refine okPost_spec (circle_ring_count_spec circle) ?_
  intro i hi
  simp only [lift, Std.bind_ok]
  rcases hadd : Usize.checked_add tr i with _ | count
  · exact okPost_ok hcs
  refine okPost_bind (vec_push_okPost cs circle) ?_
  intro cs1 hcs1
  refine okPost_ok ?_
  intro c hc
  simp only [hcs1, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact hcs c hc
  · rw [hsp]; exact hfl

/-- The margin of a geometry as `Geometry::margin` computes it. -/
def layoutMargin (g : grid.Geometry) : Int := g.walker_radius.val + g.clearance.val + 2

/-- Every circle of the layout has a center radius of at least four margins. -/
def LayoutFloor (L : scene.Layout) : Prop :=
  ∀ i, ∀ h : i < L.circles.val.length,
    4 * layoutMargin L.geometry ≤ (L.circles.val[i]'h).spec.center_radius.val

/-- The narrowing in `Layout::doorway` is exact for a layout with the center-radius floor: for a
polar edge on circle `circle` between poses with radii in `[0, COORD_LIMIT]`, `minimum` equals the
exact quotient and lies in `[1, 2048]`. -/
theorem layout_doorway_minimum_exact (L : scene.Layout) (hL : LayoutGeom L) (hF : LayoutFloor L)
    (m : Std.I32) (hmv : m.val = layoutMargin L.geometry) (circle : Std.Usize)
    (hcl : circle.val < L.circles.val.length) (from_radius to_radius : Std.I32)
    (hf : 0 ≤ from_radius.val ∧ from_radius.val ≤ 1000000)
    (ht : 0 ≤ to_radius.val ∧ to_radius.val ≤ 1000000) :
    (do
      let i2 ← lift (core.cmp.impls.OrdI32.min from_radius to_radius)
      let radius ← lift (core.cmp.impls.OrdI32.max i2 (L.circles.val[circle.val]'hcl).spec.center_radius)
      let i3 ← lift (core.convert.num.FromI64I32.from m)
      let i4 ← i3 * 2#i64
      let i5 ← lift (core.convert.num.FromI64I32.from polar.TURN)
      let i6 ← i4 * i5
      let i7 ← lift (core.convert.num.FromI64I32.from radius)
      let i8 ← i6 + i7
      let i9 ← i8 - 1#i64
      let i10 ← lift (core.convert.num.FromI64I32.from radius)
      let i11 ← i9 / i10
      lift (IScalar.cast .I32 i11)) ⦃ minimum =>
      ∃ radius : Int, 4 * m.val ≤ radius ∧ radius ≤ 1000000 ∧
        minimum.val = (2 * m.val * 4096 + radius - 1) / radius ∧
        1 ≤ minimum.val ∧ minimum.val ≤ 2048 ⦄ := by
  have hmg := hL.margin
  unfold MarginOk at hmg
  have hco := hL.circles circle.val hcl
  have hfl := hF circle.val hcl
  have hol := hco.outer_le
  have hout := hco.outer
  have hrw := hco.ring_width
  have hcrp := hco.center_radius
  have : 0 ≤ ((L.circles.val[circle.val]'hcl).spec.sectors.val.length : Int) *
      (L.circles.val[circle.val]'hcl).spec.ring_width.val := by positivity
  have hmv' : m.val = L.geometry.walker_radius.val + L.geometry.clearance.val + 2 := hmv
  exact doorway_minimum_exact m from_radius to_radius _ ⟨by omega, by omega⟩
    (by unfold layoutMargin at hfl; omega) (by omega) hf ht

end Labyrinth
