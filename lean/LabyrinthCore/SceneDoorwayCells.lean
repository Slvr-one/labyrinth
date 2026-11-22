module
public import LabyrinthCore.SceneDoorwayPhases

/-! A doorway reads only the phases of the transforms it holds, part 2: the phase reads of one end
cell. The arc, the swept arc, the swept bounds and the frame pose of a cell agree on two phase
tables that agree on the cell's reads; so does the twisting interpolation `offset_at_valid` at the
three radii a cell's pose can have (a sector's centre line, a centre, a transition cell's band
edge). -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth
/-! ### The phase reads, cell by cell -/

/-- Two tables agree on every transform the doorway computation reads for `cell`. -/
def CellAgree (L : scene.Layout) (cell : Nat) (p p' : Slice Std.I32) : Prop :=
  ∀ k, CellReads L cell k → PhAgree p p' k

theorem getElem_of_some {α : Type _} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) :
    ∃ hi : i < l.length, l[i]'hi = x := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp h
  exact ⟨hi, hx⟩

theorem sector_ring_lt {L : scene.Layout} (hL : LayoutGeom L) {cell : Nat}
    {circle ring sector : Std.Usize} {c : polar.Circle}
    (hcl : L.cells.val[cell]? = some (scene.Cell.Sector circle ring sector))
    (hc : L.circles.val[circle.val]? = some c) : ring.val < c.spec.sectors.val.length := by
  obtain ⟨hi, hx⟩ := getElem_of_some hcl
  have hok := hL.cells cell hi
  rw [hx] at hok
  obtain ⟨h1, hr, _⟩ := hok
  obtain ⟨hi2, hx2⟩ := getElem_of_some hc
  have : L.circles.val[circle.val]'h1 = c := hx2
  rw [this] at hr
  exact hr

theorem circle_ok_of {L : scene.Layout} (hL : LayoutGeom L) {i : Nat} {c : polar.Circle}
    (hc : L.circles.val[i]? = some c) : CircleOk c L.transforms.val := by
  obtain ⟨hi, hx⟩ := getElem_of_some hc
  have := hL.circles i hi
  rw [hx] at this
  exact this

theorem cell_arc_congr (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize)
    (p p' : Slice Std.I32) (h : CellAgree L cell.val p p') :
    scene.Layout.cell_arc L cell p = scene.Layout.cell_arc L cell p' := by
  unfold scene.Layout.cell_arc
  apply bind_congr_ok
  intro cl hcl
  have hcls := vec_index_some hcl
  cases cl with
  | Sector circle ring sector =>
    apply bind_congr_ok
    intro c1 hc1
    have hc1s := vec_index_some hc1
    apply bind_congr_ok
    intro arc _
    apply bind_congr_ok
    intro mm hmm
    simp only [polar.Circle.mode, ok.injEq] at hmm
    subst hmm
    cases c1.spec.mode with
    | Spinning =>
      simp only
      rw [offset_congr c1 ring p p' (h _ (Or.inl ⟨circle, ring, sector, c1, hcls, hc1s,
        sector_ring_lt hL hcls hc1s, Or.inl rfl⟩))]
    | Twisting a m => rfl
  | _ => rfl

theorem swept_arc_congr (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize)
    (p p' : Slice Std.I32) (h : CellAgree L cell.val p p') (arc : polar.Arc)
    (mode : polar.MotionMode) :
    scene.Layout.swept_arc L cell arc mode p = scene.Layout.swept_arc L cell arc mode p' := by
  unfold scene.Layout.swept_arc
  cases mode with
  | Spinning => simp only; rw [cell_arc_congr L hL cell p p' h]
  | Twisting a m => rfl

theorem cell_sweep_congr (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize)
    (p p' : Slice Std.I32) (h : CellAgree L cell.val p p') :
    scene.Layout.cell_sweep L cell p p = scene.Layout.cell_sweep L cell p' p' := by
  unfold scene.Layout.cell_sweep
  simp only [cell_arc_congr L hL cell p p' h, swept_arc_congr L hL cell p p' h]

theorem frame_pose_congr (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize)
    (p p' : Slice Std.I32) (h : CellAgree L cell.val p p') :
    scene.Layout.frame_pose L cell p = scene.Layout.frame_pose L cell p' := by
  unfold scene.Layout.frame_pose
  apply bind_congr_ok
  intro loc _
  apply bind_congr_ok
  intro cl hcl
  have hcls := vec_index_some hcl
  cases cl with
  | Sector circle ring sector =>
    apply bind_congr_ok
    intro c1 hc1
    have hc1s := vec_index_some hc1
    apply bind_congr_ok
    intro mm hmm
    simp only [polar.Circle.mode, ok.injEq] at hmm
    subst hmm
    cases c1.spec.mode with
    | Spinning =>
      cases loc with
      | Cartesian pt => rfl
      | Polar k r a =>
        simp only
        rw [offset_congr c1 ring p p' (h _ (Or.inl ⟨circle, ring, sector, c1, hcls, hc1s,
          sector_ring_lt hL hcls hc1s, Or.inl rfl⟩))]
    | Twisting a m => rfl
  | _ => rfl

/-! ### World positions on a twisting circle -/

theorem radius_ok_val {c : polar.Circle} {n : Nat} (hc : CircleOk c n) {ring : Std.Usize}
    (hr : ring.val < c.spec.sectors.val.length) {x : Std.I32} (h : polar.Circle.radius c ring = ok x) :
    x.val = ringRadius c ring.val ∧ x.val < c.outer.val := by
  have hs := circle_radius_spec c ring n hc hr
  rw [h] at hs
  have := (spec_ok _).mp hs
  exact ⟨this.1, this.2.2⟩

theorem ringRadius_lt_iff (c : polar.Circle) {n : Nat} (hc : CircleOk c n) (a b : Nat) :
    ringRadius c a < ringRadius c b ↔ a < b := by
  have hw := hc.ring_width
  unfold ringRadius
  constructor
  · intro h
    by_contra hab
    have : (b : Int) * c.spec.ring_width.val ≤ (a : Int) * c.spec.ring_width.val :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    omega
  · intro h
    have : ((a : Int) + 1) * c.spec.ring_width.val ≤ (b : Int) * c.spec.ring_width.val :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    have : ((a : Int) + 1) * c.spec.ring_width.val = a * c.spec.ring_width.val +
      c.spec.ring_width.val := by ring
    omega

theorem ringRadius_lt_outer (c : polar.Circle) {n : Nat} (hc : CircleOk c n) (j : Nat)
    (hj : j < c.spec.sectors.val.length) : ringRadius c j < c.outer.val := by
  have hw := hc.ring_width
  have ho := hc.outer
  unfold ringRadius
  have : ((j : Int) + 1) * c.spec.ring_width.val ≤
      (c.spec.sectors.val.length : Int) * c.spec.ring_width.val :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  have : ((j : Int) + 1) * c.spec.ring_width.val = j * c.spec.ring_width.val +
    c.spec.ring_width.val := by ring
  have : c.spec.ring_width.val / 2 < c.spec.ring_width.val := by omega
  omega

theorem offset_at_valid_loop_ok (c : polar.Circle) {n : Nat} (hc : CircleOk c n)
    (radius : Std.I32) (h0 : ringRadius c 0 ≤ radius.val) {R : Std.Usize}
    (h : polar.Circle.offset_at_valid_loop c radius 0#usize = ok R) :
    R.val < c.spec.sectors.val.length ∧ ringRadius c R.val ≤ radius.val ∧
      (R.val + 1 < c.spec.sectors.val.length → radius.val < ringRadius c (R.val + 1)) := by
  have hs := circle_offset_at_valid_loop_spec c radius n hc 0#usize
    (by have := hc.rings; simp; omega) (by simpa using h0)
  rw [h] at hs
  exact (spec_ok (p := fun r : Std.Usize => r.val < c.spec.sectors.val.length ∧
    ringRadius c r.val ≤ radius.val ∧
    (r.val + 1 < c.spec.sectors.val.length → radius.val < ringRadius c (r.val + 1))) R).mp hs

/-- `offset_at_valid` reads ring `0` when the radius is inside ring `0`'s centre line, and otherwise
the ring `R` the scan stops at and, if there is one, ring `R + 1`. -/
theorem offset_at_valid_congr (c : polar.Circle) {n : Nat} (hc : CircleOk c n)
    (radius band : Std.I32) (p p' : Slice Std.I32)
    (h0 : radius.val ≤ ringRadius c 0 → PhAgree p p' (c.transform_start.val + 0))
    (hR : ∀ R : Nat, R < c.spec.sectors.val.length → ringRadius c R ≤ radius.val →
      (R + 1 < c.spec.sectors.val.length → radius.val < ringRadius c (R + 1)) →
      PhAgree p p' (c.transform_start.val + R) ∧
      (R + 1 < c.spec.sectors.val.length → PhAgree p p' (c.transform_start.val + (R + 1)))) :
    polar.Circle.offset_at_valid c radius band p = polar.Circle.offset_at_valid c radius band p' := by
  have hlen := hc.rings
  unfold polar.Circle.offset_at_valid
  apply bind_congr_ok; intro first hfirst
  have hf : first.val = ringRadius c 0 := by
    have := (radius_ok_val hc (ring := 0#usize) (by simp; omega) hfirst).1
    simpa using this
  split
  · rename_i hle
    have hle' : radius.val ≤ first.val := by scalar_tac
    rw [offset_congr c 0#usize p p' (by simpa using h0 (by simpa [hf] using hle'))]
  · rename_i hle
    have hgt : ringRadius c 0 ≤ radius.val := by
      have : ¬ radius.val ≤ first.val := fun h => hle (by scalar_tac)
      omega
    apply bind_congr_ok; intro R hRl
    obtain ⟨hR1, hR2, hR3⟩ := offset_at_valid_loop_ok c hc radius hgt hRl
    obtain ⟨hagR, hagR1⟩ := hR R.val hR1 hR2 hR3
    apply bind_congr_ok; intro low _
    apply bind_congr_ok; intro i hi
    have hiv : i.val = R.val + 1 := usize_add_ok _ _ _ hi
    apply bind_congr_ok; intro i1 hi1
    apply bind_congr_ok
    rintro ⟨s, high⟩ hsh
    have hself : s = c := by
      have hpost : OkPost (if i < i1 then do
            let high1 ← polar.Circle.radius c i
            ok (c, high1)
          else do
            let high1 ← c.outer + band
            ok (c, high1) : Result (polar.Circle × Std.I32)) (fun pr => pr.1 = c) := by
        split <;> exact okPost_bind (okPost_trivial _) (fun _ _ => okPost_ok rfl)
      exact hpost _ hsh
    subst hself
    show (if radius ≥ high then _ else _) = (if radius ≥ high then _ else _)
    split
    · rfl
    · rw [offset_congr s R p p' hagR]
      apply bind_congr_ok; intro fr _
      apply bind_congr_ok; intro i2 hi2
      simp only [polar.Circle.ring_count, ok.injEq] at hi2
      subst hi2
      by_cases hlt : i < alloc.vec.Vec.len s.spec.sectors
      · have : i.val < s.spec.sectors.val.length := by simpa using hlt
        simp only [hlt, ↓reduceIte]
        rw [offset_congr s i p p' (by rw [hiv]; exact hagR1 (by omega))]
      · simp only [hlt, ↓reduceIte]

/-- A twisting sector's world position reads its ring and the ring outside it. -/
theorem offset_at_valid_sector (c : polar.Circle) {n : Nat} (hc : CircleOk c n)
    (r : Nat) (hr : r < c.spec.sectors.val.length) (radius band : Std.I32)
    (hrad : radius.val = ringRadius c r) (p p' : Slice Std.I32)
    (h1 : PhAgree p p' (c.transform_start.val + r))
    (h2 : r + 1 < c.spec.sectors.val.length → PhAgree p p' (c.transform_start.val + (r + 1))) :
    polar.Circle.offset_at_valid c radius band p = polar.Circle.offset_at_valid c radius band p' := by
  apply offset_at_valid_congr c hc radius band p p'
  · intro hle
    have : r = 0 := by
      by_contra hne
      have := (ringRadius_lt_iff c hc 0 r).mpr (by omega)
      omega
    subst this; exact h1
  · intro R hR hle hnext
    have hRr : R = r := by
      have hle' : R ≤ r := by
        by_contra hgt
        have := (ringRadius_lt_iff c hc r R).mpr (by omega)
        omega
      by_contra hne
      have h3 := hnext (by omega)
      by_cases hRr1 : R + 1 = r
      · subst hRr1; omega
      · have := (ringRadius_lt_iff c hc (R + 1) r).mpr (by omega)
        omega
    subst hRr
    exact ⟨h1, h2⟩

/-- A twisting centre's world position (radius `0`) reads ring `0`. -/
theorem offset_at_valid_center (c : polar.Circle) {n : Nat} (hc : CircleOk c n)
    (radius band : Std.I32) (hrad : radius.val = 0) (p p' : Slice Std.I32)
    (h1 : PhAgree p p' (c.transform_start.val + 0)) :
    polar.Circle.offset_at_valid c radius band p = polar.Circle.offset_at_valid c radius band p' := by
  apply offset_at_valid_congr c hc radius band p p' (fun _ => h1)
  intro R _ hle _
  exfalso
  have := hc.center_radius
  have : 0 ≤ (R : Int) * c.spec.ring_width.val := by have := hc.ring_width; positivity
  have : 0 ≤ c.spec.ring_width.val / 2 := by have := hc.ring_width; omega
  unfold ringRadius at hle
  omega

/-- A transition cell's world position (on the adapter band's outer edge) reads at most the
outermost ring. -/
theorem offset_at_valid_transition (c : polar.Circle) {n : Nat} (hc : CircleOk c n)
    (radius band : Std.I32) (hb : 0 ≤ band.val) (hrad : radius.val = c.outer.val + band.val)
    (p p' : Slice Std.I32)
    (h1 : PhAgree p p' (c.transform_start.val + (c.spec.sectors.val.length - 1))) :
    polar.Circle.offset_at_valid c radius band p = polar.Circle.offset_at_valid c radius band p' := by
  have hlen := hc.rings
  apply offset_at_valid_congr c hc radius band p p'
  · intro hle
    exfalso
    have := ringRadius_lt_outer c hc 0 (by omega)
    omega
  · intro R hR _ hnext
    have hR' : R = c.spec.sectors.val.length - 1 := by
      by_contra hne
      have := hnext (by omega)
      have := ringRadius_lt_outer c hc (R + 1) (by omega)
      omega
    subst hR'
    exact ⟨h1, fun h => absurd h (by omega)⟩


end Labyrinth
