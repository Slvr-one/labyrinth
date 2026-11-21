module
public import LabyrinthCore.SceneGeometryLayout

/-! Geometry totality (S8), cell sweeps: under `LayoutGeom`, `Layout::cell_sweep` returns for every
cell, and an accepted sweep is a valid rectangle. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

/-- What `cell_sweep` returns: a valid rectangle, or `InvalidGeometry`. -/
def SweepOk (r : core.result.Result grid.Rect topology.Error) : Prop :=
  (∀ e, r = .Ok e → RectOk e) ∧ (∀ e, r = .Err e → e = .InvalidGeometry)

/-- Ring `ring` of a valid circle ends inside the circle: `center_radius + ring * ring_width ≤ outer`
for `ring ≤ rings`. -/
theorem CircleOk.ring_end_le {c : polar.Circle} {n : Nat} (hc : CircleOk c n) (ring : Nat)
    (hr : ring ≤ c.spec.sectors.val.length) :
    c.spec.center_radius.val + (ring : ℤ) * c.spec.ring_width.val ≤ c.outer.val := by
  have h1 := hc.outer; have h3 := hc.ring_width
  have : (ring : ℤ) * c.spec.ring_width.val ≤ (c.spec.sectors.val.length : ℤ) * c.spec.ring_width.val :=
    Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hr) (by omega)
  omega

theorem layout_cell_sweep_spec (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize)
    (phases next : Slice Std.I32) (h : cell.val < L.cells.val.length)
    (hph : L.transforms.val ≤ phases.val.length) (hnext : L.transforms.val ≤ next.val.length) :
    scene.Layout.cell_sweep L cell phases next ⦃ r => SweepOk r ⦄ := by
  unfold scene.Layout.cell_sweep
  step as ⟨r, hr1, hr2, hr3⟩
  obtain ⟨m, rfl⟩ := hr2 hL.margin
  obtain ⟨_, hm⟩ := hr1 m rfl
  have hmg := hL.margin
  unfold MarginOk at hmg
  simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, alloc.vec.Vec.index_slice_index]
  step as ⟨c, hc⟩
  have hcell := hL.cell cell h
  have hc' : c = L.cells.val[cell.val]'h := hc
  subst hc'
  cases hcc : L.cells.val[cell.val]'h with
  | Grid a b bd =>
    rw [hcc] at hcell
    simp only [spec_ok, SweepOk]
    refine ⟨?_, ?_⟩
    · intro e he; cases he; exact hcell
    · intro e he; cases he
  | Center k =>
    rw [hcc] at hcell
    have hk : k.val < L.circles.val.length := hcell
    step as ⟨o, ho⟩
    rw [hcc] at ho
    simp only [cellCircle] at ho
    subst ho
    simp only [core.option.Option.ok_or, Std.bind_ok, alloc.vec.Vec.index_slice_index]
    step as ⟨c1, hc1⟩
    have hco := hL.circles k.val hk
    have hc1' : c1 = L.circles.val[k.val]'hk := hc1
    subst hc1'
    step as ⟨cen, hcen⟩
    step as ⟨mm, hmm⟩
    step as ⟨arc, harc⟩
    have hswept := layout_swept_arc_spec L hL cell arc mm next h harc
      (fun a m' he => hco.twist a m' (hmm ▸ he)) hnext
    apply spec_bind hswept
    intro sw hsw
    have hcr := hco.center_radius
    have hol := hco.outer_le
    have hle := hco.ring_end_le 0 (by omega)
    apply spec_mono (polar_bounds_spec _ 0#i32 _ sw m (hcen ▸ hco.center) (by simp) (by omega) (arcOk_bnd hsw))
    rintro x ⟨hx1, hx2, hx3⟩
    exact ⟨hx1, fun e he => hx3 (by omega) e he⟩
  | Sector k rg s =>
    rw [hcc] at hcell
    obtain ⟨hk, hr, hs⟩ := hcell
    step as ⟨o, ho⟩
    rw [hcc] at ho
    simp only [cellCircle] at ho
    subst ho
    simp only [core.option.Option.ok_or, Std.bind_ok, alloc.vec.Vec.index_slice_index]
    step as ⟨c1, hc1⟩
    have hco := hL.circles k.val hk
    have hc1' : c1 = L.circles.val[k.val]'hk := hc1
    subst hc1'
    step as ⟨cen, hcen⟩
    step as ⟨mm, hmm⟩
    have hcr := hco.center_radius
    have hrw := hco.ring_width
    have hol := hco.outer_le
    have hrl := circle_rings_le _ _ hco
    have hle0 := hco.ring_end_le rg.val (by omega)
    have hle1 := hco.ring_end_le (rg.val + 1) (by omega)
    push_cast at hle1
    step as ⟨i, hi⟩
    have hmul : 0 ≤ i.val * (L.circles.val[k.val]'hk).spec.ring_width.val ∧
        i.val * (L.circles.val[k.val]'hk).spec.ring_width.val ≤ 1000000 := by
      rw [hi]; constructor
      · exact Int.mul_nonneg (by omega) (by omega)
      · nlinarith
    step as ⟨i1, hi1⟩
    step as ⟨inner, hinner⟩
    step as ⟨outer, houter⟩
    step as ⟨arc, harc⟩
    have hswept := layout_swept_arc_spec L hL cell arc mm next h harc
      (fun a m' he => hco.twist a m' (hmm ▸ he)) hnext
    apply spec_bind hswept
    intro sw hsw
    have hi1' : i1.val = (rg.val : ℤ) * (L.circles.val[k.val]'hk).spec.ring_width.val := by
      rw [hi1, hi]
    apply spec_mono (polar_bounds_spec _ inner outer sw m (hcen ▸ hco.center) (by omega) (by
      constructor <;> nlinarith) (arcOk_bnd hsw))
    rintro x ⟨hx1, hx2, hx3⟩
    exact ⟨hx1, fun e he => hx3 (by omega) e he⟩
  | Transition p =>
    rw [hcc] at hcell
    obtain ⟨hp, hcirc, hmouth⟩ := hcell
    step as ⟨o, ho⟩
    rw [hcc] at ho
    simp only [cellCircle, hp, ↓reduceDIte] at ho
    subst ho
    simp only [core.option.Option.ok_or, Std.bind_ok, alloc.vec.Vec.index_slice_index]
    step as ⟨c1, hc1⟩
    have hco := hL.circles _ hcirc
    have hc1' : c1 = L.circles.val[(L.portals.val[p.val]'hp).spec.circle.val]'hcirc := hc1
    subst hc1'
    step as ⟨cen, hcen⟩
    step as ⟨mm, hmm⟩
    have hbl := hL.bands_len
    have hb := hL.bands (L.portals.val[p.val]'hp).spec.circle.val (by omega) hcirc
    have hout := hco.outer_pos
    have hol := hco.outer_le
    step as ⟨bd, hbd⟩
    subst hbd
    step as ⟨outer, houter⟩
    step as ⟨arc, harc⟩
    have hswept := layout_swept_arc_spec L hL cell arc mm next h harc
      (fun a m' he => hco.twist a m' (hmm ▸ he)) hnext
    apply spec_bind hswept
    intro sw hsw
    apply spec_mono (polar_bounds_spec _ _ outer sw m (hcen ▸ hco.center) (by omega) (by omega)
      (arcOk_bnd hsw))
    rintro x ⟨hx1, hx2, hx3⟩
    exact ⟨hx1, fun e he => hx3 (by omega) e he⟩

end Labyrinth
