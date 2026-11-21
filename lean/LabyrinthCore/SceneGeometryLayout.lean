module
public import LabyrinthCore.SceneGeometryCircle
public import LabyrinthCore.SceneGeometryBounds
public import LabyrinthCore.MutationValidate
import all Aeneas.Std.Scalar.SaturatingOps

@[expose] public section

/-! Geometry totality (S8), layout layer: `LayoutGeom` records what the scene validators establish;
under it `local_pose`, `frame_pose`, `world`, `cell_arc`, `swept_arc`, `holds` and `Holds::insert` return. -/

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

/-! ### The layout invariant -/

/-- What a cell of a validated layout refers to: every index it carries is in range. -/
def CellOk (L : scene.Layout) : scene.Cell → Prop
  | .Grid _ _ b => RectOk b
  | .Center c => c.val < L.circles.val.length
  | .Sector c r s => ∃ h : c.val < L.circles.val.length,
      ∃ hr : r.val < (L.circles.val[c.val]'h).spec.sectors.val.length,
        s.val < ((L.circles.val[c.val]'h).spec.sectors.val[r.val]'hr).val
  | .Transition p => ∃ h : p.val < L.portals.val.length,
      ∃ hc : (L.portals.val[p.val]'h).spec.circle.val < L.circles.val.length,
        ArcOk (L.portals.val[p.val]'h).spec.mouth

/-- The facts about a layout that the scene validators establish and that the i32 geometry needs:
a usable margin, circles within the coordinate limit, one adapter band per circle, and cells whose
indices are in range. -/
structure LayoutGeom (L : scene.Layout) : Prop where
  margin : MarginOk L.geometry
  circles : ∀ i, ∀ h : i < L.circles.val.length, CircleOk (L.circles.val[i]'h) L.transforms.val
  bands_len : L.bands.val.length = L.circles.val.length
  bands : ∀ i, ∀ h : i < L.bands.val.length, ∀ h2 : i < L.circles.val.length,
    0 ≤ (L.bands.val[i]'h).val ∧ (L.circles.val[i]'h2).outer.val + (L.bands.val[i]'h).val ≤ 1000000
  cells : ∀ i, ∀ h : i < L.cells.val.length, CellOk L (L.cells.val[i]'h)

/-- A local pose of a validated layout: a valid Cartesian point, or a polar pose on an existing
circle with radius in `[0, COORD_LIMIT]` and a normalized angle. -/
def PoseOk (L : scene.Layout) : walker.LocalPose → Prop
  | .Cartesian p => PointOk p
  | .Polar c r a => c.val < L.circles.val.length ∧ 0 ≤ r.val ∧ r.val ≤ 1000000 ∧
      0 ≤ a.val ∧ a.val < 4096

theorem LayoutGeom.cell (hL : LayoutGeom L) (cell : Std.Usize) (h : cell.val < L.cells.val.length) :
    CellOk L (L.cells.val[cell.val]'h) := hL.cells cell.val h

/-- The circle a cell belongs to, as `circle_of` computes it. -/
def cellCircle (L : scene.Layout) : scene.Cell → Option Std.Usize
  | .Grid _ _ _ => none
  | .Center c => some c
  | .Sector c _ _ => some c
  | .Transition p => if h : p.val < L.portals.val.length then some (L.portals.val[p.val]'h).spec.circle else none

theorem cellCircle_lt {L : scene.Layout} {cell : scene.Cell} (h : CellOk L cell) (k : Std.Usize)
    (hk : cellCircle L cell = some k) : k.val < L.circles.val.length := by
  cases cell with
  | Grid a b c => simp [cellCircle] at hk
  | Center c => simp [cellCircle] at hk; subst hk; exact h
  | Sector c r s => simp [cellCircle] at hk; subst hk; exact h.1
  | Transition p =>
    obtain ⟨hp, hcirc, _⟩ := h
    simp only [cellCircle, hp, ↓reduceDIte, Option.some.injEq] at hk
    subst hk; exact hcirc

theorem layout_circle_of_spec (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize)
    (h : cell.val < L.cells.val.length) :
    scene.Layout.circle_of L cell ⦃ o => o = cellCircle L (L.cells.val[cell.val]'h) ⦄ := by
  unfold scene.Layout.circle_of
  simp only [alloc.vec.Vec.index_slice_index]
  step as ⟨c, hc⟩
  have hcell := hL.cell cell h
  have hc' : c = L.cells.val[cell.val]'h := hc
  subst hc'
  cases hcc : L.cells.val[cell.val]'h with
  | Grid a b d => simp [cellCircle, spec_ok]
  | Center k => simp [cellCircle, spec_ok]
  | Sector k r s => simp [cellCircle, spec_ok]
  | Transition p =>
    rw [hcc] at hcell
    obtain ⟨hp, _⟩ := hcell
    simp only [alloc.vec.Vec.index_slice_index]
    step as ⟨pp, hpp⟩
    simp only [cellCircle, hp, ↓reduceDIte, spec_ok]
    rw [hpp]

theorem layout_local_pose_spec (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize)
    (h : cell.val < L.cells.val.length) :
    scene.Layout.local_pose L cell ⦃ p => PoseOk L p ⦄ := by
  unfold scene.Layout.local_pose
  simp only [alloc.vec.Vec.index_slice_index]
  step as ⟨c, hc⟩
  have hcell := hL.cell cell h
  have hc' : c = L.cells.val[cell.val]'h := hc
  subst hc'
  cases hcc : L.cells.val[cell.val]'h with
  | Grid a b bd =>
    rw [hcc] at hcell
    simp only [CellOk] at hcell
    simp only []
    step as ⟨p, hp⟩
    simp only [spec_ok, PoseOk]
    exact hp
  | Center k =>
    rw [hcc] at hcell
    simp only [CellOk] at hcell
    simp only [spec_ok, PoseOk]
    refine ⟨hcell, by simp, by simp, by simp, by simp⟩
  | Sector k r s =>
    rw [hcc] at hcell
    obtain ⟨hk, hr, hs⟩ := hcell
    step as ⟨c1, hc1⟩
    have hco := hL.circles k.val hk
    have hc1' : c1 = L.circles.val[k.val]'hk := hc1
    subst hc1'
    step as ⟨i, hi, hi1, hi2⟩
    step as ⟨a, ha⟩
    have hab := arcOk_bnd ha
    step as ⟨i1, hi1'⟩
    have := hco.outer_le
    refine ⟨hk, by omega, by omega, by omega, by omega⟩
  | Transition p =>
    rw [hcc] at hcell
    obtain ⟨hp, hcirc, hmouth⟩ := hcell
    step as ⟨portal1, hportal⟩
    subst hportal
    step as ⟨c1, hc1⟩
    subst hc1
    have hbl := hL.bands_len
    have hco := hL.circles _ hcirc
    have hout := hco.outer_pos
    have hb := hL.bands (L.portals.val[p.val]'hp).spec.circle.val (by omega) hcirc
    step as ⟨i, hi⟩
    subst hi
    step as ⟨i1, hi1⟩
    have hab := arcOk_bnd hmouth
    step as ⟨i2, hi2⟩
    refine ⟨hcirc, by omega, by omega, by omega, by omega⟩

@[step]
theorem layout_local_pose_step (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize)
    (h : cell.val < L.cells.val.length) :
    scene.Layout.local_pose L cell ⦃ p => PoseOk L p ⦄ := layout_local_pose_spec L hL cell h

theorem layout_frame_pose_spec (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize)
    (phases : Slice Std.I32) (h : cell.val < L.cells.val.length)
    (hph : L.transforms.val ≤ phases.val.length) :
    scene.Layout.frame_pose L cell phases ⦃ p => PoseOk L p ⦄ := by
  unfold scene.Layout.frame_pose
  simp only [alloc.vec.Vec.index_slice_index]
  step as ⟨lp, hlp⟩
  step as ⟨c, hc⟩
  have hcell := hL.cell cell h
  have hc' : c = L.cells.val[cell.val]'h := hc
  subst hc'
  cases hcc : L.cells.val[cell.val]'h with
  | Grid a b bd => simp only [spec_ok]; exact hlp
  | Center k => simp only [spec_ok]; exact hlp
  | Transition p => simp only [spec_ok]; exact hlp
  | Sector k r s =>
    rw [hcc] at hcell
    obtain ⟨hk, hr, hs⟩ := hcell
    step as ⟨c1, hc1⟩
    have hco := hL.circles k.val hk
    have hc1' : c1 = L.circles.val[k.val]'hk := hc1
    subst hc1'
    step as ⟨mm, hmm⟩
    cases mm with
    | Spinning =>
      cases lp with
      | Cartesian pt => simp only [spec_ok]; exact hlp
      | Polar ck radius angle =>
        have hpt := hco.transform
        obtain ⟨hck, hr0, hr1, ha0, ha1⟩ := hlp
        step as ⟨i, hi, hi2⟩
        step as ⟨i1, hi1⟩
        step as ⟨i2, hi2', hi2''⟩
        exact ⟨hk, hr0, hr1, hi2', hi2''⟩
    | Twisting a m => simp only [spec_ok]; exact hlp

theorem layout_world_spec (L : scene.Layout) (hL : LayoutGeom L) (pose : walker.LocalPose)
    (phases : Slice Std.I32) (hpose : PoseOk L pose) (hph : L.transforms.val ≤ phases.val.length) :
    scene.Layout.world L pose phases ⦃ p =>
      -2000000 ≤ p.x.val ∧ p.x.val ≤ 2000000 ∧ -2000000 ≤ p.y.val ∧ p.y.val ≤ 2000000 ⦄ := by
  unfold scene.Layout.world
  simp only [alloc.vec.Vec.index_slice_index]
  cases pose with
  | Cartesian pt =>
    simp only [spec_ok]
    simp only [PoseOk, PointOk] at hpose
    omega
  | Polar k radius angle =>
    obtain ⟨hk, hr0, hr1, ha0, ha1⟩ := hpose
    step as ⟨c, hc⟩
    have hco := hL.circles k.val hk
    have hc' : c = L.circles.val[k.val]'hk := hc
    subst hc'
    step as ⟨mm, hmm⟩
    have hoff : (match mm with
        | polar.MotionMode.Spinning => ok 0#i32
        | polar.MotionMode.Twisting _ _ => do
            let i ← alloc.vec.Vec.index_usize L.bands k
            polar.Circle.offset_at_valid (L.circles.val[k.val]'hk) radius i phases) ⦃ o =>
          0 ≤ o.val ∧ o.val < 4096 ⦄ := by
      cases mm with
      | Spinning => simp only [spec_ok]; simp
      | Twisting a m =>
        have hbl := hL.bands_len
        have hb := hL.bands k.val (by omega) hk
        have hpt := hco.transform
        step as ⟨i, hi⟩
        subst hi
        apply circle_offset_at_valid_spec _ radius _ phases _ hco hb (by omega) (by omega)
    apply spec_bind hoff
    intro o ho
    step as ⟨p, hp⟩
    subst hp
    step as ⟨i, hi⟩
    have hcen := hco.center
    step as ⟨pt, hpt1, hpt2⟩
    simp only [PointOk] at hcen
    rw [abs_of_nonneg hr0] at hpt1 hpt2
    simp only [abs_le] at hpt1 hpt2
    omega

theorem layout_cell_arc_spec (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize)
    (phases : Slice Std.I32) (h : cell.val < L.cells.val.length)
    (hph : L.transforms.val ≤ phases.val.length) :
    scene.Layout.cell_arc L cell phases ⦃ a => ArcOk a ⦄ := by
  unfold scene.Layout.cell_arc
  simp only [alloc.vec.Vec.index_slice_index]
  step as ⟨c, hc⟩
  have hcell := hL.cell cell h
  have hc' : c = L.cells.val[cell.val]'h := hc
  subst hc'
  have hturn := turn_val
  cases hcc : L.cells.val[cell.val]'h with
  | Grid a b bd => simp [spec_ok, ArcOk, hturn]
  | Center k => simp [spec_ok, ArcOk, hturn]
  | Transition p =>
    rw [hcc] at hcell
    obtain ⟨hp, hcirc, hmouth⟩ := hcell
    step as ⟨pp, hpp⟩
    rw [hpp]; exact hmouth
  | Sector k r s =>
    rw [hcc] at hcell
    obtain ⟨hk, hr, hs⟩ := hcell
    step as ⟨c1, hc1⟩
    have hco := hL.circles k.val hk
    have hc1' : c1 = L.circles.val[k.val]'hk := hc1
    subst hc1'
    step as ⟨arc, harc, harc2⟩
    step as ⟨mm, hmm⟩
    cases mm with
    | Spinning =>
      have hpt := hco.transform
      step as ⟨i, hi, hi2⟩
      step as ⟨a, ha⟩
      exact ha
    | Twisting a m => simp only [spec_ok]; exact harc

@[step]
theorem layout_cell_arc_step (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize)
    (phases : Slice Std.I32) (h : cell.val < L.cells.val.length)
    (hph : L.transforms.val ≤ phases.val.length) :
    scene.Layout.cell_arc L cell phases ⦃ a => ArcOk a ⦄ := layout_cell_arc_spec L hL cell phases h hph

theorem layout_swept_arc_spec (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize)
    (arc : polar.Arc) (mode : polar.MotionMode) (next : Slice Std.I32)
    (h : cell.val < L.cells.val.length) (harc : ArcOk arc)
    (hmode : ∀ a m, mode = .Twisting a m → 0 ≤ a.val ∧ a.val ≤ 512)
    (hnext : L.transforms.val ≤ next.val.length) :
    scene.Layout.swept_arc L cell arc mode next ⦃ r => ArcOk r ⦄ := by
  unfold scene.Layout.swept_arc
  cases mode with
  | Spinning =>
    step as ⟨a, ha⟩
    have harc' := harc
    have ha' := ha
    unfold ArcOk at harc' ha'
    step as ⟨i, hi, hi2⟩
    have hi' : -4096 ≤ i.val ∧ i.val ≤ 4096 := by omega
    step as ⟨r, hr⟩
    exact hr
  | Twisting amp m =>
    have hamp := hmode amp m rfl
    step as ⟨i, hi⟩
    have hi' : -1000000000 ≤ i.val ∧ i.val ≤ 1000000000 := by omega
    have harc' := harc
    unfold ArcOk at harc'
    step as ⟨a, ha, hb1, hb2⟩
    have ha' := ha
    unfold ArcOk at ha'
    step as ⟨i1, hi1⟩
    have hi1' : -4096 ≤ i1.val ∧ i1.val ≤ 4096 := by omega
    step as ⟨r, hr⟩
    exact hr

/-! ### Hold sets -/

theorem usize_saturating_sub_one (x : Std.Usize) :
    (core.num.Usize.saturating_sub x 1#usize).val = x.val - 1 := by
  simp only [core.num.Usize.saturating_sub, UScalar.saturating_sub, UScalar.val]
  have := x.hBounds
  simp [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by simp [UScalarTy.numBits] at this; omega)


/-- A hold set never records more than its four slots. -/
def HoldsOk (h : walker.Holds) : Prop := h.count.val ≤ 4

theorem walker_holds_insert_loop_spec (self : walker.Holds) (id slot : Std.Usize)
    (hc : self.count.val ≤ 4) (hs : slot.val ≤ self.count.val) :
    walker.Holds.insert_loop self id slot ⦃ r =>
      r.1 = self.ids ∧ r.2.1 = self.count ∧ r.2.2.val ≤ self.count.val ⦄ := by
  unfold walker.Holds.insert_loop
  apply loop.spec_decr_nat
    (fun slot : Std.Usize => self.count.val - slot.val)
    (fun slot : Std.Usize => slot.val ≤ self.count.val)
    _
  · intro slot hslot
    unfold walker.Holds.insert_loop.body
    by_cases hlt : slot < self.count
    · simp only [hlt, ite_true]
      have hlt' : slot.val < 4 := by scalar_tac
      step as ⟨i, hi⟩
      by_cases hne : (i != id) = true
      · simp only [hne, ite_true]
        step as ⟨slot1, hslot1⟩
        scalar_tac
      · have hne' : (i != id) = false := Bool.eq_false_iff.mpr hne
        simp only [hne', Bool.false_eq_true, ↓reduceIte, spec_ok]
        scalar_tac
    · have hlt2 : ¬ slot < self.count := hlt
      simp only [hlt2, ite_false, spec_ok]
      scalar_tac
  · exact hs

theorem array4_len_val {α : Type _} (arr : Array α 4#usize) :
    Slice.len (Array.to_slice arr) = 4#usize := by
  apply UScalar.eq_of_val_eq
  rw [Slice.len_val]
  simp [Array.to_slice, Slice.length, arr.property]

theorem walker_holds_insert_spec (self : walker.Holds) (id : Std.Usize) (hc : HoldsOk self) :
    walker.Holds.insert self id ⦃ r => HoldsOk r.2 ⦄ := by
  unfold walker.Holds.insert
  unfold HoldsOk at hc
  apply spec_bind (walker_holds_insert_loop_spec self id 0#usize hc (by simp))
  rintro ⟨a, i, slot⟩ ⟨ha, hi, hslot⟩
  simp only at ha hi hslot
  subst ha hi
  show (if slot = self.count then _ else _) ⦃ _ ⦄
  by_cases hs : slot = self.count
  · simp only [hs, ite_true]
    simp only [lift, Std.bind_ok, array4_len_val]
    by_cases hfull : self.count = 4#usize
    · simp only [hfull, ite_true, spec_ok]
      unfold HoldsOk; simp [hfull]
    · have hfull' : ¬ self.count = 4#usize := hfull
      simp only [hfull', ite_false]
      have hslot4 : slot.val < 4 := by
        have : self.count.val ≠ 4 := fun h => hfull (UScalar.eq_of_val_eq (by simpa using h))
        scalar_tac
      step as ⟨a1, ha1⟩
      step as ⟨i2, hi2⟩
      unfold HoldsOk
      scalar_tac
  · simp only [hs, ite_false, spec_ok]
    exact hc

theorem layout_holds_loop1_spec (c : polar.Circle) (last : Std.Usize) (result : walker.Holds)
    (status : core.result.Result Unit topology.Error) (ring : Std.Usize)
    (hr : HoldsOk result) (hring : ring.val ≤ last.val + 1)
    (hlast : last.val + 1 ≤ Std.Usize.max)
    (hts : c.transform_start.val + last.val ≤ Std.Usize.max) :
    scene.Layout.holds_loop1 result c last status ring ⦃ r => HoldsOk r.2 ⦄ := by
  unfold scene.Layout.holds_loop1
  apply loop.spec_decr_nat
    (fun st : walker.Holds × (core.result.Result Unit topology.Error) × Std.Usize =>
      last.val + 1 - st.2.2.val)
    (fun st : walker.Holds × (core.result.Result Unit topology.Error) × Std.Usize =>
      HoldsOk st.1 ∧ st.2.2.val ≤ last.val + 1)
    _
  · rintro ⟨res, st, rg⟩ ⟨hres, hrg⟩
    unfold scene.Layout.holds_loop1.body
    by_cases hle : rg ≤ last
    · simp only [hle, ite_true]
      step as ⟨b, hb⟩
      by_cases hb' : b = true
      · simp only [hb', ite_true]
        step as ⟨id, hid⟩
        apply spec_bind (walker_holds_insert_spec res id hres)
        rintro ⟨st1, res1⟩ hres1
        step as ⟨rg1, hrg1⟩
        exact ⟨hres1, by scalar_tac, by scalar_tac⟩
      · have hbf : b = false := by simpa using hb'
        simp only [hbf, Bool.false_eq_true, ↓reduceIte, spec_ok]
        exact hres
    · have hle2 : ¬ rg ≤ last := hle
      simp only [hle2, ite_false, spec_ok]
      exact hres
  · exact ⟨hr, hring⟩

theorem layout_holds_loop2_spec (c : polar.Circle) (last : Std.Usize) (result : walker.Holds)
    (status : core.result.Result Unit topology.Error) (ring : Std.Usize)
    (hr : HoldsOk result) (hring : ring.val ≤ last.val + 1)
    (hlast : last.val + 1 ≤ Std.Usize.max)
    (hts : c.transform_start.val + last.val ≤ Std.Usize.max) :
    scene.Layout.holds_loop2 result c last status ring ⦃ r => HoldsOk r.2 ⦄ := by
  unfold scene.Layout.holds_loop2
  apply loop.spec_decr_nat
    (fun st : walker.Holds × (core.result.Result Unit topology.Error) × Std.Usize =>
      last.val + 1 - st.2.2.val)
    (fun st : walker.Holds × (core.result.Result Unit topology.Error) × Std.Usize =>
      HoldsOk st.1 ∧ st.2.2.val ≤ last.val + 1)
    _
  · rintro ⟨res, st, rg⟩ ⟨hres, hrg⟩
    unfold scene.Layout.holds_loop2.body
    by_cases hle : rg ≤ last
    · simp only [hle, ite_true]
      step as ⟨b, hb⟩
      by_cases hb' : b = true
      · simp only [hb', ite_true]
        step as ⟨id, hid⟩
        apply spec_bind (walker_holds_insert_spec res id hres)
        rintro ⟨st1, res1⟩ hres1
        step as ⟨rg1, hrg1⟩
        exact ⟨hres1, by scalar_tac, by scalar_tac⟩
      · have hbf : b = false := by simpa using hb'
        simp only [hbf, Bool.false_eq_true, ↓reduceIte, spec_ok]
        exact hres
    · have hle2 : ¬ rg ≤ last := hle
      simp only [hle2, ite_false, spec_ok]
      exact hres
  · exact ⟨hr, hring⟩

theorem layout_holds_loop0_spec (c : polar.Circle) (result : walker.Holds)
    (status : core.result.Result Unit topology.Error) (ring : Std.Usize)
    (hr : HoldsOk result) (hring : ring.val ≤ 1)
    (hts : c.transform_start.val + 1 ≤ Std.Usize.max) :
    scene.Layout.holds_loop0 result c status ring ⦃ r => HoldsOk r.2 ⦄ := by
  unfold scene.Layout.holds_loop0
  apply loop.spec_decr_nat
    (fun st : walker.Holds × (core.result.Result Unit topology.Error) × Std.Usize =>
      1 - st.2.2.val)
    (fun st : walker.Holds × (core.result.Result Unit topology.Error) × Std.Usize =>
      HoldsOk st.1 ∧ st.2.2.val ≤ 1)
    _
  · rintro ⟨res, st, rg⟩ ⟨hres, hrg⟩
    unfold scene.Layout.holds_loop0.body
    by_cases hle : rg ≤ 0#usize
    · simp only [hle, ite_true]
      step as ⟨b, hb⟩
      by_cases hb' : b = true
      · simp only [hb', ite_true]
        step as ⟨id, hid⟩
        apply spec_bind (walker_holds_insert_spec res id hres)
        rintro ⟨st1, res1⟩ hres1
        step as ⟨rg1, hrg1⟩
        exact ⟨hres1, by scalar_tac, by scalar_tac⟩
      · have hbf : b = false := by simpa using hb'
        simp only [hbf, Bool.false_eq_true, ↓reduceIte, spec_ok]
        exact hres
    · have hle2 : ¬ rg ≤ 0#usize := hle
      simp only [hle2, ite_false, spec_ok]
      exact hres
  · exact ⟨hr, hring⟩


@[step]
theorem layout_circle_of_step (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize)
    (h : cell.val < L.cells.val.length) :
    scene.Layout.circle_of L cell ⦃ o => o = cellCircle L (L.cells.val[cell.val]'h) ⦄ :=
  layout_circle_of_spec L hL cell h

theorem layout_holds_spec (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize)
    (result : walker.Holds) (h : cell.val < L.cells.val.length) (hres : HoldsOk result) :
    scene.Layout.holds L cell result ⦃ r => HoldsOk r.2 ⦄ := by
  unfold scene.Layout.holds
  step as ⟨o, ho⟩
  have hcell := hL.cell cell h
  cases hcc : L.cells.val[cell.val]'h with
  | Grid a b bd => 
    rw [hcc] at ho
    subst ho
    simp only [cellCircle, spec_ok]
    exact hres
  | Center k =>
    rw [hcc] at ho
    subst ho
    rw [hcc] at hcell
    simp only [cellCircle]
    have hk : k.val < L.circles.val.length := hcell
    step as ⟨c, hc⟩
    step as ⟨c1, hc1⟩
    rw [hcc] at hc1
    subst hc1
    simp only []
    step as ⟨mm, hmm⟩
    have hco := hL.circles k.val hk
    have hc' : c = L.circles.val[k.val]'hk := hc
    subst hc'
    cases mm with
    | Spinning => simp only [spec_ok]; exact hres
    | Twisting a m =>
      have hts := hco.transform
      have hmax := L.transforms.hmax
      have hn := hco.rings
      apply layout_holds_loop0_spec _ result _ 0#usize hres (by simp) (by scalar_tac)
  | Sector k r s =>
    rw [hcc] at ho
    subst ho
    rw [hcc] at hcell
    obtain ⟨hk, hr, hs⟩ := hcell
    simp only [cellCircle]
    step as ⟨c, hc⟩
    step as ⟨c1, hc1⟩
    rw [hcc] at hc1
    subst hc1
    simp only []
    step as ⟨mm, hmm⟩
    have hco := hL.circles k.val hk
    have hc' : c = L.circles.val[k.val]'hk := hc
    subst hc'
    have hts := hco.transform
    have hmax := L.transforms.hmax
    have hn := hco.rings
    cases mm with
    | Spinning =>
      simp only [Std.bind_ok]
      apply layout_holds_loop1_spec _ _ result _ _ hres (by simp) (by scalar_tac) (by scalar_tac)
    | Twisting a m =>
      simp only [lift, Std.bind_ok]
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      have hsat := usize_saturating_sub_one r
      have hmin : (core.cmp.impls.OrdUsize.min i1 i3).val = min i1.val i3.val := by simp
      apply layout_holds_loop1_spec _ _ result _ _ hres (by scalar_tac) (by scalar_tac) (by scalar_tac)
  | Transition p =>
    rw [hcc] at ho
    subst ho
    rw [hcc] at hcell
    obtain ⟨hp, hcirc, hmouth⟩ := hcell
    simp only [cellCircle, hp, ↓reduceDIte]
    step as ⟨c, hc⟩
    step as ⟨c1, hc1⟩
    rw [hcc] at hc1
    subst hc1
    simp only []
    have hco := hL.circles _ hcirc
    have hc' : c = L.circles.val[(L.portals.val[p.val]'hp).spec.circle.val]'hcirc := hc
    subst hc'
    have hts := hco.transform
    have hmax := L.transforms.hmax
    have hn := hco.rings
    step as ⟨i, hi⟩
    step as ⟨first, hfirst⟩
    step as ⟨last, hlast⟩
    apply layout_holds_loop2_spec _ _ result _ _ hres (by scalar_tac) (by scalar_tac) (by scalar_tac)

end Labyrinth
