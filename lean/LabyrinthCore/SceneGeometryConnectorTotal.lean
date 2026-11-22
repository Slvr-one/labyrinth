module
public import LabyrinthCore.SceneGeometryDoorway
public import LabyrinthCore.SceneGeometryDisk

/-! Geometry totality (S8), connector verification: under `LayoutGeom` and a valid carrier,
`check_connector_pair`, the three scan loops of `check_connector`, `check_connector` and the loop
that verifies every portal return a value. A rejection is `InvalidIndex`, `InvalidGeometry` or
`InsufficientWorkspace`. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

/-- The rejections a connector check can produce. -/
def ConnectorStatusOk (s : core.result.Result Unit topology.Error) : Prop :=
  ∀ e, s = .Err e → e = .InvalidIndex ∨ e = .InvalidGeometry ∨ e = .InsufficientWorkspace

theorem connectorStatusOk_ok : ConnectorStatusOk (.Ok ()) := by
  intro e he; cases he

theorem connectorStatusOk_geom : ConnectorStatusOk (.Err .InvalidGeometry) := by
  intro e he; cases he; simp

/-- An admitted doorway has both endpoints among the cells. -/
theorem doorway_ok_in_range (L : scene.Layout) (edge : topology.Edge) (phases next : Slice Std.I32)
    (d : scene.Doorway) (h : scene.Layout.doorway L edge phases next = ok (.Ok d)) :
    edge.u.val < L.cells.val.length ∧ edge.v.val < L.cells.val.length := by
  unfold scene.Layout.doorway at h
  by_cases hu : edge.u ≥ alloc.vec.Vec.len L.cells
  · simp only [hu, ↓reduceIte] at h; simp at h
  by_cases hv : edge.v ≥ alloc.vec.Vec.len L.cells
  · simp only [hu, hv, ↓reduceIte] at h; simp at h
  constructor <;> scalar_tac

theorem edge_new_spec (a b : Std.Usize) :
    topology.Edge.new a b ⦃ e => (e.u = a ∧ e.v = b) ∨ (e.u = b ∧ e.v = a) ⦄ := by
  unfold topology.Edge.new
  split_ifs <;> simp [spec_ok]

/-- Taking the first/second `Try::branch` outcome of a doorway result. -/
theorem doorway_residual_status (L : scene.Layout) (edge : topology.Edge) (e : topology.Error)
    (he : e = .InvalidIndex ∨ e = .InvalidGeometry ∨ e = .InsufficientWorkspace) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
      (core.convert.FromSame topology.Error) (.Err e) ⦃ r => ConnectorStatusOk r ⦄ := by
  simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, Std.bind_ok, spec_ok, ConnectorStatusOk]
  simp
  exact he

theorem layout_check_connector_pair_spec (L : scene.Layout) (hL : LayoutGeom L)
    (hc : CarrierValid L.carrier) (portal : scene.Portal) (corridor : grid.Rect)
    (other : scene.Portal) (phases : Slice Std.I32) (hph : L.transforms.val ≤ phases.val.length) :
    scene.Layout.check_connector_pair L portal corridor other phases ⦃ r => ConnectorStatusOk r ⦄ := by
  unfold scene.Layout.check_connector_pair
  apply spec_bind (edge_new_spec _ _)
  intro e he
  obtain ⟨r, hr, hdoor, -⟩ := layout_doorway_total L hL hc e phases phases hph hph
  rw [hr]
  simp only [Std.bind_ok]
  cases r with
  | Err err =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    exact doorway_residual_status L e err (hdoor.2 err rfl)
  | Ok val =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    have hrange := doorway_ok_in_range L e phases phases val hr
    step as ⟨b, hb⟩
    by_cases hbt : b = true
    · simp only [hbt, ↓reduceIte, lift, Std.bind_ok]
      by_cases hg : portal.grid_cell = other.grid_cell
      · simp only [hg, ↓reduceIte]
        have hlt : other.grid_cell.val < L.cells.val.length := by
          rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have := hrange.1; rw [h1] at this; exact this
          · have := hrange.2; rw [h2] at this; exact this
        rw [← hg] at hlt
        step as ⟨c, hcell⟩
        cases c with
        | Grid a b bd =>
          step as ⟨b1, hb1⟩
          by_cases hb1t : b1 = true
          · simp only [hb1t, ↓reduceIte]
            exact (spec_ok _).mpr connectorStatusOk_ok
          · have hb1f : b1 = false := by simpa using hb1t
            simp only [hb1f, Bool.false_eq_true, ↓reduceIte]
            exact (spec_ok _).mpr connectorStatusOk_geom
        | Center k => exact (spec_ok _).mpr connectorStatusOk_geom
        | Sector k r s => exact (spec_ok _).mpr connectorStatusOk_geom
        | Transition k => exact (spec_ok _).mpr connectorStatusOk_geom
      · simp only [hg, ↓reduceIte]
        exact (spec_ok _).mpr connectorStatusOk_geom
    · have hbf : b = false := by simpa using hbt
      simp only [hbf, Bool.false_eq_true, ↓reduceIte]
      exact (spec_ok _).mpr connectorStatusOk_ok

/-- `check_connector_pair` returns for every candidate portal pair. -/
theorem layout_check_connector_pair_total (L : scene.Layout) (hL : LayoutGeom L)
    (hc : CarrierValid L.carrier) (portal : scene.Portal) (corridor : grid.Rect)
    (other : scene.Portal) (phases : Slice Std.I32) (hph : L.transforms.val ≤ phases.val.length) :
    ∃ r, scene.Layout.check_connector_pair L portal corridor other phases = ok r ∧
      ConnectorStatusOk r :=
  spec_exists_ok (layout_check_connector_pair_spec L hL hc portal corridor other phases hph)

/-! ### The scan loops -/

theorem layout_check_connector_loop0_spec (v : alloc.vec.Vec scene.Cell) (i : Std.Usize)
    (corridor : grid.Rect) (blocked : Bool) (cell : Std.Usize)
    (hcell : cell.val ≤ v.val.length) :
    scene.Layout.check_connector_loop0 v i corridor blocked cell ⦃ _ => True ⦄ := by
  unfold scene.Layout.check_connector_loop0
  apply loop.spec_decr_nat
    (fun st : Bool × Std.Usize => v.val.length - st.2.val)
    (fun st : Bool × Std.Usize => st.2.val ≤ v.val.length)
    _
  · rintro ⟨bl, k⟩ hk
    simp only at hk
    unfold scene.Layout.check_connector_loop0.body
    by_cases hlt : k < alloc.vec.Vec.len v
    · simp only [hlt, ↓reduceIte]
      have hlt' : k.val < v.val.length := by scalar_tac
      by_cases hb : bl = true
      · simp only [hb, ↓reduceIte, spec_ok]
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        simp only [alloc.vec.Vec.index_slice_index]
        step as ⟨kind, hkind⟩
        have hgi : ∀ (c : scene.Cell) (inc : Bool),
            scene.grid_intersects c corridor inc ⦃ _ => True ⦄ := by
          intro c inc
          unfold scene.grid_intersects
          split_ifs
          · cases c <;> simp [spec_ok]
            all_goals step*
          · simp [spec_ok]
        apply spec_bind (hgi kind (k != i))
        intro b1 _
        step as ⟨k1, hk1⟩
        scalar_tac
    · simp only [hlt, ↓reduceIte, spec_ok]
  · exact hcell

theorem layout_check_connector_loop1_spec (v : alloc.vec.Vec polar.Circle) (v1 : alloc.vec.Vec Std.I32)
    (i : Std.Usize) (corridor : grid.Rect) (margin : Std.I32) (blocked : Bool) (other : Std.Usize)
    (transforms : Nat) (hcirc : ∀ j, ∀ h : j < v.val.length, CircleOk (v.val[j]'h) transforms)
    (hlen : v1.val.length = v.val.length)
    (hband : ∀ j, ∀ h : j < v1.val.length, ∀ h2 : j < v.val.length,
      0 ≤ (v1.val[j]'h).val ∧ (v.val[j]'h2).outer.val + (v1.val[j]'h).val ≤ 1000000)
    (hrect : RectOk corridor) (hm0 : 0 ≤ margin.val) (hm : margin.val ≤ 1000000)
    (hother : other.val ≤ v.val.length) :
    scene.Layout.check_connector_loop1 v v1 i corridor margin blocked other ⦃ _ => True ⦄ := by
  unfold scene.Layout.check_connector_loop1
  apply loop.spec_decr_nat
    (fun st : Bool × Std.Usize => v.val.length - st.2.val)
    (fun st : Bool × Std.Usize => st.2.val ≤ v.val.length)
    _
  · rintro ⟨bl, k⟩ hk
    simp only at hk
    unfold scene.Layout.check_connector_loop1.body
    by_cases hlt : k < alloc.vec.Vec.len v
    · simp only [hlt, ↓reduceIte]
      have hlt' : k.val < v.val.length := by scalar_tac
      by_cases hb : bl = true
      · simp only [hb, ↓reduceIte, spec_ok]
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        simp only [alloc.vec.Vec.index_slice_index]
        step as ⟨c, hc⟩
        step as ⟨center, hcen⟩
        have hco := hcirc k.val hlt'
        have hc' : c = v.val[k.val]'hlt' := hc
        have hk1 : k.val < v1.val.length := by omega
        step as ⟨bd, hbd⟩
        have hbd' : bd = v1.val[k.val]'hk1 := hbd
        have hb2 := hband k.val hk1 hlt'
        subst hc' hbd'
        step as ⟨i3, hi3⟩
        step as ⟨radius, hrad⟩
        have hdi : scene.disk_intersects corridor center radius (k != i) ⦃ _ => True ⦄ := by
          unfold scene.disk_intersects
          split_ifs
          · obtain ⟨b, hb, -⟩ := grid_rect_touches_disk_total corridor center radius hrect (by
              have := hco.center; subst hcen; unfold PointOk at this; unfold BoundsPointOk; omega)
            rw [hb]; simp [spec_ok]
          · simp [spec_ok]
        apply spec_bind hdi
        intro b1 _
        step as ⟨k1, hk1'⟩
        scalar_tac
    · simp only [hlt, ↓reduceIte, spec_ok]
  · exact hother

theorem layout_check_connector_loop2_spec (L : scene.Layout) (hL : LayoutGeom L)
    (hc : CarrierValid L.carrier) (index : Std.Usize) (phases : Slice Std.I32)
    (i1 i2 i3 : Std.Usize) (a : polar.Arc) (i4 : Std.I32) (i5 i6 : Std.Usize) (corridor : grid.Rect)
    (status : core.result.Result Unit topology.Error) (other : Std.Usize)
    (hph : L.transforms.val ≤ phases.val.length) (hindex : index.val ≤ L.portals.val.length)
    (hst : ConnectorStatusOk status) (hother : other.val ≤ index.val) :
    scene.Layout.check_connector_loop2 L.cell_grid L.cells L.circles L.portals L.bands L.geometry
      L.carrier L.transforms index phases i1 i2 i3 a i4 i5 i6 corridor status other
      ⦃ r => ConnectorStatusOk r ⦄ := by
  unfold scene.Layout.check_connector_loop2
  apply loop.spec_decr_nat
    (fun st : (core.result.Result Unit topology.Error) × Std.Usize => index.val - st.2.val)
    (fun st : (core.result.Result Unit topology.Error) × Std.Usize =>
      ConnectorStatusOk st.1 ∧ st.2.val ≤ index.val)
    _
  · rintro ⟨st, k⟩ ⟨hs, hk⟩
    simp only at hs hk
    unfold scene.Layout.check_connector_loop2.body
    by_cases hlt : k < index
    · simp only [hlt, ↓reduceIte]
      have hlt' : k.val < L.portals.val.length := by scalar_tac
      step as ⟨b, hb⟩
      by_cases hbt : b = true
      · simp only [hbt, ↓reduceIte]
        step as ⟨p, hp⟩
        apply spec_bind (layout_check_connector_pair_spec L hL hc _ corridor p phases hph)
        intro st1 hst1
        step as ⟨k1, hk1⟩
        exact ⟨hst1, by scalar_tac⟩
      · simp only [hbt, Bool.false_eq_true, ↓reduceIte, spec_ok]
        exact hs
    · simp only [hlt, ↓reduceIte, spec_ok]
      exact hs
  · exact ⟨hst, hother⟩

/-- `check_connector` returns for a portal whose circle exists. -/
theorem layout_check_connector_spec (L : scene.Layout) (hL : LayoutGeom L)
    (hc : CarrierValid L.carrier) (index : Std.Usize) (phases : Slice Std.I32)
    (hph : L.transforms.val ≤ phases.val.length) (hidx : index.val < L.portals.val.length)
    (hcirc : (L.portals.val[index.val]'hidx).spec.circle.val < L.circles.val.length) :
    scene.Layout.check_connector L index phases ⦃ r => ConnectorStatusOk r ⦄ := by
  unfold scene.Layout.check_connector
  step as ⟨portal, hportal⟩
  have hportal' : portal = L.portals.val[index.val]'hidx := hportal
  subst hportal'
  apply spec_bind (edge_new_spec _ _)
  intro e he
  obtain ⟨r, hr, hdoor, -⟩ := layout_doorway_total L hL hc e phases phases hph hph
  rw [hr]
  simp only [Std.bind_ok]
  cases r with
  | Err err =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    exact doorway_residual_status L e err (hdoor.2 err rfl)
  | Ok val =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    obtain ⟨hdc, hdcor, -⟩ := hdoor.1 val rfl
    step as ⟨circle, hcircle⟩
    have hco := hL.circles _ hcirc
    have hcircle' : circle = L.circles.val[(L.portals.val[index.val]'hidx).spec.circle.val]'hcirc := hcircle
    subst hcircle'
    step as ⟨mr, hmr1, hmr2, hmr3⟩
    obtain ⟨m, rfl⟩ := hmr2 hL.margin
    obtain ⟨hmo, hm⟩ := hmr1 m rfl
    have hmg := hL.margin
    unfold MarginOk at hmg
    simp only [branch_ok_eq, Std.bind_ok]
    step as ⟨cen, hcen⟩
    have hout := hco.outer_le
    step as ⟨i, hi⟩
    obtain ⟨b, hb, -⟩ := grid_rect_touches_disk_total val.corridor cen i hdcor.1 (by
      have := hco.center; subst hcen; unfold PointOk at this; unfold BoundsPointOk; omega)
    rw [hb]
    simp only [Std.bind_ok]
    by_cases hbt : b = true
    · simp only [hbt, ↓reduceIte]
      exact (spec_ok _).mpr connectorStatusOk_geom
    · have hbf : b = false := by simpa using hbt
      simp only [hbf, Bool.false_eq_true, ↓reduceIte]
      apply spec_bind (layout_check_connector_loop0_spec L.cells _ val.corridor false 0#usize
        (by simp))
      intro blocked _
      apply spec_bind (layout_check_connector_loop1_spec L.circles L.bands _ val.corridor m blocked
        0#usize L.transforms.val hL.circles hL.bands_len hL.bands hdcor.1 (by omega) (by omega)
        (by simp))
      intro blocked1 _
      by_cases hb1 : blocked1 = true
      · simp only [hb1, ↓reduceIte]
        exact (spec_ok _).mpr connectorStatusOk_geom
      · have hb1f : blocked1 = false := by simpa using hb1
        simp only [hb1f, Bool.false_eq_true, ↓reduceIte]
        exact layout_check_connector_loop2_spec L hL hc index phases _ _ _ _ _ _ _ val.corridor
          (.Ok ()) 0#usize hph (by scalar_tac) connectorStatusOk_ok (by simp)

/-- `check_connector` returns for every portal index of a validated layout in which every portal
names an existing circle. -/
theorem layout_check_connector_total (L : scene.Layout) (hL : LayoutGeom L)
    (hc : CarrierValid L.carrier) (index : Std.Usize) (phases : Slice Std.I32)
    (hph : L.transforms.val ≤ phases.val.length) (hidx : index.val < L.portals.val.length)
    (hcirc : (L.portals.val[index.val]'hidx).spec.circle.val < L.circles.val.length) :
    ∃ r, scene.Layout.check_connector L index phases = ok r ∧ ConnectorStatusOk r :=
  spec_exists_ok (layout_check_connector_spec L hL hc index phases hph hidx hcirc)

/-- The verification loop of `Layout::new` returns, and every rejection is `InvalidIndex`,
`InvalidGeometry` or `InsufficientWorkspace`. -/
theorem layout_new_loop9_spec (L : scene.Layout) (hL : LayoutGeom L) (hc : CarrierValid L.carrier)
    (zero : alloc.vec.Vec Std.I32) (hzero : L.transforms.val ≤ zero.val.length)
    (hcirc : ∀ j, ∀ h : j < L.portals.val.length,
      (L.portals.val[j]'h).spec.circle.val < L.circles.val.length)
    (status : core.result.Result Unit topology.Error) (hst : ConnectorStatusOk status)
    (i : Std.Usize) (hi : i.val ≤ L.portals.val.length) :
    scene.Layout.new_loop9 status L.cell_grid L.cells L.circles L.portals L.bands L.geometry
      L.carrier L.transforms zero i ⦃ r => ConnectorStatusOk r ⦄ := by
  unfold scene.Layout.new_loop9
  apply loop.spec_decr_nat
    (fun st : (core.result.Result Unit topology.Error) × Std.Usize => L.portals.val.length - st.2.val)
    (fun st : (core.result.Result Unit topology.Error) × Std.Usize =>
      ConnectorStatusOk st.1 ∧ st.2.val ≤ L.portals.val.length)
    _
  · rintro ⟨st, k⟩ ⟨hs, hk⟩
    simp only at hs hk
    unfold scene.Layout.new_loop9.body
    by_cases hlt : k < alloc.vec.Vec.len L.portals
    · simp only [hlt, ↓reduceIte]
      have hlt' : k.val < L.portals.val.length := by scalar_tac
      step as ⟨b, hb⟩
      by_cases hbt : b = true
      · simp only [hbt, ↓reduceIte]
        have hph : L.transforms.val ≤ (alloc.vec.Vec.deref zero).val.length := by
          simpa [alloc.vec.Vec.deref] using hzero
        apply spec_bind (layout_check_connector_spec L hL hc k (alloc.vec.Vec.deref zero) hph hlt'
          (hcirc k.val hlt'))
        intro st1 hst1
        step as ⟨k1, hk1⟩
        exact ⟨hst1, by scalar_tac⟩
      · simp only [hbt, Bool.false_eq_true, ↓reduceIte, spec_ok]
        exact hs
    · simp only [hlt, ↓reduceIte, spec_ok]
      exact hs
  · exact ⟨hst, hi⟩

/-- `Layout::new_loop9` never fails in the model. -/
theorem layout_new_loop9_total (L : scene.Layout) (hL : LayoutGeom L) (hc : CarrierValid L.carrier)
    (zero : alloc.vec.Vec Std.I32) (hzero : L.transforms.val ≤ zero.val.length)
    (hcirc : ∀ j, ∀ h : j < L.portals.val.length,
      (L.portals.val[j]'h).spec.circle.val < L.circles.val.length)
    (status : core.result.Result Unit topology.Error) (hst : ConnectorStatusOk status)
    (i : Std.Usize) (hi : i.val ≤ L.portals.val.length) :
    ∃ r, scene.Layout.new_loop9 status L.cell_grid L.cells L.circles L.portals L.bands L.geometry
      L.carrier L.transforms zero i = ok r ∧ ConnectorStatusOk r :=
  spec_exists_ok (layout_new_loop9_spec L hL hc zero hzero hcirc status hst i hi)

end Labyrinth
