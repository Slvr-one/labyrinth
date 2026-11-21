module
public import LabyrinthCore.SceneGeometrySweep
public import LabyrinthCore.SceneRouteBudget

/-! Geometry totality (S8), doorways: under `LayoutGeom` and a valid carrier, `Layout::doorway`
returns for every edge and phase vectors covering the layout's transforms. An admitted doorway is a
carrier edge whose corridor passes `Geometry::check`; a rejection is `InvalidIndex`,
`InvalidGeometry` or `InsufficientWorkspace`. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

/-- A corridor accepted by `Geometry::check`. -/
def CorridorOk (g : grid.Geometry) (r : grid.Rect) : Prop :=
  RectOk r ∧ RectHolds g.viewport r ∧ ∀ k, ∀ h : k < g.obstacles.val.length, ¬ RectMeets r g.obstacles.val[k]

/-- What `doorway` returns for an edge of a layout satisfying `LayoutGeom`. -/
def DoorwayOk (L : scene.Layout) (edge : topology.Edge)
    (r : core.result.Result scene.Doorway topology.Error) : Prop :=
  (∀ d, r = .Ok d → carrierEdge L.carrier edge.u.val edge.v.val ∧
    CorridorOk L.geometry d.corridor ∧ HoldsOk d.holds) ∧
  (∀ e, r = .Err e → e = .InvalidIndex ∨ e = .InvalidGeometry ∨ e = .InsufficientWorkspace)

/-- `Rect::between` on points within twice the coordinate limit fails only with `InvalidGeometry`. -/
theorem grid_rect_between_near (a b : grid.Point) (m : Std.I32) (ha : BoundsPointOk a)
    (hb : BoundsPointOk b) (hm : m.val ≤ 1000000) :
    grid.Rect.between a b m ⦃ x =>
      (∀ e, x = .Ok e → RectOk e) ∧ (∀ e, x = .Err e → e = .InvalidGeometry) ⦄ := by
  unfold grid.Rect.between
  split_ifs with hm0
  · simp [spec_ok]
  · simp only [lift, Std.bind_ok]
    apply spec_mono (grid_rect_expand_spec
      { min := { x := core.cmp.impls.OrdI32.min a.x b.x, y := core.cmp.impls.OrdI32.min a.y b.y },
        max := { x := core.cmp.impls.OrdI32.max a.x b.x, y := core.cmp.impls.OrdI32.max a.y b.y } } m)
    rintro x ⟨h1, h2, h3, h4⟩
    refine ⟨fun e he => (h1 e he).2.2.2.2.2, fun e he => h4 ?_ ?_ ?_ ?_ ?_ e he⟩ <;>
      simp [BoundsPointOk] at * <;> omega

theorem branch_ok_eq {T E : Type} (v : T) :
    core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Ok v : core.result.Result T E) =
      ok (.Continue v) := rfl

theorem branch_err_eq {T E : Type} (e : E) :
    core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Err e : core.result.Result T E) =
      ok (.Break (.Err e)) := rfl

/-- A bind on an `if` between two returned values. -/
theorem bind_ite_ok {α β : Type _} (c : Prop) [Decidable c] (x y : α) (k : α → Result β) :
    Std.bind (if c then ok x else ok y) k = k (if c then x else y) := by
  split <;> simp only [Std.bind_ok]

@[step]
theorem scene_same_ring_spec (a b : scene.Cell) : scene.same_ring a b ⦃ _ => True ⦄ := by
  unfold scene.same_ring
  cases a <;> cases b <;> simp [spec_ok]

theorem doorway_err_residual (L : scene.Layout) (edge : topology.Edge) (e : topology.Error)
    (he : e = .InvalidIndex ∨ e = .InvalidGeometry ∨ e = .InsufficientWorkspace) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual scene.Doorway
      (core.convert.FromSame topology.Error) (.Err e) ⦃ r => DoorwayOk L edge r ⦄ := by
  simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, Std.bind_ok, spec_ok, DoorwayOk]
  simp
  exact he

/-- The common end of every doorway: `Geometry::check` on the corridor. -/
theorem doorway_check_tail (L : scene.Layout) (edge : topology.Edge)
    (hce : carrierEdge L.carrier edge.u.val edge.v.val) (corridor : grid.Rect) (path : walker.Path)
    (h2 : walker.Holds) (hh2 : HoldsOk h2) :
    (do
      let r4 ← grid.Geometry.check L.geometry corridor
      let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
      match cf4 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        ok (core.result.Result.Ok ({ corridor := corridor, path := path, holds := h2 } : scene.Doorway))
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          scene.Doorway (core.convert.FromSame topology.Error) residual) ⦃ r => DoorwayOk L edge r ⦄ := by
  step as ⟨x, hx1, hx2⟩
  cases x with
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, spec_ok, DoorwayOk]
    obtain ⟨h1, h2', h3⟩ := hx1.mp rfl
    refine ⟨?_, ?_⟩
    · intro d hd; cases hd; exact ⟨hce, ⟨h1, h2', h3⟩, hh2⟩
    · intro e he; cases he
  | Err e =>
    have := hx2 (by simp)
    cases this
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    exact doorway_err_residual L edge _ (by simp)

/-- The end of a doorway between two polar cells: both sweeps, their union, and the check. -/
theorem doorway_sweep_tail (L : scene.Layout) (hL : LayoutGeom L) (edge : topology.Edge)
    (hce : carrierEdge L.carrier edge.u.val edge.v.val) (phases next : Slice Std.I32)
    (hu : edge.u.val < L.cells.val.length) (hv : edge.v.val < L.cells.val.length)
    (hph : L.transforms.val ≤ phases.val.length) (hnext : L.transforms.val ≤ next.val.length)
    (path : walker.Path) (h2 : walker.Holds) (hh2 : HoldsOk h2) :
    (do
      let r3 ← scene.Layout.cell_sweep L edge.u phases next
      let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf3 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r4 ← scene.Layout.cell_sweep L edge.v phases next
        let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf4 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let corridor ← grid.Rect.union val1 val2
          let r5 ← grid.Geometry.check L.geometry corridor
          let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
          match cf5 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            ok (core.result.Result.Ok ({ corridor := corridor, path := path, holds := h2 } : scene.Doorway))
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              scene.Doorway (core.convert.FromSame topology.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            scene.Doorway (core.convert.FromSame topology.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          scene.Doorway (core.convert.FromSame topology.Error) residual) ⦃ r => DoorwayOk L edge r ⦄ := by
  apply spec_bind (layout_cell_sweep_spec L hL edge.u phases next hu hph hnext)
  rintro r3 ⟨_, h3⟩
  cases r3 with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    exact doorway_err_residual L edge _ (Or.inr (Or.inl (h3 e rfl)))
  | Ok v1 =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    apply spec_bind (layout_cell_sweep_spec L hL edge.v phases next hv hph hnext)
    rintro r4 ⟨_, h4⟩
    cases r4 with
    | Err e =>
      simp only [Std.bind_ok]
      exact doorway_err_residual L edge _ (Or.inr (Or.inl (h4 e rfl)))
    | Ok v2 =>
      simp only [Std.bind_ok]
      step as ⟨cor, hcor⟩
      exact doorway_check_tail L edge hce cor path h2 hh2

/-- The end of a doorway with a Cartesian endpoint: the straight corridor between the two world
points, and the check. -/
theorem doorway_cartesian_tail (L : scene.Layout) (hL : LayoutGeom L) (edge : topology.Edge)
    (hce : carrierEdge L.carrier edge.u.val edge.v.val) (phases : Slice Std.I32)
    (hph : L.transforms.val ≤ phases.val.length) (pf pt : walker.LocalPose)
    (hpf : PoseOk L pf) (hpt : PoseOk L pt) (m : Std.I32) (hm : m.val ≤ 1000000)
    (h2 : walker.Holds) (hh2 : HoldsOk h2) :
    (do
      let from1 ← scene.Layout.world L pf phases
      let to1 ← scene.Layout.world L pt phases
      let r3 ← grid.Rect.between from1 to1 m
      let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf3 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r4 ← grid.Geometry.check L.geometry val1
        let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf4 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (core.result.Result.Ok ({ corridor := val1, path := (walker.Path.Cartesian from1 to1),
                                       holds := h2 } : scene.Doorway))
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            scene.Doorway (core.convert.FromSame topology.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          scene.Doorway (core.convert.FromSame topology.Error) residual) ⦃ r => DoorwayOk L edge r ⦄ := by
  apply spec_bind (layout_world_spec L hL pf phases hpf hph)
  intro f hf
  apply spec_bind (layout_world_spec L hL pt phases hpt hph)
  intro t ht
  apply spec_bind (grid_rect_between_near f t m hf ht hm)
  rintro r3 ⟨_, h3⟩
  cases r3 with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    exact doorway_err_residual L edge _ (Or.inr (Or.inl (h3 e rfl)))
  | Ok v1 =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    exact doorway_check_tail L edge hce v1 _ h2 hh2

theorem layout_doorway_spec (L : scene.Layout) (hL : LayoutGeom L) (hc : CarrierValid L.carrier)
    (edge : topology.Edge) (phases next : Slice Std.I32)
    (hph : L.transforms.val ≤ phases.val.length) (hnext : L.transforms.val ≤ next.val.length) :
    scene.Layout.doorway L edge phases next ⦃ r => DoorwayOk L edge r ⦄ := by
  unfold scene.Layout.doorway
  by_cases hu : edge.u ≥ alloc.vec.Vec.len L.cells
  · simp only [hu, ↓reduceIte, spec_ok, DoorwayOk]; simp
  by_cases hv : edge.v ≥ alloc.vec.Vec.len L.cells
  · simp only [hu, hv, ↓reduceIte, spec_ok, DoorwayOk]; simp
  simp only [hu, hv, ↓reduceIte]
  have hu' : edge.u.val < L.cells.val.length := by scalar_tac
  have hv' : edge.v.val < L.cells.val.length := by scalar_tac
  apply spec_bind (mutation_carrier_contains_total L.carrier edge hc)
  intro b hb
  by_cases hbt : b = true
  swap
  · have hbf : b = false := by simpa using hbt
    simp only [hbf, Bool.false_eq_true, ↓reduceIte, spec_ok, DoorwayOk]; simp
  have hce := hb.mp hbt
  simp only [hbt, ↓reduceIte]
  step as ⟨r, hr1, hr2, hr3⟩
  obtain ⟨m, rfl⟩ := hr2 hL.margin
  obtain ⟨_, hm⟩ := hr1 m rfl
  have hmg := hL.margin
  unfold MarginOk at hmg
  simp only [branch_ok_eq, Std.bind_ok, walker.Holds.new]
  step with (layout_holds_spec L hL edge.u { ids := Array.repeat 4#usize 0#usize, count := 0#usize }
    hu' (by simp [HoldsOk])) as ⟨s1, h1, hh1, hs1⟩
  rcases hs1 with hs1 | hs1 <;> subst hs1
  swap
  · simp only [branch_err_eq, Std.bind_ok]
    exact doorway_err_residual L edge _ (by simp)
  simp only [branch_ok_eq, Std.bind_ok]
  step with (layout_holds_spec L hL edge.v _ hv' hh1) as ⟨s2, h2, hh2, hs2⟩
  rcases hs2 with hs2 | hs2 <;> subst hs2
  swap
  · simp only [branch_err_eq, Std.bind_ok]
    exact doorway_err_residual L edge _ (by simp)
  simp only [branch_ok_eq, Std.bind_ok]
  apply spec_bind (layout_frame_pose_spec L hL edge.u phases hu' hph)
  intro pf hpf
  apply spec_bind (layout_frame_pose_spec L hL edge.v phases hv' hph)
  intro pt hpt
  have hm' : m.val ≤ 1000000 := by omega
  cases pf with
  | Cartesian a =>
    exact doorway_cartesian_tail L hL edge hce phases hph _ _ hpf hpt m hm' h2 hh2
  | Polar circle fr fa =>
    cases pt with
    | Cartesian a =>
      exact doorway_cartesian_tail L hL edge hce phases hph _ _ hpf hpt m hm' h2 hh2
    | Polar other tr ta =>
      obtain ⟨hcl, hfr0, hfr1, hfa0, hfa1⟩ := hpf
      obtain ⟨hol, htr0, htr1, hta0, hta1⟩ := hpt
      by_cases hne : (circle != other) = true
      · simp only [hne, ↓reduceIte, spec_ok, DoorwayOk]; simp
      have hne' : (circle != other) = false := Bool.eq_false_iff.mpr hne
      simp only [hne', Bool.false_eq_true, ↓reduceIte]
      step as ⟨c, hcc⟩
      have hco := hL.circles circle.val hcl
      have hc' : c = L.circles.val[circle.val]'hcl := hcc
      subst hc'
      step as ⟨a, ha⟩
      step as ⟨b1, hb1⟩
      step as ⟨an, han⟩
      step as ⟨bn, hbn⟩
      step as ⟨c1, hc1⟩
      step as ⟨c2, hc2⟩
      step as ⟨sr⟩
      by_cases hsr : sr = true
      · simp only [hsr, ↓reduceIte]
        have hab := arcOk_bnd ha
        have hb1' := hb1
        unfold ArcOk at hb1'
        step as ⟨b2, hb2⟩
        simp only [bind_ite_ok]
        exact doorway_sweep_tail L hL edge hce phases next hu' hv' hph hnext _ h2 hh2
      · have hsrf : sr = false := by simpa using hsr
        simp only [hsrf, Bool.false_eq_true, ↓reduceIte]
        have hcr := hco.center_radius
        have hol' := hco.outer_le
        have hle := hco.ring_end_le 0 (by omega)
        step as ⟨i2, hi2⟩
        step as ⟨rad, hrad⟩
        have hrad' : 1 ≤ rad.val ∧ rad.val ≤ 1000000 := by
          subst hi2 hrad; simp; omega
        step as ⟨i3, hi3⟩
        step as ⟨i4, hi4⟩
        step as ⟨i5, hi5⟩
        have ht := turn_val
        step as ⟨i6, hi6⟩
        step as ⟨i7, hi7⟩
        step as ⟨i8, hi8⟩
        step as ⟨i9, hi9⟩
        step as ⟨i10, hi10⟩
        step as ⟨i11, hi11⟩
        simp only [lift, Std.bind_ok]
        have harcs : ArcsOk (Array.make 4#usize [a, b1, an, bn]) := by
          intro i hi
          have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
          rcases this with rfl | rfl | rfl | rfl <;> simpa [Array.make]
        apply spec_bind (polar_overlap_spec _ _ harcs)
        rintro ov ⟨hov1, hov2⟩
        cases ov with
        | Err e =>
          simp only [branch_err_eq, Std.bind_ok]
          exact doorway_err_residual L edge _ (Or.inr (Or.inl (hov1 e rfl)))
        | Ok arc =>
          simp only [branch_ok_eq, Std.bind_ok]
          step with (polar_arc_middle_spec arc (hov2 arc rfl)) as ⟨ang, hang⟩
          simp only [bind_ite_ok]
          exact doorway_sweep_tail L hL edge hce phases next hu' hv' hph hnext _ h2 hh2
/-- `doorway` never fails in the model: it returns a value, and that value is described by
`DoorwayOk`. Together with `layout_doorway_ok_carrier_edge` (which needs only a valid carrier),
an admitted doorway's edge is a carrier edge. -/
theorem layout_doorway_total (L : scene.Layout) (hL : LayoutGeom L) (hc : CarrierValid L.carrier)
    (edge : topology.Edge) (phases next : Slice Std.I32)
    (hph : L.transforms.val ≤ phases.val.length) (hnext : L.transforms.val ≤ next.val.length) :
    ∃ r, scene.Layout.doorway L edge phases next = ok r ∧ DoorwayOk L edge r ∧
      (r.ok? = true → carrierEdge L.carrier edge.u.val edge.v.val) := by
  obtain ⟨r, hr, hok⟩ := spec_exists_ok (layout_doorway_spec L hL hc edge phases next hph hnext)
  exact ⟨r, hr, hok, layout_doorway_ok_carrier_edge L edge phases next hc r hr⟩

end Labyrinth
