module
public import LabyrinthCore.SceneGeometryLayoutNew
public import LabyrinthCore.ScenePublication
import all LabyrinthCore.ScenePublication

/-! Geometry totality (S8), the rejected-replacement scan: under the layout invariant,
`Scene::cell_fits` returns, `reject_layout_loop` returns, and `reject_layout` is total. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

/-- What the scene geometry needs from a scene: the layout invariant, a valid carrier, and phase
vectors that cover the layout's transforms. -/
structure SceneGeom (s : scene.Scene) : Prop where
  layout : LayoutGeom s.layout
  carrier : CarrierValid s.layout.carrier
  phases : s.layout.transforms.val ≤ s.phases.val.length

/-- The errors geometry queries can report. -/
def GeomErr (e : topology.Error) : Prop :=
  e = .InvalidIndex ∨ e = .InvalidGeometry ∨ e = .InsufficientWorkspace

/-! ### `Scene::cell_pose` -/

theorem scene_cell_pose_spec (self : scene.Scene) (hg : SceneGeom self) (cell : Std.Usize) :
    scene.Scene.cell_pose self cell ⦃ r =>
      (∀ p, r = .Ok p → BoundsPointOk p) ∧ (∀ e, r = .Err e → e = .InvalidIndex) ⦄ := by
  unfold scene.Scene.cell_pose
  by_cases hc : cell ≥ alloc.vec.Vec.len self.layout.cells
  · simp only [hc, ↓reduceIte, spec_ok]; simp
  · simp only [hc, ↓reduceIte]
    have h : cell.val < self.layout.cells.val.length := by scalar_tac
    have hph : self.layout.transforms.val ≤ (alloc.vec.Vec.deref self.phases).val.length := by
      rw [vec_deref_val]; exact hg.phases
    apply spec_bind (layout_frame_pose_spec self.layout hg.layout cell _ h hph)
    intro lp hlp
    apply spec_bind (layout_world_spec self.layout hg.layout lp _ hlp hph)
    intro p hp
    simp only [spec_ok]
    refine ⟨fun q hq => ?_, fun e he => by cases he⟩
    cases hq
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩

/-! ### `Scene::cell_fits` -/

theorem scene_cell_fits_spec (self : scene.Scene) (hg : SceneGeom self) (viewport : grid.Rect)
    (cell : Std.Usize) (h : cell.val < self.tree.parents.val.length) :
    scene.Scene.cell_fits self cell viewport ⦃ r => ∀ e, r = .Err e → GeomErr e ⦄ := by
  unfold scene.Scene.cell_fits
  simp only [spanning_tree.Tree.impl.parents, Std.bind_ok]
  have hlen : cell.val < (alloc.vec.Vec.deref self.tree.parents).val.length := by
    rw [vec_deref_val]; exact h
  step as ⟨parent, hparent⟩
  have hph : self.layout.transforms.val ≤ (alloc.vec.Vec.deref self.phases).val.length := by
    rw [vec_deref_val]; exact hg.phases
  by_cases hne : parent ≠ cell
  · simp only [hne, ↓reduceIte, bne_iff_ne, ne_eq, not_false_eq_true, decide_true]
    obtain ⟨e, he⟩ : ∃ e, topology.Edge.new cell parent = ok e := by
      unfold topology.Edge.new; split <;> exact ⟨_, rfl⟩
    rw [he]; simp only [Std.bind_ok]
    obtain ⟨r, hr, hok, _⟩ := layout_doorway_total self.layout hg.layout hg.carrier e
      (alloc.vec.Vec.deref self.phases) (alloc.vec.Vec.deref self.phases) hph hph
    rw [hr]; simp only [Std.bind_ok]
    cases r with
    | Ok d =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      step as ⟨b, hb⟩
      intro e he; cases he
    | Err er =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, core.convert.FromSame.from, bind_tc_ok, spec_ok]
      intro e' he'
      cases he'
      have := hok.2 er rfl
      simpa [GeomErr] using this
  · have hpe : parent = cell := not_not.mp hne
    have hne2 : (parent != cell) = false := by simp [hpe]
    simp only [hne2, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨r, hr, hr1, hr2⟩ := spec_exists_ok (scene_cell_pose_spec self hg cell)
    rw [hr]; simp only [Std.bind_ok]
    cases r with
    | Err er =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, core.convert.FromSame.from, bind_tc_ok, spec_ok]
      intro e' he'; cases he'
      have := hr2 er rfl
      simp [GeomErr, this]
    | Ok pose =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      obtain ⟨mr, hm, hm1, hm2, hm3⟩ := spec_exists_ok (grid_geometry_margin_spec self.layout.geometry)
      obtain ⟨m, rfl⟩ := hm2 hg.layout.margin
      have hmv := hm1 m rfl
      have hmg := hg.layout.margin
      unfold MarginOk at hmg
      rw [hm]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      apply spec_bind (grid_rect_between_near pose pose m (hr1 pose rfl) (hr1 pose rfl) (by omega))
      rintro bx ⟨hbx1, hbx2⟩
      cases bx with
      | Err er =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, core.convert.FromSame.from, bind_tc_ok, spec_ok]
        intro e' he'; cases he'
        simp [GeomErr, hbx2 er rfl]
      | Ok rc =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
        step as ⟨b, hb⟩
        intro e he; cases he

/-! ### The scan of `reject_layout` -/

/-- The scan of `reject_layout` from `cell` with the running `fits` flag and a given status. -/
def rejectLoopS (self : scene.Scene) (viewport : grid.Rect) (fits : Bool)
    (status : core.result.Result Unit topology.Error) (cell : Std.Usize) :
    Result (Bool × core.result.Result Unit topology.Error) :=
  scene.Scene.reject_layout_loop self.layout self.tree self.work self.routes self.required
    self.phases self.next_phases self.holds self.walkers self.patches self.stamp.epoch
    self.stamp.revision self.clock self.wall self.reanchor self.suspended self.inactive
    self.latest_request self.pending self.trail_revision viewport fits status cell

/-- The scan from `cell` with the running flag `fits` and an `Ok` status. -/
def rejectLoop (self : scene.Scene) (viewport : grid.Rect) (fits : Bool) (cell : Std.Usize) :
    Result (Bool × core.result.Result Unit topology.Error) :=
  rejectLoopS self viewport fits (core.result.Result.Ok ()) cell

theorem rejectLoopS_unfold (self : scene.Scene) (viewport : grid.Rect) (fits : Bool)
    (status : core.result.Result Unit topology.Error) (cell : Std.Usize) :
    rejectLoopS self viewport fits status cell =
      Std.bind (scene.Scene.reject_layout_loop.body self.layout self.tree self.work self.routes
        self.required self.phases self.next_phases self.holds self.walkers self.patches
        self.stamp.epoch self.stamp.revision self.clock self.wall self.reanchor self.suspended
        self.inactive self.latest_request self.pending self.trail_revision viewport fits status cell)
        (fun r => match r with
          | .cont x => rejectLoopS self viewport x.1 x.2.1 x.2.2
          | .done y => ok y) := by
  unfold rejectLoopS scene.Scene.reject_layout_loop
  rw [loop]
  show Std.bind _ _ = Std.bind _ _
  congr 1
  funext r
  cases r with
  | cont x => obtain ⟨a, b, c⟩ := x; rfl
  | done y => rfl

theorem rejectScan_eq (self : scene.Scene) (viewport : grid.Rect) :
    rejectScan self viewport = rejectLoop self viewport true 0#usize := by
  unfold rejectScan rejectLoop; rfl

/-- What the scan returns, cell by cell. From `cell` with running flag `fits`: past the last cell
of the retired tree the scan stops with `(fits, Ok)`; a cell whose check returns an inside flag
folds it into `fits` and moves on; the first cell whose check errs stops the scan with the flag
accumulated so far and that error. -/
inductive ScanRel (self : scene.Scene) (viewport : grid.Rect) :
    Std.Usize → Bool → Bool × core.result.Result Unit topology.Error → Prop
  | stop {cell : Std.Usize} {fits : Bool} :
      ¬ cell.val < self.tree.parents.val.length → ScanRel self viewport cell fits (fits, .Ok ())
  | inside {cell next : Std.Usize} {fits inside : Bool}
      {r : Bool × core.result.Result Unit topology.Error} :
      cell.val < self.tree.parents.val.length →
      scene.Scene.cell_fits self cell viewport = ok (.Ok inside) → next.val = cell.val + 1 →
      ScanRel self viewport next (fits && inside) r → ScanRel self viewport cell fits r
  | err {cell : Std.Usize} {fits : Bool} {e : topology.Error} :
      cell.val < self.tree.parents.val.length →
      scene.Scene.cell_fits self cell viewport = ok (.Err e) →
      ScanRel self viewport cell fits (fits, .Err e)

theorem reject_loop_total (self : scene.Scene) (hg : SceneGeom self) (viewport : grid.Rect) :
    ∀ n : Nat, ∀ (cell : Std.Usize) (fits : Bool),
      self.tree.parents.val.length - cell.val = n →
      ∃ r, rejectLoop self viewport fits cell = ok r ∧ ScanRel self viewport cell fits r := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro cell fits hn
  have hfit := scene_cell_fits_spec self hg viewport
  unfold rejectLoop
  rw [rejectLoopS_unfold]
  unfold scene.Scene.reject_layout_loop.body
  simp only [spanning_tree.Tree.impl.parents, Std.bind_ok]
  have hlenv : self.tree.parents.deref.len.val = self.tree.parents.val.length := by
    simp [Slice.len, vec_deref_val]
  by_cases hlt : cell < self.tree.parents.deref.len
  · have hlt' : cell.val < self.tree.parents.val.length := by scalar_tac
    simp only [hlt, ↓reduceIte, core.result.Result.is_ok, Std.bind_ok, ite_true]
    obtain ⟨x, hx, hxe⟩ := spec_exists_ok (hfit cell hlt')
    rw [hx]; simp only [Std.bind_ok]
    obtain ⟨c1, hc1, hc1v⟩ : ∃ c, cell + 1#usize = ok c ∧ c.val = cell.val + 1 := by
      have := Usize.add_spec (x := cell) (y := 1#usize) (by scalar_tac)
      obtain ⟨c, hc, hv⟩ := spec_exists_ok this
      exact ⟨c, hc, by simpa using hv⟩
    cases x with
    | Err e =>
      simp only [Std.bind_ok, hc1]
      refine ⟨(fits, .Err e), ?_, ScanRel.err hlt' hx⟩
      change Std.bind (ok (ControlFlow.cont (fits, core.result.Result.Err e, c1))) _ = _
      rw [Std.bind_ok]
      show rejectLoopS self viewport fits (core.result.Result.Err e) c1 = _
      rw [rejectLoopS_unfold]
      unfold scene.Scene.reject_layout_loop.body
      by_cases h2 : c1 < self.tree.parents.deref.len <;>
        simp [spanning_tree.Tree.impl.parents, h2, core.result.Result.is_ok]
    | Ok inside =>
      cases fits with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Std.bind_ok, hc1]
        obtain ⟨r, hr, hrel⟩ := ih (self.tree.parents.val.length - c1.val) (by omega) c1 false rfl
        exact ⟨r, by simpa [rejectLoop] using hr, ScanRel.inside hlt' hx hc1v (by simpa using hrel)⟩
      | true =>
        simp only [ite_true, Std.bind_ok, hc1]
        obtain ⟨r, hr, hrel⟩ := ih (self.tree.parents.val.length - c1.val) (by omega) c1 inside rfl
        exact ⟨r, by simpa [rejectLoop] using hr, ScanRel.inside hlt' hx hc1v (by simpa using hrel)⟩
  · have hlt' : ¬ cell.val < self.tree.parents.val.length := by scalar_tac
    simp only [hlt, ↓reduceIte, Std.bind_ok]
    exact ⟨_, rfl, ScanRel.stop hlt'⟩

theorem rejectScan_total (self : scene.Scene) (hg : SceneGeom self) (viewport : grid.Rect) :
    ∃ r, rejectScan self viewport = ok r ∧ ScanRel self viewport 0#usize true r := by
  rw [rejectScan_eq]
  exact reject_loop_total self hg viewport _ 0#usize true rfl

/-- The scan reports `Ok` only when every cell from `cell` on returned an inside flag, and the
final flag is `fits` and-ed with all of them. -/
theorem ScanRel.ok_iff {self : scene.Scene} {viewport : grid.Rect} {cell : Std.Usize} {fits f : Bool}
    (h : ScanRel self viewport cell fits (f, .Ok ())) :
    (∀ k : Std.Usize, cell.val ≤ k.val → k.val < self.tree.parents.val.length →
      ∃ b, scene.Scene.cell_fits self k viewport = ok (.Ok b)) ∧
    (f = true ↔ fits = true ∧ ∀ k : Std.Usize, cell.val ≤ k.val →
      k.val < self.tree.parents.val.length →
      scene.Scene.cell_fits self k viewport = ok (.Ok true)) := by
  generalize hr : ((f, core.result.Result.Ok ()) : Bool × core.result.Result Unit topology.Error) = r
    at h
  induction h generalizing f with
  | stop hn =>
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    refine ⟨fun k hk hk2 => absurd (by omega) hn, ?_⟩
    exact ⟨fun h => ⟨h, fun k hk hk2 => absurd (by omega) hn⟩, fun h => h.1⟩
  | @inside cell next fits inside r hlt hx hnext hrel ih =>
    obtain ⟨ih1, ih2⟩ := ih hr
    have hcast : ∀ k : Std.Usize, cell.val ≤ k.val → k.val < self.tree.parents.val.length →
        k.val = cell.val ∨ next.val ≤ k.val := by intro k h1 h2; omega
    refine ⟨fun k hk hk2 => ?_, ?_⟩
    · rcases hcast k hk hk2 with h | h
      · have : k = cell := UScalar.eq_of_val_eq h
        subst this; exact ⟨inside, hx⟩
      · exact ih1 k h hk2
    · rw [ih2]
      constructor
      · rintro ⟨h1, h2⟩
        cases fits <;> cases inside <;> simp at h1
        refine ⟨rfl, fun k hk hk2 => ?_⟩
        rcases hcast k hk hk2 with h | h
        · have : k = cell := UScalar.eq_of_val_eq h
          subst this; exact hx
        · exact h2 k h hk2
      · rintro ⟨h1, h2⟩
        have hin : inside = true := by
          have := h2 cell (le_refl _) hlt
          rw [hx] at this
          simp at this; exact this
        subst h1; subst hin
        exact ⟨rfl, fun k hk hk2 => h2 k (by omega) hk2⟩
  | err hlt hx => simp at hr

/-- The scan reports `Err e` exactly at the first cell whose check errs, with the flag accumulated
over the cells before it. -/
theorem ScanRel.err_iff {self : scene.Scene} {viewport : grid.Rect} {cell : Std.Usize}
    {fits f : Bool} {e : topology.Error}
    (h : ScanRel self viewport cell fits (f, .Err e)) :
    ∃ k : Std.Usize, cell.val ≤ k.val ∧ k.val < self.tree.parents.val.length ∧
      scene.Scene.cell_fits self k viewport = ok (.Err e) ∧
      (∀ j : Std.Usize, cell.val ≤ j.val → j.val < k.val →
        ∃ b, scene.Scene.cell_fits self j viewport = ok (.Ok b)) ∧
      (f = true ↔ fits = true ∧ ∀ j : Std.Usize, cell.val ≤ j.val → j.val < k.val →
        scene.Scene.cell_fits self j viewport = ok (.Ok true)) := by
  generalize hr : ((f, core.result.Result.Err e) : Bool × core.result.Result Unit topology.Error) = r
    at h
  induction h generalizing f with
  | stop hn => simp at hr
  | @inside cell next fits inside r hlt hx hnext hrel ih =>
    obtain ⟨k, hk1, hk2, hk3, hk4, hk5⟩ := ih hr
    have hcast : ∀ j : Std.Usize, cell.val ≤ j.val → j.val < k.val →
        j.val = cell.val ∨ next.val ≤ j.val := by intro j h1 h2; omega
    refine ⟨k, by omega, hk2, hk3, fun j hj1 hj2 => ?_, ?_⟩
    · rcases hcast j hj1 hj2 with h | h
      · have : j = cell := UScalar.eq_of_val_eq h
        subst this; exact ⟨inside, hx⟩
      · exact hk4 j h hj2
    · rw [hk5]
      constructor
      · rintro ⟨h1, h2⟩
        cases fits <;> cases inside <;> simp at h1
        refine ⟨rfl, fun j hj1 hj2 => ?_⟩
        rcases hcast j hj1 hj2 with h | h
        · have : j = cell := UScalar.eq_of_val_eq h
          subst this; exact hx
        · exact h2 j h hj2
      · rintro ⟨h1, h2⟩
        have hin : inside = true := by
          have := h2 cell (le_refl _) (by omega)
          rw [hx] at this
          simp at this; exact this
        subst h1; subst hin
        exact ⟨rfl, fun j hj1 hj2 => h2 j (by omega) hj2⟩
  | @err cell fits e' hlt hx =>
    simp only [Prod.mk.injEq, core.result.Result.Err.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨cell, le_refl _, hlt, hx, fun j h1 h2 => absurd h2 (by omega), ?_⟩
    exact ⟨fun h => ⟨h, fun j h1 h2 => absurd h2 (by omega)⟩, fun h => h.1⟩

/-! ### `reject_layout` is total -/

/-- Every outcome of `reject_layout`, for a scene whose geometry is valid: a stale request, an
invalid viewport (`InvalidGeometry`), a revision overflow, an error found by the scan, or a commit
whose `inactive` flag is the negation of the scan's flag. The scan's meaning is `ScanRel`. -/
def RejectOutcome (self : scene.Scene) (request : Std.U64) (viewport : grid.Rect)
    (r : core.result.Result walker.Stamp topology.Error) (s' : scene.Scene) : Prop :=
  ((self.pending ≠ some request ∨ self.latest_request ≠ request) ∧
      r = .Err topology.Error.StaleEpoch ∧ s' = self) ∨
  (self.pending = some request ∧ self.latest_request = request ∧ ¬ RectOk viewport ∧
      r = .Err topology.Error.InvalidGeometry ∧ s' = self) ∨
  (self.pending = some request ∧ self.latest_request = request ∧ RectOk viewport ∧
      self.stamp.revision.val = U64.max ∧ r = .Err topology.Error.Overflow ∧ s' = self) ∨
  (self.pending = some request ∧ self.latest_request = request ∧ RectOk viewport ∧
      self.stamp.revision.val < U64.max ∧
      ∃ fits e, ScanRel self viewport 0#usize true (fits, .Err e) ∧ r = .Err e ∧ s' = self) ∨
  (self.pending = some request ∧ self.latest_request = request ∧ RectOk viewport ∧
      self.stamp.revision.val < U64.max ∧
      ∃ fits, ∃ v : Std.U64, ScanRel self viewport 0#usize true (fits, .Ok ()) ∧
        v.val = self.stamp.revision.val + 1 ∧ r = .Ok (bumped self v) ∧
        s' = { self with stamp := bumped self v, inactive := !fits, pending := none })

theorem reject_layout_total (self : scene.Scene) (hg : SceneGeom self) (request : Std.U64)
    (viewport : grid.Rect) :
    ∃ r s', scene.Scene.reject_layout self request viewport = ok (r, s') ∧
      RejectOutcome self request viewport r s' := by
  by_cases hp : self.pending = some request
  swap
  · exact ⟨_, _, reject_layout_stale_pending self request viewport hp, Or.inl ⟨Or.inl hp, rfl, rfl⟩⟩
  by_cases hl : self.latest_request = request
  swap
  · exact ⟨_, _, reject_layout_stale_latest self request viewport hp hl,
      Or.inl ⟨Or.inr hl, rfl, rfl⟩⟩
  obtain ⟨x, hx, hxa, hxb⟩ := spec_exists_ok (grid_rect_validate_spec viewport)
  cases x with
  | Err e =>
    have he : e = .InvalidGeometry := by simpa using hxb (by simp)
    subst he
    refine ⟨_, _, reject_layout_invalid_viewport self request viewport hp hl _ hx, ?_⟩
    refine Or.inr (Or.inl ⟨hp, hl, fun hr => ?_, rfl, rfl⟩)
    have := hxa.mpr hr
    simp at this
  | Ok u =>
    have hrect : RectOk viewport := hxa.mp rfl
    by_cases hmax : self.stamp.revision.val = U64.max
    · exact ⟨_, _, reject_layout_overflow self request viewport hp hl hx hmax,
        Or.inr (Or.inr (Or.inl ⟨hp, hl, hrect, hmax, rfl, rfl⟩))⟩
    have hlt : self.stamp.revision.val < U64.max := by
      have := self.stamp.revision.hBounds
      scalar_tac
    obtain ⟨⟨fits, status⟩, hs, hrel⟩ := rejectScan_total self hg viewport
    cases status with
    | Err e =>
      exact ⟨_, _, reject_layout_scan_failed self request viewport hp hl hx hlt fits e hs,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, hl, hrect, hlt, fits, e, hrel, rfl, rfl⟩)))⟩
    | Ok u2 =>
      obtain ⟨v, hv, hc⟩ := reject_layout_commit self request viewport hp hl hx hlt fits hs
      exact ⟨_, _, hc, Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, hl, hrect, hlt, fits, v, hrel, hv,
        rfl, rfl⟩)))⟩

end Labyrinth
