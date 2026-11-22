module
public import LabyrinthCore.SceneGeometryLayoutNew
public import LabyrinthCore.SceneGeometryDisk
public import LabyrinthCore.Constructors
import all Aeneas.Std.Scalar.CheckedOps.Add
import all Aeneas.Std.Scalar.CheckedOps.Mul

/-! Geometry totality, the cell grid: `Grid::new` accepts exactly the specifications whose
far corner stays inside the coordinate limit, `bounds`, `cell` and `retain` return for in-range
indices, and the cell sweep of `Layout::new` returns, keeps the grid invariant and extends the cell
list by valid grid cells only. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

/-! ### Arithmetic facts -/

theorem usize_checked_mul_cases (x y : Std.Usize) :
    (Usize.checked_mul x y = none ∧ Usize.max < x.val * y.val) ∨
    ∃ z, Usize.checked_mul x y = some z ∧ z.val = x.val * y.val ∧ x.val * y.val ≤ Usize.max := by
  have h := Usize.checked_mul_bv_spec x y
  cases hc : Usize.checked_mul x y with
  | none => rw [hc] at h; exact Or.inl ⟨rfl, h⟩
  | some z => rw [hc] at h; exact Or.inr ⟨z, rfl, h.2.1, h.1⟩

theorem i32_checked_mul_iff (x y : Std.I32) :
    (I32.checked_mul x y = none ∧ ¬ (-2147483648 ≤ x.val * y.val ∧ x.val * y.val ≤ 2147483647)) ∨
    ∃ z, I32.checked_mul x y = some z ∧ z.val = x.val * y.val := by
  have h := I32.checked_mul_bv_spec x y
  cases hc : I32.checked_mul x y with
  | none =>
    left; refine ⟨rfl, ?_⟩
    have hc' : core.num.checked_mul_IScalar x y = none := hc
    rw [hc'] at h
    simp [I32.min, I32.max, IScalar.min, IScalar.max, IScalarTy.numBits, I32.numBits] at h
    omega
  | some z =>
    right; refine ⟨z, rfl, ?_⟩
    have hc' : core.num.checked_mul_IScalar x y = some z := hc
    rw [hc'] at h
    exact h.2.2.1

theorem i32_max_val : core.num.I32.MAX.val = 2147483647 := by
  simp [core.num.I32.MAX, I32.rMax]

theorem i32_max_as_usize_val : (IScalar.hcast .Usize core.num.I32.MAX).val = 2147483647 := by
  have h := IScalar.hcast_inBounds_spec .Usize core.num.I32.MAX (by
    rw [i32_max_val]
    have hb := Usize.bounds_eq
    have : UScalar.max .Usize = Usize.max := by simp [Usize.max, UScalar.max, Usize.numBits]
    rw [this]
    refine ⟨by omega, ?_⟩
    rcases hb with h | h <;> rw [h] <;>
      simp [U32.max, U64.max, UScalar.max, UScalarTy.numBits, U32.numBits, U64.numBits])
  obtain ⟨y, hy, hyv⟩ := spec_exists_ok h
  have : y = IScalar.hcast .Usize core.num.I32.MAX := by simpa [lift] using hy.symm
  subst this
  rw [i32_max_val] at hyv
  omega

/-! ### `Grid::new` -/

/-- A grid specification `Grid::new` accepts: a valid origin, positive sizes, an id table within
the allocation limit, counts that fit `i32`, and a far corner `origin + size * cell_size` inside
the coordinate limit on both axes. -/
def GridSpecOk (s : grid.GridSpec) : Prop :=
  PointOk s.origin ∧ 0 < s.columns.val ∧ 0 < s.rows.val ∧ 0 < s.cell_size.val ∧
  s.columns.val * s.rows.val * 16 ≤ Usize.max ∧
  s.columns.val * s.rows.val * 16 ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val ∧
  s.columns.val ≤ 2147483647 ∧ s.rows.val ≤ 2147483647 ∧
  s.origin.x.val + (s.columns.val : Int) * s.cell_size.val ≤ 1000000 ∧
  s.origin.y.val + (s.rows.val : Int) * s.cell_size.val ≤ 1000000

/-- A grid as `Grid::new` builds it, and as `retain` preserves it: an accepted specification and
one id slot per cell. -/
def GridOk (g : grid.Grid) : Prop :=
  GridSpecOk g.spec ∧ g.ids.val.length = g.spec.columns.val * g.spec.rows.val

/-- What `Grid::new` guarantees. -/
def GridNewPost (spec : grid.GridSpec) (r : core.result.Result grid.Grid topology.Error) : Prop :=
  (∀ g, r = .Ok g → g.spec = spec ∧ GridOk g ∧
    spec.origin.x.val + (spec.columns.val : Int) * spec.cell_size.val ≤ 1000000 ∧
    spec.origin.y.val + (spec.rows.val : Int) * spec.cell_size.val ≤ 1000000) ∧
  (GridSpecOk spec → ∃ g, r = .Ok g) ∧
  (∀ e, r = .Err e →
    e = topology.Error.InvalidGeometry ∨ e = topology.Error.InvalidSize ∨
      e = topology.Error.Overflow)

theorem gridNewPost_err (spec : grid.GridSpec) (e : topology.Error)
    (he : e = topology.Error.InvalidGeometry ∨ e = topology.Error.InvalidSize ∨
      e = topology.Error.Overflow)
    (hn : ¬ GridSpecOk spec) : GridNewPost spec (.Err e) :=
  by
  refine ⟨?_, ?_, ?_⟩
  · intro g h; cases h
  · intro h; exact absurd h hn
  · intro e' h; cases h; exact he

theorem grid_grid_new_spec (spec : grid.GridSpec) :
    grid.Grid.new spec ⦃ r => GridNewPost spec r ⦄ := by
  unfold grid.Grid.new
  obtain ⟨v, hv, hv1, hv2⟩ := spec_exists_ok (grid_point_validate_spec spec.origin)
  rw [hv]
  cases v with
  | Err e =>
    have he : e = topology.Error.InvalidGeometry := by
      have := hv2 (by simp)
      injection this
    subst he
    have hnot : ¬ PointOk spec.origin := fun h => by simpa using hv1.mpr h
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, Std.bind_ok, spec_ok]
    exact gridNewPost_err spec _ (Or.inl rfl) (fun h => hnot h.1)
  | Ok u =>
    have hok := hv1.mp rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    by_cases h1 : spec.columns = 0#usize
    · simp only [h1, ite_true, spec_ok]
      refine gridNewPost_err spec _ (Or.inr (Or.inl rfl)) (fun h => ?_)
      have := h.2.1; simp [h1] at this
    by_cases h2 : spec.rows = 0#usize
    · simp only [h1, h2, ite_true, ite_false, spec_ok]
      refine gridNewPost_err spec _ (Or.inr (Or.inl rfl)) (fun h => ?_)
      have := h.2.2.1; simp [h2] at this
    by_cases h3 : spec.cell_size ≤ 0#i32
    · simp only [h1, h2, h3, ite_true, ite_false, spec_ok]
      refine gridNewPost_err spec _ (Or.inr (Or.inl rfl)) (fun h => ?_)
      have := h.2.2.2.1
      scalar_tac
    have hc0 : 0 < spec.columns.val := by
      have : spec.columns.val ≠ 0 := fun h0 => h1 (by simp [UScalar.eq_equiv, h0])
      omega
    have hr0 : 0 < spec.rows.val := by
      have : spec.rows.val ≠ 0 := fun h0 => h2 (by simp [UScalar.eq_equiv, h0])
      omega
    have hs0 : 0 < spec.cell_size.val := by scalar_tac
    simp only [h1, h2, h3, ite_false, lift, Std.bind_ok]
    rcases usize_checked_mul_cases spec.columns spec.rows with ⟨hn, hr⟩ | ⟨z, hz, hzv, hzle⟩
    · rw [hn]
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, spec_ok]
      refine gridNewPost_err spec _ (Or.inr (Or.inr rfl)) (fun h => ?_)
      have := h.2.2.2.2.1
      omega
    rw [hz]
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    rw [constructor_check_storage_eq]
    simp only [Std.bind_ok]
    have hfit : constructorStorageFits z 16#usize ↔
        z.val * 16 ≤ Usize.max ∧ z.val * 16 ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val := by
      simp [constructorStorageFits]
    by_cases hf : constructorStorageFits z 16#usize
    swap
    · simp only [hf, ite_false, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, Std.bind_ok, spec_ok]
      refine gridNewPost_err spec _ (Or.inr (Or.inr rfl)) (fun h => hf ?_)
      rw [hfit, hzv]
      exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩
    simp only [hf, ite_true, core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift]
    have hcol : (spec.columns > IScalar.hcast .Usize core.num.I32.MAX) ↔
        2147483647 < spec.columns.val := by
      simp [UScalar.lt_equiv, i32_max_as_usize_val]
    by_cases hc : 2147483647 < spec.columns.val
    · simp only [hcol, hc, ↓reduceIte, spec_ok]
      refine gridNewPost_err spec _ (Or.inr (Or.inr rfl)) (fun h => ?_)
      have := h.2.2.2.2.2.2.1
      omega
    simp only [hcol, hc, ↓reduceIte, Std.bind_ok]
    have hcv : (UScalar.hcast .I32 spec.columns).val = (spec.columns.val : Int) := by
      obtain ⟨y, hy, hyv⟩ := spec_exists_ok (usize_hcast_i32_spec spec.columns (by omega))
      have : y = UScalar.hcast .I32 spec.columns := by simpa [lift] using hy.symm
      subst this; exact hyv
    have hcs0 : 0 ≤ (spec.columns.val : Int) * spec.cell_size.val :=
      Int.mul_nonneg (by omega) (by omega)
    rcases i32_checked_mul_iff (UScalar.hcast .I32 spec.columns) spec.cell_size with
      ⟨hn3, hr3⟩ | ⟨w1, hw1, hw1v⟩
    · rw [hn3]
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, Std.bind_ok, spec_ok]
      refine gridNewPost_err spec _ (Or.inr (Or.inr rfl)) (fun h => hr3 ?_)
      have := h.2.2.2.2.2.2.2.2.1
      have := hok.1
      rw [hcv]
      constructor <;> omega
    rw [hw1]
    simp only [Std.bind_ok]
    rw [hcv] at hw1v
    have hrow : (spec.rows > IScalar.hcast .Usize core.num.I32.MAX) ↔
        2147483647 < spec.rows.val := by
      simp [UScalar.lt_equiv, i32_max_as_usize_val]
    by_cases hr : 2147483647 < spec.rows.val
    · simp only [hrow, hr, ↓reduceIte, spec_ok]
      refine gridNewPost_err spec _ (Or.inr (Or.inr rfl)) (fun h => ?_)
      have := h.2.2.2.2.2.2.2.1
      omega
    simp only [hrow, hr, ↓reduceIte, Std.bind_ok]
    have hrv : (UScalar.hcast .I32 spec.rows).val = (spec.rows.val : Int) := by
      obtain ⟨y, hy, hyv⟩ := spec_exists_ok (usize_hcast_i32_spec spec.rows (by omega))
      have : y = UScalar.hcast .I32 spec.rows := by simpa [lift] using hy.symm
      subst this; exact hyv
    have hrs0 : 0 ≤ (spec.rows.val : Int) * spec.cell_size.val :=
      Int.mul_nonneg (by omega) (by omega)
    rcases i32_checked_mul_iff (UScalar.hcast .I32 spec.rows) spec.cell_size with
      ⟨hn4, hr4⟩ | ⟨w2, hw2, hw2v⟩
    · rw [hn4]
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, Std.bind_ok, spec_ok]
      refine gridNewPost_err spec _ (Or.inr (Or.inr rfl)) (fun h => hr4 ?_)
      have := h.2.2.2.2.2.2.2.2.2
      have := hok.2.2.1
      rw [hrv]
      constructor <;> omega
    rw [hw2]
    simp only [Std.bind_ok]
    rw [hrv] at hw2v
    have hx := hok.2.1
    have hy := hok.2.2.2
    have hxl := hok.1
    have hyl := hok.2.2.1
    have hox := i32_val_bounds spec.origin.x
    rcases i32_checked_add_cases spec.origin.x w1 with ⟨hn5, hr5⟩ | ⟨v3, hv3, hv3v⟩
    · rw [hn5]
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, Std.bind_ok, spec_ok]
      refine gridNewPost_err spec _ (Or.inr (Or.inr rfl)) (fun h => hr5 ?_)
      have := h.2.2.2.2.2.2.2.2.1
      have := i32_val_bounds w1
      constructor <;> omega
    rw [hv3]
    simp only [Std.bind_ok]
    rcases i32_checked_add_cases spec.origin.y w2 with ⟨hn6, hr6⟩ | ⟨v4, hv4, hv4v⟩
    · rw [hn6]
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, Std.bind_ok, spec_ok]
      refine gridNewPost_err spec _ (Or.inr (Or.inr rfl)) (fun h => hr6 ?_)
      have := h.2.2.2.2.2.2.2.2.2
      have := i32_val_bounds w2
      constructor <;> omega
    rw [hv4]
    simp only [Std.bind_ok]
    obtain ⟨q, hq, hq1, hq2⟩ := spec_exists_ok (grid_point_validate_spec { x := v3, y := v4 })
    rw [hq]
    cases q with
    | Err e =>
      have he : e = topology.Error.InvalidGeometry := by
        have := hq2 (by simp)
        injection this
      subst he
      have hnot : ¬ PointOk { x := v3, y := v4 } := fun h => by simpa using hq1.mpr h
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, Std.bind_ok, spec_ok]
      refine gridNewPost_err spec _ (Or.inl rfl) (fun h => hnot ?_)
      have h9 := h.2.2.2.2.2.2.2.2.1
      have h10 := h.2.2.2.2.2.2.2.2.2
      unfold PointOk
      simp only
      omega
    | Ok u2 =>
      have hpt := hq1.mp rfl
      simp only [Std.bind_ok]
      apply spec_bind (alloc.vec.from_elem_spec (core.option.Option.Insts.CoreCloneClone
        core.clone.CloneUsize) none z rfl)
      rintro ids ⟨hids, hidl⟩
      simp only [spec_ok]
      have hpt' := hpt
      unfold PointOk at hpt'
      simp only at hpt'
      have hgs : GridSpecOk spec := by
        refine ⟨hok, hc0, hr0, hs0, ?_, ?_, by omega, by omega, by omega, by omega⟩
        · have := (hfit.mp hf).1; rw [hzv] at this; exact this
        · have := (hfit.mp hf).2; rw [hzv] at this; exact this
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        cases hg
        refine ⟨rfl, ⟨hgs, ?_⟩, by omega, by omega⟩
        simp only [hidl, hzv]
      · intro _; exact ⟨_, rfl⟩
      · intro e he; cases he


/-- `Grid::new` returns, and returns `Ok` exactly for the accepted specifications. -/
theorem grid_grid_new_ok_iff (spec : grid.GridSpec) :
    ∃ r, grid.Grid.new spec = ok r ∧ ((∃ g, r = .Ok g) ↔ GridSpecOk spec) := by
  obtain ⟨r, hr, h1, h2, -⟩ := spec_exists_ok (grid_grid_new_spec spec)
  refine ⟨r, hr, ⟨fun ⟨g, hg⟩ => ?_, h2⟩⟩
  obtain ⟨hs, hok, -⟩ := h1 g hg
  rw [← hs]; exact hok.1

/-! ### `bounds`, `cell`, `retain` -/

/-- For in-range indices `bounds` returns the cell rectangle: a valid rectangle of side `cell_size`
at `origin + index * cell_size`, inside the far corner of the grid. -/
theorem grid_grid_bounds_spec (g : grid.Grid) (hg : GridOk g) (column row : Std.Usize)
    (hc : column.val < g.spec.columns.val) (hr : row.val < g.spec.rows.val) :
    grid.Grid.bounds g column row ⦃ r =>
      r.min.x.val = g.spec.origin.x.val + (column.val : Int) * g.spec.cell_size.val ∧
      r.min.y.val = g.spec.origin.y.val + (row.val : Int) * g.spec.cell_size.val ∧
      r.max.x.val = r.min.x.val + g.spec.cell_size.val ∧
      r.max.y.val = r.min.y.val + g.spec.cell_size.val ∧
      r.max.x.val ≤ g.spec.origin.x.val + (g.spec.columns.val : Int) * g.spec.cell_size.val ∧
      r.max.y.val ≤ g.spec.origin.y.val + (g.spec.rows.val : Int) * g.spec.cell_size.val ∧
      RectOk r ⦄ := by
  obtain ⟨⟨⟨ox1, ox2, oy1, oy2⟩, hc0, hr0, hs0, -, -, hci, hri, hfx, hfy⟩, -⟩ := hg
  have hcm : (column.val : Int) * g.spec.cell_size.val + g.spec.cell_size.val ≤
      (g.spec.columns.val : Int) * g.spec.cell_size.val := by
    have : ((column.val : Int) + 1) * g.spec.cell_size.val ≤
        (g.spec.columns.val : Int) * g.spec.cell_size.val :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    linarith
  have hrm : (row.val : Int) * g.spec.cell_size.val + g.spec.cell_size.val ≤
      (g.spec.rows.val : Int) * g.spec.cell_size.val := by
    have : ((row.val : Int) + 1) * g.spec.cell_size.val ≤
        (g.spec.rows.val : Int) * g.spec.cell_size.val :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    linarith
  have hcz : 0 ≤ (column.val : Int) * g.spec.cell_size.val := Int.mul_nonneg (by omega) (by omega)
  have hrz : 0 ≤ (row.val : Int) * g.spec.cell_size.val := Int.mul_nonneg (by omega) (by omega)
  unfold grid.Grid.bounds
  have hbs := i32_val_bounds g.spec.cell_size
  step as ⟨i, hi⟩
  have hmc : i.val * g.spec.cell_size.val = (column.val : Int) * g.spec.cell_size.val := by rw [hi]
  step as ⟨i1, hi1⟩
  step as ⟨x, hx⟩
  step as ⟨i2, hi2⟩
  have hmr : i2.val * g.spec.cell_size.val = (row.val : Int) * g.spec.cell_size.val := by rw [hi2]
  step as ⟨i3, hi3⟩
  step as ⟨y, hy⟩
  step as ⟨i4, hi4⟩
  step as ⟨i5, hi5⟩
  simp only [RectOk, PointOk]
  refine ⟨?_, ?_, hi4, hi5, ?_, ?_, ?_⟩ <;> omega

/-- Row-major indexing: an in-range cell has an index below the number of cells. -/
theorem grid_index_lt (columns rows column row : Nat) (hc : column < columns) (hr : row < rows) :
    row * columns + column < columns * rows := by
  have h : (row + 1) * columns ≤ rows * columns := Nat.mul_le_mul_right _ hr
  have h2 : (row + 1) * columns = row * columns + columns := by ring
  have h3 : rows * columns = columns * rows := Nat.mul_comm _ _
  omega

/-- `cell` returns for every pair of indices: out of range gives `none`, in range reads the
id table at `row * columns + column`. -/
theorem grid_grid_cell_spec (g : grid.Grid) (hg : GridOk g) (column row : Std.Usize) :
    grid.Grid.cell g column row ⦃ r =>
      (g.spec.columns.val ≤ column.val ∨ g.spec.rows.val ≤ row.val → r = none) ∧
      (column.val < g.spec.columns.val → row.val < g.spec.rows.val →
        ∀ h : row.val * g.spec.columns.val + column.val < g.ids.val.length,
          r = g.ids.val[row.val * g.spec.columns.val + column.val]) ⦄ := by
  obtain ⟨⟨-, hc0, hr0, -, hst, -, -, -, -, -⟩, hlen⟩ := hg
  unfold grid.Grid.cell
  by_cases h1 : column ≥ g.spec.columns
  · simp only [h1, ↓reduceIte]
    have : g.spec.columns.val ≤ column.val := by scalar_tac
    exact (spec_ok _).mpr ⟨fun _ => rfl, fun h _ => by omega⟩
  by_cases h2 : row ≥ g.spec.rows
  · simp only [h1, h2, ↓reduceIte]
    have : g.spec.rows.val ≤ row.val := by scalar_tac
    exact (spec_ok _).mpr ⟨fun _ => rfl, fun _ h => by omega⟩
  simp only [h1, h2, ↓reduceIte]
  have hc : column.val < g.spec.columns.val := by scalar_tac
  have hr : row.val < g.spec.rows.val := by scalar_tac
  have hlt := grid_index_lt _ _ _ _ hc hr
  have hm : row.val * g.spec.columns.val ≤ Usize.max := by omega
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨x, hx⟩
  refine ⟨fun h => by omega, fun _ _ h => ?_⟩
  simp [hx, hi1, hi]

/-- `cell` returns for every pair of indices. -/
theorem grid_grid_cell_total (g : grid.Grid) (hg : GridOk g) (column row : Std.Usize) :
    ∃ r, grid.Grid.cell g column row = ok r :=
  let ⟨r, hr, _⟩ := spec_exists_ok (grid_grid_cell_spec g hg column row)
  ⟨r, hr⟩

/-- `retain` on an in-range cell sets that slot and keeps the specification and the grid invariant. -/
theorem grid_grid_retain_spec (g : grid.Grid) (hg : GridOk g) (column row id : Std.Usize)
    (hc : column.val < g.spec.columns.val) (hr : row.val < g.spec.rows.val) :
    grid.Grid.retain g column row id ⦃ g1 =>
      g1.spec = g.spec ∧ GridOk g1 ∧
      g1.ids.val = g.ids.val.set (row.val * g.spec.columns.val + column.val) (some id) ⦄ := by
  have hg' := hg
  obtain ⟨⟨-, hc0, hr0, -, hst, -, -, -, -, -⟩, hlen⟩ := hg
  unfold grid.Grid.retain
  have hlt := grid_index_lt _ _ _ _ hc hr
  have hm : row.val * g.spec.columns.val ≤ Usize.max := by omega
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨x, back, hx, hback⟩
  have hv : (back (some id)).val = g.ids.val.set (row.val * g.spec.columns.val + column.val) (some id) := by
    rw [hback]; simp [hi1, hi]
  refine ⟨⟨hg'.1, ?_⟩, hv⟩
  show (back (some id)).val.length = _
  rw [hv, List.length_set]; exact hlen

/-! ### Layout::new, loop 3 (grid cells) -/

theorem pointOk_boundsPointOk {p : grid.Point} (h : PointOk p) : BoundsPointOk p := by
  unfold PointOk at h; unfold BoundsPointOk; omega

/-- The disk-test loop over all circles returns, for a valid rectangle, valid circle centers and
bands that keep `outer + band` within the coordinate limit; once `removed` it stays set. -/
theorem layout_new_loop3_inner_total (circles : alloc.vec.Vec polar.Circle)
    (bands : alloc.vec.Vec Std.I32) (bounds : grid.Rect) (removed : Bool) (i : Std.Usize)
    {t : Nat} (hcirc : CirclesOk circles.val t) (hb : BandsOk bands.val circles.val.length)
    (hext : ExtentOk circles.val bands.val circles.val.length) (hr : RectOk bounds) :
    scene.Layout.new_loop3_loop0_loop0 circles bands bounds removed i ⦃ r =>
      removed = true → r = true ⦄ := by
  have hbl : bands.val.length = circles.val.length := hb.1
  unfold scene.Layout.new_loop3_loop0_loop0
  apply loop.spec_decr_nat
    (fun st : Bool × Std.Usize => circles.val.length - st.2.val)
    (fun st : Bool × Std.Usize => removed = true → st.1 = true)
    _
  · rintro ⟨rm, k⟩ hrm
    dsimp only at hrm ⊢
    unfold scene.Layout.new_loop3_loop0_loop0.body
    by_cases hlt : k.val < circles.val.length
    · have hlt' : k < alloc.vec.Vec.len circles := by simpa [alloc.vec.Vec.len] using hlt
      simp only [hlt', ite_true]
      have hck := hcirc k.val hlt
      have hbk := hb.2 k.val (by omega)
      have hek := hext k.val hlt (by omega) hlt
      have hbd := i32_val_bounds (bands.val[k.val]'(by omega))
      have hou := hck.outer_pos
      have hol := hck.outer_le
      step as ⟨c, hc⟩
      step as ⟨p, hp⟩
      step as ⟨b1, hb1⟩
      step as ⟨i3, hi3⟩
      apply spec_bind (grid_rect_touches_disk_spec bounds p i3 hr
        (by rw [hp, hc]; exact pointOk_boundsPointOk hck.center))
      intro b hbb
      have hite : (if b = true then (ok true : Result Bool) else ok rm) = ok (b || rm) := by
        cases b <;> simp
      rw [hite]
      simp only [Std.bind_ok]
      step as ⟨i4, hi4⟩
      refine ⟨?_, by omega⟩
      intro h
      simp [hrm h]
    · have hlt' : ¬ k < alloc.vec.Vec.len circles := by simpa [alloc.vec.Vec.len] using hlt
      simp only [hlt', ite_false, spec_ok]
      exact hrm
  · exact id

/-- One row of the cell sweep returns, keeps the grid invariant and the grid specification, and
extends the cell list by at most one valid grid cell per column. -/
theorem layout_new_loop3_loop0_total (n : Std.Usize) (geometry : grid.Geometry)
    (cell_grid : grid.Grid) (circles : alloc.vec.Vec polar.Circle) (bands : alloc.vec.Vec Std.I32)
    (cells : alloc.vec.Vec scene.Cell) (row column : Std.Usize) {t : Nat}
    (hg : GridOk cell_grid) (hn : n = cell_grid.spec.columns)
    (hrow : row.val < cell_grid.spec.rows.val) (hcol : column.val ≤ n.val)
    (hcap : cells.val.length + (n.val - column.val) ≤ Usize.max)
    (hcirc : CirclesOk circles.val t) (hb : BandsOk bands.val circles.val.length)
    (hext : ExtentOk circles.val bands.val circles.val.length) :
    scene.Layout.new_loop3_loop0 n geometry cell_grid circles bands cells row column ⦃ r =>
      GridOk r.1 ∧ r.1.spec = cell_grid.spec ∧
      ∃ extra : List scene.Cell, r.2.val = cells.val ++ extra ∧ (∀ c ∈ extra, GridCellOk c) ∧
        extra.length ≤ n.val - column.val ⦄ := by
  have hnv : n.val ≤ 2147483647 := by rw [hn]; exact hg.1.2.2.2.2.2.2.1
  have hUm : 4294967295 ≤ Usize.max := by
    rcases Usize.bounds_eq with h | h <;> rw [h] <;>
      simp [U32.max, U64.max, UScalar.max, UScalarTy.numBits, U32.numBits, U64.numBits]
  unfold scene.Layout.new_loop3_loop0
  apply loop.spec_decr_nat
    (fun st : grid.Grid × alloc.vec.Vec scene.Cell × Std.Usize => n.val - st.2.2.val)
    (fun st : grid.Grid × alloc.vec.Vec scene.Cell × Std.Usize =>
      GridOk st.1 ∧ st.1.spec = cell_grid.spec ∧ column.val ≤ st.2.2.val ∧ st.2.2.val ≤ n.val ∧
      ∃ extra : List scene.Cell, st.2.1.val = cells.val ++ extra ∧ (∀ c ∈ extra, GridCellOk c) ∧
        extra.length ≤ st.2.2.val - column.val)
    _
  · rintro ⟨g, cs, col⟩ ⟨hgo, hgs, h1, h2, extra, hcs, hex, hlen⟩
    dsimp only at hgo hgs h1 h2 hcs hex hlen ⊢
    unfold scene.Layout.new_loop3_loop0.body
    by_cases hlt : col < n
    · simp only [hlt, ite_true]
      have hlt' : col.val < n.val := by scalar_tac
      have hcl : col.val < g.spec.columns.val := by rw [hgs, ← hn]; exact hlt'
      have hrl : row.val < g.spec.rows.val := by rw [hgs]; exact hrow
      apply spec_bind (grid_grid_bounds_spec g hgo col row hcl hrl)
      rintro bounds ⟨-, -, -, -, -, -, hrect⟩
      apply spec_bind (grid_geometry_check_spec geometry bounds)
      rintro r ⟨hr1, hr2⟩
      apply spec_bind (result_is_err_spec r)
      intro removed hremoved
      apply spec_bind (layout_new_loop3_inner_total circles bands bounds removed 0#usize hcirc hb
        hext hrect)
      intro removed1 _
      have hpair : (if removed1 = true then ok (g, cs) else do
            let cell_grid2 ← grid.Grid.retain g col row (alloc.vec.Vec.len cs)
            let cells2 ← alloc.vec.Vec.push cs (scene.Cell.Grid col row bounds)
            ok (cell_grid2, cells2)) ⦃ p =>
          GridOk p.1 ∧ p.1.spec = cell_grid.spec ∧
          ∃ ex : List scene.Cell, p.2.val = cs.val ++ ex ∧ (∀ c ∈ ex, GridCellOk c) ∧
            ex.length ≤ 1 ⦄ := by
        by_cases hrm : removed1 = true
        · simp only [hrm, ite_true, spec_ok]
          exact ⟨hgo, hgs, [], by simp, by simp, by simp⟩
        · simp only [hrm, ite_false]
          apply spec_bind (grid_grid_retain_spec g hgo col row (alloc.vec.Vec.len cs) hcl hrl)
          rintro g2 ⟨hg2s, hg2, -⟩
          have hcsl : cs.val.length < Usize.max := by
            rw [hcs, List.length_append]
            omega
          apply spec_bind (alloc.vec.Vec.push_spec cs (scene.Cell.Grid col row bounds) hcsl)
          intro cs2 hcs2
          simp only [spec_ok]
          refine ⟨hg2, hg2s.trans hgs, [scene.Cell.Grid col row bounds], hcs2, ?_, by simp⟩
          intro c hc
          simp only [List.mem_singleton] at hc
          exact ⟨_, _, _, hc, hrect⟩
      apply spec_bind hpair
      rintro ⟨g1, cs1⟩ ⟨hg1, hg1s, ex, hcs1, hex1, hlen1⟩
      dsimp only at hg1 hg1s hcs1
      step as ⟨col1, hcol1⟩
      refine ⟨hg1, hg1s, by omega, by omega, ⟨extra ++ ex, ?_, ?_, ?_⟩, by omega⟩
      · rw [hcs1, hcs, List.append_assoc]
      · intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hex c hc
        · exact hex1 c hc
      · rw [List.length_append]; omega
    · simp only [hlt, ite_false, spec_ok]
      have : col.val = n.val := by scalar_tac
      exact ⟨hgo, hgs, extra, hcs, hex, by omega⟩
  · refine ⟨hg, rfl, le_refl _, hcol, [], by simp, by simp, by simp⟩

/-- The whole cell sweep returns, keeps the grid invariant and the grid specification, and extends
the cell list by valid grid cells, at most one per remaining grid cell. -/
theorem layout_new_loop3_total (n n1 : Std.Usize) (geometry : grid.Geometry)
    (cell_grid : grid.Grid) (circles : alloc.vec.Vec polar.Circle) (bands : alloc.vec.Vec Std.I32)
    (cells : alloc.vec.Vec scene.Cell) (row : Std.Usize) {t : Nat}
    (hg : GridOk cell_grid) (hn : n = cell_grid.spec.columns) (hn1 : n1 = cell_grid.spec.rows)
    (hrow : row.val ≤ n1.val)
    (hcap : cells.val.length + (n1.val - row.val) * n.val ≤ Usize.max)
    (hcirc : CirclesOk circles.val t) (hb : BandsOk bands.val circles.val.length)
    (hext : ExtentOk circles.val bands.val circles.val.length) :
    scene.Layout.new_loop3 n n1 geometry cell_grid circles bands cells row ⦃ r =>
      GridOk r.1 ∧ r.1.spec = cell_grid.spec ∧
      ∃ extra : List scene.Cell, r.2.val = cells.val ++ extra ∧ (∀ c ∈ extra, GridCellOk c) ∧
        extra.length ≤ (n1.val - row.val) * n.val ⦄ := by
  have hn1v : n1.val ≤ 2147483647 := by rw [hn1]; exact hg.1.2.2.2.2.2.2.2.1
  have hUm : 4294967295 ≤ Usize.max := by
    rcases Usize.bounds_eq with h | h <;> rw [h] <;>
      simp [U32.max, U64.max, UScalar.max, UScalarTy.numBits, U32.numBits, U64.numBits]
  unfold scene.Layout.new_loop3
  apply loop.spec_decr_nat
    (fun st : grid.Grid × alloc.vec.Vec scene.Cell × Std.Usize => n1.val - st.2.2.val)
    (fun st : grid.Grid × alloc.vec.Vec scene.Cell × Std.Usize =>
      GridOk st.1 ∧ st.1.spec = cell_grid.spec ∧ row.val ≤ st.2.2.val ∧ st.2.2.val ≤ n1.val ∧
      ∃ extra : List scene.Cell, st.2.1.val = cells.val ++ extra ∧ (∀ c ∈ extra, GridCellOk c) ∧
        extra.length ≤ (st.2.2.val - row.val) * n.val)
    _
  · rintro ⟨g, cs, rw⟩ ⟨hgo, hgs, h1, h2, extra, hcs, hex, hlen⟩
    dsimp only at hgo hgs h1 h2 hcs hex hlen ⊢
    unfold scene.Layout.new_loop3.body
    by_cases hlt : rw < n1
    · simp only [hlt, ite_true]
      have hlt' : rw.val < n1.val := by scalar_tac
      have hsplit : (rw.val - row.val) * n.val + (n1.val - rw.val) * n.val =
          (n1.val - row.val) * n.val := by
        rw [← Nat.add_mul]; congr 1; omega
      have hpos : n.val ≤ (n1.val - rw.val) * n.val :=
        Nat.le_mul_of_pos_left _ (by omega)
      have hcap1 : cs.val.length + (n.val - (0#usize).val) ≤ Usize.max := by
        rw [hcs, List.length_append]
        simp only [UScalar.ofNatCore_val_eq, Nat.sub_zero]
        omega
      apply spec_bind (layout_new_loop3_loop0_total n geometry g circles bands cs rw 0#usize
        hgo (by rw [hgs]; exact hn) (by rw [hgs, ← hn1]; exact hlt') (by simp) hcap1 hcirc hb hext)
      rintro ⟨g1, cs1⟩ ⟨hg1, hg1s, ex, hcs1, hex1, hlen1⟩
      dsimp only at hg1 hg1s hcs1 hlen1
      simp only [UScalar.ofNatCore_val_eq, Nat.sub_zero] at hlen1
      step as ⟨rw1, hrw1⟩
      refine ⟨hg1, hg1s.trans hgs, by omega, by omega, ⟨extra ++ ex, ?_, ?_, ?_⟩, by omega⟩
      · rw [hcs1, hcs, List.append_assoc]
      · intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hex c hc
        · exact hex1 c hc
      · rw [List.length_append, hrw1]
        have : (rw.val + 1 - row.val) * n.val = (rw.val - row.val) * n.val + n.val := by
          rw [show rw.val + 1 - row.val = (rw.val - row.val) + 1 by omega, Nat.succ_mul]
        omega
    · simp only [hlt, ite_false, spec_ok]
      have : rw.val = n1.val := by scalar_tac
      refine ⟨hgo, hgs, extra, hcs, hex, ?_⟩
      rw [this] at hlen
      omega
  · exact ⟨hg, rfl, le_refl _, hrow, [], by simp, by simp, by simp⟩

/-- The sweep as `Layout::new` starts it: from an empty cell list at row 0 it returns, every cell
it produced is a valid grid cell, and there are at most `columns * rows` of them. -/
theorem layout_new_loop3_total_new (n n1 : Std.Usize) (geometry : grid.Geometry)
    (cell_grid : grid.Grid) (circles : alloc.vec.Vec polar.Circle) (bands : alloc.vec.Vec Std.I32)
    {t : Nat} (hg : GridOk cell_grid) (hn : n = cell_grid.spec.columns)
    (hn1 : n1 = cell_grid.spec.rows) (hcirc : CirclesOk circles.val t)
    (hb : BandsOk bands.val circles.val.length)
    (hext : ExtentOk circles.val bands.val circles.val.length) :
    scene.Layout.new_loop3 n n1 geometry cell_grid circles bands (alloc.vec.Vec.new scene.Cell)
        0#usize ⦃ r =>
      GridOk r.1 ∧ r.1.spec = cell_grid.spec ∧ (∀ c ∈ r.2.val, GridCellOk c) ∧
        r.2.val.length ≤ n.val * n1.val ⦄ := by
  have hst := hg.1.2.2.2.2.1
  have hcap : (alloc.vec.Vec.new scene.Cell).val.length + (n1.val - (0#usize).val) * n.val ≤
      Usize.max := by
    have hl0 : (alloc.vec.Vec.new scene.Cell).val.length = 0 := by simp [alloc.vec.Vec.new]
    simp only [hl0, UScalar.ofNatCore_val_eq, Nat.sub_zero, Nat.zero_add]
    rw [hn, hn1, Nat.mul_comm]
    omega
  apply spec_mono (layout_new_loop3_total n n1 geometry cell_grid circles bands
    (alloc.vec.Vec.new scene.Cell) 0#usize hg hn hn1 (by simp) hcap hcirc hb hext)
  rintro r ⟨hr1, hr2, extra, hex, hall, hlen⟩
  refine ⟨hr1, hr2, ?_, ?_⟩
  · intro c hc
    rw [hex] at hc
    simp only [alloc.vec.Vec.new, List.nil_append] at hc
    exact hall c hc
  · rw [hex]
    simp only [alloc.vec.Vec.new, List.nil_append, UScalar.ofNatCore_val_eq, Nat.sub_zero] at hlen ⊢
    rw [Nat.mul_comm]; exact hlen

end Labyrinth
