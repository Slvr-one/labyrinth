module
public import LabyrinthCore.SceneRouteBudget
public import LabyrinthCore.ConstructorSceneTotal

/-! Scene construction (S2), part 1: the eight storage checks that run before the routes are
looked at (`Scene::new`). All eight fail with `Overflow`, none touches the generator, and the
checks run in a fixed order; when all pass, `Scene::new` continues with the rest of the program (see `SceneConstruction`). -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- `n * bytes` fits an allocation (`usize` and `isize` bound). -/
def sceneStorageFits (n bytes : Nat) : Prop :=
  n * bytes ≤ Usize.max ∧ n * bytes ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val

/-! ### The eight pre-route checks

With `n = layout.cells.len()`, in source order:
1. `patch_capacity * n` does not overflow `usize`;
2. `routes.len() * n` does not overflow `usize`;
3. `patch_capacity * n` bytes (element size 1) fit an allocation;
4. `routes.len() * n` elements of 8 bytes fit;
5. `patch_capacity` elements of 48 bytes fit;
6. `occupants.len()` elements of 192 bytes fit;
7. `routes.len()` elements of 32 bytes fit;
8. `layout.transforms` elements of 8 bytes fit. -/

section Checks

variable {R : Type _} (treeRngInst : tree.Rng R) (layout : scene.Layout)
  (routes : Slice scene.Route) (occupants : Slice Std.Usize) (patch_capacity : Std.Usize)
  (epoch : Std.U64) (rng : R)

private theorem checked_mul_none_of_lt (x y : Std.Usize) (h : ¬ x.val * y.val ≤ Usize.max) :
    Usize.checked_mul x y = none := by
  have hm := Usize.checked_mul_bv_spec x y
  cases he : Usize.checked_mul x y with
  | none => rfl
  | some z => simp only [he] at hm; omega

theorem storage_fits_iff (c b : Std.Usize) :
    constructorStorageFits c b ↔ sceneStorageFits c.val b.val := Iff.rfl

theorem check_ok_iff (c b : Std.Usize) (h : constructorStorageFits c b) :
    topology.check_storage c b = ok (core.result.Result.Ok ()) := by
  rw [constructor_check_storage_eq]; simp [h]

theorem check_err_of (c b : Std.Usize) (h : ¬ constructorStorageFits c b) :
    topology.check_storage c b = ok (core.result.Result.Err topology.Error.Overflow) := by
  rw [constructor_check_storage_eq]; simp [h]

/-- Check 1 failing: `Overflow`, generator untouched. -/
theorem scene_new_overflow_patch_count
    (h : ¬ patch_capacity.val * layout.cells.val.length ≤ Usize.max) :
    scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng =
      ok (core.result.Result.Err topology.Error.Overflow, rng) := by
  have hn := checked_mul_none_of_lt patch_capacity (alloc.vec.Vec.len layout.cells)
    (by simpa using h)
  unfold scene.Scene.new
  simp only [hn, lift, bind_ok, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, bind_tc_ok]



/-- Check 2 failing. -/
theorem scene_new_overflow_route_count
    (h1 : patch_capacity.val * layout.cells.val.length ≤ Usize.max)
    (h : ¬ routes.val.length * layout.cells.val.length ≤ Usize.max) :
    scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng =
      ok (core.result.Result.Err topology.Error.Overflow, rng) := by
  obtain ⟨z1, hz1, -⟩ := constructor_checked_mul_some patch_capacity
    (alloc.vec.Vec.len layout.cells) (by simpa using h1)
  have hn := checked_mul_none_of_lt (Slice.len routes) (alloc.vec.Vec.len layout.cells)
    (by simpa using h)
  unfold scene.Scene.new
  simp only [hz1, hn, lift, bind_ok, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, bind_tc_ok]

/-- Check 3 failing. -/
theorem scene_new_overflow_patch_bytes
    (h1 : patch_capacity.val * layout.cells.val.length ≤ Usize.max)
    (h2 : routes.val.length * layout.cells.val.length ≤ Usize.max)
    (h : ¬ sceneStorageFits (patch_capacity.val * layout.cells.val.length) 1) :
    scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng =
      ok (core.result.Result.Err topology.Error.Overflow, rng) := by
  obtain ⟨z1, hz1, hz1v⟩ := constructor_checked_mul_some patch_capacity
    (alloc.vec.Vec.len layout.cells) (by simpa using h1)
  obtain ⟨z2, hz2, -⟩ := constructor_checked_mul_some (Slice.len routes)
    (alloc.vec.Vec.len layout.cells) (by simpa using h2)
  have hc := check_err_of z1 1#usize (by
    rw [storage_fits_iff, hz1v]; simpa using h)
  unfold scene.Scene.new
  simp only [hz1, hz2, hc, lift, bind_ok, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, bind_tc_ok]

/-- Check 4 failing. -/
theorem scene_new_overflow_route_bytes
    (h1 : patch_capacity.val * layout.cells.val.length ≤ Usize.max)
    (h2 : routes.val.length * layout.cells.val.length ≤ Usize.max)
    (h3 : sceneStorageFits (patch_capacity.val * layout.cells.val.length) 1)
    (h : ¬ sceneStorageFits (routes.val.length * layout.cells.val.length) 8) :
    scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng =
      ok (core.result.Result.Err topology.Error.Overflow, rng) := by
  obtain ⟨z1, hz1, hz1v⟩ := constructor_checked_mul_some patch_capacity
    (alloc.vec.Vec.len layout.cells) (by simpa using h1)
  obtain ⟨z2, hz2, hz2v⟩ := constructor_checked_mul_some (Slice.len routes)
    (alloc.vec.Vec.len layout.cells) (by simpa using h2)
  have hc1 := check_ok_iff z1 1#usize (by
    rw [storage_fits_iff, hz1v]; simpa using h3)
  have hc := check_err_of z2 8#usize (by
    rw [storage_fits_iff, hz2v]; simpa using h)
  unfold scene.Scene.new
  simp only [hz1, hz2, hc1, hc, lift, bind_ok, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, bind_tc_ok]

/-- Check 5 failing. -/
theorem scene_new_overflow_patch_storage
    (h1 : patch_capacity.val * layout.cells.val.length ≤ Usize.max)
    (h2 : routes.val.length * layout.cells.val.length ≤ Usize.max)
    (h3 : sceneStorageFits (patch_capacity.val * layout.cells.val.length) 1)
    (h4 : sceneStorageFits (routes.val.length * layout.cells.val.length) 8)
    (h : ¬ sceneStorageFits patch_capacity.val 48) :
    scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng =
      ok (core.result.Result.Err topology.Error.Overflow, rng) := by
  obtain ⟨z1, hz1, hz1v⟩ := constructor_checked_mul_some patch_capacity
    (alloc.vec.Vec.len layout.cells) (by simpa using h1)
  obtain ⟨z2, hz2, hz2v⟩ := constructor_checked_mul_some (Slice.len routes)
    (alloc.vec.Vec.len layout.cells) (by simpa using h2)
  have hc1 := check_ok_iff z1 1#usize (by
    rw [storage_fits_iff, hz1v]; simpa using h3)
  have hc2 := check_ok_iff z2 8#usize (by
    rw [storage_fits_iff, hz2v]; simpa using h4)
  have hc := check_err_of patch_capacity 48#usize (by
    rw [storage_fits_iff]; simpa using h)
  unfold scene.Scene.new
  simp only [hz1, hz2, hc1, hc2, hc, lift, bind_ok, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, bind_tc_ok]

/-- Check 6 failing. -/
theorem scene_new_overflow_occupant_storage
    (h1 : patch_capacity.val * layout.cells.val.length ≤ Usize.max)
    (h2 : routes.val.length * layout.cells.val.length ≤ Usize.max)
    (h3 : sceneStorageFits (patch_capacity.val * layout.cells.val.length) 1)
    (h4 : sceneStorageFits (routes.val.length * layout.cells.val.length) 8)
    (h5 : sceneStorageFits patch_capacity.val 48)
    (h : ¬ sceneStorageFits occupants.val.length 192) :
    scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng =
      ok (core.result.Result.Err topology.Error.Overflow, rng) := by
  obtain ⟨z1, hz1, hz1v⟩ := constructor_checked_mul_some patch_capacity
    (alloc.vec.Vec.len layout.cells) (by simpa using h1)
  obtain ⟨z2, hz2, hz2v⟩ := constructor_checked_mul_some (Slice.len routes)
    (alloc.vec.Vec.len layout.cells) (by simpa using h2)
  have hc1 := check_ok_iff z1 1#usize (by
    rw [storage_fits_iff, hz1v]; simpa using h3)
  have hc2 := check_ok_iff z2 8#usize (by
    rw [storage_fits_iff, hz2v]; simpa using h4)
  have hc3 := check_ok_iff patch_capacity 48#usize (by
    rw [storage_fits_iff]; simpa using h5)
  have hc := check_err_of (Slice.len occupants) 192#usize (by
    rw [storage_fits_iff]; simpa using h)
  unfold scene.Scene.new
  simp only [hz1, hz2, hc1, hc2, hc3, hc, lift, bind_ok, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, bind_tc_ok]

/-- Check 7 failing. -/
theorem scene_new_overflow_route_storage
    (h1 : patch_capacity.val * layout.cells.val.length ≤ Usize.max)
    (h2 : routes.val.length * layout.cells.val.length ≤ Usize.max)
    (h3 : sceneStorageFits (patch_capacity.val * layout.cells.val.length) 1)
    (h4 : sceneStorageFits (routes.val.length * layout.cells.val.length) 8)
    (h5 : sceneStorageFits patch_capacity.val 48)
    (h6 : sceneStorageFits occupants.val.length 192)
    (h : ¬ sceneStorageFits routes.val.length 32) :
    scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng =
      ok (core.result.Result.Err topology.Error.Overflow, rng) := by
  obtain ⟨z1, hz1, hz1v⟩ := constructor_checked_mul_some patch_capacity
    (alloc.vec.Vec.len layout.cells) (by simpa using h1)
  obtain ⟨z2, hz2, hz2v⟩ := constructor_checked_mul_some (Slice.len routes)
    (alloc.vec.Vec.len layout.cells) (by simpa using h2)
  have hc1 := check_ok_iff z1 1#usize (by
    rw [storage_fits_iff, hz1v]; simpa using h3)
  have hc2 := check_ok_iff z2 8#usize (by
    rw [storage_fits_iff, hz2v]; simpa using h4)
  have hc3 := check_ok_iff patch_capacity 48#usize (by
    rw [storage_fits_iff]; simpa using h5)
  have hc4 := check_ok_iff (Slice.len occupants) 192#usize (by
    rw [storage_fits_iff]; simpa using h6)
  have hc := check_err_of (Slice.len routes) 32#usize (by
    rw [storage_fits_iff]; simpa using h)
  unfold scene.Scene.new
  simp only [hz1, hz2, hc1, hc2, hc3, hc4, hc, lift, bind_ok, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, bind_tc_ok]

/-- Check 8 failing. -/
theorem scene_new_overflow_transform_storage
    (h1 : patch_capacity.val * layout.cells.val.length ≤ Usize.max)
    (h2 : routes.val.length * layout.cells.val.length ≤ Usize.max)
    (h3 : sceneStorageFits (patch_capacity.val * layout.cells.val.length) 1)
    (h4 : sceneStorageFits (routes.val.length * layout.cells.val.length) 8)
    (h5 : sceneStorageFits patch_capacity.val 48)
    (h6 : sceneStorageFits occupants.val.length 192)
    (h7 : sceneStorageFits routes.val.length 32)
    (h : ¬ sceneStorageFits layout.transforms.val 8) :
    scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng =
      ok (core.result.Result.Err topology.Error.Overflow, rng) := by
  obtain ⟨z1, hz1, hz1v⟩ := constructor_checked_mul_some patch_capacity
    (alloc.vec.Vec.len layout.cells) (by simpa using h1)
  obtain ⟨z2, hz2, hz2v⟩ := constructor_checked_mul_some (Slice.len routes)
    (alloc.vec.Vec.len layout.cells) (by simpa using h2)
  have hc1 := check_ok_iff z1 1#usize (by
    rw [storage_fits_iff, hz1v]; simpa using h3)
  have hc2 := check_ok_iff z2 8#usize (by
    rw [storage_fits_iff, hz2v]; simpa using h4)
  have hc3 := check_ok_iff patch_capacity 48#usize (by
    rw [storage_fits_iff]; simpa using h5)
  have hc4 := check_ok_iff (Slice.len occupants) 192#usize (by
    rw [storage_fits_iff]; simpa using h6)
  have hc5 := check_ok_iff (Slice.len routes) 32#usize (by
    rw [storage_fits_iff]; simpa using h7)
  have hc := check_err_of layout.transforms 8#usize (by
    rw [storage_fits_iff]; simpa using h)
  unfold scene.Scene.new
  simp only [hz1, hz2, hc1, hc2, hc3, hc4, hc5, hc, lift, bind_ok, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, bind_tc_ok]

end Checks

end Labyrinth
