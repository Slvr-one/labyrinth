module
public import LabyrinthCore.SceneRouteBudget
public import LabyrinthCore.ConstructorSceneTotal

/-! Scene construction (S2), part 1: the eight storage checks that run before the routes are
looked at (`Scene::new`). All eight fail with `Overflow`, none touches the generator, and the
checks run in a fixed order; when all pass, `Scene::new` is the program `sceneNewTail`. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- `n * bytes` fits an allocation (`usize` and `isize` bound). -/
def sceneStorageFits (n bytes : Nat) : Prop :=
  n * bytes ≤ Usize.max ∧ n * bytes ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val

/-- What `Scene::new` does once the eight storage checks have passed: everything after
`check_storage(layout.transforms, 8)`. `count` is `layout.cells.len()`. -/
def sceneNewTail {R : Type _} (treeRngInst : tree.Rng R) (layout : scene.Layout)
    (routes : Slice scene.Route) (occupants : Slice Std.Usize) (patch_capacity : Std.Usize)
    (epoch : Std.U64) (rng : R) (count : Std.Usize) :
    Result ((core.result.Result scene.Scene topology.Error) × R) := do
    let phases ←
      alloc.vec.from_elem core.clone.CloneI32 0#i32
        layout.transforms
    let s ← topology.Carrier.impl.edges layout.carrier
    let i3 := Slice.len s
    let required := alloc.vec.Vec.with_capacity topology.Edge i3
    let s1 := alloc.vec.Vec.deref phases
    let s2 := alloc.vec.Vec.deref phases
    let e ← scene.Edit.Insts.CoreDefaultDefault.default
    let (r8, required1) ←
      scene.check_routes layout routes s1 s2 none e required
    let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
    match cf8 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let (s3, deref_mut_back) ←
        lift (alloc.vec.Vec.deref_mut phases)
      let (s4, deref_mut_back1) ←
        lift (alloc.vec.Vec.deref_mut phases)
      let (r9, s5, s6) ←
        scene.Layout.check_spinning_portals layout routes s3 s4
      let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r9
      match cf9 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let i4 := Slice.len s
        let live_edges :=
          alloc.vec.Vec.with_capacity topology.Edge i4
        let next_phases := deref_mut_back1 s6
        let phases1 := deref_mut_back s5
        let live_edges1 ←
          scene.Scene.new_loop0 layout.cell_grid layout.cells
            layout.circles layout.portals layout.bands
            layout.geometry layout.carrier layout.transforms
            phases1 live_edges 0#usize
        let s7 := alloc.vec.Vec.deref live_edges1
        let r10 ← topology.Carrier.from_edges count s7
        let cf10 ←
          core.result.Result.Insts.CoreOpsTry.branch r10
        match cf10 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let s8 ← topology.Carrier.impl.edges layout.carrier
          let i5 := Slice.len s8
          let r11 ← spanning_tree.Workspace.new count i5
          let cf11 ←
            core.result.Result.Insts.CoreOpsTry.branch r11
          match cf11 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let s9 := alloc.vec.Vec.deref required1
            let (r12, rng1, val4) ←
              spanning_tree.Tree.scene_dfs treeRngInst val2 s9
                0#usize rng val3
            let cf12 ←
              core.result.Result.Insts.CoreOpsTry.branch r12
            match cf12 with
            | core.ops.control_flow.ControlFlow.Continue val5 =>
              let i6 := Slice.len routes
              let saved_routes :=
                alloc.vec.Vec.with_capacity scene.Route i6
              let saved_routes1 ←
                scene.Scene.new_loop1 routes count saved_routes
                  0#usize
              let i7 := Slice.len occupants
              let walkers :=
                alloc.vec.Vec.with_capacity walker.Walker i7
              let (walkers1, valid) ←
                scene.Scene.new_loop2 layout.cell_grid
                  layout.cells layout.circles layout.portals
                  layout.bands layout.geometry layout.carrier
                  layout.transforms occupants count walkers true
                  0#usize
              if valid
              then
                let patches :=
                  alloc.vec.Vec.with_capacity shatter.Patch
                    patch_capacity
                let patches1 ←
                  scene.Scene.new_loop3 patch_capacity count
                    patches 0#usize
                let v ←
                  alloc.vec.from_elem core.clone.CloneUsize
                    0#usize layout.transforms
                ok (core.result.Result.Ok
                  {
                    layout,
                    tree := val5,
                    work := val4,
                    routes := saved_routes1,
                    required := required1,
                    phases := phases1,
                    next_phases,
                    holds := v,
                    walkers := walkers1,
                    patches := patches1,
                    stamp := { epoch, revision := 0#u64 },
                    clock := 0#u64,
                    wall := 0#u64,
                    reanchor := false,
                    suspended := false,
                    inactive := false,
                    latest_request := epoch,
                    pending := none,
                    trail_revision := 0#u64
                  }, rng1)
              else
                ok (core.result.Result.Err
                  topology.Error.InvalidIndex, rng1)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r13 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  scene.Scene (core.convert.FromSame
                  topology.Error) residual
              ok (r13, rng1)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r12 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                scene.Scene (core.convert.FromSame
                topology.Error) residual
            ok (r12, rng)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r11 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              scene.Scene (core.convert.FromSame topology.Error)
              residual
          ok (r11, rng)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r10 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            scene.Scene (core.convert.FromSame topology.Error)
            residual
        ok (r10, rng)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r9 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          scene.Scene (core.convert.FromSame topology.Error)
          residual
      ok (r9, rng)

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

private theorem checked_mul_len (x y : Std.Usize) (h : x.val * y.val ≤ Usize.max) :
    ∃ z, Usize.checked_mul x y = some z ∧ z.val = x.val * y.val :=
  constructor_checked_mul_some x y h

private theorem storage_fits_iff (c b : Std.Usize) :
    constructorStorageFits c b ↔ sceneStorageFits c.val b.val := Iff.rfl

private theorem check_ok_iff (c b : Std.Usize) (h : constructorStorageFits c b) :
    topology.check_storage c b = ok (core.result.Result.Ok ()) := by
  rw [constructor_check_storage_eq]; simp [h]

private theorem check_err_of (c b : Std.Usize) (h : ¬ constructorStorageFits c b) :
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

/-- All eight checks pass: `Scene::new` continues with `sceneNewTail`, generator untouched so
far. -/
theorem scene_new_checks_pass
    (h1 : patch_capacity.val * layout.cells.val.length ≤ Usize.max)
    (h2 : routes.val.length * layout.cells.val.length ≤ Usize.max)
    (h3 : sceneStorageFits (patch_capacity.val * layout.cells.val.length) 1)
    (h4 : sceneStorageFits (routes.val.length * layout.cells.val.length) 8)
    (h5 : sceneStorageFits patch_capacity.val 48)
    (h6 : sceneStorageFits occupants.val.length 192)
    (h7 : sceneStorageFits routes.val.length 32)
    (h8 : sceneStorageFits layout.transforms.val 8) :
    scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng =
      sceneNewTail treeRngInst layout routes occupants patch_capacity epoch rng
        (alloc.vec.Vec.len layout.cells) := by
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
  have hc6 := check_ok_iff layout.transforms 8#usize (by
    rw [storage_fits_iff]; simpa using h8)
  unfold scene.Scene.new sceneNewTail
  simp only [hz1, hz2, hc1, hc2, hc3, hc4, hc5, hc6, lift, bind_ok, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch]
  rfl


end Checks

end Labyrinth
