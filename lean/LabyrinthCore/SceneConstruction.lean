module
public import LabyrinthCore.SceneConstructionChecks
public import LabyrinthCore.SceneConstructionSpinning
public import LabyrinthCore.SceneConstructionRequired
public import LabyrinthCore.SceneConstructionLive
public import LabyrinthCore.SceneConstructionOccupants
public import LabyrinthCore.ConstructorSceneTotal
public import LabyrinthCore.ConstructorCarrierEdges

/-! Scene construction (S2): the full outcome of `Scene::new`.

The stages, in source order: eight storage checks (`Overflow`); `check_routes` on a zeroed phase
table; `check_spinning_portals` (`InvalidGeometry`, tables zero again afterwards); the live edges
(carrier edges the doorway admits); `Carrier::from_edges` on them; `Workspace::new`; `scene_dfs`
rooted at cell 0 with the route edges required; and finally the occupant check, whose
`InvalidIndex` therefore comes after the DFS has consumed the generator. Every error before the
DFS leaves the generator unchanged.

Stages that reach `Layout::doorway` or `Layout::local_pose` are partial correctness (`OkPost`):
the statement holds of every result the call returns, until geometry totality is proved. The
stages that do not (storage checks, carrier, workspace, DFS) are total in their own specs. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

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
    let pr1 ←
      scene.check_routes layout routes s1 s2 none e required
    let r8 := pr1.1
    let required1 := pr1.2
    let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
    match cf8 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let pr2 ←
        lift (alloc.vec.Vec.deref_mut phases)
      let s3 := pr2.1
      let deref_mut_back := pr2.2
      let pr3 ←
        lift (alloc.vec.Vec.deref_mut phases)
      let s4 := pr3.1
      let deref_mut_back1 := pr3.2
      let pr4 ←
        scene.Layout.check_spinning_portals layout routes s3 s4
      let r9 := pr4.1
      let s5 := pr4.2.1
      let s6 := pr4.2.2
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
            let pr5 ←
              spanning_tree.Tree.scene_dfs treeRngInst val2 s9
                0#usize rng val3
            let r12 := pr5.1
            let rng1 := pr5.2.1
            let val4 := pr5.2.2
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
              let pr6 ←
                scene.Scene.new_loop2 layout.cell_grid
                  layout.cells layout.circles layout.portals
                  layout.bands layout.geometry layout.carrier
                  layout.transforms occupants count walkers true
                  0#usize
              let walkers1 := pr6.1
              let valid := pr6.2
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

section Pass

variable {R : Type _} (treeRngInst : tree.Rng R) (layout : scene.Layout)
  (routes : Slice scene.Route) (occupants : Slice Std.Usize) (patch_capacity : Std.Usize)
  (epoch : Std.U64) (rng : R)

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

end Pass

/-- The eight storage checks pass (see `scene_new_overflow_*`). -/
def SceneStoragePass (layout : scene.Layout) (routes : Slice scene.Route)
    (occupants : Slice Std.Usize) (patch_capacity : Std.Usize) : Prop :=
  patch_capacity.val * layout.cells.val.length ≤ Usize.max ∧
  routes.val.length * layout.cells.val.length ≤ Usize.max ∧
  sceneStorageFits (patch_capacity.val * layout.cells.val.length) 1 ∧
  sceneStorageFits (routes.val.length * layout.cells.val.length) 8 ∧
  sceneStorageFits patch_capacity.val 48 ∧
  sceneStorageFits occupants.val.length 192 ∧
  sceneStorageFits routes.val.length 32 ∧
  sceneStorageFits layout.transforms.val 8

/-- The zeroed phase table `Scene::new` allocates. -/
def ScenePhasesZero (layout : scene.Layout) (phases : alloc.vec.Vec Std.I32) : Prop :=
  phases.val = List.replicate layout.transforms.val 0#i32

/-- The route check as `Scene::new` calls it: the zero tables as both phase and next table, the
default edit, no tree, and an empty scratch list. -/
def SceneRoutesCall (layout : scene.Layout) (routes : Slice scene.Route)
    (phases : alloc.vec.Vec Std.I32) (e : scene.Edit)
    (r : core.result.Result Unit topology.Error) (req : alloc.vec.Vec topology.Edge) : Prop :=
  scene.Edit.Insts.CoreDefaultDefault.default = ok e ∧
  scene.check_routes layout routes (alloc.vec.Vec.deref phases) (alloc.vec.Vec.deref phases)
    none e (alloc.vec.Vec.new topology.Edge) = ok (r, req)

/-- The live edges: the carrier edges the doorway admits under the tables the scan handed back. -/
def SceneLiveSet (layout : scene.Layout) (s5 : Slice Std.I32)
    (live : alloc.vec.Vec topology.Edge) : Prop :=
  ∀ e, e ∈ live.val ↔ e ∈ layout.carrier.edges.val ∧
    DoorwayLive layout (alloc.vec.Vec.deref ({ slice := s5 } : alloc.vec.Vec Std.I32))
      (alloc.vec.Vec.deref ({ slice := s5 } : alloc.vec.Vec Std.I32)) e

/-- Errors of the DFS on the live carrier: workspace and forest rejections leave the generator
alone; only the post-DFS `Overflow` may have consumed it. -/
def SceneDfsError {R : Type _} (x : topology.Error) (rng rng1 : R) : Prop :=
  x = topology.Error.Overflow ∨
    ((x = topology.Error.InsufficientWorkspace ∨ x = topology.Error.InvalidForest) ∧ rng1 = rng)

/-- The last stage: the occupants are checked after the DFS, with the generator it left. -/
def SceneOccupantStage {R : Type _} (layout : scene.Layout) (occupants : Slice Std.Usize)
    (epoch : Std.U64) (required1 : alloc.vec.Vec topology.Edge) (s5 s6 : Slice Std.I32)
    (tree : spanning_tree.Tree) (rng1 : R)
    (p : (core.result.Result scene.Scene topology.Error) × R) : Prop :=
  (¬ OccupantsValid occupants (alloc.vec.Vec.len layout.cells) ∧
    p = (core.result.Result.Err topology.Error.InvalidIndex, rng1)) ∨
  (OccupantsValid occupants (alloc.vec.Vec.len layout.cells) ∧
    ∃ s, p.1 = core.result.Result.Ok s ∧ p.2 = rng1 ∧ s.layout = layout ∧ s.tree = tree ∧
      s.required = required1 ∧ s.phases.slice = s5 ∧ s.next_phases.slice = s6 ∧
      s.stamp = ⟨epoch, 0#u64⟩ ∧ s.clock = 0#u64 ∧ s.wall = 0#u64 ∧
      s.latest_request = epoch ∧ s.pending = none ∧ s.trail_revision = 0#u64 ∧
      s.reanchor = false ∧ s.suspended = false ∧ s.inactive = false)

/-- The DFS stage. On success the tree is valid on the live carrier, rooted at cell 0, and
contains every route edge. -/
def SceneDfsStage {R : Type _} (treeRngInst : tree.Rng R) (layout : scene.Layout)
    (routes : Slice scene.Route) (occupants : Slice Std.Usize) (epoch : Std.U64) (rng : R)
    (required1 : alloc.vec.Vec topology.Edge) (s5 s6 : Slice Std.I32)
    (carrier : topology.Carrier) (work : spanning_tree.Workspace)
    (p : (core.result.Result scene.Scene topology.Error) × R) : Prop :=
  (∃ x rng1 work', spanning_tree.Tree.scene_dfs treeRngInst carrier
      (alloc.vec.Vec.deref required1) 0#usize rng work =
        ok (core.result.Result.Err x, rng1, work') ∧
      p = (core.result.Result.Err x, rng1) ∧ SceneDfsError x rng rng1) ∨
  (∃ tree rng1 work', spanning_tree.Tree.scene_dfs treeRngInst carrier
      (alloc.vec.Vec.deref required1) 0#usize rng work =
        ok (core.result.Result.Ok tree, rng1, work') ∧
      TreeValid carrier tree ∧ tree.root.val = 0 ∧
      (∀ e ∈ allEdges routes.val, parentEdge (parents tree) e.u.val e.v.val) ∧
      SceneOccupantStage layout occupants epoch required1 s5 s6 tree rng1 p)

/-- Everything `Scene::new` can return, by stage. -/
def SceneNewOutcome {R : Type _} (treeRngInst : tree.Rng R) (layout : scene.Layout)
    (routes : Slice scene.Route) (occupants : Slice Std.Usize) (patch_capacity : Std.Usize)
    (epoch : Std.U64) (rng : R)
    (p : (core.result.Result scene.Scene topology.Error) × R) : Prop :=
  -- the eight storage checks
  (¬ SceneStoragePass layout routes occupants patch_capacity ∧
    p = (core.result.Result.Err topology.Error.Overflow, rng)) ∨
  (SceneStoragePass layout routes occupants patch_capacity ∧
    ∃ phases : alloc.vec.Vec Std.I32, ScenePhasesZero layout phases ∧
      -- the route check
      ((∃ x req e, SceneRoutesCall layout routes phases e (core.result.Result.Err x) req ∧
          p = (core.result.Result.Err x, rng)) ∨
       (∃ required1 e, SceneRoutesCall layout routes phases e (core.result.Result.Ok ())
            required1 ∧
          required1.val = foldEdges [] (allEdges routes.val) ∧
          (∀ x ∈ required1.val, x ∈ layout.carrier.edges.val) ∧
          -- the spinning-portal scan
          ((∃ s5 s6, scene.Layout.check_spinning_portals layout routes phases.slice phases.slice =
              ok (core.result.Result.Err topology.Error.InvalidGeometry, s5, s6) ∧
            p = (core.result.Result.Err topology.Error.InvalidGeometry, rng)) ∨
           (∃ s5 s6 live,
              scene.Layout.check_spinning_portals layout routes phases.slice phases.slice =
                ok (core.result.Result.Ok (), s5, s6) ∧
              AllZeroPhases s5.val ∧ AllZeroPhases s6.val ∧
              SceneLiveSet layout s5 live ∧ (∀ x ∈ required1.val, x ∈ live.val) ∧
              -- the carrier of the live edges
              ((∃ x, topology.Carrier.from_edges (alloc.vec.Vec.len layout.cells)
                    (alloc.vec.Vec.deref live) = ok (core.result.Result.Err x) ∧
                  p = (core.result.Result.Err x, rng)) ∨
               (∃ carrier, topology.Carrier.from_edges (alloc.vec.Vec.len layout.cells)
                    (alloc.vec.Vec.deref live) = ok (core.result.Result.Ok carrier) ∧
                  CarrierValid carrier ∧
                  -- the workspace
                  ((∃ x, spanning_tree.Workspace.new (alloc.vec.Vec.len layout.cells)
                        (Slice.len (alloc.vec.Vec.deref layout.carrier.edges)) =
                          ok (core.result.Result.Err x) ∧
                      p = (core.result.Result.Err x, rng)) ∨
                   (∃ work, spanning_tree.Workspace.new (alloc.vec.Vec.len layout.cells)
                        (Slice.len (alloc.vec.Vec.deref layout.carrier.edges)) =
                          ok (core.result.Result.Ok work) ∧ WorkspaceValid work ∧
                      SceneDfsStage treeRngInst layout routes occupants epoch rng required1 s5 s6
                        carrier work p)))))))))

theorem okPost_and {α : Type _} {m : Result α} {P Q : α → Prop} (h1 : OkPost m P)
    (h2 : OkPost m Q) : OkPost m (fun a => P a ∧ Q a) := fun v hv => ⟨h1 v hv, h2 v hv⟩

theorem with_capacity_val {α : Type _} (n : Std.Usize) :
    (alloc.vec.Vec.with_capacity α n).val = [] := rfl

/-- When a storage check fails the call returns `Overflow` with the generator untouched. -/
theorem scene_new_not_pass {R : Type _} (treeRngInst : tree.Rng R) (layout : scene.Layout)
    (routes : Slice scene.Route) (occupants : Slice Std.Usize) (patch_capacity : Std.Usize)
    (epoch : Std.U64) (rng : R)
    (h : ¬ SceneStoragePass layout routes occupants patch_capacity) :
    scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng =
      ok (core.result.Result.Err topology.Error.Overflow, rng) := by
  unfold SceneStoragePass at h
  by_cases h1 : patch_capacity.val * layout.cells.val.length ≤ Usize.max
  swap
  · exact scene_new_overflow_patch_count treeRngInst layout routes occupants patch_capacity epoch
      rng h1
  by_cases h2 : routes.val.length * layout.cells.val.length ≤ Usize.max
  swap
  · exact scene_new_overflow_route_count treeRngInst layout routes occupants patch_capacity epoch
      rng h1 h2
  by_cases h3 : sceneStorageFits (patch_capacity.val * layout.cells.val.length) 1
  swap
  · exact scene_new_overflow_patch_bytes treeRngInst layout routes occupants patch_capacity epoch
      rng h1 h2 h3
  by_cases h4 : sceneStorageFits (routes.val.length * layout.cells.val.length) 8
  swap
  · exact scene_new_overflow_route_bytes treeRngInst layout routes occupants patch_capacity epoch
      rng h1 h2 h3 h4
  by_cases h5 : sceneStorageFits patch_capacity.val 48
  swap
  · exact scene_new_overflow_patch_storage treeRngInst layout routes occupants patch_capacity
      epoch rng h1 h2 h3 h4 h5
  by_cases h6 : sceneStorageFits occupants.val.length 192
  swap
  · exact scene_new_overflow_occupant_storage treeRngInst layout routes occupants patch_capacity
      epoch rng h1 h2 h3 h4 h5 h6
  by_cases h7 : sceneStorageFits routes.val.length 32
  swap
  · exact scene_new_overflow_route_storage treeRngInst layout routes occupants patch_capacity
      epoch rng h1 h2 h3 h4 h5 h6 h7
  by_cases h8 : sceneStorageFits layout.transforms.val 8
  swap
  · exact scene_new_overflow_transform_storage treeRngInst layout routes occupants patch_capacity
      epoch rng h1 h2 h3 h4 h5 h6 h7 h8
  exact absurd ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ h

/-- `Scene::new` returns only outcomes of `SceneNewOutcome`, for a valid layout carrier and a legal
generator: the first failing stage decides the error, every error before the DFS leaves the
generator unchanged, and the occupant check runs last, on the generator the DFS left. On success
the tree is valid on the carrier of the live edges, rooted at cell 0, contains every route edge,
and the scene's stamp is `{epoch, 0}`. Partial correctness: stages that reach the doorway's
geometry are only known to behave this way when they return. -/
theorem scene_new_spec {R : Type _} (treeRngInst : tree.Rng R)
    (hrng : constructorLegalRng treeRngInst) (layout : scene.Layout)
    (routes : Slice scene.Route) (occupants : Slice Std.Usize) (patch_capacity : Std.Usize)
    (epoch : Std.U64) (rng : R) (hc : CarrierValid layout.carrier) :
    OkPost (scene.Scene.new treeRngInst layout routes occupants patch_capacity epoch rng)
      (SceneNewOutcome treeRngInst layout routes occupants patch_capacity epoch rng) := by
  by_cases hpass : SceneStoragePass layout routes occupants patch_capacity
  swap
  · rw [scene_new_not_pass treeRngInst layout routes occupants patch_capacity epoch rng hpass]
    exact okPost_ok (Or.inl ⟨hpass, rfl⟩)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpass
  rw [scene_new_checks_pass treeRngInst layout routes occupants patch_capacity epoch rng h1 h2
    h3 h4 h5 h6 h7 h8]
  have hpass : SceneStoragePass layout routes occupants patch_capacity :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  unfold sceneNewTail SceneNewOutcome
  refine okPost_bind_eq (okPost_of_spec
    (alloc.vec.from_elem_spec core.clone.CloneI32 0#i32 layout.transforms rfl)) ?_
  intro phases _ hph
  have hedges : topology.Carrier.impl.edges layout.carrier =
      ok (alloc.vec.Vec.deref layout.carrier.edges) := rfl
  rw [hedges, Std.bind_ok]
  refine okPost_bind_eq (okPost_trivial _) ?_
  intro e he _
  have hphz : AllZeroPhases phases.val := by
    intro i x hx
    rw [hph.1] at hx
    simp only [List.getElem?_replicate] at hx
    split at hx
    · simp only [Option.some.injEq] at hx; subst hx; simp
    · simp at hx
  have hinv0 : RouteInv layout.carrier (alloc.vec.Vec.with_capacity topology.Edge
      (Slice.len (alloc.vec.Vec.deref layout.carrier.edges))) := by
    rw [RouteInv, with_capacity_val]; simp
  have hadm0 : AdmittedList layout (alloc.vec.Vec.deref phases) (alloc.vec.Vec.deref phases)
      (alloc.vec.Vec.with_capacity topology.Edge
        (Slice.len (alloc.vec.Vec.deref layout.carrier.edges))) := by
    intro x hx; rw [with_capacity_val] at hx; simp at hx
  refine okPost_bind_eq (okPost_and
    (scene_check_routes_required_exact layout routes (alloc.vec.Vec.deref phases)
      (alloc.vec.Vec.deref phases) none e _ hc hinv0)
    (scene_check_routes_admitted layout routes (alloc.vec.Vec.deref phases)
      (alloc.vec.Vec.deref phases) none e _ hadm0)) ?_
  rintro ⟨r8, required1⟩ hcall ⟨⟨hreq, hok, herr⟩, hadm⟩
  simp only at hreq hok herr hadm
  cases r8 with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    refine okPost_ok ?_
    exact Or.inr ⟨hpass, phases, hph.1, Or.inl ⟨x, required1, e, ⟨he, hcall⟩, rfl⟩⟩
  | Ok u =>
    dsimp only
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    have hreq1 := hok rfl
    have hzp : AllZeroPhases phases.slice.val := hphz
    -- `deref_mut` hands out the same table twice
    simp only [lift, Std.bind_ok, alloc.vec.Vec.deref_mut]
    refine okPost_bind_eq (layout_check_spinning_portals_post layout routes phases.slice
      phases.slice hzp hzp) ?_
    rintro ⟨r9, s5, s6⟩ hspin ⟨hl5, hl6, hz5, hz6, hv⟩
    simp only at hl5 hl6 hz5 hz6 hv
    have hroutes : SceneRoutesCall layout routes phases e (core.result.Result.Ok ()) required1 :=
      ⟨he, hcall⟩
    have hreq2 : ∀ x ∈ required1.val, x ∈ layout.carrier.edges.val := hreq.2
    have hreq3 : required1.val = foldEdges [] (allEdges routes.val) := hreq1
    have hadm' : AdmittedList layout (alloc.vec.Vec.deref phases) (alloc.vec.Vec.deref phases)
        required1 := hadm
    cases r9 with
    | Err x =>
      have hx : x = topology.Error.InvalidGeometry := by
        rcases hv with h | h
        · exact absurd h (by simp)
        · simpa using h
      subst hx
      simp only [Std.bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      refine okPost_ok ?_
      exact Or.inr ⟨hpass, phases, hph.1, Or.inr ⟨required1, e, hroutes, hreq3, hreq2,
        Or.inl ⟨s5, s6, hspin, rfl⟩⟩⟩
    | Ok u =>
      simp only [Std.bind_ok]
      have hlive0 : (alloc.vec.Vec.with_capacity topology.Edge
          (Slice.len (alloc.vec.Vec.deref layout.carrier.edges))).val = [] := rfl
      refine okPost_bind_eq (scene_new_live_loop layout ({ slice := s5 } : alloc.vec.Vec Std.I32)
        _ hlive0) ?_
      intro live1 hlloop hlive1
      have hsub : ∀ x ∈ required1.val, x ∈ live1.val := by
        refine scene_new_required_subset_live layout phases s5 required1 live1 hphz hz5
          (by simpa [alloc.vec.Vec.val] using hl5) hadm' hreq2 hlive1
      have hspinOk : scene.Layout.check_spinning_portals layout routes phases.slice phases.slice =
          ok (core.result.Result.Ok (), s5, s6) := hspin
      refine okPost_bind_eq (okPost_of_spec
        (constructor_carrier_from_edges_total_spec (alloc.vec.Vec.len layout.cells)
          (alloc.vec.Vec.deref live1))) ?_
      intro r10 hfe hcarrier
      cases r10 with
      | Err x =>
        simp only [Std.bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok]
        refine okPost_ok ?_
        exact Or.inr ⟨hpass, phases, hph.1, Or.inr ⟨required1, e, hroutes, hreq3, hreq2,
          Or.inr ⟨s5, s6, live1, hspinOk, hz5, hz6, hlive1, hsub, Or.inl ⟨x, hfe, rfl⟩⟩⟩⟩
      | Ok carrier =>
        simp only [Std.bind_ok]
        simp only at hcarrier
        refine okPost_bind_eq (okPost_of_spec (constructor_workspace_new_spec
          (alloc.vec.Vec.len layout.cells)
          (Slice.len (alloc.vec.Vec.deref layout.carrier.edges)))) ?_
        intro r11 hws hworkspace
        cases r11 with
        | Err x =>
          simp only [Std.bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok]
          refine okPost_ok ?_
          exact Or.inr ⟨hpass, phases, hph.1, Or.inr ⟨required1, e, hroutes, hreq3, hreq2,
            Or.inr ⟨s5, s6, live1, hspinOk, hz5, hz6, hlive1, hsub,
              Or.inr ⟨carrier, hfe, hcarrier, Or.inl ⟨x, hws, rfl⟩⟩⟩⟩⟩
        | Ok work =>
          simp only [Std.bind_ok]
          simp only at hworkspace
          have hpath : ∀ q, SceneDfsStage treeRngInst layout routes occupants epoch rng required1
              s5 s6 carrier work q →
              SceneNewOutcome treeRngInst layout routes occupants patch_capacity epoch rng q := by
            intro q hq
            exact Or.inr ⟨hpass, phases, hph.1, Or.inr ⟨required1, e, hroutes, hreq3, hreq2,
              Or.inr ⟨s5, s6, live1, hspinOk, hz5, hz6, hlive1, hsub,
                Or.inr ⟨carrier, hfe, hcarrier, Or.inr ⟨work, hws, hworkspace.1, hq⟩⟩⟩⟩⟩
          refine okPost_bind_eq (okPost_of_spec (constructor_scene_dfs_spec treeRngInst hrng
            carrier (alloc.vec.Vec.deref required1) 0#usize rng work hcarrier hworkspace.1)) ?_
          rintro ⟨r12, rng1, val4⟩ hdfs hd
          simp only at hd
          cases r12 with
          | Err x =>
            simp only [Std.bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from, bind_tc_ok]
            refine okPost_ok (hpath _ (Or.inl ⟨x, rng1, val4, hdfs, rfl, ?_⟩))
            rcases hd with ⟨pub, hpub, _⟩ | ⟨hout, hbad⟩ | ⟨hout, _⟩ | ⟨hout, _⟩ | ⟨hov, _⟩
            · exact absurd hpub (by simp)
            · exfalso
              have := hcarrier.1
              simp at hbad
              omega
            · simp only [Prod.mk.injEq, core.result.Result.Err.injEq] at hout
              obtain ⟨hx, hr, -⟩ := hout
              exact Or.inr ⟨Or.inl hx, hr⟩
            · simp only [Prod.mk.injEq, core.result.Result.Err.injEq] at hout
              obtain ⟨hx, hr, -⟩ := hout
              exact Or.inr ⟨Or.inr hx, hr⟩
            · rcases hov with hout | ⟨hx, -⟩
              · simp only [Prod.mk.injEq, core.result.Result.Err.injEq] at hout
                exact Or.inl hout.1
              · simp only [core.result.Result.Err.injEq] at hx
                exact Or.inl hx
          | Ok tree =>
            simp only [Std.bind_ok]
            obtain ⟨pub, hpub, hroot, htv, hwv, hslots⟩ :
                ∃ pub : spanning_tree.Tree, core.result.Result.Ok tree =
                    core.result.Result.Ok pub ∧ pub.root = 0#usize ∧ TreeValid carrier pub ∧
                  WorkspaceValid val4 ∧
                  (∀ slot, slot < (alloc.vec.Vec.deref required1).val.length → ∀ edge,
                    (alloc.vec.Vec.deref required1).val[slot]? = some edge →
                    parentEdge (parents pub) edge.u.val edge.v.val) := by
              rcases hd with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
              · exact h
              · simp at h
              · simp at h
              · simp at h
              · rcases h with h | ⟨h, _⟩ <;> simp at h
            simp only [core.result.Result.Ok.injEq] at hpub
            subst hpub
            have hroot' : tree.root.val = 0 := by rw [hroot]; rfl
            have hall : ∀ x ∈ allEdges routes.val,
                parentEdge (parents tree) x.u.val x.v.val := by
              intro x hx
              have hxr : x ∈ required1.val := by
                rw [hreq3, foldEdges_mem]; exact Or.inr hx
              obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hxr
              exact hslots j (by simpa [alloc.vec.Vec.deref] using hj) x (by
                simpa [alloc.vec.Vec.deref, List.getElem?_eq_getElem hj] using hjx)
            refine okPost_bind (okPost_trivial _) ?_
            intro saved _
            refine okPost_bind_eq (scene_new_occupant_loop layout occupants
              (alloc.vec.Vec.len layout.cells) _) ?_
            intro pr6 hl2 hvalid
            by_cases hv : pr6.2 = true
            · simp only [hv, ↓reduceIte]
              refine okPost_bind (okPost_trivial _) ?_
              intro patches _
              refine okPost_bind (okPost_trivial _) ?_
              intro v _
              refine okPost_ok (hpath _ (Or.inr ⟨tree, rng1, val4, hdfs, htv, hroot', hall, ?_⟩))
              unfold SceneOccupantStage
              exact Or.inr ⟨hvalid.mp hv, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                rfl, rfl, rfl, rfl, rfl, rfl⟩
            · simp only [hv, Bool.false_eq_true, ↓reduceIte]
              refine okPost_ok (hpath _ (Or.inr ⟨tree, rng1, val4, hdfs, htv, hroot', hall, ?_⟩))
              unfold SceneOccupantStage
              exact Or.inl ⟨fun h => hv (hvalid.mpr h), rfl⟩

end Labyrinth
