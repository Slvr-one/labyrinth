module
public import LabyrinthCore.ConstructorSceneAcceptance
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

def constructorScenePrepareProgram (carrier : topology.Carrier) (n : Usize)
    (required : Slice topology.Edge) := do
  let links ← alloc.vec.from_elem core.clone.CloneUsize 0#usize n
  let sizes ← alloc.vec.from_elem core.clone.CloneUsize 1#usize n
  let links1 ← spanning_tree.Tree.scene_dfs_loop0 n links 0#usize
  let (links2, status) ←
    spanning_tree.Tree.scene_dfs_loop1 carrier required links1 sizes 0#usize (.Ok ())
  let cf ← core.result.Result.Insts.CoreOpsTry.branch status
  match cf with
  | .Continue _ =>
    let components ← alloc.vec.from_elem core.clone.CloneUsize 0#usize n
    let labels ← alloc.vec.from_elem core.clone.CloneUsize n n
    let (components1, componentCount) ←
      spanning_tree.Tree.scene_dfs_loop2 n links2 0#usize components labels 0#usize
    ok (core.result.Result.Ok (links2, components1, componentCount))
  | .Break residual => ok (core.result.Result.Err residual)

def constructorSceneQuotientPrefixProgram (carrier : topology.Carrier)
    (components : alloc.vec.Vec Usize) (componentCount : Usize) :
    Result (core.result.Result (alloc.vec.Vec Usize × Usize) topology.Error) := do
  let optionCount ← lift (Usize.checked_add componentCount 1#usize)
  let countResult ← core.option.Option.ok_or optionCount topology.Error.Overflow
  let countFlow ← core.result.Result.Insts.CoreOpsTry.branch countResult
  match countFlow with
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
  | .Continue count =>
    let storageResult ← topology.check_storage count 8#usize
    let storageFlow ← core.result.Result.Insts.CoreOpsTry.branch storageResult
    match storageFlow with
    | .Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
    | .Continue _ =>
      let offsets ← alloc.vec.from_elem core.clone.CloneUsize 0#usize count
      let edges ← topology.Carrier.impl.edges carrier
      let (degreeStatus, counts) ← spanning_tree.Tree.scene_dfs_loop3 0#usize (.Ok ())
        components componentCount offsets edges
      let degreeFlow ← core.result.Result.Insts.CoreOpsTry.branch degreeStatus
      match degreeFlow with
      | .Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
      | .Continue _ =>
        let (countSlice, countBack) ← lift (alloc.vec.Vec.deref_mut counts)
        let (prefixStatus, prefixed) ← topology.prefix_offsets countSlice
        let prefixFlow ← core.result.Result.Insts.CoreOpsTry.branch prefixStatus
        match prefixFlow with
        | .Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
        | .Continue _ =>
          let prefixedCounts := countBack prefixed
          let adjacencyCount ← alloc.vec.Vec.index
            (core.slice.index.SliceIndexUsizeSlice Usize) prefixedCounts componentCount
          let adjacencyStorage8 ← topology.check_storage adjacencyCount 8#usize
          let adjacencyFlow8 ← core.result.Result.Insts.CoreOpsTry.branch adjacencyStorage8
          match adjacencyFlow8 with
          | .Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
          | .Continue _ =>
            let adjacencyStorage16 ← topology.check_storage adjacencyCount 16#usize
            let adjacencyFlow16 ← core.result.Result.Insts.CoreOpsTry.branch adjacencyStorage16
            match adjacencyFlow16 with
            | .Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
            | .Continue _ => ok (.Ok (prefixedCounts, adjacencyCount))

def constructorSceneQuotientDFSProgram {R : Type*} (adapter : tree.Rng R)
    (carrier : topology.Carrier) (components : alloc.vec.Vec Usize)
    (componentCount root : Usize) (offsets : alloc.vec.Vec Usize)
    (adjacencyCount : Usize) (rng : R) (work : spanning_tree.Workspace) :
    Result (core.result.Result Unit topology.Error × R × spanning_tree.Workspace) := do
  let neighbors ← alloc.vec.from_elem core.clone.CloneUsize 0#usize adjacencyCount
  let e ← topology.Edge.new 0#usize 0#usize
  let witnesses ← alloc.vec.from_elem topology.Edge.Insts.CoreCloneClone e adjacencyCount
  let next ← alloc.vec.from_elem core.clone.CloneUsize 0#usize componentCount
  let next1 ← spanning_tree.Tree.scene_dfs_loop4 0#usize componentCount offsets next
  let (neighbors1, _) ← spanning_tree.Tree.scene_dfs_loop5 0#usize components
    (alloc.vec.Vec.deref carrier.edges) neighbors witnesses next1
  let quotientRoot ← alloc.vec.Vec.index
    (core.slice.index.SliceIndexUsizeSlice Usize) components root
  spanning_tree.depth_first adapter (alloc.vec.Vec.deref offsets)
    (alloc.vec.Vec.deref neighbors1) quotientRoot rng work

/-- Exact evaluation of the literal preparation, quotient prefix and quotient DFS calls.
The final pair is the DFS return frame, before selection or publication. -/
def ConstructorScenePostDFSFrame {R : Type*} (adapter : tree.Rng R)
    (carrier : topology.Carrier) (required : Slice topology.Edge) (root : Usize)
    (rng : R) (work : spanning_tree.Workspace) (afterRng : R)
    (afterWork : spanning_tree.Workspace) : Prop :=
  ∃ (n : Usize) (links components : alloc.vec.Vec Usize) (componentCount : Usize)
      (offsets : alloc.vec.Vec Usize) (adjacencyCount : Usize),
    n.val = cellCount carrier ∧
    constructorScenePrepareProgram carrier n required = ok (.Ok (links, components, componentCount)) ∧
    constructorSceneQuotientPrefixProgram carrier components componentCount =
      ok (.Ok (offsets, adjacencyCount)) ∧
    constructorSceneQuotientDFSProgram adapter carrier components componentCount root offsets
      adjacencyCount rng work = ok (.Ok (), afterRng, afterWork)

theorem constructor_scene_capture {A : Type*} {program : Result A} {post : A → Prop}
    (h : WP.spec program post) :
    WP.spec program (fun value => post value ∧ program = ok value) := by
  cases program with
  | ret value => exact (WP.spec_ok _).mpr ⟨(WP.spec_ok _).mp h, rfl⟩
  | vis effect continuation => exact False.elim ((WP.spec_vis effect continuation).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

end Labyrinth
