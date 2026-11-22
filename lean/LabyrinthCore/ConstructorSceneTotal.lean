module
public import LabyrinthCore.ConstructorSceneAcceptance
public import LabyrinthCore.ConstructorSceneRejection
public import LabyrinthCore.ConstructorSceneQuotientPrefix
public import LabyrinthCore.ConstructorSceneSelectedConnectivity
public import LabyrinthCore.ConstructorSceneFrame
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

private theorem constructor_scene_residual_continuation {R : Type*} {A : Type} (rng : R)
    (work : spanning_tree.Workspace) (residual : core.result.Result Never topology.Error)
    (success : A → Result (core.result.Result spanning_tree.Tree topology.Error × R ×
      spanning_tree.Workspace)) :
    ((do
      let prefixResult ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          A (core.convert.FromSame topology.Error) residual
      match prefixResult with
      | .Err error => ok (.Err error, rng, work)
      | .Ok value => success value) :
        Result (core.result.Result spanning_tree.Tree topology.Error × R ×
          spanning_tree.Workspace)) =
    ((do
      let result ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          spanning_tree.Tree (core.convert.FromSame topology.Error) residual
      ok (result, rng, work)) :
        Result (core.result.Result spanning_tree.Tree topology.Error × R ×
          spanning_tree.Workspace)) := by
  cases residual with
  | Ok impossible => exact nomatch impossible
  | Err error =>
      unfold core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      simp only [bind_tc_eq, bind_ok]

private theorem constructor_scene_publish_attach_rng_eq {R : Type*}
    (n root : Usize) (selected : alloc.vec.Vec topology.Edge)
    (work : spanning_tree.Workspace) (rng : R) :
    Std.bind (do
      let result ← topology.Carrier.from_edges n selected.slice
      let flow ← core.result.Result.Insts.CoreOpsTry.branch result
      match flow with
      | .Continue expanded =>
        let parents ← alloc.vec.from_elem core.clone.CloneUsize root n
        let (work1, index) ← spanning_tree.Tree.scene_dfs_loop8 work n 0#usize
        let (_, seenBack) ← alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice Bool) work1.seen root
        let (_, pathBack) ← alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice Usize) work1.path 0#usize
        let (finalSeen, finalPath, finalParents) ←
          spanning_tree.Tree.scene_dfs_loop9 (seenBack true) (pathBack root)
            index expanded parents 1#usize
        ok (core.result.Result.Ok ({ parents := finalParents, root } : spanning_tree.Tree),
          { work1 with seen := finalSeen, path := finalPath })
      | .Break residual =>
        let result ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          spanning_tree.Tree (core.convert.FromSame topology.Error) residual
        ok (result, work))
      (fun output => ok (output.1, rng, output.2)) =
    (do
      let result ← topology.Carrier.from_edges n selected.slice
      let flow ← core.result.Result.Insts.CoreOpsTry.branch result
      match flow with
      | .Continue expanded =>
        let parents ← alloc.vec.from_elem core.clone.CloneUsize root n
        let (work1, index) ← spanning_tree.Tree.scene_dfs_loop8 work n 0#usize
        let (_, seenBack) ← alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice Bool) work1.seen root
        let (_, pathBack) ← alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice Usize) work1.path 0#usize
        let (finalSeen, finalPath, finalParents) ←
          spanning_tree.Tree.scene_dfs_loop9 (seenBack true) (pathBack root)
            index expanded parents 1#usize
        ok (core.result.Result.Ok ({ parents := finalParents, root } : spanning_tree.Tree),
          rng, { work1 with seen := finalSeen, path := finalPath })
      | .Break residual =>
        let result ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          spanning_tree.Tree (core.convert.FromSame topology.Error) residual
        ok (result, rng, work)) := by
  conv_lhs => rw [Std.bind_assoc]
  apply congrArg (Std.bind (topology.Carrier.from_edges n selected.slice))
  funext result
  conv_lhs => rw [Std.bind_assoc]
  apply congrArg (Std.bind (core.result.Result.Insts.CoreOpsTry.branch result))
  funext flow
  cases flow with
  | Break residual => simp only [Std.bind_assoc, bind_ok]
  | Continue expanded =>
      conv_lhs => simp only [Std.bind_assoc]
      apply congrArg (Std.bind (alloc.vec.from_elem core.clone.CloneUsize root n))
      funext parents
      apply congrArg (Std.bind (spanning_tree.Tree.scene_dfs_loop8 work n 0#usize))
      funext value
      rcases value with ⟨work1, index⟩
      dsimp only [uncurry]
      try (conv_lhs => rw [Std.bind_assoc])
      apply congrArg (Std.bind (alloc.vec.Vec.index_mut
        (core.slice.index.SliceIndexUsizeSlice Bool) work1.seen root))
      funext value
      rcases value with ⟨_, seenBack⟩
      dsimp only [uncurry]
      try (conv_lhs => rw [Std.bind_assoc])
      apply congrArg (Std.bind (alloc.vec.Vec.index_mut
        (core.slice.index.SliceIndexUsizeSlice Usize) work1.path 0#usize))
      funext value
      rcases value with ⟨_, pathBack⟩
      dsimp only [uncurry]
      try (conv_lhs => rw [Std.bind_assoc])
      apply congrArg (Std.bind (spanning_tree.Tree.scene_dfs_loop9
        (seenBack true) (pathBack root) index expanded parents 1#usize))
      funext value
      rcases value with ⟨finalSeen, finalPath, finalParents⟩
      dsimp only [uncurry]
      exact bind_ok _ _

private theorem constructor_scene_deref_eq_slice {A : Type*} (vector : alloc.vec.Vec A) :
    vector.deref = vector.slice := by
  rw [Slice.eq_iff]
  simp only [alloc.vec.Vec.deref, Slice.from_val, alloc.vec.Vec.val]

def constructor_scene_after_prefix_program {R : Type*} (adapter : tree.Rng R)
    (carrier : topology.Carrier) (required : Slice topology.Edge) (n root : Usize)
    (rng : R) (work : spanning_tree.Workspace) (components : alloc.vec.Vec Usize)
    (componentCount : Usize) (offsets : alloc.vec.Vec Usize) (adjacencyCount : Usize) :
    Result (core.result.Result spanning_tree.Tree topology.Error × R ×
      spanning_tree.Workspace) := do
  let neighbors ← alloc.vec.from_elem core.clone.CloneUsize 0#usize adjacencyCount
  let e ← topology.Edge.new 0#usize 0#usize
  let witnesses ← alloc.vec.from_elem topology.Edge.Insts.CoreCloneClone e adjacencyCount
  let next ← alloc.vec.from_elem core.clone.CloneUsize 0#usize componentCount
  let next1 ← spanning_tree.Tree.scene_dfs_loop4 0#usize componentCount offsets next
  let (neighbors1, witnesses1) ←
    spanning_tree.Tree.scene_dfs_loop5 0#usize components
      (alloc.vec.Vec.deref carrier.edges) neighbors witnesses next1
  let quotientRoot ← alloc.vec.Vec.index
    (core.slice.index.SliceIndexUsizeSlice Usize) components root
  let (dfsResult, rng1, work1) ← spanning_tree.depth_first adapter
    (alloc.vec.Vec.deref offsets) (alloc.vec.Vec.deref neighbors1)
    quotientRoot rng work
  let dfsFlow ← core.result.Result.Insts.CoreOpsTry.branch dfsResult
  match dfsFlow with
  | .Break residual =>
    let result ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      spanning_tree.Tree (core.convert.FromSame topology.Error) residual
    ok (result, rng1, work1)
  | .Continue _ =>
    let selectedCount ← n - 1#usize
    let selectedStorage ← topology.check_storage selectedCount 16#usize
    let selectedFlow ← core.result.Result.Insts.CoreOpsTry.branch selectedStorage
    match selectedFlow with
    | .Break residual =>
      let result ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        spanning_tree.Tree (core.convert.FromSame topology.Error) residual
      ok (result, rng1, work1)
    | .Continue _ =>
      let selected ← alloc.vec.from_elem
        topology.Edge.Insts.CoreCloneClone e selectedCount
      let selected1 ← spanning_tree.Tree.scene_dfs_loop6 required 0#usize selected
      let (work2, selected2) ← spanning_tree.Tree.scene_dfs_loop7 work1 0#usize
        componentCount witnesses1 quotientRoot selected1 (Slice.len required)
      let selectedSlice := alloc.vec.Vec.deref selected2
      let expandedResult ← topology.Carrier.from_edges n selectedSlice
      let expandedFlow ← core.result.Result.Insts.CoreOpsTry.branch expandedResult
      match expandedFlow with
      | .Break residual =>
        let result ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          spanning_tree.Tree (core.convert.FromSame topology.Error) residual
        ok (result, rng1, work2)
      | .Continue expanded =>
        let parents ← alloc.vec.from_elem core.clone.CloneUsize root n
        let (work3, index) ← spanning_tree.Tree.scene_dfs_loop8 work2 n 0#usize
        let (_, seenBack) ← alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice Bool) work3.seen root
        let (_, pathBack) ← alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice Usize) work3.path 0#usize
        let path := pathBack root
        let seen := seenBack true
        let (finalSeen, finalPath, finalParents) ←
          spanning_tree.Tree.scene_dfs_loop9 seen path index expanded parents 1#usize
        ok (core.result.Result.Ok ({ parents := finalParents, root } :
          spanning_tree.Tree), rng1, { work3 with seen := finalSeen, path := finalPath })

private def constructor_scene_after_prepare_program {R : Type*} (adapter : tree.Rng R)
    (carrier : topology.Carrier) (required : Slice topology.Edge) (n root : Usize)
    (rng : R) (work : spanning_tree.Workspace) (components : alloc.vec.Vec Usize)
    (componentCount : Usize) :
    Result (core.result.Result spanning_tree.Tree topology.Error × R ×
      spanning_tree.Workspace) := do
  let prefixResult ← (do
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
              let adjacencyFlow16 ←
                core.result.Result.Insts.CoreOpsTry.branch adjacencyStorage16
              match adjacencyFlow16 with
              | .Break residual =>
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
              | .Continue _ => ok (.Ok (prefixedCounts, adjacencyCount)))
  match prefixResult with
  | .Err error => ok (.Err error, rng, work)
  | .Ok (offsets, adjacencyCount) =>
    constructor_scene_after_prefix_program adapter carrier required n root rng work
      components componentCount offsets adjacencyCount

private def constructor_scene_program {R : Type*} (adapter : tree.Rng R)
    (carrier : topology.Carrier) (required : Slice topology.Edge) (root : Usize)
    (rng : R) (work : spanning_tree.Workspace) :
    Result (core.result.Result spanning_tree.Tree topology.Error × R ×
      spanning_tree.Workspace) := do
  let n ← topology.Carrier.len carrier
  if root >= n then ok (.Err .InvalidIndex, rng, work)
  else
    let edges ← topology.Carrier.impl.edges carrier
    let ensured ← spanning_tree.Workspace.ensure work n (Slice.len edges)
    let flow ← core.result.Result.Insts.CoreOpsTry.branch ensured
    match flow with
    | .Break residual =>
      let result ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        spanning_tree.Tree (core.convert.FromSame topology.Error) residual
      ok (result, rng, work)
    | .Continue _ =>
      if Slice.len required >= n then ok (.Err .InvalidForest, rng, work)
      else
        let prepared ← constructorScenePrepareProgram carrier n required
        match prepared with
        | .Ok (_, components, componentCount) =>
          constructor_scene_after_prepare_program adapter carrier required n root rng work
            components componentCount
        | .Err residual =>
          let result ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            spanning_tree.Tree (core.convert.FromSame topology.Error) residual
          ok (result, rng, work)


set_option maxHeartbeats 1000000 in
private theorem constructor_scene_program_eq {R : Type*} (adapter : tree.Rng R)
    (carrier : topology.Carrier) (required : Slice topology.Edge) (root : Usize)
    (rng : R) (work : spanning_tree.Workspace) :
    constructor_scene_program adapter carrier required root rng work =
      spanning_tree.Tree.scene_dfs adapter carrier required root rng work := by
  unfold constructor_scene_program spanning_tree.Tree.scene_dfs
  apply congrArg (Std.bind (topology.Carrier.len carrier))
  funext n
  by_cases hroot : root >= n
  · simp only [hroot, ite_true]
  · simp only [hroot, ite_false, topology.Carrier.impl.edges, bind_ok]
    apply congrArg (Std.bind
      (spanning_tree.Workspace.ensure work n (Slice.len (alloc.vec.Vec.deref carrier.edges))))
    funext ensured
    cases ensured with
    | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    | Ok ready =>
        cases ready
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        by_cases hrequired : Slice.len required >= n
        · simp only [hrequired, ite_true]
        · simp only [hrequired, ite_false]
          conv_lhs => erw [Std.bind_assoc]
          apply congrArg (Std.bind (alloc.vec.from_elem core.clone.CloneUsize 0#usize n))
          funext links
          conv_lhs => erw [Std.bind_assoc]
          apply congrArg (Std.bind (alloc.vec.from_elem core.clone.CloneUsize 1#usize n))
          funext sizes
          conv_lhs => erw [Std.bind_assoc]
          apply congrArg (Std.bind (spanning_tree.Tree.scene_dfs_loop0 n links 0#usize))
          funext links1
          conv_lhs => erw [Std.bind_assoc]
          apply congrArg (Std.bind
            (spanning_tree.Tree.scene_dfs_loop1 carrier required links1 sizes 0#usize (.Ok ())))
          funext value
          cases value with
          | mk links2' status' =>
            cases status' with
            | Err error =>
                simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
            | Ok ready =>
              cases ready
              conv_lhs => dsimp
              simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_eq, bind_ok]
              conv_lhs => erw [Std.bind_assoc]
              apply congrArg (Std.bind
                (alloc.vec.from_elem core.clone.CloneUsize 0#usize n))
              funext components
              conv_lhs => erw [Std.bind_assoc]
              apply congrArg (Std.bind (alloc.vec.from_elem core.clone.CloneUsize n n))
              funext labels
              conv_lhs => erw [Std.bind_assoc]
              apply congrArg (Std.bind (spanning_tree.Tree.scene_dfs_loop2 n links2'
                0#usize components labels 0#usize))
              funext value
              rcases value with ⟨components1, componentCount⟩
              simp only [bind_ok]
              unfold constructor_scene_after_prepare_program
              conv_lhs => erw [Std.bind_assoc]
              apply congrArg (Std.bind (lift (Usize.checked_add componentCount 1#usize)))
              funext optionCount
              conv_lhs => erw [Std.bind_assoc]
              apply congrArg (Std.bind
                (core.option.Option.ok_or optionCount topology.Error.Overflow))
              funext countResult
              conv_lhs => erw [Std.bind_assoc]
              apply congrArg (Std.bind (core.result.Result.Insts.CoreOpsTry.branch countResult))
              funext countFlow
              cases countFlow with
              | Break residual =>
                  dsimp
                  cases residual with
                  | Ok impossible => exact nomatch impossible
                  | Err error =>
                      unfold core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      simp only [bind_tc_eq, bind_ok]
              | Continue count =>
                  conv_lhs => erw [Std.bind_assoc]
                  apply congrArg (Std.bind (topology.check_storage count 8#usize))
                  funext storageResult
                  conv_lhs => erw [Std.bind_assoc]
                  apply congrArg (Std.bind
                    (core.result.Result.Insts.CoreOpsTry.branch storageResult))
                  funext storageFlow
                  cases storageFlow with
                  | Break residual =>
                      dsimp
                      cases residual with
                      | Ok impossible => exact nomatch impossible
                      | Err error =>
                          unfold core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          simp only [bind_tc_eq, bind_ok]
                  | Continue _ =>
                      conv_lhs => erw [Std.bind_assoc]
                      apply congrArg (Std.bind
                        (alloc.vec.from_elem core.clone.CloneUsize 0#usize count))
                      funext offsets
                      simp only [topology.Carrier.impl.edges, bind_ok]
                      conv_lhs => erw [Std.bind_assoc]
                      apply congrArg (Std.bind (spanning_tree.Tree.scene_dfs_loop3
                        0#usize (.Ok ()) components1 componentCount offsets
                        (alloc.vec.Vec.deref carrier.edges)))
                      funext value
                      rcases value with ⟨degreeStatus, counts⟩
                      conv_lhs => erw [Std.bind_assoc]
                      apply congrArg (Std.bind
                        (core.result.Result.Insts.CoreOpsTry.branch degreeStatus))
                      funext degreeFlow
                      cases degreeFlow with
                      | Break residual =>
                          dsimp
                          cases residual with
                          | Ok impossible => exact nomatch impossible
                          | Err error =>
                              unfold core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                              simp only [bind_tc_eq, bind_ok]
                      | Continue _ =>
                          conv_lhs => erw [Std.bind_assoc]
                          apply congrArg (Std.bind (lift (alloc.vec.Vec.deref_mut counts)))
                          funext value
                          rcases value with ⟨countSlice, countBack⟩
                          conv_lhs => erw [Std.bind_assoc]
                          apply congrArg (Std.bind (topology.prefix_offsets countSlice))
                          funext value
                          rcases value with ⟨prefixStatus, prefixed⟩
                          conv_lhs => erw [Std.bind_assoc]
                          apply congrArg (Std.bind
                            (core.result.Result.Insts.CoreOpsTry.branch prefixStatus))
                          funext prefixFlow
                          cases prefixFlow with
                          | Break residual =>
                              dsimp
                              cases residual with
                              | Ok impossible => exact nomatch impossible
                              | Err error =>
                                  unfold core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                  simp only [bind_tc_eq, bind_ok]
                          | Continue _ =>
                              conv_lhs => erw [Std.bind_assoc]
                              apply congrArg (Std.bind (alloc.vec.Vec.index
                                (core.slice.index.SliceIndexUsizeSlice Usize)
                                (countBack prefixed) componentCount))
                              funext adjacencyCount
                              conv_lhs => erw [Std.bind_assoc]
                              apply congrArg (Std.bind
                                (topology.check_storage adjacencyCount 8#usize))
                              funext adjacencyStorage8
                              conv_lhs => erw [Std.bind_assoc]
                              apply congrArg (Std.bind
                                (core.result.Result.Insts.CoreOpsTry.branch adjacencyStorage8))
                              funext adjacencyFlow8
                              cases adjacencyFlow8 with
                              | Break residual =>
                                  dsimp
                                  cases residual with
                                  | Ok impossible => exact nomatch impossible
                                  | Err error =>
                                      unfold core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                      simp only [bind_tc_eq, bind_ok]
                              | Continue _ =>
                                  conv_lhs => erw [Std.bind_assoc]
                                  apply congrArg (Std.bind
                                    (topology.check_storage adjacencyCount 16#usize))
                                  funext adjacencyStorage16
                                  conv_lhs => erw [Std.bind_assoc]
                                  apply congrArg (Std.bind
                                    (core.result.Result.Insts.CoreOpsTry.branch adjacencyStorage16))
                                  funext adjacencyFlow16
                                  cases adjacencyFlow16 with
                                  | Break residual =>
                                      dsimp
                                      cases residual with
                                      | Ok impossible => exact nomatch impossible
                                      | Err error =>
                                          unfold core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                          simp only [bind_tc_eq, bind_ok]
                                  | Continue _ =>
                                      dsimp
                                      simp only [bind_ok]
                                      unfold constructor_scene_after_prefix_program
                                      conv_lhs => erw [Std.bind_assoc]
                                      conv_rhs => erw [Std.bind_assoc]
                                      apply congrArg (Std.bind
                                        (List.clone core.clone.CloneUsize.clone
                                          (List.replicate (↑adjacencyCount) 0#usize)))
                                      funext neighbors
                                      simp only [bind_ok]
                                      apply congrArg (Std.bind (topology.Edge.new 0#usize 0#usize))
                                      funext e
                                      apply congrArg (Std.bind
                                        (alloc.vec.from_elem topology.Edge.Insts.CoreCloneClone e adjacencyCount))
                                      funext witnesses
                                      apply congrArg (Std.bind
                                        (alloc.vec.from_elem core.clone.CloneUsize 0#usize componentCount))
                                      funext next
                                      apply congrArg (Std.bind
                                        (spanning_tree.Tree.scene_dfs_loop4 0#usize componentCount
                                          (countBack prefixed) next))
                                      funext next1
                                      congr
                                      funext neighbors1 witnesses1
                                      apply congrArg (Std.bind
                                        (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Usize)
                                          components1 root))
                                      funext quotientRoot
                                      apply congrArg (Std.bind
                                        (spanning_tree.depth_first adapter (alloc.vec.Vec.deref (countBack prefixed))
                                          (alloc.vec.Vec.deref neighbors1) quotientRoot rng work))
                                      congr
                                      funext dfsResult
                                      funext pair
                                      cases pair with
                                      | mk rng1 work1 =>
                                        apply congrArg (Std.bind
                                          (core.result.Result.Insts.CoreOpsTry.branch dfsResult))
                                        funext dfsFlow
                                        cases dfsFlow with
                                        | Break residual =>
                                            dsimp
                                        | Continue _ =>
                                            apply congrArg (Std.bind (n - 1#usize))
                                            funext selectedCount
                                            apply congrArg (Std.bind
                                              (topology.check_storage selectedCount 16#usize))
                                            funext selectedStorage
                                            apply congrArg (Std.bind
                                              (core.result.Result.Insts.CoreOpsTry.branch selectedStorage))
                                            funext selectedFlow
                                            cases selectedFlow with
                                            | Break residual =>
                                                dsimp
                                            | Continue _ =>
                                                apply congrArg (Std.bind
                                                  (alloc.vec.from_elem topology.Edge.Insts.CoreCloneClone e
                                                    selectedCount))
                                                funext selected
                                                apply congrArg (Std.bind
                                                  (spanning_tree.Tree.scene_dfs_loop6 required 0#usize selected))
                                                funext selected1
                                                congr
                                                funext work2 selected2
                                                apply congrArg (Std.bind
                                                  (topology.Carrier.from_edges n (alloc.vec.Vec.deref selected2)))
                                                funext expandedResult
                                                apply congrArg (Std.bind
                                                  (core.result.Result.Insts.CoreOpsTry.branch expandedResult))
                                                funext expandedFlow
                                                cases expandedFlow with
                                                | Break residual =>
                                                    dsimp
                                                | Continue expanded =>
                                                    apply congrArg (Std.bind
                                                      (alloc.vec.from_elem core.clone.CloneUsize root n))
                                                    funext parents
                                                    congr



/-- The literal quotient suffix either publishes the required tree or returns `Overflow`
with exactly the RNG and workspace returned by its quotient DFS call. -/
theorem constructor_scene_after_prefix_total {R : Type*} (adapter : tree.Rng R)
    (hrng : constructorLegalRng adapter) (carrier : topology.Carrier)
    (required : Slice topology.Edge) (n root : Usize) (rng : R)
    (work : spanning_tree.Workspace) (links components : alloc.vec.Vec Usize)
    (componentCount : Usize)
    (hc : CarrierValid carrier) (hn : n.val = cellCount carrier)
    (hroot : root.val < cellCount carrier)
    (hw : WorkspaceValid work) (hcapacity : cellCount carrier ≤ work.path.val.length)
    (hforest : ConstructorRequiredForest carrier required)
    (hlinks : links.val.length = n.val)
    (hcomponents : components.val.length = n.val)
    (hforestCount : required.val.length + constructorSceneRootCount links = n.val)
    (hpositive : 0 < componentCount.val)
    (hcountBound : componentCount.val ≤ n.val)
    (hbounded : ∀ node : Usize, node.val < n.val →
      (constructorSceneComponentAt components node).val < componentCount.val)
    (hdense : ∀ id : Usize, id.val < componentCount.val → ∃ node : Usize,
      node.val < n.val ∧ constructorSceneComponentAt components node = id)
    (hclasses : ∀ u v : Usize, u.val < n.val → v.val < n.val →
      (constructorSceneComponentAt components u = constructorSceneComponentAt components v ↔
        Relation.ReflTransGen
          (constructorRequiredPrefixArc required required.val.length) u v))
    (hcomponentCount : componentCount.val = constructorSceneRootCount links)
    (offsets : alloc.vec.Vec Usize) (adjacencyCount : Usize)
    (hprefix : ConstructorScenePrefixSuccess carrier componentCount
      (constructorSceneComponentAt components) offsets adjacencyCount)
    (hprepareRun : constructorScenePrepareProgram carrier n required =
      ok (.Ok (links, components, componentCount)))
    (hprefixRun : constructorSceneQuotientPrefixProgram carrier components componentCount =
      ok (.Ok (offsets, adjacencyCount))) :
    WP.spec (constructor_scene_after_prefix_program adapter carrier required n root rng work
      components componentCount offsets adjacencyCount)
      (fun output =>
        (∃ published, output.1 = .Ok published ∧ published.root = root ∧
          TreeValid carrier published ∧ WorkspaceValid output.2.2 ∧
          ∀ slot, slot < required.val.length → ∀ edge,
            required.val[slot]? = some edge →
            parentEdge (parents published) edge.u.val edge.v.val) ∨
        (output.1 = .Err topology.Error.Overflow ∧ WorkspaceValid output.2.2 ∧
          ¬ ConstructorSceneAllocationFits carrier ∧
          ConstructorScenePostDFSFrame adapter carrier required root rng work
            output.2.1 output.2.2)) := by
  unfold constructor_scene_after_prefix_program
  obtain ⟨countWidth, counts, hcountWidth, hcountsLength, hcounts, hoffsetsLength,
    hoffsets, hadjacency, _hcountStorage, _hadjacency8, _hadjacency16⟩ := hprefix
  have hcomponentLookup : ∀ node : Usize, node.val < components.val.length →
      components.val[node.val]? = some (constructorSceneComponentAt components node) := by
    intro node hnode
    unfold constructorSceneComponentAt
    rw [List.getElem?_eq_getElem hnode]
    rfl
  have hedges : ∀ edge ∈ carrier.edges.val,
      edge.u.val < components.val.length ∧ edge.v.val < components.val.length ∧
      (constructorSceneComponentAt components edge.u).val < componentCount.val ∧
      (constructorSceneComponentAt components edge.v).val < componentCount.val ∧
      carrierEdge carrier edge.u.val edge.v.val := by
    intro edge hedge
    have hpairs : (edge.u.val, edge.v.val) ∈ edgePairs carrier := by
      exact List.mem_map.mpr ⟨edge, hedge, rfl⟩
    have hcarrier := (hc.2.2.2.2.2.2.2 edge.u.val edge.v.val).mp hpairs
    have hv := ((hc.2.2.2.2.1 edge.u.val hcarrier.2.1).2.2 edge.v.val hcarrier.2.2).1
    have huComponents : edge.u.val < components.val.length := by omega
    have hvComponents : edge.v.val < components.val.length := by omega
    exact ⟨huComponents, hvComponents, hbounded edge.u (by omega),
      hbounded edge.v (by omega), ⟨hcarrier.2.1, hcarrier.2.2⟩⟩
  have hvertexCount : constructorDFSVertexCount offsets.slice = componentCount.val := by
    change offsets.val.length - 1 = componentCount.val
    omega
  have hfirst : constructorDFSOffset offsets.slice 0 = 0 := by
    obtain ⟨zero, hzero, hzeroValue⟩ := hcounts 0 (by omega)
    have hzeroValue' : zero.val = 0 := by
      rw [hzeroValue, constructor_quotient_degree_zero]
    obtain ⟨first, hfirstLookup, hfirstValue⟩ := hoffsets 0 (by omega)
    change (offsets.val[0]?.map UScalar.val).getD 0 = 0
    simp only [hfirstLookup, Option.map_some, Option.getD_some, hfirstValue,
      constructorPrefixSum, hzero, hzeroValue', Nat.add_zero]
  let start : Usize → Nat := fun row => constructorDFSOffset offsets.slice row.val
  have hstart : ∀ row : Usize, row.val < componentCount.val →
      constructorDFSOffset offsets.slice row.val = start row := by
    intro row _
    rfl
  have hstop : ∀ row : Usize, row.val < componentCount.val →
      constructorDFSOffset offsets.slice (row.val + 1) =
        start row + constructorQuotientRowCount carrier.edges.val
          (constructorSceneComponentAt components) row carrier.edges.val.length := by
    intro row hrow
    exact constructor_quotient_row_capacity carrier.edges.val
      (constructorSceneComponentAt components) counts offsets.slice componentCount row
      hcountsLength (by change offsets.val.length = componentCount.val + 1; omega)
      hrow hcounts hoffsets
  have hordered : ∀ row, row < componentCount.val →
      constructorDFSOffset offsets.slice row ≤
        constructorDFSOffset offsets.slice (row + 1) := by
    intro row hrow
    have hwidth : row < 2 ^ UScalarTy.Usize.numBits :=
      lt_trans hrow componentCount.hBounds
    let actual : Usize := UScalar.ofNatCore row hwidth
    have hs := hstop actual (by simpa only [actual, UScalar.ofNatCore_val_eq] using hrow)
    simp only [actual, UScalar.ofNatCore_val_eq, start] at hs
    rw [hs]
    omega
  have hlast : constructorDFSOffset offsets.slice componentCount.val =
      adjacencyCount.val := by
    obtain ⟨last, hlastLookup, hlastValue⟩ :=
      hoffsets componentCount.val (by omega)
    change (offsets.val[componentCount.val]?.map UScalar.val).getD 0 = adjacencyCount.val
    simp only [hlastLookup, Option.map_some, Option.getD_some, hlastValue]
    rw [hadjacency, hcountsLength]
  obtain ⟨rowOf, hrowsOffsets⟩ :=
    constructor_quotient_row_owner counts offsets.slice componentCount
      (by change offsets.val.length = componentCount.val + 1; omega) hoffsets
  have hrows : ∀ row : Usize, row.val < componentCount.val → ∀ slot,
      start row ≤ slot →
      slot < start row + constructorQuotientRowCount carrier.edges.val
        (constructorSceneComponentAt components) row carrier.edges.val.length →
      rowOf slot = row := by
    intro row hrow slot hlo hhi
    apply hrowsOffsets row hrow slot
    · exact hlo
    · simpa only [hstop row hrow] using hhi
  apply WP.spec_bind (constructor_scene_capture
    (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize adjacencyCount rfl))
  intro neighbors hneighborsRun
  obtain ⟨hneighbors, hneighborsRun⟩ := hneighborsRun
  apply WP.spec_bind (constructor_scene_capture
    (constructor_edge_new_spec { u := 0#usize, v := 0#usize }))
  intro emptyEdge hemptyEdgeRun
  obtain ⟨hemptyEdge, hemptyEdgeRun⟩ := hemptyEdgeRun
  apply WP.spec_bind (constructor_scene_capture
    (alloc.vec.from_elem_spec topology.Edge.Insts.CoreCloneClone
      emptyEdge adjacencyCount rfl))
  intro witnesses hwitnessesRun
  obtain ⟨hwitnesses, hwitnessesRun⟩ := hwitnessesRun
  apply WP.spec_bind (constructor_scene_capture
    (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize componentCount rfl))
  intro next hnextRun
  obtain ⟨hnext, hnextRun⟩ := hnextRun
  apply WP.spec_bind (constructor_scene_capture
    (constructor_quotient_cursor_spec componentCount offsets next
      (by rw [hoffsetsLength, hcountsLength]; omega)
      (by rw [hnext.1, List.length_replicate])))
  intro cursor hcursorRun
  obtain ⟨hcursor, hcursorRun⟩ := hcursorRun
  have hinitial : ConstructorQuotientCursors carrier.edges.val
      (constructorSceneComponentAt components) start 0 componentCount cursor := by
    intro row hrow
    obtain ⟨value, hvalue, _⟩ := hoffsets row.val (by omega)
    refine ⟨value, hcursor.2.1 row.val hrow |>.trans hvalue, ?_⟩
    change value.val = (offsets.val[row.val]?.map UScalar.val).getD 0 +
      constructorQuotientRowCount carrier.edges.val
        (constructorSceneComponentAt components) row 0
    simp only [hvalue, Option.map_some, Option.getD_some, constructorQuotientRowCount,
      Nat.add_zero]
  have hstorage : ∀ row : Usize, row.val < componentCount.val →
      start row + constructorQuotientRowCount carrier.edges.val
          (constructorSceneComponentAt components) row carrier.edges.val.length ≤
        neighbors.val.length ∧
      start row + constructorQuotientRowCount carrier.edges.val
          (constructorSceneComponentAt components) row carrier.edges.val.length ≤
        witnesses.val.length := by
    intro row hrow
    have hpref := constructor_prefix_sum_mono counts
      (show row.val + 2 ≤ counts.length by omega)
    have hbound : constructorDFSOffset offsets.slice (row.val + 1) ≤
        adjacencyCount.val := by
      obtain ⟨value, hvalue, hvaluePrefix⟩ := hoffsets (row.val + 1) (by omega)
      change (offsets.val[row.val + 1]?.map UScalar.val).getD 0 ≤ adjacencyCount.val
      simp only [hvalue, Option.map_some, Option.getD_some, hvaluePrefix, hadjacency]
      simpa only [Nat.add_assoc] using hpref
    rw [hstop row hrow] at hbound
    simp only [hneighbors.1, hwitnesses.1, List.length_replicate]
    exact ⟨hbound, hbound⟩
  apply WP.spec_bind (constructor_scene_capture (constructor_quotient_fill_loop_spec carrier components
    (alloc.vec.Vec.deref carrier.edges) neighbors witnesses cursor componentCount
    (constructorSceneComponentAt components) start
    (fun row => start row + constructorQuotientRowCount carrier.edges.val
      (constructorSceneComponentAt components) row carrier.edges.val.length)
    rowOf (by rw [hcursor.1, hnext.1, List.length_replicate])
    hinitial hcomponentLookup
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using hedges)
    (fun row _ => by
      simpa only [alloc.vec.Vec.deref, Slice.from_val] using
        (le_refl (start row + constructorQuotientRowCount carrier.edges.val
          (constructorSceneComponentAt components) row carrier.edges.val.length)))
    hstorage hrows))
  rintro ⟨filledNeighbors, filledWitnesses⟩ hfillRun
  obtain ⟨hfill, hfillRun⟩ := hfillRun
  have hfill := And.intro (And.intro hfill.1 hfill.2.1) hfill.2.2
  simp only [alloc.vec.Vec.deref, Slice.from_val] at hfill
  apply WP.spec_bind (constructor_scene_capture
    (alloc.vec.Vec.index_usize_spec components root (by
      change root.val < components.val.length
      rw [hcomponents, hn]
      exact hroot)))
  intro quotientRoot hquotientRun
  obtain ⟨hquotientRoot, hquotientRun⟩ := hquotientRun
  have hquotientLookup : components.val[root.val]? = some quotientRoot := by
    rw [List.getElem?_eq_getElem (by omega), hquotientRoot]
  have hquotientEq : quotientRoot = constructorSceneComponentAt components root :=
    Option.some.inj (hquotientLookup.symm.trans (hcomponentLookup root (by omega)))
  have hquotientBound : quotientRoot.val < componentCount.val := by
    rw [hquotientEq]
    exact hbounded root (by omega)
  let labelNat : Nat → Nat := fun node => (components.val[node]?.getD 0#usize).val
  have hdfsInput : ConstructorDFSInput offsets.slice filledNeighbors.slice quotientRoot.val := by
    have hlabelRoot : labelNat root.val = quotientRoot.val := by
      dsimp only [labelNat]
      simp only [hquotientLookup, Option.getD_some]
    rw [← hlabelRoot]
    apply constructor_quotient_actual_dfs_input carrier hc carrier.edges.val
      (constructorSceneComponentAt components) labelNat start componentCount root offsets.slice
      filledNeighbors filledWitnesses rowOf rfl hvertexCount hpositive hfirst
    · simpa only [hfill.1.1, hneighbors.1, List.length_replicate] using hlast
    · exact hordered
    · intro node hnode
      constructor
      · exact hbounded node (by omega)
      · rfl
    · intro id hid
      obtain ⟨node, hnode, heq⟩ := hdense
        (UScalar.ofNatCore id (lt_trans hid componentCount.hBounds)) (by simp; exact hid)
      refine ⟨node, by omega, ?_⟩
      simpa only [UScalar.ofNatCore_val_eq] using congrArg UScalar.val heq
    · exact hroot
    · exact hfill.2.1
    · exact hstart
    · exact hstop
    · exact hrows
    · exact hfill.2.2
  rw [constructor_scene_deref_eq_slice offsets, constructor_scene_deref_eq_slice filledNeighbors]
  apply WP.spec_bind (constructor_scene_capture
    (constructor_quotient_depth_first_accepts adapter hrng offsets.slice
      filledNeighbors quotientRoot rng work hdfsInput hw (by
        rw [hvertexCount]
        exact le_trans hcountBound (by simpa only [hn] using hcapacity))))
  rintro ⟨dfsResult, rng1, dfsWork⟩ hdfsRun
  obtain ⟨hdfs, hdfsRun⟩ := hdfsRun
  have hdfsOk : dfsResult = .Ok () := hdfs.1
  have hquotientActual : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice Usize) components root = ok quotientRoot := by
    change components.index_usize root = ok quotientRoot
    exact hquotientRun
  have hframe : ConstructorScenePostDFSFrame adapter carrier required root rng work
      rng1 dfsWork := by
    refine ⟨n, links, components, componentCount, offsets, adjacencyCount, hn,
      hprepareRun, hprefixRun, ?_⟩
    simp only [constructorSceneQuotientDFSProgram, uncurry, hneighborsRun, bind_ok,
      hemptyEdgeRun, hwitnessesRun, hnextRun, hcursorRun, hfillRun, hquotientActual]
    simpa only [hdfsOk, constructor_scene_deref_eq_slice] using hdfsRun
  rw [hdfsOk]
  simp only [uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply WP.spec_bind (Usize.sub_spec (x := n) (y := 1#usize) (by
    simpa only [UScalar.ofNatCore_val_eq, hn] using Nat.succ_le_of_lt hc.1))
  intro selectedCount hselectedCount
  have hselectedCountValue : selectedCount.val = n.val - 1 := by
    simpa only [UScalar.ofNatCore_val_eq] using hselectedCount.1
  apply WP.spec_bind (constructor_check_storage_spec selectedCount 16#usize)
  intro selectedStorage hselectedStorage
  by_cases hselectedFits : constructorStorageFits selectedCount 16#usize
  · have hselectedStorageOk : selectedStorage = .Ok () := by
      simpa only [hselectedFits, ite_true] using hselectedStorage
    simp only [hselectedStorageOk, bind_ok]
    apply WP.spec_bind (alloc.vec.from_elem_spec topology.Edge.Insts.CoreCloneClone
      emptyEdge selectedCount rfl)
    intro selected hselected
    have hincoming := constructor_quotient_dfs_original_incoming carrier.edges.val
      (constructorSceneComponentAt components) start componentCount quotientRoot offsets.slice
      filledNeighbors filledWitnesses work dfsWork hvertexCount hstart hstop
      (fun slot hslot => by
        obtain ⟨value, original, hnbr, hwit, _⟩ := hfill.2.2 slot hslot
        exact ⟨value, original, hnbr, hwit⟩) hdfs.2
    rw [← Std.bind_assoc]
    apply WP.spec_bind (constructor_scene_selected_from_dfs_output_spec dfsWork n required links
      componentCount quotientRoot filledWitnesses selected hquotientBound
      (by
        rw [hdfs.2.valid.2.2.2.1, hdfs.2.path]
        exact le_trans hcountBound (by simpa only [hn] using hcapacity))
      hincoming hforestCount hcomponentCount (by
        rw [hselected.1, List.length_replicate, hselectedCountValue]))
    rintro ⟨selectedWork, finalSelected⟩ hselection
    have hselectedWork : selectedWork = dfsWork := hselection.1
    subst selectedWork
    simp only [uncurry]
    have hselectedLength : finalSelected.val.length = n.val - 1 := by
      rw [hselection.2.1, hselected.1, List.length_replicate, hselectedCountValue]
    have hchosenCarrier : ∀ node, node < componentCount.val →
        node ≠ quotientRoot.val →
        carrierEdge carrier
          (constructorSceneChosenWitness dfsWork filledWitnesses node).u.val
          (constructorSceneChosenWitness dfsWork filledWitnesses node).v.val := by
      intro node hnode hnonroot
      have hwidth : node < 2 ^ UScalarTy.Usize.numBits :=
        lt_trans hnode componentCount.hBounds
      let actual : Usize := UScalar.ofNatCore node hwidth
      obtain ⟨parent, slot, original, _, hin, hwit, hsemantic⟩ :=
        constructor_quotient_dfs_selected_witness carrier carrier.edges.val
          (constructorSceneComponentAt components) start rowOf componentCount quotientRoot
          offsets.slice filledNeighbors filledWitnesses work dfsWork hvertexCount hstart hstop
          hrows hfill.2.2 hdfs.2 actual (by simpa only [actual,
            UScalar.ofNatCore_val_eq] using hnode) (by
              intro he
              apply hnonroot
              simpa only [actual, UScalar.ofNatCore_val_eq] using congrArg UScalar.val he)
      have hchosenEq :=
        constructor_scene_chosen_witness_eq dfsWork filledWitnesses node slot original
          (by simpa only [actual, UScalar.ofNatCore_val_eq] using hin) hwit
      simpa only [hchosenEq] using hsemantic.1
    have hselectedEdges := constructor_scene_selected_edges_valid carrier required finalSelected
      componentCount quotientRoot
      (constructorSceneChosenWitness dfsWork filledWitnesses) hc hforest
      hselection.2.2 hchosenCarrier
    have hselectedCarrier : ∀ edge ∈ finalSelected.val,
        carrierEdge carrier edge.u.val edge.v.val := by
      intro edge hedge
      obtain ⟨slot, hlookup⟩ := List.mem_iff_getElem?.mp hedge
      have hslot : slot < finalSelected.val.length :=
        (List.getElem?_eq_some_iff.mp hlookup).1
      rcases hselection.2.2 slot hslot with hrequired | hchosen
      · have hcanonical := constructor_canonical_edge_carrier carrier hc
        cases horiginal : required.val[slot]? with
        | none =>
            simp only [horiginal, Option.map_none] at hrequired
            rw [hrequired.2] at hlookup
            contradiction
        | some original =>
            have heq : edge = constructorCanonicalEdge original :=
              Option.some.inj (hlookup.symm.trans (by
                simpa only [horiginal, Option.map_some] using hrequired.2))
            subst edge
            exact hcanonical original (hforest slot hrequired.1 original horiginal).1
      · obtain ⟨node, hnode, hnonroot, _, hchosenLookup⟩ := hchosen
        have heq : edge = constructorSceneChosenWitness dfsWork filledWitnesses node :=
          Option.some.inj (hlookup.symm.trans hchosenLookup)
        subst edge
        exact hchosenCarrier node hnode hnonroot
    have hselectedConnected : ∀ vertex, vertex < n.val →
        Relation.ReflTransGen (fun u v =>
          ∃ edge ∈ finalSelected.val, (u = edge.u.val ∧ v = edge.v.val) ∨
            (u = edge.v.val ∧ v = edge.u.val)) 0 vertex := by
      intro vertex hvertex
      apply constructor_scene_selected_connected_actual carrier required components links
        componentCount quotientRoot offsets filledNeighbors filledWitnesses start rowOf work
        dfsWork finalSelected hc hforest hvertexCount
        (le_trans hcountBound (by simpa only [hn] using hcapacity)) hquotientBound
        (by simpa only [hn] using hforestCount) hcomponentCount
        (fun node hnode => hbounded node (by simpa only [hn] using hnode))
        (fun u v hu hv => hclasses u v (by simpa only [hn] using hu)
          (by simpa only [hn] using hv))
        hstart hstop hrows hfill.2.2 hdfs.2 hselection.2.2
        (by simpa only [hn] using hselectedLength)
      simpa only [hn] using hvertex
    have hprefixSelected : ∀ slot, slot < required.val.length →
        finalSelected.val[slot]? =
          (required.val[slot]?).map constructorCanonicalEdge := by
      intro slot hslot
      have hslotSelected : slot < finalSelected.val.length := by omega
      rcases hselection.2.2 slot hslotSelected with hcopy | hchosen
      · exact hcopy.2
      · obtain ⟨node, _, _, hindex, _⟩ := hchosen
        unfold constructorSceneSelectedIndex at hindex
        split at hindex <;> omega
    have hnzero : n ≠ 0#usize := by
      intro he
      have : n.val = 0 := congrArg UScalar.val he
      rw [hn] at this
      omega
    have hlength : finalSelected.val.length + 1 = n.val := by omega
    have hdfsCapacity : n.val ≤ dfsWork.path.val.length := by
      rw [hdfs.2.path, hn]
      exact hcapacity
    rw [constructor_scene_deref_eq_slice finalSelected]
    by_cases hwidth : constructorEdgesStorageFits n finalSelected.slice
    · have hpublished := WP.spec_bind
        (Pₖ := fun output =>
          (∃ published, output.1 = .Ok published ∧ published.root = root ∧
            TreeValid carrier published ∧ WorkspaceValid output.2.2 ∧
            ∀ slot, slot < required.val.length → ∀ edge,
              required.val[slot]? = some edge →
              parentEdge (parents published) edge.u.val edge.v.val) ∨
          (output.1 = .Err topology.Error.Overflow ∧ WorkspaceValid output.2.2 ∧
            ¬ ConstructorSceneAllocationFits carrier ∧
            ConstructorScenePostDFSFrame adapter carrier required root rng work
              output.2.1 output.2.2))
        (k := fun output : core.result.Result spanning_tree.Tree topology.Error ×
          spanning_tree.Workspace => ok (output.1, rng1, output.2))
        (constructor_scene_publish_accepts carrier required n root finalSelected
          dfsWork hc hn hroot (by simpa only [hn] using hselectedEdges)
          hselectedCarrier hselectedConnected hlength hprefixSelected hwidth
          hdfs.2.valid hdfsCapacity) (by
        rintro ⟨publishedResult, finalWork⟩ hpublished
        obtain ⟨published, hresult, hpublishedRoot, htree, hwork, _hframes, _hparents,
          _hincoming, _hslots, _hnodes, _heditCount, _hedgeCapacity, hrequired⟩ := hpublished
        rw [hresult]
        exact (WP.spec_ok _).mpr (Or.inl
          ⟨published, rfl, hpublishedRoot, htree, hwork, hrequired⟩))
      refine Eq.mp ?_ hpublished
      apply congrArg₂ WP.spec
      · conv_lhs => erw [Std.bind_assoc]
        apply congrArg (Std.bind (topology.Carrier.from_edges n finalSelected.slice))
        funext expandedResult
        conv_lhs => erw [Std.bind_assoc]
        apply congrArg (Std.bind
          (core.result.Result.Insts.CoreOpsTry.branch expandedResult))
        funext expandedFlow
        cases expandedFlow with
        | Break residual =>
            dsimp
            conv_lhs => erw [Std.bind_assoc]
            simp only [bind_ok]
        | Continue expanded =>
            dsimp
            conv_lhs => erw [Std.bind_assoc]
            apply congrArg (Std.bind (alloc.vec.from_elem core.clone.CloneUsize root n))
            funext parents
            conv_lhs => erw [Std.bind_assoc]
            apply congrArg (Std.bind (spanning_tree.Tree.scene_dfs_loop8 dfsWork n 0#usize))
            funext workIndex
            cases workIndex with
            | mk work3 index =>
                conv_lhs => erw [Std.bind_assoc]
                apply congrArg (Std.bind
                  (alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Bool) work3.seen root))
                funext seenPair
                conv_lhs => erw [Std.bind_assoc]
                cases seenPair with
                | mk _ seenBack' =>
                    apply congrArg (Std.bind
                      (alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Usize)
                        work3.path 0#usize))
                    funext pathPair
                    cases pathPair with
                    | mk _ pathBack' =>
                        conv_lhs => erw [Std.bind_assoc]
                        apply congrArg (Std.bind
                          (spanning_tree.Tree.scene_dfs_loop9 (seenBack' true) (pathBack' root) index
                            expanded parents 1#usize))
                        funext result
                        cases result with
                        | mk seen' rest =>
                            cases rest with
                            | mk path' parents' =>
                                simp only [bind_ok, uncurry_apply_pair]
      · rfl
    · apply WP.spec_bind
        (constructor_scene_expanded_carrier_overflow n finalSelected hnzero hwidth)
      intro expandedResult hexpanded
      rw [hexpanded]
      simp only [bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        bind_tc_eq]
      have hnotAllocation : ¬ ConstructorSceneAllocationFits carrier := by
        intro hallocation
        rcases hallocation with
          ⟨ha1, ha2, ha3, _ha4, _ha5, _ha6, _ha7, _ha8, ha9, ha10, ha11, ha12⟩
        apply hwidth
        have hselectedSliceLength :
            finalSelected.slice.val.length = cellCount carrier - 1 := by
          change finalSelected.val.length = cellCount carrier - 1
          rw [hselectedLength, hn]
        unfold constructorEdgesStorageFits
        rw [hselectedSliceLength, hn]
        refine ⟨ha1, by omega, ha2, ha3, ha11, ha12, ?_⟩
        simp only [constructorStorageFits, Slice.len_val, hselectedSliceLength,
          UScalar.ofNatCore_val_eq]
        exact ⟨ha9, ha10⟩
      exact (WP.spec_ok _).mpr
        (Or.inr ⟨rfl, hdfs.2.valid, hnotAllocation, hframe⟩)
  · have hselectedStorageError : selectedStorage = .Err .Overflow := by
      simpa only [hselectedFits, ite_false] using hselectedStorage
    simp only [hselectedStorageError, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      bind_tc_eq]
    have hnotAllocation : ¬ ConstructorSceneAllocationFits carrier := by
      intro hallocation
      rcases hallocation with
        ⟨_ha1, _ha2, _ha3, _ha4, _ha5, _ha6, _ha7, _ha8,
          ha9, ha10, _ha11, _ha12⟩
      apply hselectedFits
      simp only [constructorStorageFits, hselectedCountValue, hn,
        UScalar.ofNatCore_val_eq]
      exact ⟨ha9, ha10⟩
    exact (WP.spec_ok _).mpr
      (Or.inr ⟨rfl, hdfs.2.valid, hnotAllocation, hframe⟩)

private theorem constructor_scene_after_prepare_total {R : Type*} (adapter : tree.Rng R)
    (hrng : constructorLegalRng adapter) (carrier : topology.Carrier)
    (required : Slice topology.Edge) (n root : Usize) (rng : R)
    (work : spanning_tree.Workspace) (links components : alloc.vec.Vec Usize)
    (componentCount : Usize)
    (hc : CarrierValid carrier) (hn : n.val = cellCount carrier)
    (hroot : root.val < cellCount carrier)
    (hw : WorkspaceValid work) (hcapacity : cellCount carrier ≤ work.path.val.length)
    (hforest : ConstructorRequiredForest carrier required)
    (hlinks : links.val.length = n.val)
    (hcomponents : components.val.length = n.val)
    (hforestCount : required.val.length + constructorSceneRootCount links = n.val)
    (hpositive : 0 < componentCount.val)
    (hcountBound : componentCount.val ≤ n.val)
    (hbounded : ∀ node : Usize, node.val < n.val →
      (constructorSceneComponentAt components node).val < componentCount.val)
    (hdense : ∀ id : Usize, id.val < componentCount.val → ∃ node : Usize,
      node.val < n.val ∧ constructorSceneComponentAt components node = id)
    (hclasses : ∀ u v : Usize, u.val < n.val → v.val < n.val →
      (constructorSceneComponentAt components u = constructorSceneComponentAt components v ↔
        Relation.ReflTransGen
          (constructorRequiredPrefixArc required required.val.length) u v))
    (hcomponentCount : componentCount.val = constructorSceneRootCount links)
    (hprepareRun : constructorScenePrepareProgram carrier n required =
      ok (.Ok (links, components, componentCount))) :
    WP.spec (constructor_scene_after_prepare_program adapter carrier required n root rng work
      components componentCount)
      (fun output =>
        (∃ published, output.1 = .Ok published ∧ published.root = root ∧
          TreeValid carrier published ∧ WorkspaceValid output.2.2 ∧
          ∀ slot, slot < required.val.length → ∀ edge,
            required.val[slot]? = some edge →
            parentEdge (parents published) edge.u.val edge.v.val) ∨
        output = (.Err topology.Error.Overflow, rng, work) ∨
        (output.1 = .Err topology.Error.Overflow ∧ WorkspaceValid output.2.2 ∧
          ¬ ConstructorSceneAllocationFits carrier ∧
          ConstructorScenePostDFSFrame adapter carrier required root rng work
            output.2.1 output.2.2)) := by
  unfold constructor_scene_after_prepare_program
  have hcomponentLookup : ∀ node : Usize, node.val < components.val.length →
      components.val[node.val]? =
        some (constructorSceneComponentAt components node) := by
    intro node hnode
    unfold constructorSceneComponentAt
    rw [List.getElem?_eq_getElem hnode]
    rfl
  apply WP.spec_bind (constructor_scene_capture
    (constructor_scene_quotient_prefix_total carrier components componentCount
      (constructorSceneComponentAt components) hc (by simpa only [hn] using hcomponents)
      hcomponentLookup (fun node hnode => hbounded node (by
        simpa only [hcomponents] using hnode))))
  intro prefixResult hprefixCaptured
  obtain ⟨hprefixResult, hprefixRun⟩ := hprefixCaptured
  change constructorSceneQuotientPrefixProgram carrier components componentCount =
    ok prefixResult at hprefixRun
  rcases hprefixResult with hprefixOverflow | hprefixSuccess
  · rw [hprefixOverflow]
    exact (WP.spec_ok _).mpr (Or.inr (Or.inl rfl))
  · obtain ⟨offsets, adjacencyCount, hprefixResult, hprefix⟩ := hprefixSuccess
    rw [hprefixResult] at hprefixRun
    rw [hprefixResult]
    apply WP.spec_mono
      (constructor_scene_after_prefix_total adapter hrng carrier required n root rng work
        links components componentCount hc hn hroot hw hcapacity hforest hlinks hcomponents
        hforestCount hpositive hcountBound hbounded hdense hclasses hcomponentCount offsets
        adjacencyCount hprefix hprepareRun hprefixRun)
    intro output houtput
    exact houtput.elim Or.inl (fun h => Or.inr (Or.inr h))

private theorem constructor_scene_after_prepare_accepts {R : Type*} (adapter : tree.Rng R)
    (hrng : constructorLegalRng adapter) (carrier : topology.Carrier)
    (required : Slice topology.Edge) (n root : Usize) (rng : R)
    (work : spanning_tree.Workspace) (links components : alloc.vec.Vec Usize)
    (componentCount : Usize)
    (hc : CarrierValid carrier) (hn : n.val = cellCount carrier)
    (hroot : root.val < cellCount carrier)
    (hw : WorkspaceValid work) (hcapacity : cellCount carrier ≤ work.path.val.length)
    (hforest : ConstructorRequiredForest carrier required)
    (hlinks : links.val.length = n.val)
    (hcomponents : components.val.length = n.val)
    (hforestCount : required.val.length + constructorSceneRootCount links = n.val)
    (hpositive : 0 < componentCount.val)
    (hcountBound : componentCount.val ≤ n.val)
    (hbounded : ∀ node : Usize, node.val < n.val →
      (constructorSceneComponentAt components node).val < componentCount.val)
    (hdense : ∀ id : Usize, id.val < componentCount.val → ∃ node : Usize,
      node.val < n.val ∧ constructorSceneComponentAt components node = id)
    (hclasses : ∀ u v : Usize, u.val < n.val → v.val < n.val →
      (constructorSceneComponentAt components u = constructorSceneComponentAt components v ↔
        Relation.ReflTransGen
          (constructorRequiredPrefixArc required required.val.length) u v))
    (hcomponentCount : componentCount.val = constructorSceneRootCount links)
    (hallocation : ConstructorSceneAllocationFits carrier)
    (hprepareRun : constructorScenePrepareProgram carrier n required =
      ok (.Ok (links, components, componentCount))) :
    WP.spec (constructor_scene_after_prepare_program adapter carrier required n root rng work
      components componentCount)
      (fun output => ∃ published,
        output.1 = .Ok published ∧ published.root = root ∧
        TreeValid carrier published ∧ WorkspaceValid output.2.2 ∧
        ∀ slot, slot < required.val.length → ∀ edge,
          required.val[slot]? = some edge →
          parentEdge (parents published) edge.u.val edge.v.val) := by
  unfold constructor_scene_after_prepare_program
  have hcomponentLookup : ∀ node : Usize, node.val < components.val.length →
      components.val[node.val]? =
        some (constructorSceneComponentAt components node) := by
    intro node hnode
    unfold constructorSceneComponentAt
    rw [List.getElem?_eq_getElem hnode]
    rfl
  apply WP.spec_bind (constructor_scene_capture
    (constructor_scene_quotient_prefix_accepts carrier components
      componentCount (constructorSceneComponentAt components) hc
      (by simpa only [hn] using hcomponents) hcomponentLookup
      (fun node hnode => hbounded node (by simpa only [hcomponents] using hnode))
      (by simpa only [hn] using hcountBound) hallocation))
  intro prefixResult hprefixCaptured
  obtain ⟨hprefixResult, hprefixRun⟩ := hprefixCaptured
  change constructorSceneQuotientPrefixProgram carrier components componentCount =
    ok prefixResult at hprefixRun
  obtain ⟨offsets, adjacencyCount, hprefixResult, hprefix⟩ := hprefixResult
  rw [hprefixResult] at hprefixRun
  rw [hprefixResult]
  apply WP.spec_mono
    (constructor_scene_after_prefix_total adapter hrng carrier required n root rng work
      links components componentCount hc hn hroot hw hcapacity hforest hlinks hcomponents
      hforestCount hpositive hcountBound hbounded hdense hclasses hcomponentCount offsets
      adjacencyCount hprefix hprepareRun hprefixRun)
  intro output houtput
  rcases houtput with hsuccess | hoverflow
  · exact hsuccess
  · exact False.elim (hoverflow.2.2.1 hallocation)

set_option maxHeartbeats 1000000 in
/-- The complete valid-guard branch preserves either the caller frame or exactly the
frame returned by the actual quotient DFS. -/
theorem constructor_scene_dfs_guarded {R : Type*} (adapter : tree.Rng R)
    (hrng : constructorLegalRng adapter) (carrier : topology.Carrier)
    (required : Slice topology.Edge) (root : Usize) (rng : R)
    (work : spanning_tree.Workspace) (hc : CarrierValid carrier)
    (hw : WorkspaceValid work) (hroot : root.val < cellCount carrier)
    (hcapacity : cellCount carrier ≤ work.path.val.length ∧
      (alloc.vec.Vec.deref carrier.edges).val.length ≤ work.edge_capacity.val)
    (hrequired : required.val.length < cellCount carrier)
    (hforest : ConstructorRequiredForest carrier required) :
    WP.spec (spanning_tree.Tree.scene_dfs adapter carrier required root rng work)
      (fun output =>
        (∃ published, output.1 = .Ok published ∧ published.root = root ∧
          TreeValid carrier published ∧ WorkspaceValid output.2.2 ∧
          ∀ slot, slot < required.val.length → ∀ edge,
            required.val[slot]? = some edge →
            parentEdge (parents published) edge.u.val edge.v.val) ∨
        output = (.Err topology.Error.Overflow, rng, work) ∨
        (output.1 = .Err topology.Error.Overflow ∧ WorkspaceValid output.2.2 ∧
          ¬ ConstructorSceneAllocationFits carrier ∧
          ConstructorScenePostDFSFrame adapter carrier required root rng work
            output.2.1 output.2.2)) := by
  rw [← constructor_scene_program_eq]
  unfold constructor_scene_program
  apply WP.spec_bind (mutation_carrier_len_total carrier hc)
  intro n hn
  have hrootGuard : ¬ root >= n := by
    change ¬ n.val ≤ root.val
    omega
  simp only [hrootGuard, ite_false, topology.Carrier.impl.edges, bind_ok]
  apply WP.spec_bind (mutation_workspace_ensure_total work n
    (Slice.len (alloc.vec.Vec.deref carrier.edges)))
  intro ensured hensured
  have hensuredOk : ensured = .Ok () := by
    rw [hensured]
    have hyes : n.val ≤ work.path.val.length ∧
        Slice.len (alloc.vec.Vec.deref carrier.edges) ≤ work.edge_capacity := by
      simpa only [hn, UScalar.le_equiv, Slice.len_val] using hcapacity
    exact ite_eq_left hyes
  simp only [hensuredOk, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hrequiredGuard : ¬ Slice.len required >= n := by
    change ¬ n.val ≤ required.val.length
    omega
  simp only [hrequiredGuard, ite_false]
  have hwrapped := WP.spec_bind
    (Pₖ := fun output =>
      (∃ published, output.1 = .Ok published ∧ published.root = root ∧
        TreeValid carrier published ∧ WorkspaceValid output.2.2 ∧
        ∀ slot, slot < required.val.length → ∀ edge,
          required.val[slot]? = some edge →
          parentEdge (parents published) edge.u.val edge.v.val) ∨
      output = (.Err topology.Error.Overflow, rng, work) ∨
      (output.1 = .Err topology.Error.Overflow ∧ WorkspaceValid output.2.2 ∧
        ¬ ConstructorSceneAllocationFits carrier ∧
        ConstructorScenePostDFSFrame adapter carrier required root rng work
          output.2.1 output.2.2))
    (k := fun prepared =>
      match prepared with
      | .Ok (_, components, componentCount) =>
        constructor_scene_after_prepare_program adapter carrier required n root rng work
          components componentCount
      | .Err residual => do
        let result ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            spanning_tree.Tree (core.convert.FromSame topology.Error) residual
        ok (result, rng, work))
    (constructor_scene_capture
      (constructor_scene_prepare_accepts carrier n required hc hn hforest)) (by
      intro prepared hpreparedCaptured
      obtain ⟨hprepared, hprepareRun⟩ := hpreparedCaptured
      change constructorScenePrepareProgram carrier n required = ok prepared at hprepareRun
      obtain ⟨links, components, componentCount, rank, component, hpreparedResult,
        hlinks, hcomponents, hforestCount, _hrank, _hcomponentLabels, hpositive,
        hcountBound, hbounded, hdense, hclasses, hcomponentCount⟩ := hprepared
      rw [hpreparedResult] at hprepareRun
      rw [hpreparedResult]
      exact constructor_scene_after_prepare_total adapter hrng carrier required n root rng work
        links components componentCount hc hn hroot hw hcapacity.1 hforest hlinks hcomponents
        hforestCount hpositive hcountBound hbounded hdense hclasses hcomponentCount hprepareRun)
  exact hwrapped

set_option maxHeartbeats 1000000 in
/-- With every input-size allocation guard representable, the literal outer `scene_dfs`
publishes a valid original-carrier tree containing every required edge. -/
theorem constructor_scene_dfs_accepts {R : Type*} (adapter : tree.Rng R)
    (hrng : constructorLegalRng adapter) (carrier : topology.Carrier)
    (required : Slice topology.Edge) (root : Usize) (rng : R)
    (work : spanning_tree.Workspace) (hc : CarrierValid carrier)
    (hw : WorkspaceValid work) (hroot : root.val < cellCount carrier)
    (hcapacity : cellCount carrier ≤ work.path.val.length ∧
      (alloc.vec.Vec.deref carrier.edges).val.length ≤ work.edge_capacity.val)
    (hrequired : required.val.length < cellCount carrier)
    (hforest : ConstructorRequiredForest carrier required)
    (hallocation : ConstructorSceneAllocationFits carrier) :
    WP.spec (spanning_tree.Tree.scene_dfs adapter carrier required root rng work)
      (fun output => ∃ published,
        output.1 = .Ok published ∧ published.root = root ∧
        TreeValid carrier published ∧ WorkspaceValid output.2.2 ∧
        ∀ slot, slot < required.val.length → ∀ edge,
          required.val[slot]? = some edge →
          parentEdge (parents published) edge.u.val edge.v.val) := by
  rw [← constructor_scene_program_eq]
  unfold constructor_scene_program
  apply WP.spec_bind (mutation_carrier_len_total carrier hc)
  intro n hn
  have hrootGuard : ¬ root >= n := by
    change ¬ n.val ≤ root.val
    omega
  simp only [hrootGuard, ite_false, topology.Carrier.impl.edges, bind_ok]
  apply WP.spec_bind (mutation_workspace_ensure_total work n
    (Slice.len (alloc.vec.Vec.deref carrier.edges)))
  intro ensured hensured
  have hensuredOk : ensured = .Ok () := by
    rw [hensured]
    have hyes : n.val ≤ work.path.val.length ∧
        Slice.len (alloc.vec.Vec.deref carrier.edges) ≤ work.edge_capacity := by
      simpa only [hn, UScalar.le_equiv, Slice.len_val] using hcapacity
    exact ite_eq_left hyes
  simp only [hensuredOk, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hrequiredGuard : ¬ Slice.len required >= n := by
    change ¬ n.val ≤ required.val.length
    omega
  simp only [hrequiredGuard, ite_false]
  have hwrapped := WP.spec_bind
    (Pₖ := fun output => ∃ published,
      output.1 = .Ok published ∧ published.root = root ∧
      TreeValid carrier published ∧ WorkspaceValid output.2.2 ∧
      ∀ slot, slot < required.val.length → ∀ edge,
        required.val[slot]? = some edge →
        parentEdge (parents published) edge.u.val edge.v.val)
    (k := fun prepared =>
      match prepared with
      | .Ok (_, components, componentCount) =>
        constructor_scene_after_prepare_program adapter carrier required n root rng work
          components componentCount
      | .Err residual => do
        let result ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            spanning_tree.Tree (core.convert.FromSame topology.Error) residual
        ok (result, rng, work))
    (constructor_scene_capture
      (constructor_scene_prepare_accepts carrier n required hc hn hforest)) (by
      intro prepared hpreparedCaptured
      obtain ⟨hprepared, hprepareRun⟩ := hpreparedCaptured
      change constructorScenePrepareProgram carrier n required = ok prepared at hprepareRun
      obtain ⟨links, components, componentCount, rank, component, hpreparedResult,
        hlinks, hcomponents, hforestCount, _hrank, _hcomponentLabels, hpositive,
        hcountBound, hbounded, hdense, hclasses, hcomponentCount⟩ := hprepared
      rw [hpreparedResult] at hprepareRun
      rw [hpreparedResult]
      exact constructor_scene_after_prepare_accepts adapter hrng carrier required n root rng work
        links components componentCount hc hn hroot hw hcapacity.1 hforest hlinks hcomponents
        hforestCount hpositive hcountBound hbounded hdense hclasses hcomponentCount hallocation
        hprepareRun)
  exact hwrapped

/-- The actual scene constructor is total at every representable input width.
Guard and pre-DFS errors preserve the caller frame. Post-DFS overflow preserves exactly
the RNG and workspace returned by the literal quotient DFS, including publication overflow. -/
theorem constructor_scene_dfs_spec {R : Type*} (adapter : tree.Rng R)
    (hrng : constructorLegalRng adapter) (carrier : topology.Carrier)
    (required : Slice topology.Edge) (root : Usize) (rng : R)
    (work : spanning_tree.Workspace) (hc : CarrierValid carrier)
    (hw : WorkspaceValid work) :
    WP.spec (spanning_tree.Tree.scene_dfs adapter carrier required root rng work)
      (fun output =>
        (∃ published, output.1 = .Ok published ∧ published.root = root ∧
          TreeValid carrier published ∧ WorkspaceValid output.2.2 ∧
          (∀ slot, slot < required.val.length → ∀ edge,
            required.val[slot]? = some edge →
            parentEdge (parents published) edge.u.val edge.v.val)) ∨
        (output = (.Err topology.Error.InvalidIndex, rng, work) ∧
          cellCount carrier ≤ root.val) ∨
        (output = (.Err topology.Error.InsufficientWorkspace, rng, work) ∧
          root.val < cellCount carrier ∧
          ¬ (cellCount carrier ≤ work.path.val.length ∧
            (alloc.vec.Vec.deref carrier.edges).val.length ≤ work.edge_capacity.val)) ∨
        (output = (.Err topology.Error.InvalidForest, rng, work) ∧
          root.val < cellCount carrier ∧
          cellCount carrier ≤ work.path.val.length ∧
          (alloc.vec.Vec.deref carrier.edges).val.length ≤ work.edge_capacity.val ∧
          (cellCount carrier ≤ required.val.length ∨
            (required.val.length < cellCount carrier ∧
              ¬ ConstructorRequiredForest carrier required))) ∨
        ((output = (.Err topology.Error.Overflow, rng, work) ∨
            (output.1 = .Err topology.Error.Overflow ∧ WorkspaceValid output.2.2 ∧
              ConstructorScenePostDFSFrame adapter carrier required root rng work
                output.2.1 output.2.2)) ∧
          root.val < cellCount carrier ∧
          cellCount carrier ≤ work.path.val.length ∧
          (alloc.vec.Vec.deref carrier.edges).val.length ≤ work.edge_capacity.val ∧
          required.val.length < cellCount carrier ∧
          ConstructorRequiredForest carrier required)) := by
  by_cases hroot : root.val < cellCount carrier
  · by_cases hcapacity : cellCount carrier ≤ work.path.val.length ∧
        (alloc.vec.Vec.deref carrier.edges).val.length ≤ work.edge_capacity.val
    · by_cases hrequired : required.val.length < cellCount carrier
      · by_cases hforest : ConstructorRequiredForest carrier required
        · apply WP.spec_mono (constructor_scene_dfs_guarded adapter hrng carrier required root
            rng work hc hw hroot hcapacity hrequired hforest)
          intro output houtput
          rcases houtput with hsuccess | hpre | hpost
          · exact Or.inl hsuccess
          · exact Or.inr (Or.inr (Or.inr (Or.inr
              ⟨Or.inl hpre, hroot, hcapacity.1, hcapacity.2, hrequired, hforest⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr
              ⟨Or.inr ⟨hpost.1, hpost.2.1, hpost.2.2.2⟩, hroot, hcapacity.1, hcapacity.2,
                hrequired, hforest⟩)))
        · apply WP.spec_mono (constructor_scene_rejects_invalid_forest adapter carrier required
            root rng work hc hroot hcapacity hrequired hforest)
          intro output houtput
          exact Or.inr (Or.inr (Or.inr (Or.inl
            ⟨houtput, hroot, hcapacity.1, hcapacity.2, Or.inr ⟨hrequired, hforest⟩⟩)))
      · have hmany : cellCount carrier ≤ required.val.length := by omega
        apply WP.spec_mono (constructor_scene_rejects_required_length adapter carrier required
          root rng work hc hroot hcapacity hmany)
        intro output houtput
        exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨houtput, hroot, hcapacity.1, hcapacity.2, Or.inl hmany⟩)))
    · apply WP.spec_mono (constructor_scene_rejects_workspace adapter carrier required root rng
        work hc hroot hcapacity)
      intro output houtput
      exact Or.inr (Or.inr (Or.inl ⟨houtput, hroot, hcapacity⟩))
  · have hbad : cellCount carrier ≤ root.val := by omega
    apply WP.spec_mono
      (constructor_scene_rejects_root adapter carrier required root rng work hc hbad)
    intro output houtput
    exact Or.inr (Or.inl ⟨houtput, hbad⟩)
end Labyrinth
