module
public import LabyrinthCore.ConstructorDepthFirst
public import LabyrinthCore.ConstructorDepthFirstCarrier
public import LabyrinthCore.ConstructorCopy
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- The production wrapper publishes exactly the proved parent prefix, not a reconstructed tree. -/
theorem constructor_tree_dfs_accepts {R : Type*} (adapter : tree.Rng R)
    (hrng : constructorLegalRng adapter) (carrier : topology.Carrier) (root : Usize)
    (rng : R) (work : spanning_tree.Workspace) (hc : CarrierValid carrier)
    (hw : WorkspaceValid work) (hroot : root.val < cellCount carrier)
    (hcapacity : cellCount carrier ≤ work.path.val.length)
    (hedges : carrier.edges.val.length ≤ work.edge_capacity.val) :
    WP.spec (spanning_tree.Tree.dfs adapter carrier root rng work) (fun output =>
      ∃ published, output.1 = .Ok published ∧ published.root = root ∧
        TreeValid carrier published ∧ WorkspaceValid output.2.2 ∧
        output.2.2.path = work.path ∧ output.2.2.edge_capacity = work.edge_capacity) := by
  have hnonempty : 0 < carrier.offsets.val.length := by have := hc.1; unfold cellCount at this; omega
  unfold spanning_tree.Tree.dfs topology.Carrier.len
  apply WP.spec_bind (Usize.sub_spec (x := alloc.vec.Vec.len carrier.offsets) (y := 1#usize) (by
    simp only [alloc.vec.Vec.len_val, UScalar.ofNatCore_val_eq]
    omega))
  intro n hn
  have hnval : n.val = cellCount carrier := by
    simpa only [alloc.vec.Vec.len_val, UScalar.ofNatCore_val_eq, cellCount] using hn.1
  have hguard : ¬ root ≥ n := by change ¬ n.val ≤ root.val; rw [hnval]; omega
  simp only [hguard, ite_false, topology.Carrier.impl.edges, bind_ok]
  have hcells : ¬ n > alloc.vec.Vec.len work.path := by
    change ¬ work.path.val.length < n.val
    rw [hnval]
    omega
  have hedgeGuard : ¬ Slice.len (alloc.vec.Vec.deref carrier.edges) > work.edge_capacity := by
    change ¬ work.edge_capacity.val < carrier.edges.val.length
    omega
  simp only [spanning_tree.Workspace.ensure, hcells, hedgeGuard, ite_false,
    core.result.Result.Insts.CoreOpsTry.branch, bind_ok, topology.Carrier.storage]
  apply WP.spec_bind (constructor_depth_first_accepts adapter hrng
    (alloc.vec.Vec.deref carrier.offsets) (alloc.vec.Vec.deref carrier.neighbors) root rng work
    (constructor_dfs_input_of_carrier carrier root.val hc hroot) hw hcapacity)
  rintro ⟨status, rng', after⟩ ⟨hstatus, hout⟩
  dsimp only at hstatus hout
  rw [hstatus]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize root n rfl)
  intro fresh hfresh
  have hfreshLen : fresh.val.length = cellCount carrier := by simp only [hfresh.1, List.length_replicate, hnval]
  apply WP.spec_bind (constructor_dfs_copy_spec after fresh (by
    rw [hfreshLen, hout.valid.2.2.1, hout.path]
    exact hcapacity))
  rintro ⟨copiedWork, copiedParents⟩ ⟨rfl, hcopy⟩
  apply (WP.spec_ok _).mpr
  refine ⟨{ parents := copiedParents, root }, rfl, rfl, ?_, hout.valid, hout.path, hout.edge_capacity⟩
  exact constructor_dfs_output_tree_valid carrier root work after
    { parents := copiedParents, root } hc hcapacity hout (by simpa only [hfreshLen] using hcopy) rfl

/-- Invalid roots return before touching workspace or RNG, and still terminate. -/
theorem constructor_tree_dfs_invalid_root {R : Type*} (adapter : tree.Rng R)
    (carrier : topology.Carrier) (root : Usize) (rng : R) (work : spanning_tree.Workspace)
    (hc : CarrierValid carrier) (hroot : cellCount carrier ≤ root.val) :
    WP.spec (spanning_tree.Tree.dfs adapter carrier root rng work)
      (fun output => output = (.Err .InvalidIndex, rng, work)) := by
  have hnonempty : 0 < carrier.offsets.val.length := by have := hc.1; unfold cellCount at this; omega
  unfold spanning_tree.Tree.dfs topology.Carrier.len
  apply WP.spec_bind (Usize.sub_spec (x := alloc.vec.Vec.len carrier.offsets) (y := 1#usize) (by
    simp only [alloc.vec.Vec.len_val, UScalar.ofNatCore_val_eq]
    omega))
  intro n hn
  have hnval : n.val = cellCount carrier := by
    simpa only [alloc.vec.Vec.len_val, UScalar.ofNatCore_val_eq, cellCount] using hn.1
  have hguard : root ≥ n := by change n.val ≤ root.val; rw [hnval]; exact hroot
  simp only [hguard, ite_true]
  exact (WP.spec_ok _).mpr rfl

/-- Capacity errors return no partial tree and preserve both published arguments exactly. -/
theorem constructor_tree_dfs_insufficient_workspace {R : Type*} (adapter : tree.Rng R)
    (carrier : topology.Carrier) (root : Usize) (rng : R) (work : spanning_tree.Workspace)
    (hc : CarrierValid carrier) (hroot : root.val < cellCount carrier)
    (hcapacity : work.path.val.length < cellCount carrier ∨
      work.edge_capacity.val < carrier.edges.val.length) :
    WP.spec (spanning_tree.Tree.dfs adapter carrier root rng work)
      (fun output => output = (.Err .InsufficientWorkspace, rng, work)) := by
  have hnonempty : 0 < carrier.offsets.val.length := by have := hc.1; unfold cellCount at this; omega
  unfold spanning_tree.Tree.dfs topology.Carrier.len
  apply WP.spec_bind (Usize.sub_spec (x := alloc.vec.Vec.len carrier.offsets) (y := 1#usize) (by
    simp only [alloc.vec.Vec.len_val, UScalar.ofNatCore_val_eq]
    omega))
  intro n hn
  have hnval : n.val = cellCount carrier := by
    simpa only [alloc.vec.Vec.len_val, UScalar.ofNatCore_val_eq, cellCount] using hn.1
  have hguard : ¬ root ≥ n := by change ¬ n.val ≤ root.val; rw [hnval]; omega
  simp only [hguard, ite_false, topology.Carrier.impl.edges, bind_ok, spanning_tree.Workspace.ensure]
  by_cases hcells : n > alloc.vec.Vec.len work.path
  · simp only [hcells, ite_true, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame]
    exact (WP.spec_ok _).mpr rfl
  · have hedgeGuard : Slice.len (alloc.vec.Vec.deref carrier.edges) > work.edge_capacity := by
      change work.edge_capacity.val < carrier.edges.val.length
      have hnot : ¬ work.path.val.length < cellCount carrier := by simpa only [hnval] using hcells
      omega
    simp only [hcells, hedgeGuard, ite_false, ite_true, core.result.Result.Insts.CoreOpsTry.branch,
      bind_ok, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame]
    exact (WP.spec_ok _).mpr rfl

/-- Every valid carrier and reusable workspace has a total constructor result under legal RNG.
Rejected guards return the original arguments; successful publication is a full carrier tree. -/
theorem constructor_tree_dfs_spec {R : Type*} (adapter : tree.Rng R)
    (hrng : constructorLegalRng adapter) (carrier : topology.Carrier) (root : Usize)
    (rng : R) (work : spanning_tree.Workspace)
    (hc : CarrierValid carrier) (hw : WorkspaceValid work) :
    WP.spec (spanning_tree.Tree.dfs adapter carrier root rng work) (fun output =>
      (∃ published, output.1 = .Ok published ∧ published.root = root ∧
        TreeValid carrier published ∧ WorkspaceValid output.2.2 ∧
        output.2.2.path = work.path ∧ output.2.2.edge_capacity = work.edge_capacity) ∨
      (output = (.Err .InvalidIndex, rng, work) ∧ cellCount carrier ≤ root.val) ∨
      (output = (.Err .InsufficientWorkspace, rng, work) ∧
        root.val < cellCount carrier ∧
        (work.path.val.length < cellCount carrier ∨
          work.edge_capacity.val < carrier.edges.val.length))) := by
  by_cases hr : root.val < cellCount carrier
  · by_cases hcap : cellCount carrier ≤ work.path.val.length ∧
        carrier.edges.val.length ≤ work.edge_capacity.val
    · apply WP.spec_mono (constructor_tree_dfs_accepts adapter hrng carrier root rng work
        hc hw hr hcap.1 hcap.2)
      intro output hout
      exact Or.inl hout
    · have hbad : work.path.val.length < cellCount carrier ∨
          work.edge_capacity.val < carrier.edges.val.length := by omega
      apply WP.spec_mono (constructor_tree_dfs_insufficient_workspace adapter carrier root rng work
        hc hr hbad)
      intro output hout
      exact Or.inr (Or.inr ⟨hout, hr, hbad⟩)
  · have hbad : cellCount carrier ≤ root.val := by omega
    apply WP.spec_mono (constructor_tree_dfs_invalid_root adapter carrier root rng work hc hbad)
    intro output hout
    exact Or.inr (Or.inl ⟨hout, hbad⟩)

end Labyrinth
