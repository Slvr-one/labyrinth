module
public import LabyrinthCore.MutationValidate
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- The actual scene wrapper rejects an out-of-range root before touching RNG or workspace. -/
theorem constructor_scene_rejects_root {R : Type _} (adapter : tree.Rng R)
    (carrier : topology.Carrier) (required : Slice topology.Edge) (root : Usize)
    (rng : R) (work : spanning_tree.Workspace) (hc : CarrierValid carrier)
    (hroot : cellCount carrier ≤ root.val) :
    WP.spec (spanning_tree.Tree.scene_dfs adapter carrier required root rng work)
      (fun output => output = (.Err topology.Error.InvalidIndex, rng, work)) := by
  unfold spanning_tree.Tree.scene_dfs
  apply WP.spec_bind (mutation_carrier_len_total carrier hc)
  intro n hn
  have hbad : root >= n := by
    change n.val ≤ root.val
    omega
  simp only [hbad, ite_true]
  exact (WP.spec_ok _).mpr rfl

/-- Insufficient reusable storage is rejected without consuming choices or changing workspace. -/
theorem constructor_scene_rejects_workspace {R : Type _} (adapter : tree.Rng R)
    (carrier : topology.Carrier) (required : Slice topology.Edge) (root : Usize)
    (rng : R) (work : spanning_tree.Workspace) (hc : CarrierValid carrier)
    (hroot : root.val < cellCount carrier)
    (hcapacity : ¬ (cellCount carrier ≤ work.path.val.length ∧
      (alloc.vec.Vec.deref carrier.edges).val.length ≤ work.edge_capacity.val)) :
    WP.spec (spanning_tree.Tree.scene_dfs adapter carrier required root rng work)
      (fun output => output = (.Err topology.Error.InsufficientWorkspace, rng, work)) := by
  unfold spanning_tree.Tree.scene_dfs
  apply WP.spec_bind (mutation_carrier_len_total carrier hc)
  intro n hn
  have hbad : ¬ root >= n := by
    change ¬ n.val ≤ root.val
    omega
  simp only [hbad, ite_false, topology.Carrier.impl.edges, bind_ok]
  apply WP.spec_bind (mutation_workspace_ensure_total work n
    (Slice.len (alloc.vec.Vec.deref carrier.edges)))
  intro status hs
  have herr : status = .Err topology.Error.InsufficientWorkspace := by
    rw [hs]
    have hnot : ¬ (n.val ≤ work.path.val.length ∧
        Slice.len (alloc.vec.Vec.deref carrier.edges) ≤ work.edge_capacity) := by
      simpa only [hn, UScalar.le_equiv, Slice.len_val] using hcapacity
    simp only [hnot, ite_false]
  simp [herr, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- A forest cannot contain as many edges as vertices; this guard precedes all allocation. -/
theorem constructor_scene_rejects_required_length {R : Type _} (adapter : tree.Rng R)
    (carrier : topology.Carrier) (required : Slice topology.Edge) (root : Usize)
    (rng : R) (work : spanning_tree.Workspace) (hc : CarrierValid carrier)
    (hroot : root.val < cellCount carrier)
    (hcapacity : cellCount carrier ≤ work.path.val.length ∧
      (alloc.vec.Vec.deref carrier.edges).val.length ≤ work.edge_capacity.val)
    (hrequired : cellCount carrier ≤ required.val.length) :
    WP.spec (spanning_tree.Tree.scene_dfs adapter carrier required root rng work)
      (fun output => output = (.Err topology.Error.InvalidForest, rng, work)) := by
  unfold spanning_tree.Tree.scene_dfs
  apply WP.spec_bind (mutation_carrier_len_total carrier hc)
  intro n hn
  have hbad : ¬ root >= n := by
    change ¬ n.val ≤ root.val
    omega
  simp only [hbad, ite_false, topology.Carrier.impl.edges, bind_ok]
  apply WP.spec_bind (mutation_workspace_ensure_total work n
    (Slice.len (alloc.vec.Vec.deref carrier.edges)))
  intro status hs
  have hok : status = .Ok () := by
    rw [hs]
    have hyes : n.val ≤ work.path.val.length ∧
        Slice.len (alloc.vec.Vec.deref carrier.edges) ≤ work.edge_capacity := by
      simpa only [hn, UScalar.le_equiv, Slice.len_val] using hcapacity
    exact ite_eq_left hyes
  have hmany : Slice.len required >= n := by
    change n.val ≤ (Slice.len required).val
    simpa only [hn, Slice.len_val] using hrequired
  simp [hok, hmany, core.result.Result.Insts.CoreOpsTry.branch]

end Labyrinth
