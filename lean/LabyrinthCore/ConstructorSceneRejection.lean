module
public import LabyrinthCore.ConstructorSceneValidation
public import LabyrinthCore.ConstructorSceneReject
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- A noncarrier edge after a valid required prefix is the exact first rejected slot. -/
theorem constructor_required_noncarrier_first_invalid (carrier : topology.Carrier)
    (required : Slice topology.Edge) (slot : Nat) (edge : topology.Edge)
    (hslot : slot < required.val.length)
    (hprefix : ConstructorRequiredForestPrefix carrier required slot)
    (hlookup : required.val[slot]? = some edge)
    (hbad : ¬ carrierEdge carrier edge.u.val edge.v.val) :
    ConstructorRequiredFirstInvalid carrier required slot :=
  ⟨hslot, hprefix, edge, hlookup, Or.inl hbad⟩

/-- A carrier edge closing an earlier required path is the exact first rejected slot. -/
theorem constructor_required_cycle_first_invalid (carrier : topology.Carrier)
    (required : Slice topology.Edge) (slot : Nat) (edge : topology.Edge)
    (hslot : slot < required.val.length)
    (hprefix : ConstructorRequiredForestPrefix carrier required slot)
    (hlookup : required.val[slot]? = some edge)
    (hcycle : Relation.ReflTransGen (constructorRequiredPrefixArc required slot)
      edge.u edge.v) :
    ConstructorRequiredFirstInvalid carrier required slot :=
  ⟨hslot, hprefix, edge, hlookup, Or.inr hcycle⟩

/-- Repeating an earlier required edge is a concrete cycle rejection, not a separate assumption. -/
theorem constructor_required_duplicate_first_invalid (carrier : topology.Carrier)
    (required : Slice topology.Edge) (earlier slot : Nat) (edge : topology.Edge)
    (hslot : slot < required.val.length) (hearlier : earlier < slot)
    (hprefix : ConstructorRequiredForestPrefix carrier required slot)
    (hcurrent : required.val[slot]? = some edge)
    (hprevious : required.val[earlier]? = some edge) :
    ConstructorRequiredFirstInvalid carrier required slot := by
  apply constructor_required_cycle_first_invalid carrier required slot edge hslot hprefix hcurrent
  exact Relation.ReflTransGen.single
    ⟨earlier, hearlier, edge, hprevious, Or.inl ⟨rfl, rfl⟩⟩

/-- Repeating an earlier undirected edge in the opposite orientation closes the same path. -/
theorem constructor_required_reverse_duplicate_first_invalid (carrier : topology.Carrier)
    (required : Slice topology.Edge) (earlier slot : Nat)
    (edge previous : topology.Edge) (hslot : slot < required.val.length)
    (hearlier : earlier < slot)
    (hprefix : ConstructorRequiredForestPrefix carrier required slot)
    (hcurrent : required.val[slot]? = some edge)
    (hprevious : required.val[earlier]? = some previous)
    (hu : edge.u = previous.v) (hv : edge.v = previous.u) :
    ConstructorRequiredFirstInvalid carrier required slot := by
  apply constructor_required_cycle_first_invalid carrier required slot edge hslot hprefix hcurrent
  exact Relation.ReflTransGen.single
    ⟨earlier, hearlier, previous, hprevious, Or.inr ⟨hu, hv⟩⟩

/-- Once the root, workspace and count guards pass, failure of the genuine required-forest
predicate is rejected by the actual constructor before quotient construction or RNG use.
The frame is exactly the source frame: allocations are local, while caller RNG/workspace remain
bit-for-bit the original values. -/
theorem constructor_scene_rejects_invalid_forest {R : Type _} (adapter : tree.Rng R)
    (carrier : topology.Carrier) (required : Slice topology.Edge) (root : Usize)
    (rng : R) (work : spanning_tree.Workspace) (hc : CarrierValid carrier)
    (hroot : root.val < cellCount carrier)
    (hcapacity : cellCount carrier ≤ work.path.val.length ∧
      (alloc.vec.Vec.deref carrier.edges).val.length ≤ work.edge_capacity.val)
    (hcount : required.val.length < cellCount carrier)
    (hforest : ¬ ConstructorRequiredForest carrier required) :
    WP.spec (spanning_tree.Tree.scene_dfs adapter carrier required root rng work)
      (fun output => output = (.Err topology.Error.InvalidForest, rng, work)) := by
  unfold spanning_tree.Tree.scene_dfs
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
  have hcountGuard : ¬ Slice.len required >= n := by
    change ¬ n.val ≤ required.val.length
    omega
  simp only [hcountGuard, ite_false]
  apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize n rfl)
  intro links hlinks
  apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize 1#usize n rfl)
  intro sizes hsizes
  have hlinksCapacity : n.val ≤ links.val.length := by
    rw [hlinks.1, List.length_replicate]
  apply WP.spec_bind (constructor_scene_links_spec n links hlinksCapacity)
  intro initialized hinitialized
  have hinitializedLength : initialized.val.length = cellCount carrier := by
    rw [hinitialized.1, hlinks.1, List.length_replicate, hn]
  have hsizesLength : sizes.val.length = initialized.val.length := by
    simp only [hsizes.1, hinitialized.1, hlinks.1, List.length_replicate]
  have hones : ∀ node : Usize, node.val < n.val →
      sizes.val[node.val]? = some 1#usize := by
    intro node hnode
    simp [hsizes.1, hnode]
  have hinitialState : ConstructorSceneForestState initialized.val required 0 initialized sizes :=
    constructor_scene_initial_forest_state n required initialized sizes
      (by omega) (fun node hnode => hinitialized.2.1 node hnode)
      (by rw [hsizes.1, List.length_replicate]) hones
  have hwidth : initialized.val.length ≤ Usize.max := by
    rw [hinitialized.1, hlinks.1, List.length_replicate]
    scalar_tac
  apply WP.spec_bind (constructor_scene_forest_loop_total carrier required initialized.val
    initialized sizes 0#usize hc hwidth hinitializedLength hsizesLength (by simp)
    (constructor_required_forest_prefix_zero carrier required) hinitialState)
  rintro ⟨finalLinks, status⟩ hvalidation
  have hstatus : status = .Err topology.Error.InvalidForest := hvalidation.2.2.1.mpr hforest
  simp [hstatus,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- The rejection theorem specialized to a witnessed first invalid slot. -/
theorem constructor_scene_rejects_first_invalid {R : Type _} (adapter : tree.Rng R)
    (carrier : topology.Carrier) (required : Slice topology.Edge) (root : Usize)
    (rng : R) (work : spanning_tree.Workspace) (hc : CarrierValid carrier)
    (hroot : root.val < cellCount carrier)
    (hcapacity : cellCount carrier ≤ work.path.val.length ∧
      (alloc.vec.Vec.deref carrier.edges).val.length ≤ work.edge_capacity.val)
    (hcount : required.val.length < cellCount carrier) (slot : Nat)
    (hinvalid : ConstructorRequiredFirstInvalid carrier required slot) :
    WP.spec (spanning_tree.Tree.scene_dfs adapter carrier required root rng work)
      (fun output => output = (.Err topology.Error.InvalidForest, rng, work)) :=
  constructor_scene_rejects_invalid_forest adapter carrier required root rng work hc hroot
    hcapacity hcount (constructor_required_first_invalid_not_forest carrier required slot hinvalid)

end Labyrinth
