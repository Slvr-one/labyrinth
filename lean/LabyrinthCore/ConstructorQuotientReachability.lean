module
public import LabyrinthCore.ConstructorQuotientConnectivity
public import LabyrinthCore.ConstructorDepthFirstModel
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

/-- A complete original-edge slot realization transfers quotient walks to the actual raw CSR.
No symmetry, simplicity, or duplicate removal is imposed on the slot representation. -/
theorem constructor_quotient_walk_to_csr (carrier : topology.Carrier) (label : Nat → Nat)
    (offsets neighbors : Slice Usize)
    (hslots : ∀ u v, carrierEdge carrier u v → label u ≠ label v →
      constructorDFSArc offsets neighbors (label u) (label v))
    {a b : Nat} (path : Relation.ReflTransGen (constructorQuotientEdge carrier label) a b) :
    Relation.ReflTransGen (constructorDFSArc offsets neighbors) a b := by
  induction path with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge ih =>
    obtain ⟨hne, u, v, he, hu, hv⟩ := edge
    have hne' : label u ≠ label v := by simpa only [hu, hv] using hne
    exact ih.tail (by simpa only [hu, hv] using hslots u v he hne')

/-- Dense component IDs plus original crossing-edge slots supply the exact generic DFS reachability field. -/
theorem constructor_quotient_csr_reachable (carrier : topology.Carrier) (label : Nat → Nat)
    (offsets neighbors : Slice Usize) (hc : CarrierValid carrier)
    (hdense : ∀ id, id < constructorDFSVertexCount offsets →
      ∃ vertex, vertex < cellCount carrier ∧ label vertex = id)
    (hslots : ∀ u v, carrierEdge carrier u v → label u ≠ label v →
      constructorDFSArc offsets neighbors (label u) (label v))
    (root : Nat) (hroot : root < cellCount carrier) :
    ∀ id, id < constructorDFSVertexCount offsets →
      Relation.ReflTransGen (constructorDFSArc offsets neighbors) (label root) id := by
  intro id hid
  apply constructor_quotient_walk_to_csr carrier label offsets neighbors hslots
  exact constructor_quotient_dense_connected carrier label (constructorDFSVertexCount offsets)
    hc hdense root hroot id hid

/-- Structural CSR facts and the proved witness transfer assemble the checked DFS input interface. -/
theorem constructor_quotient_dfs_input (carrier : topology.Carrier) (label : Nat → Nat)
    (offsets neighbors : Slice Usize) (hc : CarrierValid carrier)
    (hn : 0 < constructorDFSVertexCount offsets)
    (hfirst : constructorDFSOffset offsets 0 = 0)
    (hlast : constructorDFSOffset offsets (constructorDFSVertexCount offsets) = neighbors.val.length)
    (hordered : ∀ v, v < constructorDFSVertexCount offsets →
      constructorDFSOffset offsets v ≤ constructorDFSOffset offsets (v + 1))
    (hbounded : ∀ value ∈ neighbors.val, value.val < constructorDFSVertexCount offsets)
    (hlabels : ∀ vertex, vertex < cellCount carrier → label vertex < constructorDFSVertexCount offsets)
    (hdense : ∀ id, id < constructorDFSVertexCount offsets →
      ∃ vertex, vertex < cellCount carrier ∧ label vertex = id)
    (hslots : ∀ u v, carrierEdge carrier u v → label u ≠ label v →
      constructorDFSArc offsets neighbors (label u) (label v))
    (root : Nat) (hroot : root < cellCount carrier) :
    ConstructorDFSInput offsets neighbors (label root) := by
  exact ⟨hn, hlabels root hroot, hfirst, hlast, hordered, hbounded,
    constructor_quotient_csr_reachable carrier label offsets neighbors hc hdense hslots root hroot⟩

end Labyrinth
