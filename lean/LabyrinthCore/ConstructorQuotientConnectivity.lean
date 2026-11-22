module
public import LabyrinthCore.ConstructorContraction
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- Original undirected witnesses make quotient adjacency symmetric without deduplication. -/
theorem constructor_quotient_edge_symm (carrier : topology.Carrier) (label : Nat → Nat)
    (hc : CarrierValid carrier) {a b : Nat}
    (h : constructorQuotientEdge carrier label a b) :
    constructorQuotientEdge carrier label b a := by
  obtain ⟨hne, u, v, hedge, hu, hv⟩ := h
  have hvbound := ((hc.2.2.2.2.1 u hedge.1).2.2 v hedge.2).1
  have hreverse := ((hc.2.2.2.2.1 u hedge.1).2.2 v hedge.2).2
  exact ⟨Ne.symm hne, v, u, ⟨hvbound, hreverse⟩, hv, hu⟩

/-- Reverse a quotient walk using its actual original carrier-edge witnesses. -/
theorem constructor_quotient_path_reverse (carrier : topology.Carrier) (label : Nat → Nat)
    (hc : CarrierValid carrier) {a b : Nat}
    (h : Relation.ReflTransGen (constructorQuotientEdge carrier label) a b) :
    Relation.ReflTransGen (constructorQuotientEdge carrier label) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail current next _ hedge ih =>
    exact (Relation.ReflTransGen.single
      (constructor_quotient_edge_symm carrier label hc hedge)).trans ih

/-- Any requested original root reaches every quotient class in the carrier image. -/
theorem constructor_quotient_connected_from (carrier : topology.Carrier) (label : Nat → Nat)
    (hc : CarrierValid carrier) (root vertex : Nat)
    (hroot : root < cellCount carrier) (hvertex : vertex < cellCount carrier) :
    Relation.ReflTransGen (constructorQuotientEdge carrier label) (label root) (label vertex) := by
  exact (constructor_quotient_path_reverse carrier label hc
    (constructor_quotient_connected carrier label hc root hroot)).trans
      (constructor_quotient_connected carrier label hc vertex hvertex)

/-- Dense component labels transfer original connectivity to every quotient ID. -/
theorem constructor_quotient_dense_connected (carrier : topology.Carrier)
    (label : Nat → Nat) (count : Nat) (hc : CarrierValid carrier)
    (hdense : ∀ component, component < count →
      ∃ vertex, vertex < cellCount carrier ∧ label vertex = component)
    (root : Nat) (hroot : root < cellCount carrier) (component : Nat)
    (hcomponent : component < count) :
    Relation.ReflTransGen (constructorQuotientEdge carrier label) (label root) component := by
  obtain ⟨vertex, hv, he⟩ := hdense component hcomponent
  simpa only [he] using constructor_quotient_connected_from carrier label hc root vertex hroot hv

end Labyrinth
