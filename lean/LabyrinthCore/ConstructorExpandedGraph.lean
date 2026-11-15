module
public import LabyrinthCore.ConstructorCarrierEdges
public import Mathlib.Combinatorics.SimpleGraph.Basic
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

/-- Undirected simple graph represented by a validated carrier. -/
def constructorCarrierGraph (carrier : topology.Carrier) : SimpleGraph (Fin (cellCount carrier)) where
  Adj u v := u ≠ v ∧
    (carrierEdge carrier u.val v.val ∨ carrierEdge carrier v.val u.val)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem constructor_carrier_edge_symmetric (carrier : topology.Carrier)
    (hc : CarrierValid carrier) {u v : Nat} (edge : carrierEdge carrier u v) :
    carrierEdge carrier v u := by
  obtain ⟨hu, huv⟩ := edge
  obtain ⟨hv, hvu⟩ := (hc.2.2.2.2.1 u hu).2.2 v huv
  exact ⟨hv, hvu⟩

/-- On a valid carrier the graph adjacency is exactly one stored row adjacency; reciprocity
makes the apparently oriented predicate independent of endpoint order. -/
theorem constructor_carrierGraph_adj_iff (carrier : topology.Carrier)
    (hc : CarrierValid carrier) (u v : Fin (cellCount carrier)) :
    (constructorCarrierGraph carrier).Adj u v ↔ carrierEdge carrier u.val v.val := by
  constructor
  · rintro ⟨_, edge | edge⟩
    · exact edge
    · exact constructor_carrier_edge_symmetric carrier hc edge
  · intro edge
    refine ⟨?_, Or.inl edge⟩
    intro heq
    have hval : u.val = v.val := congrArg Fin.val heq
    have hloop : u.val ∈ row carrier u.val := by simpa only [hval] using edge.2
    exact (hc.2.2.2.2.1 u.val edge.1).2.1 hloop

end Labyrinth
