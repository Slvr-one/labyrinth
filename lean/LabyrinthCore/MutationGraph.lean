module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

public section

namespace Labyrinth

 theorem mutation_forest_full_card_isTree {V : Type*} [Fintype V] [Nonempty V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj]
    (hforest : graph.IsAcyclic)
    (hcard : graph.edgeFinset.card + 1 = Fintype.card V) : graph.IsTree := by
  classical
  obtain ⟨tree, hsub, _, htree⟩ :=
    SimpleGraph.Connected.exists_isTree_le_of_le_of_isAcyclic
      (G := (⊤ : SimpleGraph V)) (H := graph) SimpleGraph.connected_top le_top hforest
  have htreecard := htree.card_edgeFinset
  have heq : graph.edgeFinset = tree.edgeFinset :=
    Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hsub) (by omega)
  have hgraph : graph = tree := SimpleGraph.edgeFinset_inj.mp heq
  exact hgraph.symm ▸ htree

 theorem mutation_batch_edge_card {E : Type*} [DecidableEq E]
    (old remove add : Finset E)
    (hremove : remove ⊆ old) (hdisjoint : Disjoint (old \ remove) add)
    (hcounts : remove.card = add.card) :
    ((old \ remove) ∪ add).card = old.card := by
  rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_sdiff_of_subset hremove]
  have hle := Finset.card_le_card hremove
  omega

 theorem mutation_batch_graph_connected {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (old final : SimpleGraph V) [DecidableRel old.Adj] [DecidableRel final.Adj]
    (remove add : Finset (Sym2 V))
    (hold : old.IsTree)
    (hremove : remove ⊆ old.edgeFinset)
    (hdisjoint : Disjoint (old.edgeFinset \ remove) add)
    (hcounts : remove.card = add.card)
    (hedges : final.edgeFinset = (old.edgeFinset \ remove) ∪ add)
    (hforest : final.IsAcyclic) : final.IsTree := by
  apply mutation_forest_full_card_isTree final hforest
  rw [hedges, mutation_batch_edge_card _ _ _ hremove hdisjoint hcounts]
  exact hold.card_edgeFinset

end Labyrinth
