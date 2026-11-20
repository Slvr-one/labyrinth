module
public import LabyrinthCore.Model
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- Union-find links point inside storage and descend a mathematical rank off their roots. -/
def constructorRankedLinks (links : Slice Usize) (rank : Usize → Nat) : Prop :=
  ∀ (node parent : Usize), node.val < links.val.length →
    links.val[node.val]? = some parent →
    parent.val < links.val.length ∧ (parent ≠ node → rank parent < rank node)

/-- Actual representative search terminates and returns a reachable fixed point of the links. -/
theorem constructor_representative_spec (links : Slice Usize) (rank : Usize → Nat)
    (hlinks : constructorRankedLinks links rank) (start : Usize)
    (hstart : start.val < links.val.length) :
    WP.spec (spanning_tree.representative links start) (fun root =>
      root.val < links.val.length ∧ links.val[root.val]? = some root ∧
      Relation.ReflTransGen (fun u v : Usize => links.val[u.val]? = some v) start root) := by
  let invariant : Usize → Prop := fun current =>
    current.val < links.val.length ∧
    Relation.ReflTransGen (fun u v : Usize => links.val[u.val]? = some v) start current
  unfold spanning_tree.representative spanning_tree.representative_loop
  apply loop.spec_decr_nat rank invariant
  · intro current hi
    obtain ⟨hbound, hpath⟩ := hi
    unfold spanning_tree.representative_loop.body
    apply WP.spec_bind (Slice.index_usize_spec links current hbound)
    intro parent hp
    have hget : links.val[current.val]? = some parent := by
      rw [List.getElem?_eq_getElem hbound, hp]
    obtain ⟨hparent, hdecreases⟩ := hlinks current parent hbound hget
    by_cases he : parent = current
    · simp only [bne_iff_ne, ne_eq, he, not_true_eq_false, ite_false]
      apply (WP.spec_ok _).mpr
      exact ⟨hbound, hget.trans (congrArg some he), hpath⟩
    · simp only [bne_iff_ne, ne_eq, he, not_false_eq_true, ite_true]
      apply (WP.spec_ok _).mpr
      exact ⟨⟨hparent, hpath.tail hget⟩, hdecreases he⟩
  · exact ⟨hstart, Relation.ReflTransGen.refl⟩

/-- Every quotient adjacency carries an original carrier-edge witness. -/
def constructorQuotientEdge (carrier : topology.Carrier) (label : Nat → Nat)
    (a b : Nat) : Prop :=
  a ≠ b ∧ ∃ u v, carrierEdge carrier u v ∧ label u = a ∧ label v = b

/-- Collapsing any vertex classes preserves carrier connectivity on the quotient's image. -/
theorem constructor_quotient_connected (carrier : topology.Carrier) (label : Nat → Nat)
    (hcarrier : CarrierValid carrier) (v : Nat) (hv : v < cellCount carrier) :
    Relation.ReflTransGen (constructorQuotientEdge carrier label) (label 0) (label v) := by
  have hpath := hcarrier.2.2.2.2.2.1 v hv
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | @tail w z path edge ih =>
    specialize ih edge.1
    by_cases he : label w = label z
    · simpa only [he] using ih
    · exact ih.tail ⟨he, w, z, edge, rfl, rfl⟩

end Labyrinth
