module
public import LabyrinthCore.ConstructorUnion
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- The component map after linking one distinct root below another. -/
def constructorMergedComponent (component : Usize → Usize) (winner loser node : Usize) : Usize :=
  if component node = loser then winner else component node

/-- Increasing every rank in the losing class preserves its internal strict order. -/
def constructorMergedRank (rank : Usize → Nat) (component : Usize → Usize)
    (winner loser node : Usize) : Nat :=
  if component node = loser then rank node + rank winner + 1 else rank node

/-- A single generated union update preserves representative termination and exact root labels. -/
theorem constructor_union_preserves (links : Slice Usize) (rank : Usize → Nat)
    (component : Usize → Usize) (winner loser : Usize)
    (hlinks : constructorRankedLinks links rank)
    (hlabels : constructorComponentLabels links component)
    (hw : winner.val < links.val.length) (hl : loser.val < links.val.length)
    (hwroot : links.val[winner.val]? = some winner)
    (hlroot : links.val[loser.val]? = some loser) (hne : winner ≠ loser) :
    constructorRankedLinks (links.set loser winner)
      (constructorMergedRank rank component winner loser) ∧
    constructorComponentLabels (links.set loser winner)
      (constructorMergedComponent component winner loser) := by
  have hwlabel := hlabels.2 winner hw hwroot
  have hllabel := hlabels.2 loser hl hlroot
  constructor
  · intro node parent hnode hparent
    have hbound : node.val < links.val.length := by simpa [Slice.set] using hnode
    by_cases he : node = loser
    · subst node
      have hp : parent = winner := by
        have : some winner = some parent := by simpa [Slice.set, hl] using hparent
        exact Option.some.inj this.symm
      subst parent
      refine ⟨by simpa [Slice.set] using hw, ?_⟩
      intro _
      simp only [constructorMergedRank, hwlabel, hllabel, hne, ite_false, ite_true]
      omega
    · have hnval : node.val ≠ loser.val := fun h => he ((UScalar.eq_equiv _ _).mpr h)
      have hp : links.val[node.val]? = some parent := by
        simpa [Slice.set, Slice.setAtNat, hnval, Ne.symm hnval] using hparent
      obtain ⟨hb, hr⟩ := hlinks node parent hbound hp
      refine ⟨by simpa [Slice.set] using hb, ?_⟩
      intro hpn
      have hc := hlabels.1 node parent hbound hp
      have hlt := hr hpn
      unfold constructorMergedRank
      rw [hc]
      split <;> omega
  · constructor
    · intro node parent hnode hparent
      have hbound : node.val < links.val.length := by simpa [Slice.set] using hnode
      by_cases he : node = loser
      · subst node
        have hp : parent = winner := by
          have : some winner = some parent := by simpa [Slice.set, hl] using hparent
          exact Option.some.inj this.symm
        subst parent
        simp [constructorMergedComponent, hwlabel, hllabel, hne]
      · have hnval : node.val ≠ loser.val := fun h => he ((UScalar.eq_equiv _ _).mpr h)
        have hp : links.val[node.val]? = some parent := by
          simpa [Slice.set, Slice.setAtNat, hnval, Ne.symm hnval] using hparent
        simp only [constructorMergedComponent, hlabels.1 node parent hbound hp]
    · intro node hnode hfixed
      have hbound : node.val < links.val.length := by simpa [Slice.set] using hnode
      have he : node ≠ loser := by
        intro he
        subst node
        have : some winner = some loser := by simpa [Slice.set, hl] using hfixed
        exact hne (Option.some.inj this)
      have hnval : node.val ≠ loser.val := fun h => he ((UScalar.eq_equiv _ _).mpr h)
      have hp : links.val[node.val]? = some node := by
        simpa [Slice.set, Slice.setAtNat, hnval, Ne.symm hnval] using hfixed
      simp [constructorMergedComponent, hlabels.2 node hbound hp, he]

/-- Joining two classes identifies exactly those classes, without identifying any third class. -/
theorem constructor_merged_component_eq_iff (component : Usize → Usize)
    (winner loser u v : Usize) :
    constructorMergedComponent component winner loser u =
      constructorMergedComponent component winner loser v ↔
    component u = component v ∨
      (component u = winner ∧ component v = loser) ∨
      (component u = loser ∧ component v = winner) := by
  unfold constructorMergedComponent
  by_cases hu : component u = loser <;> by_cases hv : component v = loser <;>
    simp_all [eq_comm]

/-- A noncarrier required edge is rejected before either mutable slice is touched. -/
theorem constructor_join_required_rejects_edge (carrier : topology.Carrier)
    (links sizes : Slice Usize) (edge : topology.Edge) (hcarrier : CarrierValid carrier)
    (hedge : ¬ carrierEdge carrier edge.u.val edge.v.val) :
    WP.spec (spanning_tree.join_required carrier links sizes edge) (fun output =>
      output = (.Err topology.Error.InvalidForest, links, sizes)) := by
  unfold spanning_tree.join_required
  apply WP.spec_bind (mutation_carrier_contains_total carrier edge hcarrier)
  intro contains hc
  have hf : contains = false := by
    cases contains with
    | false => rfl
    | true => exact False.elim (hedge (hc.mp rfl))
  simp only [hf, Bool.false_eq_true, ite_false]
  exact (WP.spec_ok _).mpr rfl

/-- An already connected required edge is rejected with both slices unchanged. -/
theorem constructor_join_required_rejects_cycle (carrier : topology.Carrier)
    (links sizes : Slice Usize) (edge : topology.Edge) (rank : Usize → Nat)
    (component : Usize → Usize) (hcarrier : CarrierValid carrier)
    (hedge : carrierEdge carrier edge.u.val edge.v.val)
    (hlen : links.val.length = cellCount carrier)
    (hlinks : constructorRankedLinks links rank)
    (hlabels : constructorComponentLabels links component)
    (heq : component edge.u = component edge.v) :
    WP.spec (spanning_tree.join_required carrier links sizes edge) (fun output =>
      output = (.Err topology.Error.InvalidForest, links, sizes)) := by
  unfold spanning_tree.join_required
  apply WP.spec_bind (mutation_carrier_contains_total carrier edge hcarrier)
  intro contains hc
  have ht := hc.mpr hedge
  simp only [ht, ite_true]
  apply WP.spec_bind (constructor_representative_component_spec links rank component hlinks hlabels
    edge.u (by rw [hlen]; exact hedge.1))
  intro u hu
  apply WP.spec_bind (constructor_representative_component_spec links rank component hlinks hlabels
    edge.v (by
      rw [hlen]
      exact ((hcarrier.2.2.2.2.1 edge.u.val hedge.1).2.2 edge.v.val hedge.2).1))
  intro v hv
  have huv : u = v := hu.1.trans (heq.trans hv.1.symm)
  simp only [huv, ite_true]
  exact (WP.spec_ok _).mpr rfl

end Labyrinth
