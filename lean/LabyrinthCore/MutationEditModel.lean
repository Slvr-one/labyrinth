module
public import LabyrinthCore.MutationBatchAttach
public import LabyrinthCore.MutationCommit
public import LabyrinthCore.MutationCut

@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

def mutationAddition (add : Slice topology.Edge) (u v : Nat) : Prop :=
  ∃ edge ∈ add.val,
    (edge.u.val = u ∧ edge.v.val = v) ∨ (edge.v.val = u ∧ edge.u.val = v)

def MutationEditedEdge (before : List Nat) (remove add : Slice topology.Edge)
    (u v : Nat) : Prop :=
  (parentEdge before u v ∧ ¬ mutationRemoval remove u v) ∨ mutationAddition add u v

theorem mutation_added_before_full (add : Slice topology.Edge) (u v : Nat) :
    mutationAddedBefore add add.val.length u v ↔ mutationAddition add u v := by
  constructor
  · rintro ⟨j, _, edge, hedge, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩
    · exact ⟨edge, List.mem_of_getElem? hedge, Or.inl ⟨hu.symm, hv.symm⟩⟩
    · exact ⟨edge, List.mem_of_getElem? hedge, Or.inr ⟨hu.symm, hv.symm⟩⟩
  · rintro ⟨edge, hedge, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩
    · obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hedge
      exact ⟨j, hj, edge, by simp [hj, hget], Or.inl ⟨hu.symm, hv.symm⟩⟩
    · obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hedge
      exact ⟨j, hj, edge, by simp [hj, hget], Or.inr ⟨hu.symm, hv.symm⟩⟩
/-- A concrete parent vector whose parent function is `next` has exactly the
functional undirected edge relation. -/
theorem mutation_parent_edge_functional_exact (p : List Nat) (n : Nat)
    (next : Nat → Nat) (hlen : p.length = n)
    (hnext : ∀ u, u < n → parentAt p u = next u) :
    ∀ u v, parentEdge p u v ↔ mutationFunctionalEdge n next u v := by
  intro u v
  by_cases hu : u < n
  · by_cases hv : v < n
    · by_cases hne : u ≠ v
      · have hup : u < p.length := by omega
        have hvp : v < p.length := by omega
        have hedge : parentEdge p u v ↔ parentAt p u = v ∨ parentAt p v = u := by
          simp [parentEdge, parentAt, hup, hvp, hne]
        rw [hedge, hnext u hu, hnext v hv]
        simp only [mutationFunctionalEdge, hu, hv, true_and]
        exact ⟨fun h => ⟨hne, h⟩, And.right⟩
      · have he : u = v := Classical.not_not.mp hne
        simp [he, parentEdge, mutationFunctionalEdge]
    · have hvp : ¬ v < p.length := by omega
      simp [parentEdge, mutationFunctionalEdge, hv, hvp]
  · have hup : ¬ u < p.length := by omega
    simp [parentEdge, mutationFunctionalEdge, hu, hup]

/-- Cutting the requested parent edges in the sparse overlay removes exactly
those undirected edges and no others. -/
theorem mutation_cut_functional_edges_exact
    (published : alloc.vec.Vec Usize) (after : Nat → Nat) (root : Nat)
    (remove : Slice topology.Edge)
    (ht : RootedTree (published.val.map (·.val)) root)
    (hremove : ∀ edge ∈ remove.val,
      parentEdge (published.val.map (·.val)) edge.u.val edge.v.val)
    (hparents : ∀ u, u < published.val.length → after u =
      if ∃ edge ∈ remove.val, mutationCutChild published edge = u then u
      else parentAt (published.val.map (·.val)) u) :
    ∀ u v, mutationFunctionalEdge published.val.length after u v ↔
      parentEdge (published.val.map (·.val)) u v ∧ ¬ mutationRemoval remove u v := by
  classical
  have hdir : ∀ u v, u < published.val.length → u ≠ v →
      (after u = v ↔ parentAt (published.val.map (·.val)) u = v ∧
        ¬ mutationRemoval remove u v) := by
    intro u v hu hne
    rw [hparents u hu]
    by_cases htouched : ∃ edge ∈ remove.val, mutationCutChild published edge = u
    · simp only [htouched, ite_true]
      constructor
      · intro he
        exact (hne he).elim
      · rintro ⟨hparent, hnot⟩
        exact (hnot ((mutation_cut_child_membership published root u v remove ht hremove
          hu hne hparent).mp htouched)).elim
    · simp only [htouched, ite_false]
      constructor
      · intro hparent
        refine ⟨hparent, ?_⟩
        intro hremoved
        exact htouched ((mutation_cut_child_membership published root u v remove ht hremove
          hu hne hparent).mpr hremoved)
      · exact And.left
  intro u v
  by_cases hu : u < published.val.length
  · by_cases hv : v < published.val.length
    · by_cases hne : u ≠ v
      · rw [show mutationFunctionalEdge published.val.length after u v ↔
              after u = v ∨ after v = u by simp [mutationFunctionalEdge, hu, hv, hne],
            show parentEdge (published.val.map (·.val)) u v ↔
              parentAt (published.val.map (·.val)) u = v ∨
                parentAt (published.val.map (·.val)) v = u by
              simp [parentEdge, parentAt, hu, hv, hne],
            hdir u v hu hne, hdir v u hv hne.symm,
            ← mutation_removal_symmetric remove u v]
        tauto
      · have he : u = v := Classical.not_not.mp hne
        simp [he, mutationFunctionalEdge, parentEdge]
    · simp [mutationFunctionalEdge, parentEdge, hv]
  · simp [mutationFunctionalEdge, parentEdge, hu]

end Labyrinth
