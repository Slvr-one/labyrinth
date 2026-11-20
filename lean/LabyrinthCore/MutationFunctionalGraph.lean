module
public import LabyrinthCore.MutationAttachmentModel
public import LabyrinthCore.MutationGraph
public import LabyrinthCore.ConstructorTreeInterpretation

@[expose] public section

namespace Labyrinth

 def mutationFunctionalGraph (n : Nat) (next : Nat → Nat) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (next u.val = v.val ∨ next v.val = u.val)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

 theorem mutation_functional_graph_adj (n : Nat) (next : Nat → Nat) (u v : Fin n) :
    (mutationFunctionalGraph n next).Adj u v ↔ mutationFunctionalEdge n next u.val v.val := by
  constructor
  · rintro ⟨hne, he⟩
    exact ⟨u.isLt, v.isLt, fun h => hne (Fin.ext h), he⟩
  · rintro ⟨_, _, hne, he⟩
    exact ⟨fun h => hne (congrArg Fin.val h), he⟩

 theorem mutation_functional_cut_acyclic (p : List Nat) (root : Nat)
    (after : Nat → Nat) (touched : Nat → Prop) [DecidablePred touched]
    (ht : RootedTree p root)
    (hparents : ∀ u, u < p.length →
      after u = if touched u then u else parentAt p u) :
    (mutationFunctionalGraph p.length after).IsAcyclic := by
  apply (constructor_rooted_isTree ht).isAcyclic.anti
  intro u v hadj
  refine ⟨hadj.1, ?_⟩
  rcases hadj.2 with huv | hvu
  · rw [hparents u.val u.isLt] at huv
    by_cases hcut : touched u.val
    · have he : u.val = v.val := by simpa only [hcut, ite_true] using huv
      exact (hadj.1 (Fin.ext he)).elim
    · exact Or.inl (by simpa only [hcut, ite_false] using huv)
  · rw [hparents v.val v.isLt] at hvu
    by_cases hcut : touched v.val
    · have he : v.val = u.val := by simpa only [hcut, ite_true] using hvu
      exact (hadj.1 (Fin.ext he.symm)).elim
    · exact Or.inr (by simpa only [hcut, ite_false] using hvu)

 theorem mutation_functional_reachable_root (n : Nat) (next : Nat → Nat)
    (u v : Fin n) (root : Nat) (hfixed : next root = root)
    (hpath : (mutationFunctionalGraph n next).Reachable u v)
    (hreach : ∃ k, next^[k] u.val = root) : ∃ k, next^[k] v.val = root := by
  obtain ⟨walk⟩ := hpath
  revert hreach
  induction walk with
  | nil => exact id
  | @cons a b c hadj walk ih =>
    intro hreach
    apply ih
    rcases hadj.2 with hab | hba
    · obtain ⟨k, hk⟩ := hreach
      cases k with
      | zero =>
        have ha : a.val = root := by
          simpa only [Function.iterate_zero_apply] using hk
        exact ⟨0, by
          simp only [Function.iterate_zero_apply]
          exact hab.symm.trans ((congrArg next ha).trans hfixed)⟩
      | succ k =>
        exact ⟨k, by simpa only [Function.iterate_succ_apply, hab] using hk⟩
    · obtain ⟨k, hk⟩ := hreach
      exact ⟨k + 1, by simpa only [Function.iterate_succ_apply, hba] using hk⟩

 theorem mutation_functional_separate_not_reachable (n : Nat) (next : Nat → Nat)
    (u v : Fin n) (a b : Nat)
    (hu : MutationVirtualRootWitness next n u.val a)
    (hv : MutationVirtualRootWitness next n v.val b) (hne : a ≠ b) :
    ¬ (mutationFunctionalGraph n next).Reachable u v := by
  intro hpath
  obtain ⟨i, _, hi, hfa, _⟩ := hu
  obtain ⟨j, _, hj, hfb, _⟩ := hv
  have hreach := mutation_functional_reachable_root n next u v a hfa hpath ⟨i, hi⟩
  exact hne (mutation_fixed_reach_unique next v.val a b hreach hfa ⟨j, hj⟩ hfb)

 theorem mutation_functional_attach_acyclic (n : Nat) (before after : Nat → Nat)
    (u v : Fin n) (a b : Nat)
    (hu : MutationVirtualRootWitness before n u.val a)
    (hv : MutationVirtualRootWitness before n v.val b) (hne : a ≠ b)
    (hforest : (mutationFunctionalGraph n before).IsAcyclic)
    (hedges : ∀ x y, mutationFunctionalEdge n after x y ↔
      mutationFunctionalEdge n before x y ∨
        (x = u.val ∧ y = v.val) ∨ (y = u.val ∧ x = v.val)) :
    (mutationFunctionalGraph n after).IsAcyclic := by
  have hnot := mutation_functional_separate_not_reachable n before u v a b hu hv hne
  have huv : u ≠ v := by
    intro he
    apply hnot
    subst v
    exact SimpleGraph.Reachable.rfl
  have hgraph : mutationFunctionalGraph n after =
      mutationFunctionalGraph n before ⊔ SimpleGraph.edge u v := by
    ext x y
    rw [mutation_functional_graph_adj, hedges]
    simp only [SimpleGraph.sup_adj, SimpleGraph.edge_adj, mutation_functional_graph_adj,
      Fin.ext_iff]
    constructor
    · rintro (hold | ⟨hxu, hyv⟩ | ⟨hyu, hxv⟩)
      · exact Or.inl hold
      · have huvVal : u.val ≠ v.val := fun he => huv (Fin.ext he)
        exact Or.inr ⟨Or.inl ⟨hxu, hyv⟩, by
          intro hxy
          exact huvVal (hxu.symm.trans ((congrArg Fin.val hxy).trans hyv))⟩
      · have huvVal : u.val ≠ v.val := fun he => huv (Fin.ext he)
        exact Or.inr ⟨Or.inr ⟨hxv, hyu⟩, by
          intro hxy
          exact huvVal (hyu.symm.trans ((congrArg Fin.val hxy).symm.trans hxv))⟩
    · rintro (hold | ⟨hnew, _⟩)
      · exact Or.inl hold
      · rcases hnew with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h.symm)
  rw [hgraph]
  exact hforest.sup_edge_of_not_reachable hnot

end Labyrinth
