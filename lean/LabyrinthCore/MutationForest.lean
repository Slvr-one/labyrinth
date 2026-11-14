module
public import LabyrinthCore.MutationVirtualRoot
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace Labyrinth

 def MutationFunctionalForest (n : Nat) (next : Nat → Nat) : Prop :=
  ∀ start, start < n → ∃ root, MutationVirtualRootWitness next n start root

 theorem mutation_functional_first_reach (next : Nat → Nat) (n start root : Nat)
    (hbounded : ∀ u, u < n → next u < n) (hstart : start < n)
    (hexists : ∃ k, next^[k] start = root) :
    ∃ k, k < n ∧ next^[k] start = root ∧
      (∀ j, j < k → next^[j] start ≠ root) ∧
      (∀ i j, i ≤ k → j ≤ k → next^[i] start = next^[j] start → i = j) := by
  classical
  let k := Nat.find hexists
  have hk : next^[k] start = root := Nat.find_spec hexists
  have hfirst : ∀ j, j < k → next^[j] start ≠ root := fun j hj => Nat.find_min hexists hj
  have hdistinct : ∀ i j, i < j → j ≤ k → next^[i] start ≠ next^[j] start := by
    intro i j hij hj heq
    apply hfirst (k - j + i) (by omega)
    rw [Function.iterate_add_apply, heq, ← Function.iterate_add_apply, Nat.sub_add_cancel hj]
    exact hk
  have hiterBound : ∀ i, next^[i] start < n := by
    intro i
    induction i with
    | zero => exact hstart
    | succ i ih => simpa only [Function.iterate_succ_apply'] using hbounded _ ih
  let f : Fin (k + 1) → Fin n := fun i => ⟨next^[i.val] start, hiterBound i.val⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have he : next^[a.val] start = next^[b.val] start := congrArg Fin.val hab
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact hdistinct a.val b.val hlt (by omega) he
    · exact hdistinct b.val a.val hgt (by omega) he.symm
  have hcard := Fintype.card_le_of_injective f hinj
  have hklt : k < n := by simpa using hcard
  refine ⟨k, hklt, hk, hfirst, ?_⟩
  intro i j hi hj heq
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact hdistinct i j hlt hj heq
  · exact hdistinct j i hgt hi heq.symm

 theorem mutation_functional_forest_of_reaches (next : Nat → Nat) (n : Nat)
    (hbounded : ∀ u, u < n → next u < n)
    (hreaches : ∀ u, u < n → ∃ root k, next^[k] u = root ∧ next root = root) :
    MutationFunctionalForest n next := by
  intro start hstart
  obtain ⟨root, k, hreach, hfixed⟩ := hreaches start hstart
  obtain ⟨first, hfirst, hfirstReach, _, _⟩ := mutation_functional_first_reach next n start root
    hbounded hstart ⟨k, hreach⟩
  have hiter : ∀ j, next^[j] start < n := by
    intro j
    induction j with
    | zero => exact hstart
    | succ j ih =>
      simpa only [Function.iterate_succ_apply'] using hbounded _ ih
  exact ⟨root, first, hfirst, hfirstReach, hfixed, fun j _ => hiter j⟩

 theorem mutation_functional_forest_bounds (n : Nat) (next : Nat → Nat)
    (hf : MutationFunctionalForest n next) : ∀ u, u < n → next u < n := by
  intro u hu
  obtain ⟨root, k, hk, hreach, hfixed, hbound⟩ := hf u hu
  cases k with
  | zero =>
    have he : u = root := hreach
    simpa only [he, hfixed] using hu
  | succ k => simpa using hbound 1 (by omega)

 theorem mutation_virtual_root_unique (next : Nat → Nat) (n start a b : Nat)
    (ha : MutationVirtualRootWitness next n start a)
    (hb : MutationVirtualRootWitness next n start b) : a = b := by
  obtain ⟨i, _, hi, hfa, _⟩ := ha
  obtain ⟨j, _, hj, hfb, _⟩ := hb
  by_cases hij : i ≤ j
  · have he : j = (j - i) + i := by omega
    rw [he, Function.iterate_add_apply, hi, Function.iterate_fixed hfa] at hj
    exact hj
  · have he : i = (i - j) + j := by omega
    rw [he, Function.iterate_add_apply, hj, Function.iterate_fixed hfb] at hi
    exact hi.symm

 theorem mutation_functional_cut_preserves (n : Nat) (next : Nat → Nat) (child : Nat)
    (hf : MutationFunctionalForest n next) :
    MutationFunctionalForest n (fun u => if u = child then child else next u) := by
  let cut := fun u => if u = child then child else next u
  have hbounds := mutation_functional_forest_bounds n next hf
  apply mutation_functional_forest_of_reaches cut n
  · intro u hu
    by_cases he : u = child
    · simpa only [cut, he, ite_true] using hu
    · simpa only [cut, he, ite_false] using hbounds u hu
  · intro u hu
    obtain ⟨root, k, _, hreach, hfixed, _⟩ := hf u hu
    have hind : ∀ k u, next^[k] u = root → ∃ target j,
        cut^[j] u = target ∧ cut target = target := by
      intro k
      induction k with
      | zero =>
        intro v hv
        have he : v = root := hv
        refine ⟨v, 0, rfl, ?_⟩
        by_cases hc : v = child
        · simp [cut, hc]
        · simp [cut, hc, he, hfixed]
      | succ k ih =>
        intro v hv
        by_cases hc : v = child
        · exact ⟨child, 0, hc, by simp [cut]⟩
        · obtain ⟨target, j, htarget, htargetFixed⟩ := ih (next v) hv
          refine ⟨target, j + 1, ?_, htargetFixed⟩
          simpa only [Function.iterate_succ_apply, cut, hc, ite_false] using htarget
    exact hind k u hreach

end Labyrinth
