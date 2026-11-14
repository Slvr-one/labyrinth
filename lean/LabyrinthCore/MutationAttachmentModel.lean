module
public import LabyrinthCore.MutationForest

@[expose] public section

namespace Labyrinth

 theorem mutation_fixed_reach_unique (next : Nat → Nat) (start a b : Nat)
    (ha : ∃ i, next^[i] start = a) (hfa : next a = a)
    (hb : ∃ j, next^[j] start = b) (hfb : next b = b) : a = b := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  by_cases hij : i ≤ j
  · have he : j = (j - i) + i := by omega
    rw [he, Function.iterate_add_apply, hi, Function.iterate_fixed hfa] at hj
    exact hj
  · have he : i = (i - j) + j := by omega
    rw [he, Function.iterate_add_apply, hj, Function.iterate_fixed hfb] at hi
    exact hi.symm

 theorem mutation_functional_attach_preserves
    (n : Nat) (before after : Nat → Nat) (inside outside component other k : Nat)
    (hf : MutationFunctionalForest n before)
    (hinside : inside < n) (houtside : outside < n)
    (hreach : before^[k] inside = component) (hfixed : before component = component)
    (hother : MutationVirtualRootWitness before n outside other)
    (hdifferent : component ≠ other)
    (hnew : after inside = outside)
    (hback : ∀ j, j < k → after (before^[j + 1] inside) = before^[j] inside)
    (hoff : ∀ u, u < n → (∀ j, j ≤ k → before^[j] inside ≠ u) → after u = before u) :
    MutationFunctionalForest n after := by
  have hbeforeBound := mutation_functional_forest_bounds n before hf
  have hiterBound : ∀ j u, u < n → before^[j] u < n := by
    intro j
    induction j with
    | zero => exact fun _ h => h
    | succ j ih =>
      intro u hu
      rw [Function.iterate_succ_apply']
      exact hbeforeBound _ (ih u hu)
  have hpathBound : ∀ j, before^[j] inside < n := fun j => hiterBound j inside hinside
  have hafterBound : ∀ u, u < n → after u < n := by
    intro u hu
    by_cases hon : ∃ j, j ≤ k ∧ before^[j] inside = u
    · obtain ⟨j, hj, hju⟩ := hon
      cases j with
      | zero =>
        have he : inside = u := hju
        simpa only [← he, hnew] using houtside
      | succ j =>
        rw [← hju, hback j (by omega)]
        exact hpathBound j
    · rw [hoff u hu (fun j hj he => hon ⟨j, hj, he⟩)]
      exact hbeforeBound u hu
  obtain ⟨otherSteps, _, hotherReach, hotherFixed, _⟩ := hother
  have havoid : ∀ i j, j ≤ k → before^[j] inside ≠ before^[i] outside := by
    intro i j hj heq
    apply hdifferent
    apply mutation_fixed_reach_unique before outside component other
    · refine ⟨(k - j) + i, ?_⟩
      rw [Function.iterate_add_apply, ← heq, ← Function.iterate_add_apply,
        Nat.sub_add_cancel hj]
      exact hreach
    · exact hfixed
    · exact ⟨otherSteps, hotherReach⟩
    · exact hotherFixed
  have houtsideIter : ∀ i, after^[i] outside = before^[i] outside := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact hoff _ (hiterBound i outside houtside) (fun j hj => havoid i j hj)
  have hafterOtherFixed : after other = other := by
    rw [← hotherReach, hoff _ (hiterBound otherSteps outside houtside)
      (fun j hj => havoid otherSteps j hj), hotherReach, hotherFixed]
  have hpathReaches : ∀ j, j ≤ k → after^[j + 1] (before^[j] inside) = outside := by
    intro j
    induction j with
    | zero => intro _; simpa using hnew
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply, hback j (by omega)]
      exact ih (by omega)
  have hpathOther : ∀ j, j ≤ k → ∃ steps,
      after^[steps] (before^[j] inside) = other := by
    intro j hj
    refine ⟨otherSteps + (j + 1), ?_⟩
    rw [Function.iterate_add_apply, hpathReaches j hj, houtsideIter, hotherReach]
  apply mutation_functional_forest_of_reaches after n hafterBound
  intro u hu
  obtain ⟨root, steps, _, hrootReach, hrootFixed, _⟩ := hf u hu
  have hind : ∀ steps v, v < n → before^[steps] v = root →
      ∃ target i, after^[i] v = target ∧ after target = target := by
    intro steps
    induction steps with
    | zero =>
      intro v hv hvr
      by_cases hon : ∃ j, j ≤ k ∧ before^[j] inside = v
      · obtain ⟨j, hj, hju⟩ := hon
        obtain ⟨i, hi⟩ := hpathOther j hj
        exact ⟨other, i, by simpa only [hju] using hi, hafterOtherFixed⟩
      · refine ⟨v, 0, rfl, ?_⟩
        rw [hoff v hv (fun j hj he => hon ⟨j, hj, he⟩)]
        have he : v = root := hvr
        simpa only [he] using hrootFixed
    | succ steps ih =>
      intro v hv hvr
      by_cases hon : ∃ j, j ≤ k ∧ before^[j] inside = v
      · obtain ⟨j, hj, hju⟩ := hon
        obtain ⟨i, hi⟩ := hpathOther j hj
        exact ⟨other, i, by simpa only [hju] using hi, hafterOtherFixed⟩
      · obtain ⟨target, i, hi, htargetFixed⟩ := ih (before v) (hbeforeBound v hv) hvr
        refine ⟨target, i + 1, ?_, htargetFixed⟩
        rw [Function.iterate_succ_apply, hoff v hv (fun j hj he => hon ⟨j, hj, he⟩)]
        exact hi
  exact hind steps u hu hrootReach

 def mutationFunctionalEdge (n : Nat) (next : Nat → Nat) (u v : Nat) : Prop :=
  u < n ∧ v < n ∧ u ≠ v ∧ (next u = v ∨ next v = u)

 theorem mutation_functional_attach_edges
    (n : Nat) (before after path : Nat → Nat) (k outside : Nat)
    (hinside : path 0 < n) (houtside : outside < n) (hne : path 0 ≠ outside)
    (hforward : ∀ j, j < k → before (path j) = path (j + 1))
    (hroot : before (path k) = path k)
    (hnew : after (path 0) = outside)
    (hback : ∀ j, j < k → after (path (j + 1)) = path j)
    (hoff : ∀ u, u < n → (∀ j, j ≤ k → path j ≠ u) → after u = before u) :
    ∀ u v, mutationFunctionalEdge n after u v ↔
      mutationFunctionalEdge n before u v ∨
        (u = path 0 ∧ v = outside) ∨ (v = path 0 ∧ u = outside) := by
  have hnewOld : ∀ u v, u < n → u ≠ v → after u = v →
      (before u = v ∨ before v = u) ∨ (u = path 0 ∧ v = outside) := by
    intro u v hu huv hparent
    by_cases hon : ∃ j, j ≤ k ∧ path j = u
    · obtain ⟨j, hj, hju⟩ := hon
      cases j with
      | zero =>
        right
        exact ⟨hju.symm, (hparent.symm.trans (hju ▸ hnew))⟩
      | succ j =>
        have he := hback j (by omega)
        rw [hju, hparent] at he
        exact Or.inl (Or.inr (by rw [he, hforward j (by omega), hju]))
    · exact Or.inl (Or.inl ((hoff u hu (fun j hj he => hon ⟨j, hj, he⟩)).symm.trans hparent))
  have holdNew : ∀ u v, u < n → u ≠ v → before u = v →
      after u = v ∨ after v = u := by
    intro u v hu huv hparent
    by_cases hon : ∃ j, j ≤ k ∧ path j = u
    · obtain ⟨j, hj, hju⟩ := hon
      by_cases hlast : j = k
      · have he := hroot
        rw [← hlast, hju, hparent] at he
        exact (huv he.symm).elim
      · have he := hforward j (by omega)
        rw [hju, hparent] at he
        exact Or.inr (by rw [he, hback j (by omega), hju])
    · exact Or.inl ((hoff u hu (fun j hj he => hon ⟨j, hj, he⟩)).trans hparent)
  intro u v
  constructor
  · rintro ⟨hu, hv, huv, hp | hp⟩
    · rcases hnewOld u v hu huv hp with hold | hadd
      · exact Or.inl ⟨hu, hv, huv, hold⟩
      · exact Or.inr (Or.inl hadd)
    · rcases hnewOld v u hv huv.symm hp with hold | hadd
      · exact Or.inl ⟨hu, hv, huv, hold.symm⟩
      · exact Or.inr (Or.inr hadd)
  · rintro (⟨hu, hv, huv, hp | hp⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨hu, hv, huv, holdNew u v hu huv hp⟩
    · exact ⟨hu, hv, huv, (holdNew v u hv huv.symm hp).symm⟩
    · exact ⟨hinside, houtside, hne, Or.inl hnew⟩
    · exact ⟨houtside, hinside, hne.symm, Or.inr hnew⟩

 theorem mutation_functional_attach_fixed_root
    (n : Nat) (before after : Nat → Nat) (inside component root k : Nat)
    (hroot : root < n) (hfixed : before root = root)
    (hreach : before^[k] inside = component) (hne : root ≠ component)
    (hoff : ∀ u, u < n →
      (∀ j, j ≤ k → before^[j] inside ≠ u) → after u = before u) :
    after root = root := by
  rw [hoff root hroot, hfixed]
  intro j hj he
  apply hne
  have hremaining : before^[k - j] root = component := by
    rw [← he, ← Function.iterate_add_apply, Nat.sub_add_cancel hj]
    exact hreach
  simpa only [Function.iterate_fixed hfixed] using hremaining

end Labyrinth
