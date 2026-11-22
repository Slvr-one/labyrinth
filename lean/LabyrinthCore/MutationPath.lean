module
public import LabyrinthCore.Model

public section

namespace Labyrinth

 theorem mutation_path_reversal_edges
    (before after : List Nat) (path : Nat → Nat) (last : Nat)
    (hlen : after.length = before.length)
    (hforward : ∀ j, j < last → before[path j]? = some (path (j + 1)))
    (hroot : before[path last]? = some (path last))
    (hnewRoot : after[path 0]? = some (path 0))
    (hbackward : ∀ j, j < last → after[path (j + 1)]? = some (path j))
    (houtside : ∀ u, u < before.length →
      (∀ j, j ≤ last → path j ≠ u) → after[u]? = before[u]?) :
    ∀ u v, parentEdge after u v ↔ parentEdge before u v := by
  classical
  have hnewOld : ∀ u v, u < before.length → u ≠ v → after[u]? = some v →
      before[u]? = some v ∨ before[v]? = some u := by
    intro u v hu hne huv
    by_cases hon : ∃ j, j ≤ last ∧ path j = u
    · obtain ⟨j, hj, hju⟩ := hon
      cases j with
      | zero =>
        have he := hnewRoot
        rw [hju, huv] at he
        exact (hne (Option.some.inj he).symm).elim
      | succ j =>
        have hjlt : j < last := by omega
        have he := hbackward j hjlt
        rw [hju, huv] at he
        have hv : v = path j := Option.some.inj he
        right
        rw [hv, hforward j hjlt, hju]
    · have hoff : ∀ j, j ≤ last → path j ≠ u := by
        intro j hj he
        exact hon ⟨j, hj, he⟩
      exact Or.inl ((houtside u hu hoff).symm.trans huv)
  have holdNew : ∀ u v, u < before.length → u ≠ v → before[u]? = some v →
      after[u]? = some v ∨ after[v]? = some u := by
    intro u v hu hne huv
    by_cases hon : ∃ j, j ≤ last ∧ path j = u
    · obtain ⟨j, hj, hju⟩ := hon
      by_cases hlast : j = last
      · have he := hroot
        rw [← hlast, hju, huv] at he
        exact (hne (Option.some.inj he).symm).elim
      · have hjlt : j < last := by omega
        have he := hforward j hjlt
        rw [hju, huv] at he
        have hv : v = path (j + 1) := Option.some.inj he
        right
        rw [hv, hbackward j hjlt, hju]
    · have hoff : ∀ j, j ≤ last → path j ≠ u := by
        intro j hj he
        exact hon ⟨j, hj, he⟩
      exact Or.inl ((houtside u hu hoff).trans huv)
  intro u v
  constructor
  · rintro ⟨hu, hv, hne, huv | hvu⟩
    · exact ⟨by omega, by omega, hne, hnewOld u v (by omega) hne huv⟩
    · exact ⟨by omega, by omega, hne, (hnewOld v u (by omega) hne.symm hvu).symm⟩
  · rintro ⟨hu, hv, hne, huv | hvu⟩
    · exact ⟨by omega, by omega, hne, holdNew u v hu hne huv⟩
    · exact ⟨by omega, by omega, hne, (holdNew v u hv hne.symm hvu).symm⟩

end Labyrinth
