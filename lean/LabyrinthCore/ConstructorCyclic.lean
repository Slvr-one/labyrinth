module
public import LabyrinthCore.ConstructorDFS
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

/-- Mathematical index of the `step`-th entry visited by the production cyclic row scan. -/
def constructorCyclicIndex (lo hi next step : Nat) : Nat :=
  lo + (next - lo + step) % (hi - lo)

theorem constructor_cyclic_index_bounds (lo hi next step : Nat) (hrow : lo < hi) :
    lo ≤ constructorCyclicIndex lo hi next step ∧ constructorCyclicIndex lo hi next step < hi := by
  have hmod := Nat.mod_lt (next - lo + step) (show 0 < hi - lo by omega)
  unfold constructorCyclicIndex
  omega

theorem constructor_cyclic_index_zero (lo hi next : Nat) (hnext : lo ≤ next ∧ next < hi) :
    constructorCyclicIndex lo hi next 0 = next := by
  unfold constructorCyclicIndex
  rw [Nat.add_zero, Nat.mod_eq_of_lt (show next - lo < hi - lo by omega)]
  omega

/-- Advancing exactly as the extracted loop does removes the head of the remaining cyclic scan. -/
theorem constructor_cyclic_index_step (lo hi next step : Nat) (hnext : lo ≤ next ∧ next < hi) :
    constructorCyclicIndex lo hi next (step + 1) =
      constructorCyclicIndex lo hi (if next + 1 = hi then lo else next + 1) step := by
  by_cases hwrap : next + 1 = hi
  · simp only [hwrap, ite_true, constructorCyclicIndex, Nat.sub_self, Nat.zero_add]
    have hsum : next - lo + (step + 1) = (hi - lo) + step := by omega
    rw [hsum, Nat.add_mod]
    simp
  · simp only [hwrap, ite_false, constructorCyclicIndex]
    have he : next - lo + (step + 1) = next + 1 - lo + step := by omega
    rw [he]

/-- Every entry of a nonempty row occurs in the full scan for every legal adapter choice. -/
theorem constructor_cyclic_index_covers (lo hi next index : Nat)
    (hnext : lo ≤ next ∧ next < hi) (hindex : lo ≤ index ∧ index < hi) :
    ∃ step, step < hi - lo ∧ constructorCyclicIndex lo hi next step = index := by
  by_cases hafter : next ≤ index
  · refine ⟨index - next, by omega, ?_⟩
    have he : next - lo + (index - next) = index - lo := by omega
    unfold constructorCyclicIndex
    rw [he, Nat.mod_eq_of_lt (show index - lo < hi - lo by omega)]
    omega
  · refine ⟨hi - lo - (next - index), by omega, ?_⟩
    have he : next - lo + (hi - lo - (next - index)) = hi - lo + (index - lo) := by omega
    unfold constructorCyclicIndex
    rw [he, Nat.add_mod]
    simp only [Nat.mod_self, Nat.zero_add, Nat.mod_mod]
    rw [Nat.mod_eq_of_lt (show index - lo < hi - lo by omega)]
    omega

/-- The next pointer remains in the row until the remaining-count reaches zero. -/
theorem constructor_cyclic_advance_bounds (lo hi next : Nat) (hnext : lo ≤ next ∧ next < hi) :
    lo ≤ (if next + 1 = hi then lo else next + 1) ∧
      (if next + 1 = hi then lo else next + 1) < hi := by
  split_ifs <;> omega

end Labyrinth
