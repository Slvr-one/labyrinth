module
public import LabyrinthCore.ConstructorQuotientRowCount
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

/-- Exactly the occupied row prefixes after processing original-edge slots below `processed`. -/
def constructorQuotientFilled (edges : List topology.Edge) (label : Usize → Usize)
    (start : Usize → Nat) (count : Usize) (processed slot : Nat) : Prop :=
  ∃ row : Usize, row.val < count.val ∧ start row ≤ slot ∧
    slot < start row + constructorQuotientRowCount edges label row processed

/-- Each crossing edge extends precisely two row prefixes by one; all prior slots survive. -/
theorem constructor_quotient_filled_crossing (edges : List topology.Edge)
    (label : Usize → Usize) (start : Usize → Nat) (count : Usize) (processed : Nat)
    (edge : topology.Edge) (u v : Usize) (a b : Nat)
    (he : edges[processed]? = some edge) (hu : label edge.u = u) (hv : label edge.v = v)
    (hne : u ≠ v) (hub : u.val < count.val) (hvb : v.val < count.val)
    (ha : a = start u + constructorQuotientRowCount edges label u processed)
    (hb : b = start v + constructorQuotientRowCount edges label v processed) (slot : Nat) :
    constructorQuotientFilled edges label start count (processed + 1) slot ↔
      constructorQuotientFilled edges label start count processed slot ∨ slot = a ∨ slot = b := by
  have hstepU : constructorQuotientRowCount edges label u (processed + 1) =
      constructorQuotientRowCount edges label u processed + 1 := by
    simp only [constructorQuotientRowCount, he, hu, hv]
    exact ite_eq_left ⟨hne, Or.inl True.intro⟩
  have hstepV : constructorQuotientRowCount edges label v (processed + 1) =
      constructorQuotientRowCount edges label v processed + 1 := by
    simp only [constructorQuotientRowCount, he, hu, hv]
    exact ite_eq_left ⟨hne, Or.inr True.intro⟩
  constructor
  · rintro ⟨row, hr, hstart, hstop⟩
    by_cases hru : row = u
    · subst row
      rw [hstepU] at hstop
      by_cases hlt : slot < a
      · exact Or.inl ⟨u, hr, hstart, by omega⟩
      · exact Or.inr (Or.inl (by omega))
    · by_cases hrv : row = v
      · subst row
        rw [hstepV] at hstop
        by_cases hlt : slot < b
        · exact Or.inl ⟨v, hr, hstart, by omega⟩
        · exact Or.inr (Or.inr (by omega))
      · have hunchanged : constructorQuotientRowCount edges label row (processed + 1) =
            constructorQuotientRowCount edges label row processed := by
          simp only [constructorQuotientRowCount, he, hu, hv]
          exact ite_eq_right (by
            rintro ⟨_, hr⟩
            exact hr.elim hru hrv)
        exact Or.inl ⟨row, hr, hstart, by simpa only [hunchanged] using hstop⟩
  · rintro (⟨row, hr, hstart, hstop⟩ | heqa | heqb)
    · have hm := constructor_quotient_row_count_mono edges label row (show processed ≤ processed + 1 by omega)
      exact ⟨row, hr, hstart, by omega⟩
    · subst slot
      exact ⟨u, hub, by omega, by rw [hstepU]; omega⟩
    · subst slot
      exact ⟨v, hvb, by omega, by rw [hstepV]; omega⟩

/-- Internal edges do not move the occupied-slot frontier. -/
theorem constructor_quotient_filled_internal (edges : List topology.Edge)
    (label : Usize → Usize) (start : Usize → Nat) (count : Usize) (processed : Nat)
    (edge : topology.Edge) (he : edges[processed]? = some edge)
    (hsame : label edge.u = label edge.v) :
    constructorQuotientFilled edges label start count (processed + 1) =
      constructorQuotientFilled edges label start count processed := by
  funext slot
  apply propext
  have hcounts : ∀ row, constructorQuotientRowCount edges label row (processed + 1) =
      constructorQuotientRowCount edges label row processed := by
    intro row
    simp only [constructorQuotientRowCount, he]
    exact ite_eq_right (by rintro ⟨hne, _⟩; exact hne hsame)
  simp only [constructorQuotientFilled, hcounts]

/-- The next row cursor is outside every previously occupied row prefix. -/
theorem constructor_quotient_frontier_fresh (edges : List topology.Edge)
    (label : Usize → Usize) (start stop : Usize → Nat) (count : Usize)
    (processed : Nat) (row : Usize) (slot : Nat) (rowOf : Nat → Usize)
    (hr : row.val < count.val)
    (hslot : slot = start row + constructorQuotientRowCount edges label row processed)
    (hstop : slot < stop row)
    (hcapacity : ∀ other : Usize, other.val < count.val →
      start other + constructorQuotientRowCount edges label other processed ≤ stop other)
    (hrows : ∀ other : Usize, other.val < count.val → ∀ k,
      start other ≤ k → k < stop other → rowOf k = other) :
    ¬ constructorQuotientFilled edges label start count processed slot := by
  rintro ⟨other, ho, hstart, hfilled⟩
  have hrow := hrows row hr slot (by omega) hstop
  have hother := hrows other ho slot hstart (by have := hcapacity other ho; omega)
  have heq : other = row := hother.symm.trans hrow
  rw [heq] at hfilled
  omega

/-- Previously written original witnesses are never overwritten by later crossing edges. -/
theorem constructor_quotient_prior_slot_preserved
    (neighbors : alloc.vec.Vec Usize) (witnesses : alloc.vec.Vec topology.Edge)
    (a b targetA targetB : Usize) (edge : topology.Edge) (valid : Nat → Prop)
    (ha : ¬ valid a.val) (hb : ¬ valid b.val) (slot : Nat) (hslot : valid slot) :
    ((neighbors.set a targetA).set b targetB).val[slot]? = neighbors.val[slot]? ∧
      ((witnesses.set a edge).set b edge).val[slot]? = witnesses.val[slot]? := by
  have hna : slot ≠ a.val := by intro he; exact ha (he ▸ hslot)
  have hnb : slot ≠ b.val := by intro he; exact hb (he ▸ hslot)
  constructor <;> simp [alloc.vec.Vec.set, Ne.symm hna, Ne.symm hnb]

end Labyrinth
