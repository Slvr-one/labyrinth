module
public import LabyrinthCore.ConstructorQuotientFrontier
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

/-- Every processed crossing original edge still has both of its original witness slots. -/
def ConstructorQuotientHistory (edges : List topology.Edge) (label : Usize → Usize)
    (start : Usize → Nat) (count : Usize) (processed : Nat)
    (neighbors : alloc.vec.Vec Usize) (witnesses : alloc.vec.Vec topology.Edge) : Prop :=
  ∀ previous, previous < processed → ∀ edge, edges[previous]? = some edge →
    label edge.u ≠ label edge.v → ∃ a b : Nat,
      constructorQuotientFilled edges label start count processed a ∧
      constructorQuotientFilled edges label start count processed b ∧
      neighbors.val[a]? = some (label edge.v) ∧ witnesses.val[a]? = some edge ∧
      neighbors.val[b]? = some (label edge.u) ∧ witnesses.val[b]? = some edge

theorem constructor_quotient_history_crossing (edges : List topology.Edge)
    (label : Usize → Usize) (start : Usize → Nat) (count : Usize) (processed : Nat)
    (neighbors : alloc.vec.Vec Usize) (witnesses : alloc.vec.Vec topology.Edge)
    (edge : topology.Edge) (a b : Usize)
    (hhistory : ConstructorQuotientHistory edges label start count processed neighbors witnesses)
    (he : edges[processed]? = some edge)
    (ha : a.val < neighbors.val.length) (hb : b.val < neighbors.val.length)
    (haw : a.val < witnesses.val.length) (hbw : b.val < witnesses.val.length)
    (hab : a.val ≠ b.val)
    (hafresh : ¬ constructorQuotientFilled edges label start count processed a.val)
    (hbfresh : ¬ constructorQuotientFilled edges label start count processed b.val)
    (hfrontier : ∀ slot, constructorQuotientFilled edges label start count (processed + 1) slot ↔
      constructorQuotientFilled edges label start count processed slot ∨ slot = a.val ∨ slot = b.val) :
    ConstructorQuotientHistory edges label start count (processed + 1)
      ((neighbors.set a (label edge.v)).set b (label edge.u)) ((witnesses.set a edge).set b edge) := by
  intro previous hp original ho hcross
  by_cases hcurrent : previous = processed
  · rw [hcurrent] at ho
    have hoeq : original = edge := Option.some.inj (ho.symm.trans he)
    rw [hoeq]
    exact ⟨a.val, b.val, (hfrontier a.val).mpr (Or.inr (Or.inl rfl)),
      (hfrontier b.val).mpr (Or.inr (Or.inr rfl)),
      by simp [alloc.vec.Vec.set, ha, hab], by simp [alloc.vec.Vec.set, haw, hab],
      by simp [alloc.vec.Vec.set, hb], by simp [alloc.vec.Vec.set, hbw]⟩
  · obtain ⟨oldA, oldB, hfa, hfb, hna, hwa, hnb, hwb⟩ := hhistory previous (by omega) original ho hcross
    have hpresA := constructor_quotient_prior_slot_preserved neighbors witnesses a b
      (label edge.v) (label edge.u) edge
      (constructorQuotientFilled edges label start count processed) hafresh hbfresh oldA hfa
    have hpresB := constructor_quotient_prior_slot_preserved neighbors witnesses a b
      (label edge.v) (label edge.u) edge
      (constructorQuotientFilled edges label start count processed) hafresh hbfresh oldB hfb
    exact ⟨oldA, oldB, (hfrontier oldA).mpr (Or.inl hfa), (hfrontier oldB).mpr (Or.inl hfb),
      hpresA.1.trans hna, hpresA.2.trans hwa, hpresB.1.trans hnb, hpresB.2.trans hwb⟩

theorem constructor_quotient_history_internal (edges : List topology.Edge)
    (label : Usize → Usize) (start : Usize → Nat) (count : Usize) (processed : Nat)
    (neighbors : alloc.vec.Vec Usize) (witnesses : alloc.vec.Vec topology.Edge)
    (edge : topology.Edge)
    (hhistory : ConstructorQuotientHistory edges label start count processed neighbors witnesses)
    (he : edges[processed]? = some edge) (hsame : label edge.u = label edge.v) :
    ConstructorQuotientHistory edges label start count (processed + 1) neighbors witnesses := by
  intro previous hp original ho hcross
  by_cases hcurrent : previous = processed
  · rw [hcurrent] at ho
    have hoeq : original = edge := Option.some.inj (ho.symm.trans he)
    exact False.elim (hcross (by simpa only [hoeq] using hsame))
  · obtain ⟨a, b, hfa, hfb, hna, hwa, hnb, hwb⟩ := hhistory previous (by omega) original ho hcross
    have hfrontier := constructor_quotient_filled_internal edges label start count processed edge he hsame
    exact ⟨a, b, by simpa only [hfrontier] using hfa, by simpa only [hfrontier] using hfb,
      hna, hwa, hnb, hwb⟩

end Labyrinth
