module
public import LabyrinthCore.ConstructorQuotientFill
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

/-- A quotient slot retains the original undirected carrier edge, in either row orientation. -/
def constructorQuotientSlotWitness (carrier : topology.Carrier) (label : Usize → Usize)
    (source target : Usize) (edge : topology.Edge) : Prop :=
  carrierEdge carrier edge.u.val edge.v.val ∧
    ((label edge.u = source ∧ label edge.v = target) ∨
      (label edge.v = source ∧ label edge.u = target))

/-- Updating one quotient slot preserves all other original-edge witness pairs. -/
theorem constructor_quotient_witness_write (carrier : topology.Carrier) (label : Usize → Usize)
    (neighbors : alloc.vec.Vec Usize) (witnesses : alloc.vec.Vec topology.Edge)
    (slot : Usize) (target : Usize) (edge : topology.Edge)
    (hn : slot.val < neighbors.val.length) (hw : slot.val < witnesses.val.length)
    (row : Nat → Usize) (he : constructorQuotientSlotWitness carrier label (row slot.val) target edge)
    (valid : Nat → Prop)
    (hvalid : ∀ k, valid k → ∃ value original,
      neighbors.val[k]? = some value ∧ witnesses.val[k]? = some original ∧
        constructorQuotientSlotWitness carrier label (row k) value original) :
    ∀ k, valid k ∨ k = slot.val → ∃ value original,
      (neighbors.set slot target).val[k]? = some value ∧
      (witnesses.set slot edge).val[k]? = some original ∧
        constructorQuotientSlotWitness carrier label (row k) value original := by
  intro k hk
  by_cases heq : k = slot.val
  · subst k
    exact ⟨target, edge, by simp [alloc.vec.Vec.set, hn],
      by simp [alloc.vec.Vec.set, hw], he⟩
  · have hold : valid k := hk.resolve_right heq
    obtain ⟨value, original, hv, ho, hs⟩ := hvalid k hold
    exact ⟨value, original, by simpa [alloc.vec.Vec.set, heq, Ne.symm heq] using hv,
      by simpa [alloc.vec.Vec.set, heq, Ne.symm heq] using ho, hs⟩

/-- Both directed writes of a crossing input edge retain that same original witness.
A separate slot per direction follows from disjoint quotient row intervals. -/
theorem constructor_quotient_crossing_witnesses (carrier : topology.Carrier)
    (label : Usize → Usize) (neighbors : alloc.vec.Vec Usize)
    (witnesses : alloc.vec.Vec topology.Edge) (edge : topology.Edge) (a b : Usize)
    (ha : a.val < neighbors.val.length) (hb : b.val < neighbors.val.length)
    (haw : a.val < witnesses.val.length) (hbw : b.val < witnesses.val.length)
    (hedge : carrierEdge carrier edge.u.val edge.v.val)
    (row : Nat → Usize) (hra : row a.val = label edge.u) (hrb : row b.val = label edge.v)
    (valid : Nat → Prop)
    (hvalid : ∀ k, valid k → ∃ value original,
      neighbors.val[k]? = some value ∧ witnesses.val[k]? = some original ∧
        constructorQuotientSlotWitness carrier label (row k) value original) :
    ∀ k, valid k ∨ k = a.val ∨ k = b.val → ∃ value original,
      ((neighbors.set a (label edge.v)).set b (label edge.u)).val[k]? = some value ∧
      ((witnesses.set a edge).set b edge).val[k]? = some original ∧
        constructorQuotientSlotWitness carrier label (row k) value original := by
  have hfirst := constructor_quotient_witness_write carrier label neighbors witnesses a (label edge.v)
    edge ha haw row ⟨hedge, Or.inl ⟨hra.symm, rfl⟩⟩ valid hvalid
  have hsecond := constructor_quotient_witness_write carrier label
    (neighbors.set a (label edge.v)) (witnesses.set a edge) b (label edge.u) edge
    (by simpa using hb) (by simpa using hbw) row
    ⟨hedge, Or.inr ⟨hrb.symm, rfl⟩⟩ (fun k => valid k ∨ k = a.val) hfirst
  intro k hk
  apply hsecond k
  tauto

/-- Ordered row endpoints prevent a write in one row from destroying another row's witness. -/
theorem constructor_quotient_row_slots_distinct (offset : Nat → Nat)
    (hmono : Monotone offset) (u v a b : Nat) (hne : u ≠ v)
    (ha : offset u ≤ a ∧ a < offset (u + 1))
    (hb : offset v ≤ b ∧ b < offset (v + 1)) : a ≠ b := by
  by_cases huv : u < v
  · have hord := hmono (show u + 1 ≤ v by omega)
    omega
  · have hord := hmono (show v + 1 ≤ u by omega)
    omega

end Labyrinth
