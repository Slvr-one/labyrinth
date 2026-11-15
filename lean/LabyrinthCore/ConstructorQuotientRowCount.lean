module
public import LabyrinthCore.ConstructorQuotientWitnesses
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

/-- Count original crossing-edge incidences in a quotient row, without identifying parallel edges. -/
def constructorQuotientRowCount (edges : List topology.Edge) (label : Usize → Usize)
    (row : Usize) : Nat → Nat
  | 0 => 0
  | processed + 1 =>
    let previous := constructorQuotientRowCount edges label row processed
    match edges[processed]? with
    | none => previous
    | some edge =>
      if label edge.u ≠ label edge.v ∧ (row = label edge.u ∨ row = label edge.v)
      then previous + 1 else previous

theorem constructor_quotient_row_count_mono (edges : List topology.Edge)
    (label : Usize → Usize) (row : Usize) :
    Monotone (constructorQuotientRowCount edges label row) := by
  apply monotone_nat_of_le_succ
  intro processed
  simp only [constructorQuotientRowCount]
  split
  · exact le_rfl
  · split <;> omega

/-- A bounded row cursor records the number of actual original incidences already filled. -/
def ConstructorQuotientCursors (edges : List topology.Edge) (label : Usize → Usize)
    (start : Usize → Nat) (processed : Nat) (count : Usize) (cursor : alloc.vec.Vec Usize) : Prop :=
  ∀ row : Usize, row.val < count.val → ∃ value : Usize,
    cursor.val[row.val]? = some value ∧
      value.val = start row + constructorQuotientRowCount edges label row processed

/-- Updating the two crossing rows gives exact next cursors for every row. -/
theorem constructor_quotient_cursors_crossing (edges : List topology.Edge)
    (label : Usize → Usize) (start : Usize → Nat) (processed : Nat) (count : Usize)
    (cursor : alloc.vec.Vec Usize) (edge : topology.Edge) (u v a b nextA nextB : Usize)
    (hcursor : ConstructorQuotientCursors edges label start processed count cursor)
    (he : edges[processed]? = some edge) (hu : label edge.u = u) (hv : label edge.v = v)
    (hne : u ≠ v)
    (huc : u.val < cursor.val.length) (hvc : v.val < cursor.val.length)
    (ha : cursor.val[u.val]? = some a) (hb : cursor.val[v.val]? = some b)
    (hnextA : nextA.val = a.val + 1) (hnextB : nextB.val = b.val + 1) :
    ConstructorQuotientCursors edges label start (processed + 1) count
      ((cursor.set u nextA).set v nextB) := by
  intro row hrow
  obtain ⟨old, hold, hvalue⟩ := hcursor row hrow
  have huv : u.val ≠ v.val := fun he => hne ((UScalar.eq_equiv _ _).mpr he)
  by_cases hru : row = u
  · subst row
    have holdEq : old = a := Option.some.inj (hold.symm.trans ha)
    refine ⟨nextA, ?_, ?_⟩
    · simp [alloc.vec.Vec.set, huc, huv]
    · simp only [constructorQuotientRowCount, he, hu, hv]
      rw [ite_eq_left (show u ≠ v ∧ (True ∨ u = v) from ⟨hne, Or.inl True.intro⟩)]
      have := congrArg UScalar.val holdEq
      omega
  · by_cases hrv : row = v
    · subst row
      have holdEq : old = b := Option.some.inj (hold.symm.trans hb)
      refine ⟨nextB, by simp [alloc.vec.Vec.set, hvc], ?_⟩
      simp only [constructorQuotientRowCount, he, hu, hv]
      rw [ite_eq_left (show u ≠ v ∧ (v = u ∨ True) from ⟨hne, Or.inr True.intro⟩)]
      have := congrArg UScalar.val holdEq
      omega
    · have hruv : row.val ≠ u.val := fun he => hru ((UScalar.eq_equiv _ _).mpr he)
      have hrvv : row.val ≠ v.val := fun he => hrv ((UScalar.eq_equiv _ _).mpr he)
      refine ⟨old, ?_, ?_⟩
      · simpa [alloc.vec.Vec.set, hruv, Ne.symm hruv, hrvv, Ne.symm hrvv] using hold
      · simpa only [constructorQuotientRowCount, he, hu, hv, hru, hrv, false_or,
          and_false, ite_false] using hvalue

/-- Internal original edges leave every row cursor unchanged. -/
theorem constructor_quotient_cursors_internal (edges : List topology.Edge)
    (label : Usize → Usize) (start : Usize → Nat) (processed : Nat) (count : Usize)
    (cursor : alloc.vec.Vec Usize) (edge : topology.Edge)
    (hcursor : ConstructorQuotientCursors edges label start processed count cursor)
    (he : edges[processed]? = some edge) (hsame : label edge.u = label edge.v) :
    ConstructorQuotientCursors edges label start (processed + 1) count cursor := by
  intro row hrow
  obtain ⟨value, hv, hc⟩ := hcursor row hrow
  exact ⟨value, hv, by simpa only [constructorQuotientRowCount, he, hsame, ne_self_iff_false,
    false_and, ite_false] using hc⟩

/-- Final row capacity bounds every earlier crossing write strictly inside its allocated row. -/
theorem constructor_quotient_crossing_slot_bound (edges : List topology.Edge)
    (label : Usize → Usize) (start stop : Usize → Nat) (processed : Nat)
    (edge : topology.Edge) (row : Usize)
    (he : edges[processed]? = some edge) (hne : label edge.u ≠ label edge.v)
    (hrow : row = label edge.u ∨ row = label edge.v)
    (hprocessed : processed < edges.length)
    (hcapacity : start row + constructorQuotientRowCount edges label row edges.length ≤ stop row) :
    start row + constructorQuotientRowCount edges label row processed < stop row := by
  have hmono := constructor_quotient_row_count_mono edges label row
    (show processed + 1 ≤ edges.length by omega)
  have hstep : constructorQuotientRowCount edges label row (processed + 1) =
      constructorQuotientRowCount edges label row processed + 1 := by
    simp only [constructorQuotientRowCount, he]
    exact ite_eq_left ⟨hne, hrow⟩
  omega

end Labyrinth
