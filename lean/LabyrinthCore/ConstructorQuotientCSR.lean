module
public import LabyrinthCore.ConstructorQuotientFillLoop
public import LabyrinthCore.ConstructorQuotientDegrees
public import LabyrinthCore.ConstructorPrefixOffsets
public import LabyrinthCore.ConstructorQuotientReachability
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

/-- The degree loop and fill loop count the same crossing incidences in each quotient row. -/
theorem constructor_quotient_degree_row_count (edges : List topology.Edge)
    (label : Usize → Usize) (row : Usize) (processed : Nat) :
    constructorQuotientDegreeSlot edges label (row.val + 1) processed =
      constructorQuotientRowCount edges label row processed := by
  induction processed with
  | zero => rfl
  | succ processed ih =>
    cases he : edges[processed]? with
    | none => simp only [constructorQuotientDegreeSlot, constructorQuotientRowCount, he, ih]
    | some edge =>
      have hu : row.val + 1 = (label edge.u).val + 1 ↔ row = label edge.u := by
        constructor
        · intro h
          exact (UScalar.eq_equiv _ _).mpr (by omega)
        · intro h
          subst row
          rfl
      have hv : row.val + 1 = (label edge.v).val + 1 ↔ row = label edge.v := by
        constructor
        · intro h
          exact (UScalar.eq_equiv _ _).mpr (by omega)
        · intro h
          subst row
          rfl
      by_cases hsame : label edge.u = label edge.v
      · simp only [constructorQuotientDegreeSlot, constructorQuotientRowCount, he, hsame,
          ne_self_iff_false, false_and, ite_false, ite_true, ih]
      · simp only [constructorQuotientDegreeSlot, constructorQuotientRowCount, he, hsame,
          ite_false, ih]
        unfold constructorCanonicalEdge
        by_cases hle : label edge.u ≤ label edge.v
        · simp only [hle, ite_true, hu, hv]
          by_cases hcross : row = label edge.u ∨ row = label edge.v
          · rw [ite_eq_left hcross, ite_eq_left ⟨hsame, hcross⟩]
          · rw [ite_eq_right hcross, ite_eq_right (fun h => hcross h.2)]
        · simp only [hle, ite_false, hu, hv]
          by_cases hcross : row = label edge.u ∨ row = label edge.v
          · have hcross' : row = label edge.v ∨ row = label edge.u := hcross.elim Or.inr Or.inl
            rw [ite_eq_left hcross', ite_eq_left ⟨hsame, hcross⟩]
          · have hcross' : ¬(row = label edge.v ∨ row = label edge.u) :=
              fun h => h.elim (fun hv => hcross (Or.inr hv)) (fun hu => hcross (Or.inl hu))
            rw [ite_eq_right hcross', ite_eq_right (fun h => hcross h.2)]

/-- The actual prefix sum places the next row immediately after all crossing incidences. -/
theorem constructor_quotient_prefix_row (edges : List topology.Edge)
    (label : Usize → Usize) (counts : List Usize) (count row : Usize)
    (hcountLen : counts.length = count.val + 1)
    (hrow : row.val < count.val)
    (hcounts : ∀ j, j < counts.length → ∃ value : Usize,
      counts[j]? = some value ∧
        value.val = constructorQuotientDegreeSlot edges label j edges.length) :
    constructorPrefixSum counts (row.val + 2) =
      constructorPrefixSum counts (row.val + 1) +
        constructorQuotientRowCount edges label row edges.length := by
  obtain ⟨value, hvalue, hdegree⟩ := hcounts (row.val + 1) (by omega)
  simp only [constructorPrefixSum, hvalue, Option.getD_some, hdegree,
    constructor_quotient_degree_row_count]

/-- Exact values produced by the degree and prefix loops give exact row capacities. -/
theorem constructor_quotient_row_capacity (edges : List topology.Edge)
    (label : Usize → Usize) (counts : List Usize) (offsets : Slice Usize)
    (count row : Usize)
    (hcountLen : counts.length = count.val + 1)
    (hoffsetLen : offsets.val.length = count.val + 1)
    (hrow : row.val < count.val)
    (hcounts : ∀ j, j < counts.length → ∃ value : Usize,
      counts[j]? = some value ∧
        value.val = constructorQuotientDegreeSlot edges label j edges.length)
    (hoffsets : ∀ j, j < offsets.val.length → ∃ value : Usize,
      offsets.val[j]? = some value ∧ value.val = constructorPrefixSum counts (j + 1)) :
    constructorDFSOffset offsets (row.val + 1) =
      constructorDFSOffset offsets row.val +
        constructorQuotientRowCount edges label row edges.length := by
  obtain ⟨start, hs, hsvalue⟩ := hoffsets row.val (by omega)
  obtain ⟨stop, ht, htvalue⟩ := hoffsets (row.val + 1) (by omega)
  rw [show row.val + 1 + 1 = row.val + 2 by omega] at htvalue
  have hprefix := constructor_quotient_prefix_row edges label counts count row hcountLen hrow hcounts
  simp only [constructorDFSOffset, hs, ht, Option.map_some, Option.getD_some]
  omega

/-- Every slot in an exact final row is one of the slots occupied by the actual fill loop. -/
theorem constructor_quotient_row_covered (edges : List topology.Edge)
    (label : Usize → Usize) (start stop : Usize → Nat) (count row : Usize)
    (hrow : row.val < count.val)
    (hcapacity : stop row = start row +
      constructorQuotientRowCount edges label row edges.length) (slot : Nat)
    (hstart : start row ≤ slot) (hstop : slot < stop row) :
    constructorQuotientFilled edges label start count edges.length slot := by
  exact ⟨row, hrow, hstart, by omega⟩

end Labyrinth
