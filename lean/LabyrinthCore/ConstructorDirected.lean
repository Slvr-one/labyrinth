module
public import LabyrinthCore.ConstructorCanonicalCardinality
public import LabyrinthCore.ConstructorFill
public import LabyrinthCore.ConstructorSearch
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

def constructorDirectedPrefix (cell : Nat) (values : List Usize) (start : Nat) :
    Nat → List (Nat × Nat)
  | 0 => []
  | count + 1 =>
    let emitted := constructorDirectedPrefix cell values start count
    match values[start + count]? with
    | none => emitted
    | some value => emitted ++ [(cell, value.val)]

theorem constructor_directed_prefix_mem (cell : Nat) (values : List Usize) (start count : Nat)
    (edge : Nat × Nat) :
    edge ∈ constructorDirectedPrefix cell values start count ↔
      ∃ k, k < count ∧ ∃ value : Usize, values[start + k]? = some value ∧
        edge = (cell, value.val) := by
  induction count with
  | zero => simp [constructorDirectedPrefix]
  | succ count ih =>
    simp only [constructorDirectedPrefix]
    cases hlookup : values[start + count]? with
    | none =>
      rw [ih]
      constructor
      · rintro ⟨k, hk, value, hv, he⟩
        exact ⟨k, by omega, value, hv, he⟩
      · rintro ⟨k, hk, value, hv, he⟩
        have hlt : k < count := by
          by_contra hnot
          have heq : k = count := by omega
          subst k
          rw [hlookup] at hv
          cases hv
        exact ⟨k, hlt, value, hv, he⟩
    | some last =>
      simp only [List.mem_append, List.mem_singleton, ih]
      constructor
      · rintro (⟨k, hk, value, hv, he⟩ | he)
        · exact ⟨k, by omega, value, hv, he⟩
        · exact ⟨count, by omega, last, hlookup, he⟩
      · rintro ⟨k, hk, value, hv, he⟩
        by_cases heq : k = count
        · subst k
          have hvalue : value = last := Option.some.inj (hv.symm.trans hlookup)
          exact Or.inr (by simpa only [hvalue] using he)
        · exact Or.inl ⟨k, by omega, value, hv, he⟩

theorem constructor_directed_prefix_length (cell : Nat) (values : List Usize) (start count : Nat)
    (hbound : start + count ≤ values.length) :
    (constructorDirectedPrefix cell values start count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have hi : start + count < values.length := by omega
    let value := values[start + count]'hi
    have hv : values[start + count]? = some value := List.getElem?_eq_getElem hi
    simp only [constructorDirectedPrefix, hv, List.length_append, List.length_singleton]
    rw [ih (by omega)]

theorem constructor_directed_prefix_nodup (cell : Nat) (values : List Usize) (start count : Nat)
    (hunique : ∀ i j, i < j → j < count → ∀ value : Usize,
      values[start + i]? = some value → values[start + j]? ≠ some value) :
    (constructorDirectedPrefix cell values start count).Nodup := by
  induction count with
  | zero => simp [constructorDirectedPrefix]
  | succ count ih =>
    have hprefix := ih (fun i j hij hj => hunique i j hij (by omega))
    simp only [constructorDirectedPrefix]
    cases hlookup : values[start + count]? with
    | none => exact hprefix
    | some value =>
      apply List.nodup_append.mpr
      refine ⟨hprefix, by simp, ?_⟩
      intro edge hedge last hlast heq
      have hlastEq : last = (cell, value.val) := by simpa only [List.mem_singleton] using hlast
      obtain ⟨k, hk, other, hother, hedgeEq⟩ :=
        (constructor_directed_prefix_mem cell values start count edge).mp hedge
      have hval : other.val = value.val := by
        have h := congrArg Prod.snd (hedgeEq.symm.trans (heq.trans hlastEq))
        exact h
      have hsame : other = value := (UScalar.eq_equiv _ _).mpr hval
      subst other
      exact hunique k count hk (by omega) value hother hlookup

theorem constructor_directed_prefix_filter (cell : Nat) (values : List Usize) (start count : Nat) :
    (constructorDirectedPrefix cell values start count).filter
        (fun edge => decide (edge.1 < edge.2)) =
      constructorCanonicalPairPrefix cell values start count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    cases hlookup : values[start + count]? with
    | none =>
      simp only [constructorDirectedPrefix, constructorCanonicalPairPrefix, hlookup]
      exact ih
    | some value =>
      simp only [constructorDirectedPrefix, constructorCanonicalPairPrefix, hlookup,
        List.filter_append, ih]
      split <;> simp_all

/-- The complete generated fill represents exactly the original undirected edges.
Parallel incidences are preserved; row simplicity is checked separately by `from_csr`. -/
theorem constructor_filled_csr_adjacent (edges : List topology.Edge) (starts : Nat → Nat)
    (initial : List Usize) (n : Nat) (offsets neighbors : alloc.vec.Vec Usize)
    (hedges : ∀ edge ∈ edges, edge.u.val < n ∧ edge.v.val < n ∧ edge.u ≠ edge.v)
    (hcapacity : ∀ cell, cell < n →
      starts cell + constructorDegreeSlot edges (cell + 1) edges.length ≤ initial.length)
    (hseparated : ∀ u v, u < n → v < n → u ≠ v →
      starts u + constructorDegreeSlot edges (u + 1) edges.length ≤ starts v ∨
      starts v + constructorDegreeSlot edges (v + 1) edges.length ≤ starts u)
    (hlen : offsets.val.length = n + 1)
    (hstarts : ∀ cell, cell < n → (offsets.val[cell]?.getD 0#usize).val = starts cell)
    (hstops : ∀ cell, cell < n → (offsets.val[cell + 1]?.getD 0#usize).val =
      starts cell + constructorDegreeSlot edges (cell + 1) edges.length)
    (hfilled : neighbors.val = constructorFilledNeighbors edges starts initial edges.length)
    (u v : Nat) :
    constructorCsrAdjacent offsets neighbors u v ↔
      ∃ edge ∈ edges, (u = edge.u.val ∧ v = edge.v.val) ∨
        (u = edge.v.val ∧ v = edge.u.val) := by
  constructor
  · rintro ⟨hu, index, hlo, hhi, value, hvalue, hv⟩
    have hun : u < n := by omega
    rw [hstarts u hun] at hlo
    rw [hstops u hun] at hhi
    have hrow : ∃ rank, rank < constructorDegreeSlot edges (u + 1) edges.length ∧
        (constructorFilledNeighbors edges starts initial edges.length)[starts u + rank]? =
          some value := by
      refine ⟨index - starts u, by omega, ?_⟩
      have he : starts u + (index - starts u) = index := by omega
      simpa only [he, hfilled] using hvalue
    obtain ⟨edge, hedge, hc⟩ :=
      (constructor_filled_row_iff edges starts initial n u value
        hedges hcapacity hseparated).mp hrow
    refine ⟨edge, hedge, ?_⟩
    rcases hc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
    · exact Or.inl ⟨hc, hv.symm⟩
    · exact Or.inr ⟨hc, hv.symm⟩
  · rintro ⟨edge, hedge, hc⟩
    have hb := hedges edge hedge
    have hun : u < n := by rcases hc with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
    have hrow (value : Usize)
        (hincident : (u = edge.u.val ∧ value = edge.v) ∨
          (u = edge.v.val ∧ value = edge.u)) (hv : value.val = v) :
        constructorCsrAdjacent offsets neighbors u v := by
      obtain ⟨rank, hrank, hvalue⟩ :=
        (constructor_filled_row_iff edges starts initial n u value
          hedges hcapacity hseparated).mpr ⟨edge, hedge, hincident⟩
      refine ⟨by omega, starts u + rank, ?_, ?_, value, ?_, hv⟩
      · rw [hstarts u hun]
        omega
      · rw [hstops u hun]
        omega
      · simpa only [hfilled] using hvalue
    rcases hc with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact hrow edge.v (Or.inl ⟨hu, rfl⟩) hv.symm
    · exact hrow edge.u (Or.inr ⟨hu, rfl⟩) hv.symm

end Labyrinth
