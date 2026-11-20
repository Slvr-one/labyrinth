module
public import LabyrinthCore.ConstructorDirectedRows
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

theorem constructor_offset_value (values : List Usize) (index : Nat) :
    (values.map (·.val))[index]?.getD 0 = (values[index]?.getD 0#usize).val := by
  simp only [List.getElem?_map]
  cases values[index]? <;> simp

theorem constructor_row_lookup (carrier : topology.Carrier) (cell index : Nat) :
    (row carrier cell)[index]? =
      if index < (carrier.offsets.val[cell + 1]?.getD 0#usize).val -
          (carrier.offsets.val[cell]?.getD 0#usize).val then
        (carrier.neighbors.val[(carrier.offsets.val[cell]?.getD 0#usize).val + index]?).map (·.val)
      else none := by
  simp only [row, offsets, neighbors,
    List.getElem?_take, List.getElem?_drop, List.getElem?_map]
  cases carrier.offsets.val[cell]? <;> cases carrier.offsets.val[cell + 1]? <;> simp

theorem constructor_carrier_edge_iff (carrier : topology.Carrier) (u v : Nat) :
    carrierEdge carrier u v ↔ constructorCsrAdjacent carrier.offsets carrier.neighbors u v := by
  constructor
  · rintro ⟨hu, hmem⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
    rw [constructor_row_lookup] at hi
    split at hi
    · rename_i hindex
      cases hv : carrier.neighbors.val[(carrier.offsets.val[u]?.getD 0#usize).val + i]? with
      | none => simp only [hv, Option.map_none, reduceCtorEq] at hi
      | some value =>
        have he : value.val = v := by simpa only [hv, Option.map_some, Option.some.injEq] using hi
        refine ⟨hu, _, by omega, ?_, value, hv, he⟩
        omega
    · cases hi
  · rintro ⟨hu, j, hjl, hjh, value, hv, he⟩
    refine ⟨hu, List.mem_iff_getElem?.mpr ⟨j - (carrier.offsets.val[u]?.getD 0#usize).val, ?_⟩⟩
    rw [constructor_row_lookup]
    have hindex : j - (carrier.offsets.val[u]?.getD 0#usize).val <
        (carrier.offsets.val[u + 1]?.getD 0#usize).val -
          (carrier.offsets.val[u]?.getD 0#usize).val := by omega
    have hsum : (carrier.offsets.val[u]?.getD 0#usize).val +
        (j - (carrier.offsets.val[u]?.getD 0#usize).val) = j := by omega
    simp only [hindex, ite_true, hsum, hv, Option.map_some, he]

/-- The raw row-validation and canonical-extraction facts entail the public carrier predicate. -/
theorem constructor_carrier_valid_of_rows (carrier : topology.Carrier)
    (hsize : 2 ≤ carrier.offsets.val.length)
    (hfirst : carrier.offsets.val[0]? = some 0#usize)
    (hlast : carrier.offsets.val[carrier.offsets.val.length - 1]? =
      some (alloc.vec.Vec.len carrier.neighbors))
    (hrows : constructorRawRows (alloc.vec.Vec.deref carrier.offsets)
      (alloc.vec.Vec.deref carrier.neighbors))
    (hentries : constructorAllRows carrier.offsets carrier.neighbors (carrier.offsets.val.length - 1))
    (hconnected : ∀ v, v < carrier.offsets.val.length - 1 →
      Relation.ReflTransGen (constructorCsrAdjacent carrier.offsets carrier.neighbors) 0 v)
    (hedges : edgePairs carrier =
      constructorCanonicalPairs carrier.offsets carrier.neighbors (carrier.offsets.val.length - 1)) :
    CarrierValid carrier := by
  have hraw := hrows
  simp only [constructorRawRows, alloc.vec.Vec.deref, Slice.from_val] at hraw
  have hentry (u : Nat) (hu : u < cellCount carrier) (j : Nat)
      (hjl : (carrier.offsets.val[u]?.getD 0#usize).val ≤ j)
      (hjh : j < (carrier.offsets.val[u + 1]?.getD 0#usize).val) :
      ∃ cell value : Usize, cell.val = u ∧ carrier.neighbors.val[j]? = some value ∧
        value.val < cellCount carrier ∧ value ≠ cell ∧
        (∀ i, (carrier.offsets.val[u]?.getD 0#usize).val ≤ i → i < j →
          carrier.neighbors.val[i]? ≠ some value) ∧
        ∃ k, (carrier.offsets.val[value.val]?.getD 0#usize).val ≤ k ∧
          k < (carrier.offsets.val[value.val + 1]?.getD 0#usize).val ∧
          carrier.neighbors.val[k]? = some cell := by
    obtain ⟨cell, hc⟩ := constructor_usize_index carrier.offsets u (by
      unfold cellCount at hu
      omega)
    have h := hentries cell (by simpa only [hc, cellCount] using hu) j
      (by simpa only [hc] using hjl) (by simpa only [hc] using hjh)
    obtain ⟨value, hv, hb, hs, hn, hr⟩ := h
    exact ⟨cell, value, hc, hv, hb, hs, by simpa only [hc] using hn, hr⟩
  refine ⟨by unfold cellCount; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [offsets, List.getElem?_map, hfirst, Option.map_some, UScalar.ofNatCore_val_eq]
  · simp only [offsets, neighbors, cellCount, List.getElem?_map, hlast,
      Option.map_some, alloc.vec.Vec.len_val, List.length_map]
  · intro u hu
    obtain ⟨lo, hi, hlo, hhi, hordered, _⟩ := hraw u hu
    simpa only [offsets, constructor_offset_value, hlo, hhi, Option.getD_some] using hordered
  · intro u hu
    refine ⟨?_, ?_, ?_⟩
    · apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij heq
      have hlooki : (row carrier u)[i]? = some ((row carrier u)[i]) := List.getElem?_eq_getElem hi
      have hlookj : (row carrier u)[j]? = some ((row carrier u)[j]) := List.getElem?_eq_getElem hj
      rw [constructor_row_lookup] at hlooki hlookj
      split at hlooki
      · rename_i hib
        split at hlookj
        · rename_i hjb
          have hjlo : (carrier.offsets.val[u]?.getD 0#usize).val ≤
              (carrier.offsets.val[u]?.getD 0#usize).val + j := by omega
          have hjhi : (carrier.offsets.val[u]?.getD 0#usize).val + j <
              (carrier.offsets.val[u + 1]?.getD 0#usize).val := by omega
          obtain ⟨cell, value, hc, hv, _, _, hnodup, _⟩ := hentry u hu _ hjlo hjhi
          rw [hv] at hlookj
          have hvalj : value.val = (row carrier u)[j] := by simpa using hlookj
          cases hvi : carrier.neighbors.val[(carrier.offsets.val[u]?.getD 0#usize).val + i]? with
          | none => simp only [hvi, Option.map_none, reduceCtorEq] at hlooki
          | some other =>
            have hvali : other.val = (row carrier u)[i] := by
              simpa only [hvi, Option.map_some, Option.some.injEq] using hlooki
            have hsame : other = value := (UScalar.eq_equiv _ _).mpr (by omega)
            subst other
            exact hnodup _ (by omega) (by omega) hvi
        · cases hlookj
      · cases hlooki
    · intro hself
      obtain ⟨_, j, hjl, hjh, value, hv, hvalue⟩ :=
        (constructor_carrier_edge_iff carrier u u).mp ⟨hu, hself⟩
      obtain ⟨cell, actual, hc, ha, _, hne, _⟩ := hentry u hu j hjl hjh
      have he : actual = value := Option.some.inj (ha.symm.trans hv)
      subst actual
      exact hne ((UScalar.eq_equiv _ _).mpr (hvalue.trans hc.symm))
    · intro v hmem
      obtain ⟨_, j, hjl, hjh, value, hv, hvalue⟩ :=
        (constructor_carrier_edge_iff carrier u v).mp ⟨hu, hmem⟩
      obtain ⟨cell, actual, hc, ha, hb, _, _, k, hkl, hkh, hk⟩ := hentry u hu j hjl hjh
      have he : actual = value := Option.some.inj (ha.symm.trans hv)
      subst actual
      refine ⟨by omega, ?_⟩
      have hreverse : constructorCsrAdjacent carrier.offsets carrier.neighbors v u := by
        refine ⟨by simpa only [← hvalue, cellCount] using hb, k, ?_, ?_, cell, hk, hc⟩
        · simpa only [hvalue] using hkl
        · simpa only [hvalue] using hkh
      exact ((constructor_carrier_edge_iff carrier v u).mpr hreverse).2
  · intro v hv
    have hp := hconnected v hv
    clear hv
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ edge ih => exact ih.tail ((constructor_carrier_edge_iff carrier _ _).mpr edge)
  · rw [hedges, ← constructor_directed_pairs_filter]
    exact (constructor_directed_pairs_nodup carrier.offsets carrier.neighbors hrows hentries _ le_rfl).filter _
  · intro u v
    rw [hedges, ← constructor_directed_pairs_filter]
    simp only [List.mem_filter, decide_eq_true_eq,
      constructor_directed_pairs_mem carrier.offsets carrier.neighbors _ le_rfl,
      ← constructor_carrier_edge_iff]
    constructor
    · rintro ⟨⟨_, hedge⟩, hlt⟩
      exact ⟨hlt, hedge⟩
    · rintro ⟨hlt, hedge⟩
      exact ⟨⟨hedge.1, hedge⟩, hlt⟩

end Labyrinth
