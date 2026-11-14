module
public import LabyrinthCore.Mutations

public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

 theorem mutation_carrier_neighbors_total (c : topology.Carrier) (cell : Usize)
    (hc : CarrierValid c) (hcell : cell.val < cellCount c) :
    topology.Carrier.impl.neighbors c cell ⦃ result =>
      result.val.map (·.val) = row c cell.val ⦄ := by
  unfold topology.Carrier.impl.neighbors
  step with (mutation_carrier_len_total c hc) as ⟨count, hcount⟩
  have hvalid : ¬ cell ≥ count := by scalar_tac
  simp only [hvalid, ite_false]
  have hlen : c.offsets.val.length = cellCount c + 1 := by
    have := hc.1
    unfold cellCount at *
    omega
  have hcellIndex : cell.val < c.offsets.val.length := by omega
  step with (alloc.vec.Vec.index_usize_spec c.offsets cell hcellIndex) as ⟨start, hstart⟩
  step with (Usize.add_spec (x := cell) (y := 1#usize) (by
    have := c.offsets.property
    scalar_tac)) as ⟨next, hnext⟩
  have hnextval : next.val = cell.val + 1 := by simpa using hnext
  have hnextIndex : next.val < c.offsets.val.length := by omega
  step with (alloc.vec.Vec.index_usize_spec c.offsets next hnextIndex) as ⟨stop, hstop⟩
  have hs : start.val = (offsets c)[cell.val]?.getD 0 := by
    rw [hstart]
    simp [offsets, hcellIndex]
  have he : stop.val = (offsets c)[cell.val + 1]?.getD 0 := by
    rw [hstop]
    simp [offsets, ← hnextval, hnextIndex]
  have horder : start.val ≤ stop.val := by
    rw [hs, he]
    exact hc.2.2.2.1 cell.val hcell
  have hbound : stop.val ≤ c.neighbors.val.length := by
    rw [he]
    simpa [neighbors] using mutation_carrier_offsets_bound c hc (cell.val + 1) (by omega)
  apply spec_mono (alloc.vec.Vec.index_Range_spec c.neighbors
    { start := start, «end» := stop } horder hbound)
  intro result hresult
  simp [hresult.1, List.slice, row, neighbors, ← hs, ← he]

 theorem mutation_usize_mem_map (values : List Usize) (value : Usize) :
    value.val ∈ values.map (·.val) ↔ value ∈ values := by
  constructor
  · intro h
    obtain ⟨other, hother, heq⟩ := List.mem_map.mp h
    have he : other = value := UScalar.eq_of_val_eq heq
    simpa [he] using hother
  · intro h
    exact List.mem_map.mpr ⟨value, h, rfl⟩

 theorem mutation_carrier_scan_membership (target : Usize) (values : Slice Usize) :
    topology.Carrier.contains_edge_loop target values 0#usize ⦃ result =>
      (result.val < values.val.length ↔ target ∈ values.val) ⦄ := by
  apply spec_mono (mutation_carrier_scan_total target values 0#usize (by simp) (by simp))
  intro result hresult
  constructor
  · intro hlt
    exact List.mem_iff_getElem?.mpr ⟨result.val, hresult.2.2 hlt⟩
  · intro hmem
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hmem
    by_contra hnot
    have hlast : result.val = values.val.length := by omega
    apply hresult.2.1 j (by omega)
    rw [List.getElem?_eq_getElem hj]
    exact congrArg some heq

 theorem mutation_carrier_contains_total (c : topology.Carrier) (edge : topology.Edge)
    (hc : CarrierValid c) :
    topology.Carrier.contains_edge c edge ⦃ result =>
      (result = true ↔ carrierEdge c edge.u.val edge.v.val) ⦄ := by
  unfold topology.Carrier.contains_edge
  step with (mutation_carrier_len_total c hc) as ⟨count, hcount⟩
  by_cases hu : edge.u ≥ count
  · have hnot : ¬ edge.u.val < cellCount c := by scalar_tac
    simp [hu, carrierEdge, hnot]
  · simp only [hu, ite_false]
    have hub : edge.u.val < cellCount c := by scalar_tac
    by_cases hv : edge.v ≥ count
    · have hnot : edge.v.val ∉ row c edge.u.val := by
        intro hmem
        have hbound := (hc.2.2.2.2.1 edge.u.val hub).2.2 edge.v.val hmem
        scalar_tac
      simp [hv, carrierEdge, hnot]
    · simp only [hv, ite_false]
      by_cases heq : edge.u = edge.v
      · have hnot := (hc.2.2.2.2.1 edge.u.val hub).2.1
        simp [heq] at hnot
        simp [heq, carrierEdge, hnot]
      · simp only [heq, ite_false]
        step with (mutation_carrier_neighbors_total c edge.u hc hub) as ⟨values, hvalues⟩
        step with (mutation_carrier_scan_membership edge.v values) as ⟨index, hindex⟩
        have hmem : edge.v ∈ values.val ↔ edge.v.val ∈ row c edge.u.val := by
          rw [← hvalues, mutation_usize_mem_map]
        simpa [carrierEdge, hub, hmem] using hindex

end Labyrinth
