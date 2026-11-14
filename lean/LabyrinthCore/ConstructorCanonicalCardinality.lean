module
public import LabyrinthCore.ConstructorCanonicalRows
public import Mathlib.Data.Finset.Card
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

/-- A simple reciprocal directed-edge list has exactly twice as many entries as canonical edges. -/
theorem constructor_reciprocal_edge_count (directed : List (Nat × Nat))
    (hnodup : directed.Nodup)
    (hself : ∀ edge ∈ directed, edge.1 ≠ edge.2)
    (hreverse : ∀ edge ∈ directed, edge.swap ∈ directed) :
    2 * (directed.filter (fun edge => decide (edge.1 < edge.2))).length = directed.length := by
  let all := directed.toFinset
  let lower := all.filter (fun edge => edge.1 < edge.2)
  let upper := all.filter (fun edge => ¬ edge.1 < edge.2)
  have hswap : lower.image Prod.swap = upper := by
    ext edge
    constructor
    · intro he
      obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp horiginal
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · exact List.mem_toFinset.mpr (hreverse original (List.mem_toFinset.mp hmem))
      · dsimp only [Prod.swap]
        omega
    · intro he
      obtain ⟨hmem, hnot⟩ := Finset.mem_filter.mp he
      have hlist := List.mem_toFinset.mp hmem
      have hne := hself edge hlist
      apply Finset.mem_image.mpr
      refine ⟨edge.swap, ?_, by simp⟩
      apply Finset.mem_filter.mpr
      refine ⟨List.mem_toFinset.mpr (hreverse edge hlist), ?_⟩
      dsimp only [Prod.swap]
      omega
  have hsame : lower.card = upper.card := by
    rw [← hswap]
    symm
    apply Finset.card_image_of_injective
    intro x y he
    simpa using congrArg Prod.swap he
  have hsplit := Finset.card_filter_add_card_filter_not (s := all)
    (fun edge => edge.1 < edge.2)
  have hall : all.card = directed.length := List.toFinset_card_of_nodup hnodup
  have hlower : lower.card =
      (directed.filter (fun edge => decide (edge.1 < edge.2))).length := by
    have hfiltered := List.toFinset_card_of_nodup
      (hnodup.filter (fun edge => decide (edge.1 < edge.2)))
    simpa [lower, all] using hfiltered
  change lower.card + upper.card = all.card at hsplit
  omega

end Labyrinth
