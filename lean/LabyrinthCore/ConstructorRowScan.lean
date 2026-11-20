module
public import LabyrinthCore.Model
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

private theorem constructor_scan_body
    (xs : Slice Usize) (stop needle current : Usize)
    (hstop : stop.val ≤ xs.val.length) :
    WP.spec (topology.validate_row_entry_loop0.body xs stop needle current)
      (fun r => match r with
      | .done found => found = current ∧
          (current.val < stop.val → xs.val[current.val]? = some needle)
      | .cont next => current.val < stop.val ∧ next.val = current.val + 1 ∧
          xs.val[current.val]? ≠ some needle) := by
  unfold topology.validate_row_entry_loop0.body
  by_cases hc : current < stop
  · have hcv : current.val < stop.val := by simpa using hc
    simp only [hc, ite_true]
    apply WP.spec_bind (Slice.index_usize_spec xs current (by
      change current.val < xs.val.length
      omega))
    intro x hx
    have hget : xs.val[current.val]? = some x := by
      rw [List.getElem?_eq_getElem (show current.val < xs.val.length by omega), hx]
    by_cases he : x = needle
    · simp only [bne_iff_ne, ne_eq, he, not_true_eq_false, ite_false]
      apply (WP.spec_ok _).mpr
      exact ⟨rfl, fun _ => hget.trans (congrArg some he)⟩
    · simp only [bne_iff_ne, ne_eq, he, not_false_eq_true, ite_true]
      apply WP.spec_bind (Usize.add_spec (x := current) (y := 1#usize) (by
        have := xs.property
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro next hn
      apply (WP.spec_ok _).mpr
      exact ⟨hcv, by simpa using hn, by simpa only [hget, Option.some.injEq] using he⟩
  · have hcv : ¬ current.val < stop.val := by simpa using hc
    simp [hc, hcv]

/-- The actual duplicate-search loop terminates and returns the first matching row slot, or its end. -/
theorem constructor_row_scan_spec
    (xs : Slice Usize) (stop needle start : Usize)
    (hstart : start.val ≤ stop.val) (hstop : stop.val ≤ xs.val.length) :
    WP.spec (topology.validate_row_entry_loop0 xs stop needle start)
      (fun found => start.val ≤ found.val ∧ found.val ≤ stop.val ∧
        (∀ i, start.val ≤ i → i < found.val → xs.val[i]? ≠ some needle) ∧
        (found.val < stop.val → xs.val[found.val]? = some needle)) := by
  let invariant : Usize → Prop := fun current =>
    start.val ≤ current.val ∧ current.val ≤ stop.val ∧
    ∀ i, start.val ≤ i → i < current.val → xs.val[i]? ≠ some needle
  unfold topology.validate_row_entry_loop0
  apply loop.spec_decr_nat (fun current : Usize => stop.val - current.val) invariant
  · intro current hi
    obtain ⟨hlo, hhi, hprefix⟩ := hi
    apply WP.spec_mono (constructor_scan_body xs stop needle current hstop)
    intro r hr
    cases r with
    | done found =>
      obtain ⟨rfl, hfound⟩ := hr
      exact ⟨hlo, hhi, hprefix, hfound⟩
    | cont next =>
      obtain ⟨hlt, hnext, hne⟩ := hr
      refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
      intro i hil hih
      by_cases he : i = current.val
      · simpa only [he] using hne
      · exact hprefix i hil (by omega)
  · exact ⟨le_rfl, hstart, fun _ hlo hhi => by omega⟩

end Labyrinth
