module
public import LabyrinthCore.ConstructorRowScan
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- The actual reciprocal-entry loop searches its complete CSR row and cannot run out of bounds. -/
theorem constructor_reverse_scan_spec
    (offsets xs : Slice Usize) (cell neighbor start stop : Usize)
    (hneighbor : neighbor.val + 1 < offsets.val.length)
    (hstopLookup : offsets.val[neighbor.val + 1]? = some stop)
    (hstart : start.val ≤ stop.val) (hstop : stop.val ≤ xs.val.length) :
    WP.spec (topology.validate_row_entry_loop1 offsets xs cell neighbor start)
      (fun found => start.val ≤ found.val ∧ found.val ≤ stop.val ∧
        (∀ i, start.val ≤ i → i < found.val → xs.val[i]? ≠ some cell) ∧
        (found.val < stop.val → xs.val[found.val]? = some cell)) := by
  let invariant : Usize → Prop := fun current =>
    start.val ≤ current.val ∧ current.val ≤ stop.val ∧
    ∀ i, start.val ≤ i → i < current.val → xs.val[i]? ≠ some cell
  unfold topology.validate_row_entry_loop1
  apply loop.spec_decr_nat (fun current : Usize => stop.val - current.val) invariant
  · intro current hi
    obtain ⟨hlo, hhi, hprefix⟩ := hi
    unfold topology.validate_row_entry_loop1.body
    apply WP.spec_bind (Usize.add_spec (x := neighbor) (y := 1#usize) (by
      have := offsets.property
      simp only [UScalar.ofNatCore_val_eq]
      omega))
    intro next hn
    have hnext : next.val = neighbor.val + 1 := by simpa using hn
    apply WP.spec_bind (Slice.index_usize_spec offsets next (by
      change next.val < offsets.val.length
      omega))
    intro rowEnd he
    have hgetEnd : offsets.val[next.val]? = some rowEnd := by
      rw [List.getElem?_eq_getElem (show next.val < offsets.val.length by omega), he]
    rw [hnext, hstopLookup] at hgetEnd
    have hend : rowEnd = stop := Option.some.inj hgetEnd.symm
    rw [hend]
    by_cases hc : current < stop
    · have hcv : current.val < stop.val := by simpa using hc
      simp only [hc, ite_true]
      apply WP.spec_bind (Slice.index_usize_spec xs current (by
        change current.val < xs.val.length
        omega))
      intro x hx
      have hget : xs.val[current.val]? = some x := by
        rw [List.getElem?_eq_getElem (show current.val < xs.val.length by omega), hx]
      by_cases heq : x = cell
      · simp only [bne_iff_ne, ne_eq, heq, not_true_eq_false, ite_false]
        apply (WP.spec_ok _).mpr
        exact ⟨hlo, hhi, hprefix, fun _ => hget.trans (congrArg some heq)⟩
      · simp only [bne_iff_ne, ne_eq, heq, not_false_eq_true, ite_true]
        apply WP.spec_bind (Usize.add_spec (x := current) (y := 1#usize) (by
          have := xs.property
          simp only [UScalar.ofNatCore_val_eq]
          omega))
        intro current' hcurrent'
        have hvalue : current'.val = current.val + 1 := by simpa using hcurrent'
        apply (WP.spec_ok _).mpr
        refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
        intro i hil hih
        by_cases he : i = current.val
        · rw [he, hget]
          exact fun h => heq (Option.some.inj h)
        · exact hprefix i hil (by omega)
    · have hcv : ¬ current.val < stop.val := by simpa using hc
      simp only [hc, ite_false]
      apply (WP.spec_ok _).mpr
      exact ⟨hlo, hhi, hprefix, fun hlt => (hcv hlt).elim⟩
  · exact ⟨le_rfl, hstart, fun _ hlo hhi => by omega⟩

def constructorRawRows (offsets xs : Slice Usize) : Prop :=
  ∀ v, v < offsets.val.length - 1 →
    ∃ lo hi : Usize, offsets.val[v]? = some lo ∧ offsets.val[v + 1]? = some hi ∧
      lo.val ≤ hi.val ∧ hi.val ≤ xs.val.length

def constructorRowEntryValid (offsets xs : Slice Usize)
    (cell index value : Usize) : Prop :=
  value.val < offsets.val.length - 1 ∧ value ≠ cell ∧
  (∀ i, (offsets.val[cell.val]?.getD 0#usize).val ≤ i → i < index.val →
    xs.val[i]? ≠ some value) ∧
  ∃ j, (offsets.val[value.val]?.getD 0#usize).val ≤ j ∧
    j < (offsets.val[value.val + 1]?.getD 0#usize).val ∧ xs.val[j]? = some cell

/-- Total row-entry validation with both soundness and acceptance of every valid entry. -/
theorem constructor_row_entry_spec
    (offsets xs : Slice Usize) (cell index value lo hi : Usize)
    (hsize : 2 ≤ offsets.val.length)
    (hrows : constructorRawRows offsets xs)
    (hcell : cell.val < offsets.val.length - 1)
    (hlo : offsets.val[cell.val]? = some lo)
    (_hhi : offsets.val[cell.val + 1]? = some hi)
    (hindex : lo.val ≤ index.val ∧ index.val < hi.val)
    (hstorage : hi.val ≤ xs.val.length)
    (hvalue : xs.val[index.val]? = some value) :
    WP.spec (topology.validate_row_entry offsets xs cell index) (fun result =>
      result = .Ok () ↔ constructorRowEntryValid offsets xs cell index value) := by
  unfold topology.validate_row_entry
  apply WP.spec_bind (Slice.index_usize_spec xs index (by
    change index.val < xs.val.length
    omega))
  intro value' hv
  have hevalue : value' = value := by
    have hg : xs.val[index.val]? = some value' := by
      rw [List.getElem?_eq_getElem (show index.val < xs.val.length by omega), hv]
    exact Option.some.inj (hg.symm.trans hvalue)
  rw [hevalue]
  apply WP.spec_bind (Usize.sub_spec (x := Slice.len offsets) (y := 1#usize) (by
    change 1 ≤ offsets.val.length
    omega))
  intro count hc
  have hcount : count.val = offsets.val.length - 1 := by
    simpa only [Slice.len_val, UScalar.ofNatCore_val_eq] using hc.1
  by_cases hbad : value ≥ count
  · simp only [hbad, ite_true]
    apply (WP.spec_ok _).mpr
    simp only [reduceCtorEq, false_iff]
    intro h
    have hbound := h.1
    have : count.val ≤ value.val := by simpa using hbad
    omega
  · simp only [hbad, ite_false]
    have hbounded : value.val < offsets.val.length - 1 := by
      have : ¬ count.val ≤ value.val := by simpa using hbad
      omega
    by_cases hself : value = cell
    · simp only [hself, ite_true]
      apply (WP.spec_ok _).mpr
      simp only [reduceCtorEq, false_iff]
      exact fun h => h.2.1 rfl
    · simp only [hself, ite_false]
      apply WP.spec_bind (Slice.index_usize_spec offsets cell (by
        change cell.val < offsets.val.length
        omega))
      intro start hs
      have hstart : start = lo := by
        have hg : offsets.val[cell.val]? = some start := by
          rw [List.getElem?_eq_getElem (show cell.val < offsets.val.length by omega), hs]
        exact Option.some.inj (hg.symm.trans hlo)
      rw [hstart]
      apply WP.spec_bind (constructor_row_scan_spec xs index value lo hindex.1 (by omega))
      intro found hf
      by_cases hduplicate : found < index
      · simp only [hduplicate, ite_true]
        apply (WP.spec_ok _).mpr
        simp only [reduceCtorEq, false_iff]
        intro hentry
        have hfound : found.val < index.val := by simpa using hduplicate
        have hnodup := hentry.2.2.1 found.val (by
          simpa only [hlo, Option.getD_some] using hf.1) hfound
        exact hnodup (hf.2.2.2 hfound)
      · simp only [hduplicate, ite_false]
        have hefound : found.val = index.val := by
          have : ¬ found.val < index.val := by simpa using hduplicate
          omega
        have hprefix : ∀ i, lo.val ≤ i → i < index.val → xs.val[i]? ≠ some value := by
          simpa only [hefound] using hf.2.2.1
        obtain ⟨reverseLo, reverseHi, hrlo, hrhi, hrordered, hrstorage⟩ :=
          hrows value.val hbounded
        apply WP.spec_bind (Slice.index_usize_spec offsets value (by
          change value.val < offsets.val.length
          omega))
        intro reverseStart hrs
        have hrstart : reverseStart = reverseLo := by
          have hg : offsets.val[value.val]? = some reverseStart := by
            rw [List.getElem?_eq_getElem (show value.val < offsets.val.length by omega), hrs]
          exact Option.some.inj (hg.symm.trans hrlo)
        rw [hrstart]
        apply WP.spec_bind (constructor_reverse_scan_spec offsets xs cell value reverseLo
          reverseHi (by omega) hrhi hrordered hrstorage)
        intro reverseFound hrf
        apply WP.spec_bind (Usize.add_spec (x := value) (y := 1#usize) (by
          have := offsets.property
          simp only [UScalar.ofNatCore_val_eq]
          omega))
        intro reverseNext hrnext
        have hnext : reverseNext.val = value.val + 1 := by simpa using hrnext
        apply WP.spec_bind (Slice.index_usize_spec offsets reverseNext (by
          change reverseNext.val < offsets.val.length
          omega))
        intro reverseEnd hre
        have hrend : reverseEnd = reverseHi := by
          have hg : offsets.val[reverseNext.val]? = some reverseEnd := by
            rw [List.getElem?_eq_getElem (show reverseNext.val < offsets.val.length by omega), hre]
          rw [hnext, hrhi] at hg
          exact Option.some.inj hg.symm
        rw [hrend]
        by_cases hmissing : reverseFound = reverseHi
        · simp only [hmissing, ite_true]
          apply (WP.spec_ok _).mpr
          simp only [reduceCtorEq, false_iff]
          intro hentry
          obtain ⟨j, hjlo, hjhi, hj⟩ := hentry.2.2.2
          simp only [hrlo, hrhi, Option.getD_some] at hjlo hjhi
          exact hrf.2.2.1 j hjlo (by simpa only [hmissing] using hjhi) hj
        · simp only [hmissing, ite_false]
          apply (WP.spec_ok _).mpr
          simp only [true_iff]
          have hlt : reverseFound.val < reverseHi.val := by
            have hne : reverseFound.val ≠ reverseHi.val := by
              intro he
              exact hmissing ((UScalar.eq_equiv _ _).mpr he)
            omega
          refine ⟨hbounded, hself, ?_, reverseFound.val, ?_, ?_, hrf.2.2.2 hlt⟩
          · simpa only [hlo, Option.getD_some] using hprefix
          · simpa only [hrlo, Option.getD_some] using hrf.1
          · simpa only [hrhi, Option.getD_some] using hlt

end Labyrinth
