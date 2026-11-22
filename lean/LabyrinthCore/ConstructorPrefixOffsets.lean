module
public import LabyrinthCore.Model
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- Mathematical prefix sum of the original degree vector, independent of the operation. -/
def constructorPrefixSum (values : List Usize) : Nat → Nat
  | 0 => 0
  | k + 1 => constructorPrefixSum values k + (values[k]?.getD 0#usize).val

theorem constructor_checked_add_some (x y : Usize)
    (h : x.val + y.val ≤ Usize.max) :
    ∃ z, Usize.checked_add x y = some z ∧ z.val = x.val + y.val := by
  have hs := Usize.checked_add_bv_spec x y
  cases he : Usize.checked_add x y with
  | none => simp only [he] at hs; omega
  | some z =>
    simp only [he] at hs
    exact ⟨z, rfl, hs.2.1⟩

/-- Every numeric prefix is bounded by the complete degree sum. -/
theorem constructor_prefix_sum_mono (values : List Usize) {a b : Nat} (h : a ≤ b) :
    constructorPrefixSum values a ≤ constructorPrefixSum values b := by
  induction h with
  | refl => exact le_rfl
  | @step b h ih =>
    exact le_trans ih (by simp only [constructorPrefixSum]; omega)

/-- The actual checked prefix-sum loop accepts every representable nonempty degree vector. -/
theorem constructor_prefix_offsets_spec (input : Slice Usize)
    (hnonempty : 0 < input.val.length)
    (hwidth : constructorPrefixSum input.val input.val.length ≤ Usize.max) :
    WP.spec (topology.prefix_offsets input) (fun result =>
      result.1 = .Ok () ∧ result.2.val.length = input.val.length ∧
      ∀ j, j < input.val.length → ∃ value : Usize,
        result.2.val[j]? = some value ∧ value.val = constructorPrefixSum input.val (j + 1)) := by
  let invariant : Slice Usize × Usize × core.result.Result Unit topology.Error → Prop :=
    fun state =>
      state.1.val.length = input.val.length ∧
      1 ≤ state.2.1.val ∧ state.2.1.val ≤ input.val.length ∧ state.2.2 = .Ok () ∧
      (∀ j, j < state.2.1.val → ∃ value : Usize,
        state.1.val[j]? = some value ∧ value.val = constructorPrefixSum input.val (j + 1)) ∧
      (∀ j, state.2.1.val ≤ j → state.1.val[j]? = input.val[j]?)
  unfold topology.prefix_offsets topology.prefix_offsets_loop
  apply loop.spec_decr_nat
    (fun state : Slice Usize × Usize × core.result.Result Unit topology.Error =>
      input.val.length - state.2.1.val) invariant
  · rintro ⟨current, index, status⟩ hinv
    obtain ⟨hlen, hpositive, hindex, hstatus, hprefix, hsuffix⟩ := hinv
    dsimp only at hlen hpositive hindex hstatus hprefix hsuffix
    subst status
    unfold topology.prefix_offsets_loop.body
    by_cases hmore : index < Slice.len current
    · have hi : index.val < current.val.length := by simpa using hmore
      simp only [hmore, ite_true, core.result.Result.is_ok, bind_ok]
      apply WP.spec_bind (Slice.index_usize_spec current index hi)
      intro degree hd
      have hdegree : current.val[index.val]? = some degree := by
        rw [List.getElem?_eq_getElem hi, hd]
      have hsource : input.val[index.val]? = some degree :=
        (hsuffix index.val le_rfl).symm.trans hdegree
      apply WP.spec_bind (Usize.sub_spec (x := index) (y := 1#usize) (by
        simpa only [UScalar.ofNatCore_val_eq] using hpositive))
      intro previous hp
      have hprevious : previous.val = index.val - 1 := by simpa using hp.1
      have hpreviousBound : previous.val < current.val.length := by omega
      apply WP.spec_bind (Slice.index_usize_spec current previous hpreviousBound)
      intro accumulated hpref
      have hprefLookup : current.val[previous.val]? = some accumulated := by
        rw [List.getElem?_eq_getElem hpreviousBound, hpref]
      obtain ⟨prefix', hlookup', hsum'⟩ := hprefix previous.val (by omega)
      have heq : prefix' = accumulated := Option.some.inj (hlookup'.symm.trans hprefLookup)
      subst prefix'
      have hsum : accumulated.val = constructorPrefixSum input.val index.val := by
        have hsucc : previous.val + 1 = index.val := by omega
        simpa only [hsucc] using hsum'
      have hnextSum : degree.val + accumulated.val =
          constructorPrefixSum input.val (index.val + 1) := by
        simp only [constructorPrefixSum, hsource, Option.getD_some, hsum]
        omega
      have hfits : degree.val + accumulated.val ≤ Usize.max := by
        rw [hnextSum]
        exact le_trans (constructor_prefix_sum_mono input.val (by omega)) hwidth
      obtain ⟨sum, hchecked, hsumValue⟩ := constructor_checked_add_some degree accumulated hfits
      simp only [hchecked, lift, bind_ok]
      apply WP.spec_bind (Slice.update_spec current index sum hi)
      intro updated hupdated
      subst updated
      apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
        have := current.property
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro next hn
      have hnext : next.val = index.val + 1 := by simpa using hn
      apply (WP.spec_ok _).mpr
      dsimp only [invariant]
      refine ⟨⟨by simpa using hlen, by omega, by omega, rfl, ?_, ?_⟩, by omega⟩
      · intro j hj
        by_cases he : j = index.val
        · subst j
          refine ⟨sum, ?_, hsumValue.trans hnextSum⟩
          simp [hi]
        · obtain ⟨value, hv, hvsum⟩ := hprefix j (by omega)
          exact ⟨value, by simpa [he, Ne.symm he] using hv, hvsum⟩
      · intro j hj
        have he : j ≠ index.val := by omega
        simpa [he, Ne.symm he] using hsuffix j (by omega)
    · have he : index.val = input.val.length := by
        have : ¬ index.val < current.val.length := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      exact ⟨rfl, hlen, by simpa only [he] using hprefix⟩
  · refine ⟨rfl, by simp, by change 1 ≤ input.val.length; omega, rfl, ?_, ?_⟩
    · intro j hj
      have hjzero : j = 0 := by simpa using hj
      subst j
      let value := input.val[0]'hnonempty
      have hvalue : input.val[0]? = some value := List.getElem?_eq_getElem hnonempty
      exact ⟨value, hvalue, by simp [constructorPrefixSum, hvalue]⟩
    · intro j _
      rfl

end Labyrinth
