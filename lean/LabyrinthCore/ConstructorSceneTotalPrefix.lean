module
public import LabyrinthCore.ConstructorPrefixOffsets
public import LabyrinthCore.ConstructorQuotientDegrees
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- Exact successful state at the end of the literal quotient prefix/allocation guards.
`counts` is retained existentially because the generated constructor keeps only the prefixed
offset vector. -/
def ConstructorScenePrefixSuccess (carrier : topology.Carrier)
    (componentCount : Usize) (label : Usize → Usize)
    (offsets : alloc.vec.Vec Usize) (adjacencyCount : Usize) : Prop :=
  ∃ (countWidth : Usize) (counts : List Usize),
    countWidth.val = counts.length ∧ counts.length = componentCount.val + 1 ∧
    (∀ slot, slot < counts.length → ∃ value : Usize,
      counts[slot]? = some value ∧ value.val =
        constructorQuotientDegreeSlot carrier.edges.val label slot carrier.edges.val.length) ∧
    offsets.val.length = counts.length ∧
    (∀ slot, slot < offsets.val.length → ∃ value : Usize,
      offsets.val[slot]? = some value ∧
        value.val = constructorPrefixSum counts (slot + 1)) ∧
    adjacencyCount.val = constructorPrefixSum counts counts.length ∧
    constructorStorageFits countWidth 8#usize ∧
    constructorStorageFits adjacencyCount 8#usize ∧
    constructorStorageFits adjacencyCount 16#usize

/-- The literal checked prefix-sum operation is total on every nonempty representable slice.
It preserves the slice length, returns only success or the checked-add `Overflow`, and a success
contains the exact mathematical prefix sums of the original input. -/
theorem constructor_prefix_offsets_total_spec (input : Slice Usize)
    (hnonempty : 0 < input.val.length) :
    WP.spec (topology.prefix_offsets input) (fun output =>
      output.2.val.length = input.val.length ∧
      (output.1 = .Ok () → ∀ j, j < input.val.length → ∃ value : Usize,
        output.2.val[j]? = some value ∧ value.val = constructorPrefixSum input.val (j + 1)) ∧
      (output.1 = .Ok () ∨ output.1 = .Err topology.Error.Overflow)) := by
  let invariant : Slice Usize × Usize × core.result.Result Unit topology.Error → Prop :=
    fun state =>
      state.1.val.length = input.val.length ∧
      1 ≤ state.2.1.val ∧ state.2.1.val ≤ input.val.length ∧
      ((state.2.2 = .Ok () ∧
          (∀ j, j < state.2.1.val → ∃ value : Usize,
            state.1.val[j]? = some value ∧
              value.val = constructorPrefixSum input.val (j + 1)) ∧
          (∀ j, state.2.1.val ≤ j → state.1.val[j]? = input.val[j]?)) ∨
        state.2.2 = .Err topology.Error.Overflow)
  unfold topology.prefix_offsets topology.prefix_offsets_loop
  apply loop.spec_decr_nat
    (fun state : Slice Usize × Usize × core.result.Result Unit topology.Error =>
      input.val.length - state.2.1.val) invariant
  · rintro ⟨current, index, status⟩ hinvariant
    obtain ⟨hlen, hpositive, hindex, hok | hoverflow⟩ := hinvariant
    · obtain ⟨hstatus, hprefix, hsuffix⟩ := hok
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
        obtain ⟨previousValue, hprefixLookup, hprefixValue⟩ :=
          hprefix previous.val (by omega)
        have heq : previousValue = accumulated :=
          Option.some.inj (hprefixLookup.symm.trans hprefLookup)
        subst previousValue
        have hsum : accumulated.val = constructorPrefixSum input.val index.val := by
          have hsucc : previous.val + 1 = index.val := by omega
          simpa only [hsucc] using hprefixValue
        cases hchecked : Usize.checked_add degree accumulated with
        | none =>
            simp only [lift, bind_ok]
            apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
              have := current.property
              simp only [UScalar.ofNatCore_val_eq]
              omega))
            intro next hn
            have hnext : next.val = index.val + 1 := by simpa using hn
            apply (WP.spec_ok _).mpr
            dsimp only [invariant]
            exact ⟨⟨hlen, by omega, by omega, Or.inr rfl⟩, by omega⟩
        | some sum =>
            simp only [lift, bind_ok]
            have hcheckedSpec := Usize.checked_add_bv_spec degree accumulated
            simp only [hchecked] at hcheckedSpec
            have hsumValue : sum.val = degree.val + accumulated.val := hcheckedSpec.2.1
            have hnextSum : sum.val = constructorPrefixSum input.val (index.val + 1) := by
              simp only [constructorPrefixSum, hsource, Option.getD_some, hsumValue, hsum]
              omega
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
            refine ⟨⟨by simpa using hlen, by omega, by omega, Or.inl ⟨rfl, ?_, ?_⟩⟩,
              by omega⟩
            · intro j hj
              by_cases he : j = index.val
              · subst j
                exact ⟨sum, by simp [hi], hnextSum⟩
              · obtain ⟨value, hv, hvsum⟩ := hprefix j (by omega)
                exact ⟨value, by simpa [he, Ne.symm he] using hv, hvsum⟩
            · intro j hj
              have he : j ≠ index.val := by omega
              simpa [he, Ne.symm he] using hsuffix j (by omega)
      · have heq : index.val = input.val.length := by
          have : ¬ index.val < current.val.length := by simpa using hmore
          omega
        simp only [hmore, ite_false]
        apply (WP.spec_ok _).mpr
        refine ⟨hlen, ?_, Or.inl rfl⟩
        intro _ j hj
        exact hprefix j (by omega)
    · dsimp only at hlen hpositive hindex hoverflow
      subst status
      unfold topology.prefix_offsets_loop.body
      by_cases hmore : index < Slice.len current
      · simp only [hmore, ite_true, core.result.Result.is_ok, bind_ok,
          Bool.false_eq_true, ite_false]
        apply (WP.spec_ok _).mpr
        exact ⟨hlen, by simp, Or.inr rfl⟩
      · simp only [hmore, ite_false]
        apply (WP.spec_ok _).mpr
        exact ⟨hlen, by simp, Or.inr rfl⟩
  · dsimp only [invariant]
    refine ⟨rfl, by simp, ?_, Or.inl ⟨rfl, ?_, ?_⟩⟩
    · change 1 ≤ input.val.length
      omega
    · intro j hj
      have hjzero : j = 0 := by
        change j < 1 at hj
        omega
      subst j
      let value := input.val[0]'hnonempty
      have hvalue : input.val[0]? = some value := List.getElem?_eq_getElem hnonempty
      exact ⟨value, hvalue, by simp [constructorPrefixSum, hvalue]⟩
    · intro j hj
      rfl

end Labyrinth
