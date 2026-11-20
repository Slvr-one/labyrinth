module
public import LabyrinthCore.MutationValidate

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

 theorem mutation_carrier_symmetric (c : topology.Carrier) (hc : CarrierValid c)
    (u v : Nat) : carrierEdge c u v ↔ carrierEdge c v u := by
  constructor
  · rintro ⟨hu, hmem⟩
    exact (hc.2.2.2.2.1 u hu).2.2 v hmem
  · rintro ⟨hv, hmem⟩
    exact (hc.2.2.2.2.1 v hv).2.2 u hmem

 theorem mutation_canonical_contains_total (c : topology.Carrier) (u v : Usize)
    (hc : CarrierValid c) :
    (do
      let edge ← topology.Edge.new u v
      topology.Carrier.contains_edge c edge) ⦃ result =>
        (result = true ↔ carrierEdge c u.val v.val) ⦄ := by
  unfold topology.Edge.new
  split
  · simpa only [bind_ok] using mutation_carrier_contains_total c {u, v} hc
  · simpa only [bind_ok, mutation_carrier_symmetric c hc v.val u.val] using
      mutation_carrier_contains_total c {u := v, v := u} hc

 theorem mutation_check_carrier_loop_total
    (v : alloc.vec.Vec Usize) (root : Usize) (c : topology.Carrier)
    (start : Usize) (valid : Bool) (hc : CarrierValid c)
    (hs : start.val ≤ v.val.length) :
    spanning_tree.Tree.check_carrier_loop v root c start valid ⦃ result =>
      (result = true ↔ valid = true ∧
        ∀ j, start.val ≤ j → j < v.val.length →
          j = root.val ∨ carrierEdge c j (parentAt (v.val.map (·.val)) j)) ⦄ := by
  let good := fun j => j = root.val ∨ carrierEdge c j (parentAt (v.val.map (·.val)) j)
  let suffix := fun k => ∀ j, k ≤ j → j < v.val.length → good j
  let target := valid = true ∧ suffix start.val
  unfold spanning_tree.Tree.check_carrier_loop
  apply loop.spec_decr_nat
    (fun state : Usize × Bool => v.val.length - state.1.val)
    (fun state : Usize × Bool => state.1.val ≤ v.val.length ∧
      ((state.2 = true ∧ suffix state.1.val) ↔ target))
    (fun result : Bool => result = true ↔ target)
  · rintro ⟨current, flag⟩ ⟨hcurrent, hinv⟩
    dsimp only at hcurrent hinv ⊢
    unfold spanning_tree.Tree.check_carrier_loop.body
    by_cases hlt : current < alloc.vec.Vec.len v
    · have hltNat : current.val < v.val.length := hlt
      simp only [hlt, ite_true]
      cases flag with
      | false => simpa [target] using hinv
      | true =>
        simp only [ite_true]
        have htest : (if current = root then Result.ok true else do
            let next ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Usize) v current
            let edge ← topology.Edge.new current next
            topology.Carrier.contains_edge c edge) ⦃ answer =>
              (answer = true ↔ good current.val) ⦄ := by
          by_cases heq : current = root
          · simp [heq, good]
          · simp only [heq, ite_false, alloc.vec.Vec.index_slice_index]
            step with (alloc.vec.Vec.index_usize_spec v current hltNat) as ⟨next, hnext⟩
            have hnval : next.val = parentAt (v.val.map (·.val)) current.val := by
              rw [hnext]
              exact (mutation_parent_get v current hltNat).symm
            have hne : current.val ≠ root.val := fun h => heq (UScalar.eq_of_val_eq h)
            simpa only [good, hne, false_or, hnval] using
              mutation_canonical_contains_total c current next hc
        apply spec_bind htest
        intro answer hanswer
        apply spec_bind (Usize.add_spec (x := current) (y := 1#usize) (by scalar_tac))
        intro next hnext
        have hnextval : next.val = current.val + 1 := by simpa using hnext
        have hsplit : suffix current.val ↔ good current.val ∧ suffix next.val := by
          constructor
          · intro h
            exact ⟨h _ (by omega) hltNat, fun j hj hjn => h j (by omega) hjn⟩
          · rintro ⟨hhere, hrest⟩ j hj hjn
            by_cases heq : j = current.val
            · simpa [heq] using hhere
            · exact hrest j (by omega) hjn
        simp only [spec_ok]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        simpa only [hsplit, Bool.true_eq, true_and, hanswer] using hinv
    · have hge : v.val.length ≤ current.val := Nat.le_of_not_lt hlt
      have hempty : suffix current.val := by
        intro j hj hjn
        omega
      simpa [hlt, hempty] using hinv
  · exact ⟨hs, Iff.rfl⟩

 def MutationCarrierCompatible (c : topology.Carrier) (t : spanning_tree.Tree) : Prop :=
  t.parents.val.length = cellCount c ∧
  t.root.val < t.parents.val.length ∧
  t.parents.val[t.root.val]? = some t.root ∧
  ∀ j, j < t.parents.val.length → j ≠ t.root.val →
    carrierEdge c j (parentAt (parents t) j)

 theorem mutation_compatible_bounds (c : topology.Carrier) (t : spanning_tree.Tree)
    (hc : CarrierValid c) (ht : MutationCarrierCompatible c t) :
    (∀ x ∈ parents t, x < (parents t).length) ∧
    (parents t)[t.root.val]? = some t.root.val := by
  have hroot : (parents t)[t.root.val]? = some t.root.val := by
    simp [parents, ht.2.2.1]
  refine ⟨?_, hroot⟩
  intro x hx
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hx
  have hparent : parentAt (parents t) j = x := by
    simp only [parentAt, List.getElem?_eq_getElem hj, Option.getD_some, hget]
  by_cases hrootIndex : j = t.root.val
  · have hxRoot : x = t.root.val := by
      rw [hrootIndex] at hparent
      simpa [parentAt, hroot] using hparent.symm
    simpa [hxRoot, parents] using ht.2.1
  · have hjRaw : j < t.parents.val.length := by simpa [parents] using hj
    have hedge := ht.2.2.2 j hjRaw hrootIndex
    have hxBound := (hc.2.2.2.2.1 j hedge.1).2.2 _ hedge.2
    have hx : x < cellCount c := by simpa only [hparent] using hxBound.1
    simpa only [parents, List.length_map, ht.1] using hx

 theorem mutation_tree_valid_compatible (c : topology.Carrier) (t : spanning_tree.Tree)
    (ht : TreeValid c t) : MutationCarrierCompatible c t := by
  have hrootbound : t.root.val < t.parents.val.length := by
    simpa [parents] using ht.2.1.1
  have hrootGet : t.parents.val[t.root.val]? = some t.root := by
    rw [List.getElem?_eq_getElem hrootbound]
    apply congrArg some
    apply UScalar.eq_of_val_eq
    have hroot := ht.2.1.2.1
    simpa [parents, hrootbound] using hroot
  exact ⟨by simpa [parents] using ht.1, hrootbound, hrootGet,
    fun j hj hne => ht.2.2 j (by simpa [parents] using hj) hne⟩

 theorem mutation_check_carrier_total (c : topology.Carrier) (t : spanning_tree.Tree)
    (hc : CarrierValid c) :
    spanning_tree.Tree.check_carrier t c ⦃ result =>
      (result = core.result.Result.Ok () ∨ result = core.result.Result.Err topology.Error.InvalidTree) ∧
      (result = core.result.Result.Ok () ↔ MutationCarrierCompatible c t) ⦄ := by
  unfold spanning_tree.Tree.check_carrier
  step with (mutation_carrier_len_total c hc) as ⟨count, hcount⟩
  by_cases heq : alloc.vec.Vec.len t.parents = count
  · have hlen : t.parents.val.length = cellCount c := by scalar_tac
    have hbeq : (alloc.vec.Vec.len t.parents != count) = false := by simp [heq]
    simp only [hbeq, Bool.false_eq_true, ite_false]
    by_cases hbadRoot : t.root ≥ alloc.vec.Vec.len t.parents
    · have hnot : ¬ t.root.val < t.parents.val.length := by scalar_tac
      simp [hbadRoot, MutationCarrierCompatible, hnot]
    · simp only [hbadRoot, ite_false]
      have hrootbound : t.root.val < t.parents.val.length := by scalar_tac
      step with (alloc.vec.Vec.index_usize_spec t.parents t.root hrootbound)
        as ⟨rootParent, hrootParent⟩
      by_cases hroot : rootParent = t.root
      · have hrootGet : t.parents.val[t.root.val]? = some t.root := by
          rw [List.getElem?_eq_getElem hrootbound]
          exact congrArg some (hrootParent.symm.trans hroot)
        simp only [hroot, bne_self_eq_false, Bool.false_eq_true, ite_false]
        step with (mutation_check_carrier_loop_total t.parents t.root c 0#usize true hc (by simp))
          as ⟨answer, hanswer⟩
        have hloop : answer = true ↔ ∀ j, j < t.parents.val.length →
            j = t.root.val ∨ carrierEdge c j (parentAt (parents t) j) := by
          simpa [parents] using hanswer
        have hcompatible : MutationCarrierCompatible c t ↔ answer = true := by
          constructor
          · intro h
            apply hloop.mpr
            intro j hj
            by_cases he : j = t.root.val
            · exact Or.inl he
            · exact Or.inr (h.2.2.2 j hj he)
          · intro h
            refine ⟨hlen, hrootbound, hrootGet, ?_⟩
            intro j hj hne
            exact (hloop.mp h j hj).resolve_left hne
        cases answer with
        | false =>
          have hnot : ¬ MutationCarrierCompatible c t := by
            simpa only [Bool.false_eq_true, iff_false] using hcompatible
          simp [hnot]
        | true =>
          have hyes : MutationCarrierCompatible c t := hcompatible.mpr rfl
          simp [hyes]
      · have hbne : (rootParent != t.root) = true := by simp [hroot]
        have hnot : t.parents.val[t.root.val]? ≠ some t.root := by
          intro hget
          rw [List.getElem?_eq_getElem hrootbound] at hget
          exact hroot (hrootParent.trans (Option.some.inj hget))
        simp [hbne, MutationCarrierCompatible, hnot]
  · have hbne : (alloc.vec.Vec.len t.parents != count) = true := by simp [heq]
    have hnot : t.parents.val.length ≠ cellCount c := by
      intro h
      apply heq
      apply UScalar.eq_of_val_eq
      simpa using h.trans hcount.symm
    simp [hbne, MutationCarrierCompatible, hnot]

 theorem mutation_validate_total (c : topology.Carrier) (t : spanning_tree.Tree)
    (hc : CarrierValid c) :
    spanning_tree.Tree.validate t c ⦃ result =>
      (result = core.result.Result.Ok () ∨ result = core.result.Result.Err topology.Error.InvalidTree) ∧
      (result = core.result.Result.Ok () ↔ TreeValid c t) ⦄ := by
  unfold spanning_tree.Tree.validate
  step with (mutation_check_carrier_total c t hc) as ⟨checked, hcases, hchecked⟩
  cases checked with
  | Err error =>
    have he : error = topology.Error.InvalidTree := by simpa using hcases
    have hnotCompatible : ¬ MutationCarrierCompatible c t := by simpa using hchecked.symm
    have hnotTree : ¬ TreeValid c t := fun ht => hnotCompatible (mutation_tree_valid_compatible c t ht)
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, he, hnotTree]
  | Ok value =>
    cases value
    have hcompatible : MutationCarrierCompatible c t := hchecked.mp rfl
    obtain ⟨hbounded, hroot⟩ := mutation_compatible_bounds c t hc hcompatible
    have hfixed : parentAt (parents t) t.root.val = t.root.val := by simp [parentAt, hroot]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with (mutation_validate_sweep_total t.parents t.root (alloc.vec.Vec.len t.parents)
      0#usize true rfl (by simpa [parents] using hbounded) hfixed (by simp))
      as ⟨answer, hanswer⟩
    have hloop : answer = true ↔ ∀ j, j < (parents t).length →
        follow (parents t) (parents t).length j = t.root.val := by
      simpa [parents] using hanswer
    have hvalid : TreeValid c t ↔ answer = true := by
      rw [hloop]
      constructor
      · intro h
        exact h.2.1.2.2.2
      · intro h
        refine ⟨by simpa [parents] using hcompatible.1, ?_, ?_⟩
        · exact ⟨by simpa [parents] using hcompatible.2.1, hroot, hbounded, h⟩
        · intro j hj hne
          exact hcompatible.2.2.2 j (by simpa [parents] using hj) hne
    cases answer with
    | false =>
      have hnot : ¬ TreeValid c t := by
        simpa only [Bool.false_eq_true, iff_false] using hvalid
      simp [hnot]
    | true =>
      have hyes : TreeValid c t := hvalid.mpr rfl
      simp [hyes]

end Labyrinth
