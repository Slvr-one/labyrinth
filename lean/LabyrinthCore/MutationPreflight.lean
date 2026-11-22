module
public import LabyrinthCore.MutationValidator

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

 theorem mutation_has_edge_total (t : spanning_tree.Tree) (edge : topology.Edge) :
    spanning_tree.Tree.has_edge t edge ⦃ answer =>
      (answer = true ↔ parentEdge (parents t) edge.u.val edge.v.val) ⦄ := by
  unfold spanning_tree.Tree.has_edge
  by_cases hu : edge.u < alloc.vec.Vec.len t.parents
  · simp only [hu, ite_true]
    have huNat : edge.u.val < t.parents.val.length := hu
    by_cases hv : edge.v < alloc.vec.Vec.len t.parents
    · simp only [hv, ite_true]
      have hvNat : edge.v.val < t.parents.val.length := hv
      by_cases heq : edge.u = edge.v
      · simp [heq, parentEdge]
      · have hbne : (edge.u != edge.v) = true := by simp [heq]
        have hne : edge.u.val ≠ edge.v.val := fun h => heq (UScalar.eq_of_val_eq h)
        simp only [hbne, ite_true, alloc.vec.Vec.index_slice_index]
        apply spec_bind (alloc.vec.Vec.index_usize_spec t.parents edge.u huNat)
        intro up hup
        have hupGet : (parents t)[edge.u.val]? = some up.val := by
          simp [parents, huNat, hup]
        by_cases hupEq : up = edge.v
        · simp only [hupEq, ite_true]
          apply (spec_ok _).mpr
          exact ⟨fun _ => ⟨by simpa [parents] using huNat,
            by simpa [parents] using hvNat, hne,
            Or.inl (by simpa only [hupEq] using hupGet)⟩, fun _ => rfl⟩
        · have hupNe : up.val ≠ edge.v.val := fun h => hupEq (UScalar.eq_of_val_eq h)
          simp only [hupEq, ite_false]
          apply spec_bind (alloc.vec.Vec.index_usize_spec t.parents edge.v hvNat)
          intro vp hvp
          have hvpGet : (parents t)[edge.v.val]? = some vp.val := by
            simp [parents, hvNat, hvp]
          apply (spec_ok _).mpr
          simp only [decide_eq_true_eq]
          constructor
          · intro he
            exact ⟨by simpa [parents] using huNat, by simpa [parents] using hvNat, hne,
              Or.inr (by simpa only [he] using hvpGet)⟩
          · rintro ⟨_, _, _, hleft | hright⟩
            · exact (hupNe (Option.some.inj (hupGet.symm.trans hleft))).elim
            · exact UScalar.eq_of_val_eq (Option.some.inj (hvpGet.symm.trans hright))
    · have hvNat : ¬ edge.v.val < t.parents.val.length := hv
      simp [hv, parentEdge, parents, hvNat]
  · have huNat : ¬ edge.u.val < t.parents.val.length := hu
    simp [hu, parentEdge, parents, huNat]

 def mutationCanonicalEdge (edge : topology.Edge) : topology.Edge :=
  if edge.u ≤ edge.v then edge else { u := edge.v, v := edge.u }

 theorem mutation_edge_new_total (u v : Usize) :
    topology.Edge.new u v ⦃ result => result = mutationCanonicalEdge {u, v} ⦄ := by
  unfold topology.Edge.new mutationCanonicalEdge
  split <;> simp

 theorem mutation_edge_equal_total (a b : topology.Edge) :
    topology.Edge.Insts.CoreCmpPartialEqEdge.eq a b ⦃ answer =>
      (answer = true ↔ a.u = b.u ∧ a.v = b.v) ⦄ := by
  unfold topology.Edge.Insts.CoreCmpPartialEqEdge.eq
  split <;> simp_all

 theorem mutation_edge_ne_total (a b : topology.Edge) :
    core.cmp.PartialEq.ne.trait_default topology.Edge.Insts.CoreCmpPartialEqEdge a b
      ⦃ answer => answer = true ↔ a ≠ b ⦄ := by
  apply core.cmp.PartialEq.ne.trait_default.spec
  apply spec_mono (mutation_edge_equal_total a b)
  intro answer hanswer
  rw [hanswer]
  constructor
  · intro h
    cases a
    cases b
    simp_all
  · intro h
    cases h
    exact ⟨rfl, rfl⟩

 theorem mutation_removed_scan_total (remove : Slice topology.Edge)
    (u v start : Usize) (hs : start.val ≤ remove.val.length)
    (hprefix : ∀ j, j < start.val → ∀ edge, remove.val[j]? = some edge →
      (mutationCanonicalEdge edge).u ≠ u ∨ (mutationCanonicalEdge edge).v ≠ v) :
    spanning_tree.Tree.check_edit_loop1 remove u v start ⦃ result =>
      result.val ≤ remove.val.length ∧
      (∀ j, j < result.val → ∀ edge, remove.val[j]? = some edge →
        (mutationCanonicalEdge edge).u ≠ u ∨ (mutationCanonicalEdge edge).v ≠ v) ∧
      (result.val < remove.val.length → ∃ edge, remove.val[result.val]? = some edge ∧
        (mutationCanonicalEdge edge).u = u ∧ (mutationCanonicalEdge edge).v = v) ⦄ := by
  unfold spanning_tree.Tree.check_edit_loop1
  apply loop.spec_decr_nat
    (fun i : Usize => remove.val.length - i.val)
    (fun i : Usize => i.val ≤ remove.val.length ∧
      ∀ j, j < i.val → ∀ edge, remove.val[j]? = some edge →
        (mutationCanonicalEdge edge).u ≠ u ∨ (mutationCanonicalEdge edge).v ≠ v)
    _
  · intro current hcurrent
    unfold spanning_tree.Tree.check_edit_loop1.body
    by_cases hlt : current < Slice.len remove
    · have hltNat : current.val < remove.val.length := hlt
      simp only [hlt, ite_true]
      apply spec_bind (Slice.index_usize_spec remove current hltNat)
      intro edge hedge
      have hedgeGet : remove.val[current.val]? = some edge := by
        rw [List.getElem?_eq_getElem hltNat]
        exact congrArg some hedge.symm
      apply spec_bind (mutation_edge_new_total edge.u edge.v)
      intro canonical hcanonical
      have hcanonicalEq : canonical = mutationCanonicalEdge edge := hcanonical
      apply spec_bind (mutation_edge_ne_total canonical {u, v})
      intro different hdifferent
      cases different with
      | false =>
        have heq : canonical = {u, v} := by
          by_contra hne
          exact Bool.false_ne_true (hdifferent.mpr hne)
        have he : canonical.u = u ∧ canonical.v = v := by simp [heq]
        simp only [Bool.false_eq_true, ite_false, spec_ok]
        exact ⟨hcurrent.1, hcurrent.2, fun _ => ⟨edge, hedgeGet, by simpa only [hcanonicalEq] using he⟩⟩
      | true =>
        have hne : (mutationCanonicalEdge edge).u ≠ u ∨ (mutationCanonicalEdge edge).v ≠ v := by
          have hn := hdifferent.mp rfl
          by_contra h
          push Not at h
          apply hn
          rw [hcanonicalEq]
          cases hcanon : mutationCanonicalEdge edge
          simp_all
        simp only [ite_true]
        apply spec_bind (Usize.add_spec (x := current) (y := 1#usize) (by scalar_tac))
        intro next hnext
        have hnextVal : next.val = current.val + 1 := by simpa using hnext
        simp only [spec_ok]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        intro j hj earlier hearlier
        by_cases heq : j = current.val
        · have he : earlier = edge := by
            rw [heq, hedgeGet] at hearlier
            exact (Option.some.inj hearlier).symm
          simpa only [he] using hne
        · exact hcurrent.2 j (by omega) earlier hearlier
    · simp only [hlt, ite_false, spec_ok]
      exact ⟨hcurrent.1, hcurrent.2, fun h => False.elim (hlt h)⟩
  · exact ⟨hs, hprefix⟩

 def mutationDuplicateAt (remove add : Slice topology.Edge)
    (ru rv au av : Usize) (j : Nat) : Prop :=
    (∃ edge, remove.val[j]? = some edge ∧
      (mutationCanonicalEdge edge).u = ru ∧ (mutationCanonicalEdge edge).v = rv) ∨
    (∃ edge, add.val[j]? = some edge ∧
      (mutationCanonicalEdge edge).u = au ∧ (mutationCanonicalEdge edge).v = av)

 theorem mutation_duplicate_scan_total (remove add : Slice topology.Edge)
    (index ru rv au av : Usize)
    (hr : index.val ≤ remove.val.length) (ha : index.val ≤ add.val.length) :
    spanning_tree.Tree.check_edit_loop0 remove add index ru rv au av false 0#usize
      ⦃ answer => answer = true ↔
        ∃ j, j < index.val ∧ mutationDuplicateAt remove add ru rv au av j ⦄ := by
  let duplicateAt := mutationDuplicateAt remove add ru rv au av
  unfold spanning_tree.Tree.check_edit_loop0
  apply loop.spec_decr_nat
    (fun state : Bool × Usize => index.val - state.2.val)
    (fun state : Bool × Usize => state.2.val ≤ index.val ∧
      (state.1 = true ↔ ∃ j, j < state.2.val ∧ duplicateAt j))
    _
  · rintro ⟨duplicate, current⟩ ⟨hcurrent, hprefix⟩
    dsimp only at hcurrent hprefix ⊢
    unfold spanning_tree.Tree.check_edit_loop0.body
    by_cases hlt : current < index
    · have hltNat : current.val < index.val := hlt
      simp only [hlt, ite_true]
      cases duplicate with
      | true =>
        simp only [ite_true]
        apply (spec_ok _).mpr
        constructor
        · intro _
          obtain ⟨j, hj, hd⟩ := hprefix.mp rfl
          exact ⟨j, by omega, hd⟩
        · intro _
          rfl
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        have hnone : ∀ j, j < current.val → ¬ duplicateAt j := by
          intro j hj hd
          exact Bool.false_ne_true (hprefix.mpr ⟨j, hj, hd⟩)
        have hrbound : current.val < remove.val.length := by omega
        have habound : current.val < add.val.length := by omega
        apply spec_bind (Slice.index_usize_spec remove current hrbound)
        intro removal hremoval
        have hremovalGet : remove.val[current.val]? = some removal := by
          rw [List.getElem?_eq_getElem hrbound, ← hremoval]
        apply spec_bind (mutation_edge_new_total removal.u removal.v)
        intro canonicalRemoval hcanonicalRemoval
        have hcr : canonicalRemoval = mutationCanonicalEdge removal := hcanonicalRemoval
        apply spec_bind (mutation_edge_equal_total canonicalRemoval {u := ru, v := rv})
        intro sameRemoval hsameRemoval
        have hstep (found : Bool) (hfound : found = true ↔ duplicateAt current.val) :
            (do
              let next ← current + 1#usize
              (Result.ok (ControlFlow.cont (found, next)) :
                Result (ControlFlow (Bool × Usize) Bool))) ⦃ state =>
                match state with
                | .done answer => answer = true ↔
                    ∃ j, j < index.val ∧ duplicateAt j
                | .cont next => (next.2.val ≤ index.val ∧
                    (next.1 = true ↔ ∃ j, j < next.2.val ∧ duplicateAt j)) ∧
                    index.val - next.2.val < index.val - current.val ⦄ := by
          apply spec_bind (Usize.add_spec (x := current) (y := 1#usize) (by scalar_tac))
          intro next hnext
          have hn : next.val = current.val + 1 := by simpa using hnext
          apply (spec_ok _).mpr
          dsimp only
          refine ⟨⟨by omega, ?_⟩, by omega⟩
          constructor
          · intro hf
            exact ⟨current.val, by omega, hfound.mp hf⟩
          · rintro ⟨j, hj, hd⟩
            have he : j = current.val := by
              by_contra hne
              exact hnone j (by omega) hd
            exact hfound.mpr (by simpa only [he] using hd)
        cases sameRemoval with
        | true =>
          simp only [ite_true, bind_ok]
          have he := hsameRemoval.mp rfl
          have hd : duplicateAt current.val :=
            Or.inl ⟨removal, hremovalGet, by simpa only [hcr] using he⟩
          apply spec_mono (hstep true ⟨fun _ => hd, fun _ => rfl⟩)
          intro state hstate
          cases state <;> exact hstate
        | false =>
          simp only [Bool.false_eq_true, ite_false, Std.bind_assoc]
          apply spec_bind (Slice.index_usize_spec add current habound)
          intro addition haddition
          have hadditionGet : add.val[current.val]? = some addition := by
            rw [List.getElem?_eq_getElem habound, ← haddition]
          apply spec_bind (mutation_edge_new_total addition.u addition.v)
          intro canonicalAddition hcanonicalAddition
          have hca : canonicalAddition = mutationCanonicalEdge addition := hcanonicalAddition
          apply spec_bind (mutation_edge_equal_total canonicalAddition {u := au, v := av})
          intro sameAddition hsameAddition
          have hremovalNe : ¬ ((mutationCanonicalEdge removal).u = ru ∧
              (mutationCanonicalEdge removal).v = rv) := by
            intro he
            apply Bool.false_ne_true
            exact hsameRemoval.mpr (by simpa only [hcr] using he)
          have hfound : sameAddition = true ↔ duplicateAt current.val := by
            constructor
            · intro hsame
              exact Or.inr ⟨addition, hadditionGet,
                by simpa only [hca] using hsameAddition.mp hsame⟩
            · rintro (⟨earlier, hearlier, he⟩ | ⟨earlier, hearlier, he⟩)
              · have heq : earlier = removal :=
                  Option.some.inj (hearlier.symm.trans hremovalGet)
                exact (hremovalNe (by simpa only [heq] using he)).elim
              · have heq : earlier = addition :=
                  Option.some.inj (hearlier.symm.trans hadditionGet)
                apply hsameAddition.mpr
                simpa only [hca, heq] using he
          apply spec_mono (hstep sameAddition hfound)
          intro state hstate
          cases state <;> exact hstate
    · have he : current.val = index.val := by
        have hnot : ¬ current.val < index.val := hlt
        omega
      simp only [hlt, ite_false]
      apply (spec_ok _).mpr
      simpa only [he] using hprefix
  · exact ⟨by simp, by simp⟩

end Labyrinth
