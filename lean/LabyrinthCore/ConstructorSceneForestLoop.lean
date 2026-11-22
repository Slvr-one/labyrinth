module
public import LabyrinthCore.ConstructorSceneForestPrefix
public import LabyrinthCore.ConstructorSceneSizes
public import LabyrinthCore.ConstructorSceneJoin
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- Whether one concrete union-find entry is a fixed root. -/
def constructorSceneRootTest (links : alloc.vec.Vec Usize) (index : Nat) : Bool :=
  match links.val[index]? with
  | some root => root.val == index
  | none => false

/-- Number of fixed union-find roots in the actual links vector. -/
def constructorSceneRootCount (links : alloc.vec.Vec Usize) : Nat :=
  ((List.range links.val.length).filter (constructorSceneRootTest links)).length

theorem constructor_filter_length_eq (values : List Nat) (left right : Nat → Bool)
    (heq : ∀ value ∈ values, left value = right value) :
    (values.filter left).length = (values.filter right).length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    have hvalue := heq value (by simp)
    have htail := ih (fun item hitem => heq item (by simp [hitem]))
    cases hl : left value <;>
      have hr : right value = left value := hvalue.symm <;>
      simp [hl, hr, htail]

/-- If two Boolean filters differ only by removing one member, their lengths differ by one. -/
theorem constructor_filter_length_remove_one (values : List Nat) (left right : Nat → Bool)
    (removed : Nat) (hnodup : values.Nodup) (hmember : removed ∈ values)
    (hleft : left removed = true) (hright : right removed = false)
    (hother : ∀ value ∈ values, value ≠ removed → left value = right value) :
    (values.filter right).length + 1 = (values.filter left).length := by
  induction values with
  | nil => simp at hmember
  | cons value rest ih =>
    simp only [List.mem_cons] at hmember
    by_cases he : value = removed
    · subst value
      have hnotmem : removed ∉ rest := (List.nodup_cons.mp hnodup).1
      have heq : (rest.filter left).length = (rest.filter right).length :=
        constructor_filter_length_eq rest left right (fun item hitem =>
          hother item (by simp [hitem]) (fun hir => hnotmem (by simpa [hir] using hitem)))
      simp [hleft, hright, heq]
    · have hrest : removed ∈ rest := hmember.resolve_left (Ne.symm he)
      have hvalue := hother value (by simp) he
      have htail := ih (List.nodup_cons.mp hnodup).2 hrest
        (fun item hitem hne => hother item (by simp [hitem]) hne)
      cases hr : right value <;> simp [hvalue, hr] at htail ⊢
      exact htail
      exact htail

/-- Initial singleton links contain one fixed root per concrete entry. -/
theorem constructor_scene_root_count_identity (links : alloc.vec.Vec Usize)
    (hidentity : ∀ node : Usize, node.val < links.val.length →
      links.val[node.val]? = some node) :
    constructorSceneRootCount links = links.val.length := by
  unfold constructorSceneRootCount
  rw [List.filter_eq_self.2]
  · simp
  · intro index hindex
    have hi : index < links.val.length := by simpa using hindex
    have hwidth : index < 2 ^ UScalarTy.Usize.numBits :=
      lt_trans hi (by simpa using (alloc.vec.Vec.len links).hBounds)
    let node : Usize := UScalar.ofNatCore index hwidth
    have hn : node.val = index := by simp only [node, UScalar.ofNatCore_val_eq]
    simp only [constructorSceneRootTest, ← hn, hidentity node (by simpa only [hn] using hi),
      beq_self_eq_true]

/-- Linking one distinct fixed root under another removes exactly the losing root. -/
theorem constructor_scene_root_count_set (links : alloc.vec.Vec Usize)
    (winner loser : Usize) (hloser : loser.val < links.val.length)
    (hfixed : links.val[loser.val]? = some loser) (hne : winner ≠ loser) :
    constructorSceneRootCount (links.set loser winner) + 1 =
      constructorSceneRootCount links := by
  have hlength : (links.set loser winner).val.length = links.val.length := by
    simp [alloc.vec.Vec.set]
  have hvalue : winner.val ≠ loser.val := fun he => hne ((UScalar.eq_equiv _ _).mpr he)
  unfold constructorSceneRootCount
  rw [hlength]
  apply constructor_filter_length_remove_one
  · exact List.nodup_range
  · simpa using hloser
  · simp [constructorSceneRootTest, hfixed]
  · simp [constructorSceneRootTest, alloc.vec.Vec.set, hloser, hvalue]
  · intro index hindex hine
    simp [constructorSceneRootTest, alloc.vec.Vec.set, Ne.symm hine]

/-- Semantic loop state: ranks terminate representative search, live sizes count real vertices,
and equal labels are exactly connectivity in the processed required-edge prefix. -/
def ConstructorSceneForestState (vertices : List Usize) (required : Slice topology.Edge)
    (processed : Nat) (links sizes : alloc.vec.Vec Usize) : Prop :=
  ∃ rank component, constructorRankedLinks links.slice rank ∧
    constructorComponentLabels links.slice component ∧
    constructorComponentSizes vertices links.slice sizes.slice component ∧
    (∀ u v, Relation.ReflTransGen (constructorRequiredPrefixArc required processed) u v ↔
      component u = component v) ∧
    processed + constructorSceneRootCount links = links.val.length

/-- The extracted required-forest loop accepts every acyclic carrier-edge prefix and retains
its exact component relation. Overflow is discharged by real component populations. -/
theorem constructor_scene_forest_loop_accepts (carrier : topology.Carrier)
    (required : Slice topology.Edge) (vertices : List Usize)
    (links sizes : alloc.vec.Vec Usize) (start : Usize)
    (hc : CarrierValid carrier) (hforest : ConstructorRequiredForest carrier required)
    (hwidth : vertices.length ≤ Usize.max)
    (hlen : links.val.length = cellCount carrier)
    (hslen : sizes.val.length = links.val.length)
    (hstart : start.val ≤ required.val.length)
    (hstate : ConstructorSceneForestState vertices required start.val links sizes) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop1 carrier required links sizes start (.Ok ()))
      (fun output => output.2 = .Ok () ∧ output.1.val.length = links.val.length ∧
        required.val.length + constructorSceneRootCount output.1 = links.val.length ∧
        ∃ rank component, constructorRankedLinks output.1.slice rank ∧
          constructorComponentLabels output.1.slice component ∧
          ∀ u v, Relation.ReflTransGen
            (constructorRequiredPrefixArc required required.val.length) u v ↔
              component u = component v) := by
  let invariant : alloc.vec.Vec Usize × alloc.vec.Vec Usize × Usize ×
      core.result.Result Unit topology.Error → Prop := fun state =>
    state.1.val.length = links.val.length ∧ state.2.1.val.length = state.1.val.length ∧
    state.2.2.1.val ≤ required.val.length ∧ state.2.2.2 = .Ok () ∧
    ConstructorSceneForestState vertices required state.2.2.1.val state.1 state.2.1
  unfold spanning_tree.Tree.scene_dfs_loop1
  apply loop.spec_decr_nat
    (fun state : alloc.vec.Vec Usize × alloc.vec.Vec Usize × Usize ×
      core.result.Result Unit topology.Error => required.val.length - state.2.2.1.val) invariant
  · rintro ⟨currentLinks, currentSizes, index, status⟩ hi
    obtain ⟨hll, hsl, hindex, hstatus, hcurrent⟩ := hi
    dsimp only at hll hsl hindex hstatus hcurrent
    obtain ⟨rank, component, hrank, hlabel, hsize, hcomponent, hcardinality⟩ := hcurrent
    unfold spanning_tree.Tree.scene_dfs_loop1.body
    by_cases hmore : index < Slice.len required
    · have hib : index.val < required.val.length := by simpa using hmore
      simp only [hmore, ite_true, hstatus, core.result.Result.is_ok, bind_ok,
        alloc.vec.Vec.deref_mut, lift]
      apply WP.spec_bind (Slice.index_usize_spec required index hib)
      intro edge hedge
      have hedgeLookup : required.val[index.val]? = some edge := by
        rw [List.getElem?_eq_getElem hib, hedge]
      obtain ⟨hcarrierEdge, hnoCycle⟩ := hforest index.val hib edge hedgeLookup
      have hdistinct : component edge.u ≠ component edge.v := by
        intro heq
        exact hnoCycle ((hcomponent edge.u edge.v).mpr heq)
      have hcurrentLen : currentLinks.slice.val.length = cellCount carrier := by
        change currentLinks.val.length = cellCount carrier
        omega
      have hcurrentSizeLen : currentSizes.slice.val.length = currentLinks.slice.val.length := hsl
      apply WP.spec_bind (constructor_join_required_accepts carrier currentLinks.slice currentSizes.slice
        edge rank component hc hcarrierEdge hcurrentLen hcurrentSizeLen hrank hlabel hdistinct
        (constructor_component_sizes_sum vertices currentLinks.slice currentSizes.slice component hsize hwidth))
      rintro ⟨joinedStatus, joinedLinks, joinedSizes⟩ hj
      dsimp only at hj
      obtain ⟨hok, winner, loser, winnerSize, loserSize, combined,
        hchoice, hws, hls, _, hcombined, hlinked, hsized⟩ := hj
      have hu : edge.u.val < currentLinks.slice.val.length := by
        rw [hcurrentLen]
        exact hcarrierEdge.1
      have hv : edge.v.val < currentLinks.slice.val.length := by
        rw [hcurrentLen]
        exact ((hc.2.2.2.2.1 edge.u.val hcarrierEdge.1).2.2 edge.v.val hcarrierEdge.2).1
      have hur := constructor_component_root_properties currentLinks.slice rank component hrank hlabel edge.u hu
      have hvr := constructor_component_root_properties currentLinks.slice rank component hrank hlabel edge.v hv
      have hroots : winner.val < currentLinks.slice.val.length ∧
          loser.val < currentLinks.slice.val.length ∧
          currentLinks.slice.val[winner.val]? = some winner ∧
          currentLinks.slice.val[loser.val]? = some loser ∧ winner ≠ loser := by
        rcases hchoice with ⟨hw, hl⟩ | ⟨hw, hl⟩
        · simpa only [hw, hl] using And.intro hur.1
            (And.intro hvr.1 (And.intro hur.2 (And.intro hvr.2 hdistinct)))
        · simpa only [hw, hl] using And.intro hvr.1
            (And.intro hur.1 (And.intro hvr.2 (And.intro hur.2 (Ne.symm hdistinct))))
      have hpreserved := constructor_union_preserves currentLinks.slice rank component winner loser
        hrank hlabel hroots.1 hroots.2.1 hroots.2.2.1 hroots.2.2.2.1 hroots.2.2.2.2
      have hsizesPreserved := constructor_component_sizes_preserved vertices
        currentLinks.slice currentSizes.slice component winner loser combined winnerSize loserSize
        hsize hcurrentSizeLen hroots.1 hroots.2.1 hroots.2.2.1 hroots.2.2.2.1 hroots.2.2.2.2
        hws hls hcombined
      have hrootCountRaw := constructor_scene_root_count_set currentLinks winner loser
        (by simpa only [alloc.vec.Vec.slice, alloc.vec.Vec.val] using hroots.2.1)
        (by simpa only [alloc.vec.Vec.slice, alloc.vec.Vec.val] using hroots.2.2.2.1)
        hroots.2.2.2.2
      apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
        have := required.property
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro nextIndex hn
      have hn' : nextIndex.val = index.val + 1 := by simpa using hn
      apply (WP.spec_ok _).mpr
      dsimp only [invariant, ConstructorSceneForestState]
      refine ⟨⟨?_, ?_, by omega, hok,
        constructorMergedRank rank component winner loser,
        constructorMergedComponent component winner loser, ?_, ?_, ?_, ?_, ?_⟩, by omega⟩
      · change joinedLinks.val.length = links.val.length
        simpa [hlinked, alloc.vec.Vec.val] using hll
      · change joinedSizes.val.length = joinedLinks.val.length
        simpa [hlinked, hsized, alloc.vec.Vec.val] using hsl
      · simpa only [hlinked] using hpreserved.1
      · simpa only [hlinked] using hpreserved.2
      · simpa only [hlinked, hsized] using hsizesPreserved
      · intro u v
        simpa only [hn'] using constructor_required_prefix_merge_iff required index.val edge hedgeLookup
          component winner loser hcomponent hchoice u v
      · simp only [hlinked]
        change nextIndex.val + constructorSceneRootCount (currentLinks.set loser winner) =
          (currentLinks.set loser winner).val.length
        have hsetLength :
            (currentLinks.set loser winner).val.length = currentLinks.val.length := by
          simp [alloc.vec.Vec.set]
        omega
    · have he : index.val = required.val.length := by
        have : ¬ index.val < required.val.length := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      have hfinalCardinality :
          required.val.length + constructorSceneRootCount currentLinks = links.val.length := by
        omega
      exact ⟨hstatus, hll, hfinalCardinality,
        rank, component, hrank, hlabel, by simpa only [he] using hcomponent⟩
  · exact ⟨rfl, hslen, hstart, rfl, hstate⟩

end Labyrinth
