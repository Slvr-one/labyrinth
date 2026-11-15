module
public import LabyrinthCore.ConstructorSceneForestPrefix
public import LabyrinthCore.ConstructorSceneSizes
public import LabyrinthCore.ConstructorSceneJoin
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- Semantic loop state: ranks terminate representative search, live sizes count real vertices,
and equal labels are exactly connectivity in the processed required-edge prefix. -/
def ConstructorSceneForestState (vertices : List Usize) (required : Slice topology.Edge)
    (processed : Nat) (links sizes : alloc.vec.Vec Usize) : Prop :=
  ∃ rank component, constructorRankedLinks links.slice rank ∧
    constructorComponentLabels links.slice component ∧
    constructorComponentSizes vertices links.slice sizes.slice component ∧
    ∀ u v, Relation.ReflTransGen (constructorRequiredPrefixArc required processed) u v ↔
      component u = component v

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
    obtain ⟨rank, component, hrank, hlabel, hsize, hcomponent⟩ := hcurrent
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
        constructorMergedComponent component winner loser, ?_, ?_, ?_, ?_⟩, by omega⟩
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
    · have he : index.val = required.val.length := by
        have : ¬ index.val < required.val.length := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      exact ⟨hstatus, hll, rank, component, hrank, hlabel, by simpa only [he] using hcomponent⟩
  · exact ⟨rfl, hslen, hstart, rfl, hstate⟩

end Labyrinth
