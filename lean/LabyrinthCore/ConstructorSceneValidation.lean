module
public import LabyrinthCore.ConstructorSceneForestLoop
public import LabyrinthCore.ConstructorSceneInitialize
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- Every required edge strictly before `processed` is a carrier edge and joins two
previously distinct required components. -/
def ConstructorRequiredForestPrefix (carrier : topology.Carrier)
    (required : Slice topology.Edge) (processed : Nat) : Prop :=
  ∀ slot, slot < processed → ∀ edge, required.val[slot]? = some edge →
    carrierEdge carrier edge.u.val edge.v.val ∧
      ¬ Relation.ReflTransGen (constructorRequiredPrefixArc required slot) edge.u edge.v

/-- The first rejected slot is characterized only by the input carrier and required list. -/
def ConstructorRequiredFirstInvalid (carrier : topology.Carrier)
    (required : Slice topology.Edge) (slot : Nat) : Prop :=
  slot < required.val.length ∧ ConstructorRequiredForestPrefix carrier required slot ∧
    ∃ edge, required.val[slot]? = some edge ∧
      (¬ carrierEdge carrier edge.u.val edge.v.val ∨
        Relation.ReflTransGen (constructorRequiredPrefixArc required slot) edge.u edge.v)

theorem constructor_required_forest_prefix_zero (carrier : topology.Carrier)
    (required : Slice topology.Edge) :
    ConstructorRequiredForestPrefix carrier required 0 := by
  intro slot hslot
  omega

theorem constructor_required_forest_prefix_step (carrier : topology.Carrier)
    (required : Slice topology.Edge) (processed : Nat) (edge : topology.Edge)
    (hprefix : ConstructorRequiredForestPrefix carrier required processed)
    (hlookup : required.val[processed]? = some edge)
    (hvalid : carrierEdge carrier edge.u.val edge.v.val ∧
      ¬ Relation.ReflTransGen (constructorRequiredPrefixArc required processed) edge.u edge.v) :
    ConstructorRequiredForestPrefix carrier required (processed + 1) := by
  intro slot hslot actual hactual
  by_cases heq : slot = processed
  · subst slot
    have : actual = edge := Option.some.inj (hactual.symm.trans hlookup)
    simpa only [this] using hvalid
  · exact hprefix slot (by omega) actual hactual

theorem constructor_required_forest_prefix_full_iff (carrier : topology.Carrier)
    (required : Slice topology.Edge) :
    ConstructorRequiredForestPrefix carrier required required.val.length ↔
      ConstructorRequiredForest carrier required := by
  rfl

theorem constructor_required_first_invalid_not_forest (carrier : topology.Carrier)
    (required : Slice topology.Edge) (slot : Nat)
    (hinvalid : ConstructorRequiredFirstInvalid carrier required slot) :
    ¬ ConstructorRequiredForest carrier required := by
  intro hforest
  obtain ⟨hslot, _, edge, hlookup, hbad⟩ := hinvalid
  obtain ⟨hcarrier, hacyclic⟩ := hforest slot hslot edge hlookup
  exact hbad.elim (fun h => h hcarrier) (fun h => hacyclic h)

/-- A concrete identity vector has no duplicate entries. -/
theorem constructor_scene_identity_nodup (values : List Usize)
    (hwidth : values.length ≤ Usize.max)
    (hidentity : ∀ node : Usize, node.val < values.length →
      values[node.val]? = some node) :
    values.Nodup := by
  apply List.nodup_iff_getElem?_ne_getElem?.mpr
  intro i j hij hj heq
  have hi : i < values.length := by omega
  have hiwidth : i < 2 ^ UScalarTy.Usize.numBits := by
    have hmax : Usize.max < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
    omega
  have hjwidth : j < 2 ^ UScalarTy.Usize.numBits := by
    have hmax : Usize.max < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
    omega
  let left : Usize := UScalar.ofNatCore i hiwidth
  let right : Usize := UScalar.ofNatCore j hjwidth
  have hleft := hidentity left (by simpa only [left, UScalar.ofNatCore_val_eq] using hi)
  have hright := hidentity right (by simpa only [right, UScalar.ofNatCore_val_eq] using hj)
  have hlr : left = right := Option.some.inj (hleft.symm.trans (heq.trans hright))
  have : i = j := by
    simpa only [left, right, UScalar.ofNatCore_val_eq] using congrArg UScalar.val hlr
  omega

/-- In an identity vector, the population of each identity component is exactly one. -/
theorem constructor_scene_identity_population (values : List Usize)
    (hwidth : values.length ≤ Usize.max)
    (hidentity : ∀ node : Usize, node.val < values.length →
      values[node.val]? = some node) (root : Usize) (hroot : root.val < values.length) :
    constructorComponentPopulation values (fun node => node) root = 1 := by
  have hn := constructor_scene_identity_nodup values hwidth hidentity
  have hmem : root ∈ values := List.mem_of_getElem? (hidentity root hroot)
  have hperm : List.Perm (values.filter (fun node => node == root)) [root] := by
    apply (List.perm_ext_iff_of_nodup (hn.filter _) (by simp)).mpr
    intro node
    simp only [List.mem_filter, beq_iff_eq, List.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro h
      subst node
      exact ⟨hmem, rfl⟩
  exact hperm.length_eq

/-- The two freshly allocated vectors after loop0 satisfy the complete semantic union state. -/
theorem constructor_scene_initial_forest_state (n : Usize) (required : Slice topology.Edge)
    (links sizes : alloc.vec.Vec Usize)
    (hlinks : links.val.length = n.val)
    (hidentity : ∀ node : Usize, node.val < n.val → links.val[node.val]? = some node)
    (hsizes : sizes.val.length = n.val)
    (hones : ∀ node : Usize, node.val < n.val → sizes.val[node.val]? = some 1#usize) :
    ConstructorSceneForestState links.val required 0 links sizes := by
  refine ⟨(fun _ => 0), (fun node => node), ?_, ?_, ?_, ?_, ?_⟩
  · intro node parent hnode hparent
    have hnode' : node.val < n.val := by
      change node.val < links.val.length at hnode
      simpa only [hlinks] using hnode
    have heq : parent = node := Option.some.inj (hparent.symm.trans (hidentity node hnode'))
    subst parent
    refine ⟨?_, fun h => False.elim (h rfl)⟩
    change node.val < links.val.length
    simpa only [hlinks] using hnode'
  · constructor
    · intro node parent hnode hparent
      have hnode' : node.val < n.val := by
        change node.val < links.val.length at hnode
        simpa only [hlinks] using hnode
      exact Option.some.inj (hparent.symm.trans (hidentity node hnode')) |>.symm
    · intro node _ _
      rfl
  · intro root hroot _
    have hroot' : root.val < n.val := by
      change root.val < links.val.length at hroot
      simpa only [hlinks] using hroot
    refine ⟨1#usize, ?_, ?_⟩
    · simpa only [alloc.vec.Vec.slice, alloc.vec.Vec.val] using hones root hroot'
    · exact (constructor_scene_identity_population links.val
        (by rw [hlinks]; scalar_tac) (fun node hnode => hidentity node (by omega))
        root (by omega)).symm
  · intro u v
    exact constructor_required_prefix_zero_iff required u v
  · have hcount := constructor_scene_root_count_identity links (fun node hnode =>
      hidentity node (by omega))
    omega

/-- Total, bounded status theorem for the actual union-validation loop. It either consumes the
whole genuine forest or stops immediately after the first noncarrier/cyclic required edge. -/
theorem constructor_scene_forest_loop_total (carrier : topology.Carrier)
    (required : Slice topology.Edge) (vertices : List Usize)
    (links sizes : alloc.vec.Vec Usize) (start : Usize)
    (hc : CarrierValid carrier) (hwidth : vertices.length ≤ Usize.max)
    (hlen : links.val.length = cellCount carrier)
    (hslen : sizes.val.length = links.val.length)
    (hstart : start.val ≤ required.val.length)
    (hprefix : ConstructorRequiredForestPrefix carrier required start.val)
    (hstate : ConstructorSceneForestState vertices required start.val links sizes) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop1 carrier required links sizes start (.Ok ()))
      (fun output => output.1.val.length = links.val.length ∧
        (output.2 = .Ok () ↔ ConstructorRequiredForest carrier required) ∧
        (output.2 = .Err topology.Error.InvalidForest ↔
          ¬ ConstructorRequiredForest carrier required) ∧
        (output.2 = .Err topology.Error.InvalidForest →
          ∃ slot finalSizes, ConstructorRequiredFirstInvalid carrier required slot ∧
            ConstructorSceneForestState vertices required slot output.1 finalSizes)) := by
  let invariant : alloc.vec.Vec Usize × alloc.vec.Vec Usize × Usize ×
      core.result.Result Unit topology.Error → Prop := fun state =>
    state.1.val.length = links.val.length ∧ state.2.1.val.length = state.1.val.length ∧
    state.2.2.1.val ≤ required.val.length ∧
    ((state.2.2.2 = .Ok () ∧
        ConstructorRequiredForestPrefix carrier required state.2.2.1.val ∧
        ConstructorSceneForestState vertices required state.2.2.1.val state.1 state.2.1) ∨
      (state.2.2.2 = .Err topology.Error.InvalidForest ∧
        ∃ slot, state.2.2.1.val = slot + 1 ∧
          ConstructorRequiredFirstInvalid carrier required slot ∧
          ConstructorSceneForestState vertices required slot state.1 state.2.1))
  unfold spanning_tree.Tree.scene_dfs_loop1
  apply loop.spec_decr_nat
    (fun state : alloc.vec.Vec Usize × alloc.vec.Vec Usize × Usize ×
      core.result.Result Unit topology.Error => required.val.length - state.2.2.1.val) invariant
  · rintro ⟨currentLinks, currentSizes, index, status⟩ hi
    obtain ⟨hll, hsl, hindex, hok | herr⟩ := hi
    · obtain ⟨hstatus, hcurrentPrefix, hcurrent⟩ := hok
      dsimp only at hll hsl hindex hstatus hcurrentPrefix hcurrent
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
        by_cases hcarrierEdge : carrierEdge carrier edge.u.val edge.v.val
        · by_cases hcycle : Relation.ReflTransGen
            (constructorRequiredPrefixArc required index.val) edge.u edge.v
          · have heq : component edge.u = component edge.v :=
              (hcomponent edge.u edge.v).mp hcycle
            have hcurrentLen : currentLinks.slice.val.length = cellCount carrier := by
              change currentLinks.val.length = cellCount carrier
              omega
            apply WP.spec_bind (constructor_join_required_rejects_cycle carrier
              currentLinks.slice currentSizes.slice edge rank component hc hcarrierEdge
              hcurrentLen hrank hlabel heq)
            rintro ⟨joinedStatus, joinedLinks, joinedSizes⟩ hj
            have hj' : joinedStatus = .Err topology.Error.InvalidForest ∧
                joinedLinks = currentLinks.slice ∧ joinedSizes = currentSizes.slice := by
              simpa using hj
            obtain ⟨rfl, rfl, rfl⟩ := hj'
            apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
              have := required.property
              simp only [UScalar.ofNatCore_val_eq]
              omega))
            intro nextIndex hn
            have hn' : nextIndex.val = index.val + 1 := by simpa using hn
            apply (WP.spec_ok _).mpr
            dsimp only [invariant]
            refine ⟨⟨hll, hsl, by omega, Or.inr ⟨rfl, index.val, hn', ?_, ?_⟩⟩, by omega⟩
            · exact ⟨hib, hcurrentPrefix, edge, hedgeLookup, Or.inr hcycle⟩
            · exact ⟨rank, component, hrank, hlabel, hsize, hcomponent, hcardinality⟩
          · have hvalid : carrierEdge carrier edge.u.val edge.v.val ∧
                ¬ Relation.ReflTransGen
                  (constructorRequiredPrefixArc required index.val) edge.u edge.v :=
              ⟨hcarrierEdge, hcycle⟩
            have hdistinct : component edge.u ≠ component edge.v := by
              intro heq
              exact hcycle ((hcomponent edge.u edge.v).mpr heq)
            have hcurrentLen : currentLinks.slice.val.length = cellCount carrier := by
              change currentLinks.val.length = cellCount carrier
              omega
            have hcurrentSizeLen : currentSizes.slice.val.length = currentLinks.slice.val.length := hsl
            apply WP.spec_bind (constructor_join_required_accepts carrier currentLinks.slice
              currentSizes.slice edge rank component hc hcarrierEdge hcurrentLen hcurrentSizeLen
              hrank hlabel hdistinct (constructor_component_sizes_sum vertices currentLinks.slice
                currentSizes.slice component hsize hwidth))
            rintro ⟨joinedStatus, joinedLinks, joinedSizes⟩ hj
            dsimp only at hj
            obtain ⟨hjoined, winner, loser, winnerSize, loserSize, combined,
              hchoice, hws, hls, _, hcombined, hlinked, hsized⟩ := hj
            have hu : edge.u.val < currentLinks.slice.val.length := by
              rw [hcurrentLen]
              exact hcarrierEdge.1
            have hv : edge.v.val < currentLinks.slice.val.length := by
              rw [hcurrentLen]
              exact ((hc.2.2.2.2.1 edge.u.val hcarrierEdge.1).2.2 edge.v.val hcarrierEdge.2).1
            have hur := constructor_component_root_properties currentLinks.slice rank component
              hrank hlabel edge.u hu
            have hvr := constructor_component_root_properties currentLinks.slice rank component
              hrank hlabel edge.v hv
            have hroots : winner.val < currentLinks.slice.val.length ∧
                loser.val < currentLinks.slice.val.length ∧
                currentLinks.slice.val[winner.val]? = some winner ∧
                currentLinks.slice.val[loser.val]? = some loser ∧ winner ≠ loser := by
              rcases hchoice with ⟨hw, hl⟩ | ⟨hw, hl⟩
              · simpa only [hw, hl] using And.intro hur.1
                  (And.intro hvr.1 (And.intro hur.2 (And.intro hvr.2 hdistinct)))
              · simpa only [hw, hl] using And.intro hvr.1
                  (And.intro hur.1 (And.intro hvr.2 (And.intro hur.2 (Ne.symm hdistinct))))
            have hpreserved := constructor_union_preserves currentLinks.slice rank component
              winner loser hrank hlabel hroots.1 hroots.2.1 hroots.2.2.1
              hroots.2.2.2.1 hroots.2.2.2.2
            have hsizesPreserved := constructor_component_sizes_preserved vertices
              currentLinks.slice currentSizes.slice component winner loser combined winnerSize
              loserSize hsize hcurrentSizeLen hroots.1 hroots.2.1 hroots.2.2.1
              hroots.2.2.2.1 hroots.2.2.2.2 hws hls hcombined
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
            refine ⟨⟨?_, ?_, by omega, Or.inl ⟨hjoined, ?_,
              constructorMergedRank rank component winner loser,
              constructorMergedComponent component winner loser, ?_, ?_, ?_, ?_, ?_⟩⟩, by omega⟩
            · change joinedLinks.val.length = links.val.length
              simpa [hlinked, alloc.vec.Vec.val] using hll
            · change joinedSizes.val.length = joinedLinks.val.length
              simpa [hlinked, hsized, alloc.vec.Vec.val] using hsl
            · simpa only [hn'] using constructor_required_forest_prefix_step carrier required
                index.val edge hcurrentPrefix hedgeLookup hvalid
            · simpa only [hlinked] using hpreserved.1
            · simpa only [hlinked] using hpreserved.2
            · simpa only [hlinked, hsized] using hsizesPreserved
            · intro u v
              simpa only [hn'] using constructor_required_prefix_merge_iff required index.val
                edge hedgeLookup component winner loser hcomponent hchoice u v
            · simp only [hlinked]
              change nextIndex.val + constructorSceneRootCount (currentLinks.set loser winner) =
                (currentLinks.set loser winner).val.length
              have hsetLength : (currentLinks.set loser winner).val.length =
                  currentLinks.val.length := by simp [alloc.vec.Vec.set]
              omega
        · apply WP.spec_bind (constructor_join_required_rejects_edge carrier
            currentLinks.slice currentSizes.slice edge hc hcarrierEdge)
          rintro ⟨joinedStatus, joinedLinks, joinedSizes⟩ hj
          have hj' : joinedStatus = .Err topology.Error.InvalidForest ∧
              joinedLinks = currentLinks.slice ∧ joinedSizes = currentSizes.slice := by
            simpa using hj
          obtain ⟨rfl, rfl, rfl⟩ := hj'
          apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
            have := required.property
            simp only [UScalar.ofNatCore_val_eq]
            omega))
          intro nextIndex hn
          have hn' : nextIndex.val = index.val + 1 := by simpa using hn
          apply (WP.spec_ok _).mpr
          dsimp only [invariant]
          refine ⟨⟨hll, hsl, by omega, Or.inr ⟨rfl, index.val, hn', ?_, ?_⟩⟩, by omega⟩
          · exact ⟨hib, hcurrentPrefix, edge, hedgeLookup, Or.inl hcarrierEdge⟩
          · exact ⟨rank, component, hrank, hlabel, hsize, hcomponent, hcardinality⟩
      · have he : index.val = required.val.length := by
          have : ¬ index.val < required.val.length := by simpa using hmore
          omega
        have hforest : ConstructorRequiredForest carrier required :=
          (constructor_required_forest_prefix_full_iff carrier required).mp (by
            simpa only [he] using hcurrentPrefix)
        simp only [hmore, ite_false]
        apply (WP.spec_ok _).mpr
        refine ⟨hll, ?_, ?_, ?_⟩
        · simp [hstatus, hforest]
        · simp [hstatus, hforest]
        · intro h
          simp [hstatus] at h
    · obtain ⟨hstatus, slot, hslotIndex, hfirst, hfirstState⟩ := herr
      dsimp only at hll hsl hindex hstatus hslotIndex hfirst hfirstState
      have hnot := constructor_required_first_invalid_not_forest carrier required slot hfirst
      unfold spanning_tree.Tree.scene_dfs_loop1.body
      by_cases hmore : index < Slice.len required
      · simp only [hmore, ite_true, hstatus, core.result.Result.is_ok, bind_ok,
          Bool.false_eq_true, ite_false]
        apply (WP.spec_ok _).mpr
        refine ⟨hll, ?_, ?_, ?_⟩
        · simp [hnot]
        · simp [hnot]
        · intro _
          exact ⟨slot, currentSizes, hfirst, hfirstState⟩
      · simp only [hmore, ite_false]
        apply (WP.spec_ok _).mpr
        refine ⟨hll, ?_, ?_, ?_⟩
        · simp [hstatus, hnot]
        · simp [hstatus, hnot]
        · intro _
          exact ⟨slot, currentSizes, hfirst, hfirstState⟩
  · exact ⟨rfl, hslen, hstart, Or.inl ⟨rfl, hprefix, hstate⟩⟩

end Labyrinth
