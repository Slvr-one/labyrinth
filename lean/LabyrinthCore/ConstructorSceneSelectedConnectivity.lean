module
public import LabyrinthCore.ConstructorSceneAcceptance
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- The required-prefix copy and exact incoming quotient witnesses connect the literal selected
edge list. This bridges the quotient DFS result to the selected-carrier constructor. -/
theorem constructor_scene_selected_connected_actual
    (carrier : topology.Carrier) (required : Slice topology.Edge)
    (components links : alloc.vec.Vec Usize) (componentCount quotientRoot : Usize)
    (offsets : alloc.vec.Vec Usize) (neighbors : alloc.vec.Vec Usize)
    (witnesses : alloc.vec.Vec topology.Edge) (start : Usize → Nat)
    (rowOf : Nat → Usize) (before after : spanning_tree.Workspace)
    (selected : alloc.vec.Vec topology.Edge)
    (hc : CarrierValid carrier) (_hforest : ConstructorRequiredForest carrier required)
    (hcount : constructorDFSVertexCount offsets.slice = componentCount.val)
    (hcapacity : componentCount.val ≤ before.path.val.length)
    (hroot : quotientRoot.val < componentCount.val)
    (hforestCount : required.val.length + constructorSceneRootCount links = cellCount carrier)
    (hcomponentCount : componentCount.val = constructorSceneRootCount links)
    (hbounded : ∀ node : Usize, node.val < cellCount carrier →
      (constructorSceneComponentAt components node).val < componentCount.val)
    (hclasses : ∀ u v : Usize, u.val < cellCount carrier → v.val < cellCount carrier →
      (constructorSceneComponentAt components u = constructorSceneComponentAt components v ↔
        Relation.ReflTransGen
          (constructorRequiredPrefixArc required required.val.length) u v))
    (hstart : ∀ row : Usize, row.val < componentCount.val →
      constructorDFSOffset offsets.slice row.val = start row)
    (hstop : ∀ row : Usize, row.val < componentCount.val →
      constructorDFSOffset offsets.slice (row.val + 1) =
        start row + constructorQuotientRowCount carrier.edges.val
          (constructorSceneComponentAt components) row carrier.edges.val.length)
    (hrows : ∀ row : Usize, row.val < componentCount.val → ∀ slot,
      start row ≤ slot →
      slot < start row + constructorQuotientRowCount carrier.edges.val
        (constructorSceneComponentAt components) row carrier.edges.val.length →
      rowOf slot = row)
    (hfilled : ∀ slot,
      constructorQuotientFilled carrier.edges.val
        (constructorSceneComponentAt components) start componentCount
        carrier.edges.val.length slot →
      ∃ value original, neighbors.val[slot]? = some value ∧
        witnesses.val[slot]? = some original ∧
        constructorQuotientSlotWitness carrier
          (constructorSceneComponentAt components) (rowOf slot) value original)
    (hout : ConstructorDFSOutput offsets.slice neighbors.slice quotientRoot before after)
    (hselection : ∀ slot, slot < selected.val.length →
      (slot < required.val.length ∧
        selected.val[slot]? = (required.val[slot]?).map constructorCanonicalEdge) ∨
      ∃ node, node < componentCount.val ∧ node ≠ quotientRoot.val ∧
        slot = constructorSceneSelectedIndex required.val.length quotientRoot.val node ∧
        selected.val[slot]? =
          some (constructorSceneChosenWitness after witnesses node))
    (hselectedLength : selected.val.length = cellCount carrier - 1) :
    ∀ vertex, vertex < cellCount carrier →
      Relation.ReflTransGen (fun u v =>
        ∃ edge ∈ selected.val, (u = edge.u.val ∧ v = edge.v.val) ∨
          (u = edge.v.val ∧ v = edge.u.val)) 0 vertex := by
  let selectedArc : Nat → Nat → Prop := fun u v =>
    ∃ edge ∈ selected.val, (u = edge.u.val ∧ v = edge.v.val) ∨
      (u = edge.v.val ∧ v = edge.u.val)
  let labelNat : Nat → Nat := fun node =>
    (components.val[node]?.getD 0#usize).val
  have hpositive : 0 < componentCount.val := by
    have hzero : (0#usize).val < cellCount carrier := by simpa using hc.1
    have hlabelBound := hbounded 0#usize hzero
    omega
  have hrequiredLength : required.val.length ≤ selected.val.length := by
    rw [hselectedLength]
    omega
  have hselectedSymm {u v : Nat} (h : selectedArc u v) : selectedArc v u := by
    obtain ⟨edge, hedge, horient⟩ := h
    exact ⟨edge, hedge, horient.elim
      (fun h => Or.inr ⟨h.2, h.1⟩)
      (fun h => Or.inl ⟨h.2, h.1⟩)⟩
  have hrequiredIncluded :
      ∀ u v, constructorRequiredPrefixArc required required.val.length u v →
        selectedArc u.val v.val := by
    intro u v harc
    obtain ⟨slot, hslot, edge, hedge, horient⟩ := harc
    have hslotSelected : slot < selected.val.length := lt_of_lt_of_le hslot hrequiredLength
    rcases hselection slot hslotSelected with hcopy | hchosen
    · have hlookup : selected.val[slot]? = some (constructorCanonicalEdge edge) := by
        simpa only [hedge, Option.map_some] using hcopy.2
      refine ⟨constructorCanonicalEdge edge, List.mem_of_getElem? hlookup, ?_⟩
      exact (constructor_canonical_edge_incidence edge u.val v.val).mpr
        (horient.elim (fun h => Or.inl ⟨congrArg UScalar.val h.1,
          congrArg UScalar.val h.2⟩) (fun h => Or.inr ⟨congrArg UScalar.val h.1,
          congrArg UScalar.val h.2⟩))
    · obtain ⟨node, hnode, hnonroot, hindex, _⟩ := hchosen
      unfold constructorSceneSelectedIndex at hindex
      split at hindex <;> omega
  have hclassesNat : ∀ u v, u < cellCount carrier → v < cellCount carrier →
      labelNat u = labelNat v → Relation.ReflTransGen selectedArc u v := by
    intro u v hu hv heq
    have huwidth : u < 2 ^ UScalarTy.Usize.numBits := by
      have := carrier.offsets.property
      have hmax : Usize.max < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
      unfold cellCount at hu
      omega
    have hvwidth : v < 2 ^ UScalarTy.Usize.numBits := by
      have := carrier.offsets.property
      have hmax : Usize.max < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
      unfold cellCount at hv
      omega
    let actualU : Usize := UScalar.ofNatCore u huwidth
    let actualV : Usize := UScalar.ofNatCore v hvwidth
    have hcomponentEq :
        constructorSceneComponentAt components actualU =
          constructorSceneComponentAt components actualV := by
      apply UScalar.eq_of_val_eq
      simpa only [labelNat, constructorSceneComponentAt, actualU, actualV,
        UScalar.ofNatCore_val_eq] using heq
    have hpath := (hclasses actualU actualV (by simpa only [actualU,
      UScalar.ofNatCore_val_eq] using hu) (by simpa only [actualV,
      UScalar.ofNatCore_val_eq] using hv)).mp hcomponentEq
    simpa only [Function.onFun, actualU, actualV, UScalar.ofNatCore_val_eq] using
      hpath.lift UScalar.val (fun a b edge => hrequiredIncluded a b edge)
  have hafterParents : after.parents.val.length = before.path.val.length := by
    rw [hout.valid.2.2.1, hout.path]
  have hpLength :
      (constructorDFSParents offsets.slice after).length = componentCount.val := by
    simp only [constructorDFSParents, List.length_map, List.length_take, hcount,
      hafterParents, Nat.min_eq_left hcapacity]
  have hlabelNat : ∀ node : Usize, node.val < cellCount carrier →
      labelNat node.val = (constructorSceneComponentAt components node).val := by
    intro node _
    rfl
  have directedWitness (child parent : Nat) (hchild : child < componentCount.val)
      (hnonroot : child ≠ quotientRoot.val)
      (hparent : (constructorDFSParents offsets.slice after)[child]? = some parent) :
      ∃ u v, u < cellCount carrier ∧ v < cellCount carrier ∧
        labelNat u = parent ∧ labelNat v = child ∧ selectedArc u v := by
    have hchildWidth : child < 2 ^ UScalarTy.Usize.numBits :=
      lt_trans hchild componentCount.hBounds
    let actualChild : Usize := UScalar.ofNatCore child hchildWidth
    have hactualChild : actualChild.val = child := by
      simp only [actualChild, UScalar.ofNatCore_val_eq]
    have hactualNonroot : actualChild ≠ quotientRoot := by
      intro he
      exact hnonroot (by simpa only [hactualChild] using congrArg UScalar.val he)
    obtain ⟨actualParent, slot, original, hparentRaw, hincoming, hwitness, hsemantic⟩ :=
      constructor_quotient_dfs_selected_witness carrier carrier.edges.val
        (constructorSceneComponentAt components) start rowOf componentCount quotientRoot
        offsets.slice neighbors witnesses before after hcount hstart hstop hrows hfilled hout
        actualChild (by simpa only [hactualChild] using hchild) hactualNonroot
    have hparentRawChild :
        after.parents.val[child]? = some actualParent := by
      simpa only [hactualChild] using hparentRaw
    have hparentModel :
        (constructorDFSParents offsets.slice after)[child]? = some actualParent.val := by
      simp [constructorDFSParents, hcount, hchild, hparentRawChild]
    have hparentValue : actualParent.val = parent :=
      Option.some.inj (hparentModel.symm.trans hparent)
    let selectedIndex :=
      constructorSceneSelectedIndex required.val.length quotientRoot.val child
    have hselectedIndexStart : required.val.length ≤ selectedIndex := by
      unfold selectedIndex constructorSceneSelectedIndex
      split <;> omega
    have hselectedIndexBound : selectedIndex < selected.val.length := by
      rw [hselectedLength]
      rw [hcomponentCount] at hchild
      unfold selectedIndex constructorSceneSelectedIndex
      split <;> omega
    rcases hselection selectedIndex hselectedIndexBound with hrequired | hchosen
    · omega
    · obtain ⟨node, hnode, hnodeNonroot, hindex, hlookup⟩ := hchosen
      have hnodeEq : node = child := by
        unfold selectedIndex constructorSceneSelectedIndex at hindex
        by_cases hn : quotientRoot.val < node
        · simp only [hn, ite_true] at hindex
          by_cases hc' : quotientRoot.val < child
          · simp only [hc', ite_true] at hindex
            omega
          · simp only [hc', ite_false] at hindex
            omega
        · simp only [hn, ite_false] at hindex
          by_cases hc' : quotientRoot.val < child
          · simp only [hc', ite_true] at hindex
            omega
          · simp only [hc', ite_false] at hindex
            omega
      subst node
      have hchosenEq :
          constructorSceneChosenWitness after witnesses child = original :=
        constructor_scene_chosen_witness_eq after witnesses child slot original
          (by simpa only [hactualChild] using hincoming) hwitness
      have horiginal : original ∈ selected.val := by
        apply List.mem_of_getElem?
        simpa only [hchosenEq] using hlookup
      obtain ⟨hu, hv, hne⟩ := constructor_carrier_edge_facts carrier hc original hsemantic.1
      rcases hsemantic.2 with horient | horient
      · refine ⟨original.u.val, original.v.val, hu, hv, ?_, ?_,
          ⟨original, horiginal, Or.inl ⟨rfl, rfl⟩⟩⟩
        · rw [hlabelNat original.u hu, horient.1, hparentValue]
        · rw [hlabelNat original.v hv, horient.2, hactualChild]
      · refine ⟨original.v.val, original.u.val, hv, hu, ?_, ?_,
          ⟨original, horiginal, Or.inr ⟨rfl, rfl⟩⟩⟩
        · rw [hlabelNat original.v hv, horient.1, hparentValue]
        · rw [hlabelNat original.u hu, horient.2, hactualChild]
  have hparentWitness : ∀ a b,
      parentEdge (constructorDFSParents offsets.slice after) a b →
      ∃ u v, u < cellCount carrier ∧ v < cellCount carrier ∧
        labelNat u = a ∧ labelNat v = b ∧ selectedArc u v := by
    intro a b hedge
    obtain ⟨ha, hb, hne, hab | hba⟩ := hedge
    · obtain ⟨u, v, hu, hv, hlu, hlv, hselected⟩ :=
        directedWitness a b (by rw [← hpLength]; exact ha)
          (by
            intro he
            subst a
            have hbroot : b = quotientRoot.val :=
              Option.some.inj (hab.symm.trans hout.tree.2.1)
            exact hne hbroot.symm) hab
      exact ⟨v, u, hv, hu, hlv, hlu, hselectedSymm hselected⟩
    · apply directedWitness b a (by rw [← hpLength]; exact hb)
        (by
          intro he
          subst b
          have haroot : a = quotientRoot.val :=
            Option.some.inj (hba.symm.trans hout.tree.2.1)
          exact hne haroot)
        hba
  have hall := constructor_scene_selected_connected (cellCount carrier)
    componentCount.val (constructorDFSParents offsets.slice after) quotientRoot.val
    labelNat selectedArc hpLength hout.tree
    (fun u hu => by
      have huwidth : u < 2 ^ UScalarTy.Usize.numBits := by
        have := carrier.offsets.property
        have hmax : Usize.max < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
        unfold cellCount at hu
        omega
      let actual : Usize := UScalar.ofNatCore u huwidth
      simpa only [labelNat, constructorSceneComponentAt, actual,
        UScalar.ofNatCore_val_eq] using
        hbounded actual (by simpa only [actual, UScalar.ofNatCore_val_eq] using hu))
    hclassesNat hparentWitness
  intro vertex hvertex
  exact hall 0 vertex (Nat.zero_lt_of_lt hc.1) hvertex
end Labyrinth
