module
public import LabyrinthCore.ConstructorQuotientCSR
public import LabyrinthCore.ConstructorDepthFirst
public import LabyrinthCore.ConstructorDepthFirstCarrier
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

/-- Every validated carrier adjacency is represented by one actual stored undirected edge,
with either endpoint orientation. -/
theorem constructor_carrier_edge_stored (carrier : topology.Carrier) (hc : CarrierValid carrier)
    {u v : Nat} (he : carrierEdge carrier u v) :
    ∃ index : Nat, ∃ edge : topology.Edge, carrier.edges.val[index]? = some edge ∧
      ((edge.u.val = u ∧ edge.v.val = v) ∨ (edge.u.val = v ∧ edge.v.val = u)) := by
  have hne : u ≠ v := by
    intro huv
    subst v
    exact (hc.2.2.2.2.1 u he.1).2.1 he.2
  have hreverseFacts := (hc.2.2.2.2.1 u he.1).2.2 v he.2
  have hreverse : carrierEdge carrier v u := ⟨hreverseFacts.1, hreverseFacts.2⟩
  by_cases huv : u < v
  · have hp : (u, v) ∈ edgePairs carrier := (hc.2.2.2.2.2.2.2 u v).mpr ⟨huv, he⟩
    obtain ⟨edge, hedge, hpairs⟩ := List.mem_map.mp hp
    obtain ⟨index, hlookup⟩ := List.mem_iff_getElem?.mp hedge
    refine ⟨index, edge, hlookup, Or.inl ?_⟩
    simpa only [Prod.mk.injEq] using hpairs
  · have hvu : v < u := by omega
    have hp : (v, u) ∈ edgePairs carrier := (hc.2.2.2.2.2.2.2 v u).mpr ⟨hvu, hreverse⟩
    obtain ⟨edge, hedge, hpairs⟩ := List.mem_map.mp hp
    obtain ⟨index, hlookup⟩ := List.mem_iff_getElem?.mp hedge
    refine ⟨index, edge, hlookup, Or.inr ?_⟩
    simpa only [Prod.mk.injEq] using hpairs

/-- The two historical slots of one processed crossing edge are the two directed raw-CSR arcs.
The proof recovers row ownership from the actual fill witness, so parallel edges keep distinct slots. -/
theorem constructor_quotient_history_edge_arcs (carrier : topology.Carrier)
    (edges : List topology.Edge) (label : Usize → Usize) (labelNat : Nat → Nat)
    (start : Usize → Nat) (count : Usize) (offsets : Slice Usize)
    (hcount : constructorDFSVertexCount offsets = count.val)
    (neighbors : alloc.vec.Vec Usize) (witnesses : alloc.vec.Vec topology.Edge)
    (rowOf : Nat → Usize) (index : Nat) (edge : topology.Edge)
    (hhistory : ConstructorQuotientHistory edges label start count edges.length neighbors witnesses)
    (hlookup : edges[index]? = some edge)
    (hcross : label edge.u ≠ label edge.v)
    (hlabelNat : labelNat edge.u.val = (label edge.u).val ∧
      labelNat edge.v.val = (label edge.v).val)
    (hlabelBound : (label edge.u).val < count.val ∧ (label edge.v).val < count.val)
    (hstart : ∀ row : Usize, row.val < count.val →
      constructorDFSOffset offsets row.val = start row)
    (hstop : ∀ row : Usize, row.val < count.val →
      constructorDFSOffset offsets (row.val + 1) =
        start row + constructorQuotientRowCount edges label row edges.length)
    (hrows : ∀ row : Usize, row.val < count.val → ∀ slot,
      start row ≤ slot →
      slot < start row + constructorQuotientRowCount edges label row edges.length →
      rowOf slot = row)
    (hfilled : ∀ slot, constructorQuotientFilled edges label start count edges.length slot →
      ∃ value original, neighbors.val[slot]? = some value ∧
        witnesses.val[slot]? = some original ∧
        constructorQuotientSlotWitness carrier label (rowOf slot) value original) :
    constructorDFSArc offsets neighbors.slice (labelNat edge.u.val) (labelNat edge.v.val) ∧
      constructorDFSArc offsets neighbors.slice (labelNat edge.v.val) (labelNat edge.u.val) := by
  obtain ⟨a, b, hfa, hfb, hna, hwa, hnb, hwb⟩ :=
    hhistory index (List.getElem?_eq_some_iff.mp hlookup).1 edge hlookup hcross
  have directed (slot : Nat) (source target : Usize)
      (hf : constructorQuotientFilled edges label start count edges.length slot)
      (hn : neighbors.val[slot]? = some target) (hw : witnesses.val[slot]? = some edge)
      (hsource : source = label edge.u ∧ target = label edge.v ∨
        source = label edge.v ∧ target = label edge.u) :
      constructorDFSOffset offsets source.val ≤ slot ∧
        slot < constructorDFSOffset offsets (source.val + 1) := by
    have hfilledSlot := hfilled slot hf
    obtain ⟨row, hr, hlo, hhi⟩ := hf
    have hrowOf : rowOf slot = row := hrows row hr slot hlo hhi
    obtain ⟨actualTarget, original, hactual, horiginal, hwitness⟩ := hfilledSlot
    have ht : actualTarget = target := Option.some.inj (hactual.symm.trans hn)
    have he : original = edge := Option.some.inj (horiginal.symm.trans hw)
    subst actualTarget
    subst original
    have hsrow : rowOf slot = source := by
      rcases hwitness.2 with horient | horient
      · rcases hsource with hsource | hsource
        · exact horient.1.symm.trans hsource.1.symm
        · exact False.elim (hcross (horient.2.trans hsource.2).symm)
      · rcases hsource with hsource | hsource
        · exact False.elim (hcross (horient.2.trans hsource.2))
        · exact horient.1.symm.trans hsource.1.symm
    have hrs : row = source := hrowOf.symm.trans hsrow
    have hrsource : source.val < count.val := by simpa only [← hrs] using hr
    have hlosource : start source ≤ slot := by simpa only [← hrs] using hlo
    have hhisource :
        slot < start source + constructorQuotientRowCount edges label source edges.length := by
      simpa only [← hrs] using hhi
    rw [hstart source hrsource, hstop source hrsource]
    exact ⟨hlosource, hhisource⟩
  have habounds := directed a (label edge.u) (label edge.v) hfa hna hwa (Or.inl ⟨rfl, rfl⟩)
  have hbbounds := directed b (label edge.v) (label edge.u) hfb hnb hwb (Or.inr ⟨rfl, rfl⟩)
  constructor
  · rw [hlabelNat.1, hlabelNat.2]
    exact ⟨by simpa only [hcount] using hlabelBound.1,
      a, label edge.v, habounds.1, habounds.2, hna, rfl⟩
  · rw [hlabelNat.1, hlabelNat.2]
    exact ⟨by simpa only [hcount] using hlabelBound.2,
      b, label edge.u, hbbounds.1, hbbounds.2, hnb, rfl⟩

/-- Actual final fill history supplies every crossing carrier arc required by the generic DFS. -/
theorem constructor_quotient_history_carrier_arcs (carrier : topology.Carrier)
    (hc : CarrierValid carrier) (edges : List topology.Edge)
    (label : Usize → Usize) (labelNat : Nat → Nat) (start : Usize → Nat)
    (count : Usize) (offsets : Slice Usize)
    (hcount : constructorDFSVertexCount offsets = count.val)
    (neighbors : alloc.vec.Vec Usize) (witnesses : alloc.vec.Vec topology.Edge)
    (rowOf : Nat → Usize)
    (hedges : edges = carrier.edges.val)
    (hhistory : ConstructorQuotientHistory edges label start count edges.length neighbors witnesses)
    (hlabelNat : ∀ node : Usize, node.val < cellCount carrier →
      labelNat node.val = (label node).val)
    (hlabelBound : ∀ node : Usize, node.val < cellCount carrier →
      (label node).val < count.val)
    (hstart : ∀ row : Usize, row.val < count.val →
      constructorDFSOffset offsets row.val = start row)
    (hstop : ∀ row : Usize, row.val < count.val →
      constructorDFSOffset offsets (row.val + 1) =
        start row + constructorQuotientRowCount edges label row edges.length)
    (hrows : ∀ row : Usize, row.val < count.val → ∀ slot,
      start row ≤ slot →
      slot < start row + constructorQuotientRowCount edges label row edges.length → rowOf slot = row)
    (hfilled : ∀ slot, constructorQuotientFilled edges label start count edges.length slot →
      ∃ value original, neighbors.val[slot]? = some value ∧ witnesses.val[slot]? = some original ∧
        constructorQuotientSlotWitness carrier label (rowOf slot) value original) :
    ∀ u v, carrierEdge carrier u v → labelNat u ≠ labelNat v →
      constructorDFSArc offsets neighbors.slice (labelNat u) (labelNat v) := by
  intro u v hedge hcross
  obtain ⟨index, edge, hlookup, horient⟩ := constructor_carrier_edge_stored carrier hc hedge
  have hu : u < cellCount carrier := hedge.1
  have hv : v < cellCount carrier :=
    ((hc.2.2.2.2.1 u hu).2.2 v hedge.2).1
  have heu : edge.u.val < cellCount carrier := by
    rcases horient with h | h
    · simpa only [h.1] using hu
    · simpa only [h.1] using hv
  have hev : edge.v.val < cellCount carrier := by
    rcases horient with h | h
    · simpa only [h.2] using hv
    · simpa only [h.2] using hu
  have hlabel : labelNat edge.u.val = (label edge.u).val ∧
      labelNat edge.v.val = (label edge.v).val :=
    ⟨hlabelNat edge.u heu, hlabelNat edge.v hev⟩
  have hbound : (label edge.u).val < count.val ∧ (label edge.v).val < count.val :=
    ⟨hlabelBound edge.u heu, hlabelBound edge.v hev⟩
  have hcrossEdge : label edge.u ≠ label edge.v := by
    intro heq
    apply hcross
    rcases horient with h | h
    · calc
        labelNat u = labelNat edge.u.val := congrArg labelNat h.1.symm
        _ = (label edge.u).val := hlabel.1
        _ = (label edge.v).val := congrArg UScalar.val heq
        _ = labelNat edge.v.val := hlabel.2.symm
        _ = labelNat v := congrArg labelNat h.2
    · calc
        labelNat u = labelNat edge.v.val := congrArg labelNat h.2.symm
        _ = (label edge.v).val := hlabel.2
        _ = (label edge.u).val := (congrArg UScalar.val heq).symm
        _ = labelNat edge.u.val := hlabel.1.symm
        _ = labelNat v := congrArg labelNat h.1
  have harcs := constructor_quotient_history_edge_arcs carrier edges label labelNat start count
    offsets hcount neighbors witnesses rowOf index edge hhistory
    (by simpa only [hedges] using hlookup) hcrossEdge hlabel hbound hstart hstop hrows hfilled
  rcases horient with h | h
  · simpa only [h.1, h.2] using harcs.1
  · simpa only [h.1, h.2] using harcs.2

/-- Complete exact quotient rows contain only dense component IDs. This is derived from the
actual occupied-slot witnesses, not assumed as a property of the allocated neighbor array. -/
theorem constructor_quotient_neighbors_bounded (carrier : topology.Carrier)
    (hc : CarrierValid carrier) (edges : List topology.Edge) (label : Usize → Usize)
    (start : Usize → Nat) (count : Usize) (offsets : Slice Usize)
    (neighbors : alloc.vec.Vec Usize) (witnesses : alloc.vec.Vec topology.Edge)
    (rowOf : Nat → Usize)
    (hfirst : constructorDFSOffset offsets 0 = 0)
    (hlast : constructorDFSOffset offsets count.val = neighbors.val.length)
    (hstart : ∀ row : Usize, row.val < count.val →
      constructorDFSOffset offsets row.val = start row)
    (hstop : ∀ row : Usize, row.val < count.val →
      constructorDFSOffset offsets (row.val + 1) =
        start row + constructorQuotientRowCount edges label row edges.length)
    (hlabelBound : ∀ node : Usize, node.val < cellCount carrier →
      (label node).val < count.val)
    (hfilled : ∀ slot, constructorQuotientFilled edges label start count edges.length slot →
      ∃ value original, neighbors.val[slot]? = some value ∧ witnesses.val[slot]? = some original ∧
        constructorQuotientSlotWitness carrier label (rowOf slot) value original) :
    ∀ value ∈ neighbors.val, value.val < count.val := by
  intro value hmem
  obtain ⟨slot, hlookup⟩ := List.mem_iff_getElem?.mp hmem
  have hslot : slot < neighbors.val.length := (List.getElem?_eq_some_iff.mp hlookup).1
  have hterminal : slot < constructorDFSOffset offsets count.val := by
    rw [hlast]
    exact hslot
  obtain ⟨row, hr, hlo, hhi⟩ :=
    constructor_dfs_slot_covered (constructorDFSOffset offsets) count.val slot hfirst hterminal
  have hwidth : row < 2 ^ UScalarTy.Usize.numBits := lt_trans hr count.hBounds
  let actualRow : Usize := UScalar.ofNatCore row hwidth
  have hactualRow : actualRow.val = row := by simp only [actualRow, UScalar.ofNatCore_val_eq]
  have hrow : actualRow.val < count.val := by rw [hactualRow]; exact hr
  have hlo' : start actualRow ≤ slot := by
    rw [← hstart actualRow hrow]
    simpa only [hactualRow] using hlo
  have hhi' : slot <
      start actualRow + constructorQuotientRowCount edges label actualRow edges.length := by
    rw [← hstop actualRow hrow]
    simpa only [hactualRow] using hhi
  have hoccupied : constructorQuotientFilled edges label start count edges.length slot :=
    ⟨actualRow, hrow, hlo', hhi'⟩
  obtain ⟨actual, original, hactual, _, hwitness⟩ := hfilled slot hoccupied
  have heq : actual = value := Option.some.inj (hactual.symm.trans hlookup)
  subst actual
  have hu := hwitness.1.1
  have hreverse := (hc.2.2.2.2.1 original.u.val hu).2.2 original.v.val hwitness.1.2
  rcases hwitness.2 with horient | horient
  · rw [← horient.2]
    exact hlabelBound original.v hreverse.1
  · rw [← horient.2]
    exact hlabelBound original.u hu

/-- The actual quotient CSR facts, final fill witnesses, and dense labels form the exact input
accepted by the checked generic DFS theorem. -/
theorem constructor_quotient_actual_dfs_input (carrier : topology.Carrier)
    (hc : CarrierValid carrier) (edges : List topology.Edge)
    (label : Usize → Usize) (labelNat : Nat → Nat) (start : Usize → Nat)
    (count root : Usize) (offsets : Slice Usize) (neighbors : alloc.vec.Vec Usize)
    (witnesses : alloc.vec.Vec topology.Edge) (rowOf : Nat → Usize)
    (hedges : edges = carrier.edges.val)
    (hcount : constructorDFSVertexCount offsets = count.val) (hpositive : 0 < count.val)
    (hfirst : constructorDFSOffset offsets 0 = 0)
    (hlast : constructorDFSOffset offsets count.val = neighbors.val.length)
    (hordered : ∀ v, v < count.val →
      constructorDFSOffset offsets v ≤ constructorDFSOffset offsets (v + 1))
    (hlabels : ∀ node : Usize, node.val < cellCount carrier →
      (label node).val < count.val ∧ labelNat node.val = (label node).val)
    (hdense : ∀ id, id < count.val → ∃ node : Usize,
      node.val < cellCount carrier ∧ (label node).val = id)
    (hroot : root.val < cellCount carrier)
    (hhistory : ConstructorQuotientHistory edges label start count edges.length neighbors witnesses)
    (hstart : ∀ row : Usize, row.val < count.val →
      constructorDFSOffset offsets row.val = start row)
    (hstop : ∀ row : Usize, row.val < count.val →
      constructorDFSOffset offsets (row.val + 1) =
        start row + constructorQuotientRowCount edges label row edges.length)
    (hrows : ∀ row : Usize, row.val < count.val → ∀ slot,
      start row ≤ slot →
      slot < start row + constructorQuotientRowCount edges label row edges.length → rowOf slot = row)
    (hfilled : ∀ slot, constructorQuotientFilled edges label start count edges.length slot →
      ∃ value original, neighbors.val[slot]? = some value ∧ witnesses.val[slot]? = some original ∧
        constructorQuotientSlotWitness carrier label (rowOf slot) value original) :
    ConstructorDFSInput offsets neighbors.slice (labelNat root.val) := by
  apply constructor_quotient_dfs_input carrier labelNat offsets neighbors.slice hc
  · simpa only [hcount] using hpositive
  · exact hfirst
  · simpa only [hcount, alloc.vec.Vec.slice, alloc.vec.Vec.val] using hlast
  · simpa only [hcount] using hordered
  · have hbounded := constructor_quotient_neighbors_bounded carrier hc edges label start count
      offsets neighbors witnesses rowOf hfirst hlast hstart hstop (fun node hn => (hlabels node hn).1)
      hfilled
    simpa only [alloc.vec.Vec.slice, alloc.vec.Vec.val, hcount] using hbounded
  · intro node hn
    obtain ⟨actual, hactual⟩ := constructor_usize_index carrier.offsets node (by
      unfold cellCount at hn
      omega)
    have hactualBound : actual.val < cellCount carrier := by simpa only [hactual] using hn
    have hb := (hlabels actual hactualBound).1
    have heq := (hlabels actual hactualBound).2
    rw [← hactual, heq, hcount]
    exact hb
  · intro id hid
    obtain ⟨node, hn, hl⟩ := hdense id (by simpa only [hcount] using hid)
    exact ⟨node.val, hn, by rw [hlabels node hn |>.2]; exact hl⟩
  · exact constructor_quotient_history_carrier_arcs carrier hc edges label labelNat start count
      offsets hcount neighbors witnesses rowOf hedges hhistory (fun node hn => (hlabels node hn).2)
      (fun node hn => (hlabels node hn).1) hstart hstop hrows hfilled
  · exact hroot

/-- Applying the checked generic DFS to a composed quotient input preserves its exact incoming
slot for every nonroot component, including parallel original-edge witnesses. -/
theorem constructor_quotient_depth_first_accepts {R : Type*} (adapter : tree.Rng R)
    (hrng : constructorLegalRng adapter) (offsets : Slice Usize)
    (neighbors : alloc.vec.Vec Usize) (root : Usize) (rng : R)
    (work : spanning_tree.Workspace)
    (hinput : ConstructorDFSInput offsets neighbors.slice root.val)
    (hvalid : WorkspaceValid work)
    (hcapacity : constructorDFSVertexCount offsets ≤ work.path.val.length) :
    WP.spec (spanning_tree.depth_first adapter offsets neighbors.slice root rng work)
      (fun output => output.1 = .Ok () ∧
        ConstructorDFSOutput offsets neighbors.slice root work output.2.2) :=
  constructor_depth_first_accepts adapter hrng offsets neighbors.slice root rng work
    hinput hvalid hcapacity

/-- Every nonroot quotient parent chosen by the actual DFS points to the retained original edge
stored at that exact incoming slot. -/
theorem constructor_quotient_dfs_original_incoming
    (edges : List topology.Edge) (label : Usize → Usize) (start : Usize → Nat)
    (count root : Usize) (offsets : Slice Usize) (neighbors : alloc.vec.Vec Usize)
    (witnesses : alloc.vec.Vec topology.Edge)
    (before after : spanning_tree.Workspace)
    (hcount : constructorDFSVertexCount offsets = count.val)
    (hstart : ∀ row : Usize, row.val < count.val →
      constructorDFSOffset offsets row.val = start row)
    (hstop : ∀ row : Usize, row.val < count.val →
      constructorDFSOffset offsets (row.val + 1) =
        start row + constructorQuotientRowCount edges label row edges.length)
    (hfilled : ∀ slot, constructorQuotientFilled edges label start count edges.length slot →
      ∃ value original, neighbors.val[slot]? = some value ∧
        witnesses.val[slot]? = some original)
    (hout : ConstructorDFSOutput offsets neighbors.slice root before after) :
    ∀ node : Usize, node.val < count.val → node ≠ root →
      ∃ selected : Usize × topology.Edge,
        after.incoming.val[node.val]? = some selected.1 ∧
        witnesses.val[selected.1.val]? = some selected.2 := by
  intro node hnode hnonroot
  obtain ⟨parent, slot, value, hparentLookup, hincoming, hlo, hhi, _, _⟩ :=
    hout.incoming node.val (by simpa only [hcount] using hnode) (by
      intro he
      exact hnonroot ((UScalar.eq_equiv _ _).mpr he))
  have hparentOutput :
      (constructorDFSParents offsets after)[node.val]? = some parent.val := by
    simp [constructorDFSParents, hcount, hnode, hparentLookup]
  have hparentBound : parent.val < count.val := by
    have hparentList := hout.tree.2.2.1 parent.val
      (List.mem_of_getElem? hparentOutput)
    have hlength :
        (constructorDFSParents offsets after).length ≤ count.val := by
      simp [constructorDFSParents, hcount]
    omega
  have hoccupied :
      constructorQuotientFilled edges label start count edges.length slot.val := by
    exact ⟨parent, hparentBound, by simpa only [hstart parent hparentBound] using hlo,
      by simpa only [hstop parent hparentBound] using hhi⟩
  obtain ⟨actual, original, _, hwitness⟩ := hfilled slot.val hoccupied
  exact ⟨(slot, original), hincoming, hwitness⟩

end Labyrinth
