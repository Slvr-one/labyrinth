module
public import LabyrinthCore.ConstructorScenePrepare
public import LabyrinthCore.ConstructorQuotientCSR
public import LabyrinthCore.ConstructorQuotientCursor
public import LabyrinthCore.ConstructorQuotientDFS
public import LabyrinthCore.ConstructorSceneExpandedCarrier
public import LabyrinthCore.ConstructorOrientation
public import LabyrinthCore.ConstructorSceneTotalPrefix
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth
/-- Quotient degree counting contributes two directed incidences for each crossing original
edge and none for an internal edge. -/
theorem constructor_quotient_degree_sum_le (edges : List topology.Edge)
    (label : Usize → Usize) (count processed : Nat)
    (hprocessed : processed ≤ edges.length)
    (hlabels : ∀ edge ∈ edges,
      (label edge.u).val < count ∧ (label edge.v).val < count) :
    (∑ slot ∈ Finset.range (count + 1),
      constructorQuotientDegreeSlot edges label slot processed) ≤ 2 * processed := by
  induction processed with
  | zero => simp [constructorQuotientDegreeSlot]
  | succ processed ih =>
    have hi : processed < edges.length := by omega
    let edge := edges[processed]'hi
    have hlookup : edges[processed]? = some edge := List.getElem?_eq_getElem hi
    obtain ⟨hu, hv⟩ := hlabels edge (List.getElem_mem hi)
    by_cases hsame : label edge.u = label edge.v
    · have hstep (slot : Nat) :
          constructorQuotientDegreeSlot edges label slot (processed + 1) =
            constructorQuotientDegreeSlot edges label slot processed := by
        simp [constructorQuotientDegreeSlot, hlookup, hsame]
      simp only [hstep]
      exact le_trans (ih (by omega)) (by omega)
    · let quotient := constructorCanonicalEdge { u := label edge.u, v := label edge.v }
      have hquotient :
          quotient.u.val < count ∧ quotient.v.val < count ∧ quotient.u ≠ quotient.v := by
        unfold quotient constructorCanonicalEdge
        split
        · exact ⟨hu, hv, hsame⟩
        · exact ⟨hv, hu, Ne.symm hsame⟩
      have hslots : quotient.u.val + 1 ≠ quotient.v.val + 1 := by
        intro he
        exact hquotient.2.2 ((UScalar.eq_equiv _ _).mpr (by omega))
      have hstep (slot : Nat) :
          constructorQuotientDegreeSlot edges label slot (processed + 1) =
            constructorQuotientDegreeSlot edges label slot processed +
              (if slot = quotient.u.val + 1 then 1 else 0) +
              (if slot = quotient.v.val + 1 then 1 else 0) := by
        simp only [constructorQuotientDegreeSlot, hlookup, hsame, ite_false]
        change (if slot = quotient.u.val + 1 ∨ slot = quotient.v.val + 1 then
          constructorQuotientDegreeSlot edges label slot processed + 1
        else constructorQuotientDegreeSlot edges label slot processed) =
          constructorQuotientDegreeSlot edges label slot processed +
            (if slot = quotient.u.val + 1 then 1 else 0) +
            (if slot = quotient.v.val + 1 then 1 else 0)
        split_ifs <;> omega
      simp only [hstep, Finset.sum_add_distrib]
      have huMem : quotient.u.val + 1 ∈ Finset.range (count + 1) :=
        Finset.mem_range.mpr (by omega)
      have hvMem : quotient.v.val + 1 ∈ Finset.range (count + 1) :=
        Finset.mem_range.mpr (by omega)
      have hbound := ih (by omega)
      simp only [Finset.sum_ite_eq', huMem, hvMem, ite_true]
      omega

/-- The exact generated quotient counts have a representable final prefix whenever twice the
original edge count is representable. -/
theorem constructor_quotient_prefix_sum_le (edges : List topology.Edge)
    (label : Usize → Usize) (count : Usize) (counts : List Usize)
    (hlength : counts.length = count.val + 1)
    (hlabels : ∀ edge ∈ edges,
      (label edge.u).val < count.val ∧ (label edge.v).val < count.val)
    (hcounts : ∀ slot, slot < counts.length → ∃ value : Usize,
      counts[slot]? = some value ∧
        value.val = constructorQuotientDegreeSlot edges label slot edges.length) :
    constructorPrefixSum counts counts.length ≤ 2 * edges.length := by
  rw [constructor_prefix_sum_as_sum, hlength]
  calc
    (∑ slot ∈ Finset.range (count.val + 1), (counts[slot]?.getD 0#usize).val) =
        ∑ slot ∈ Finset.range (count.val + 1),
          constructorQuotientDegreeSlot edges label slot edges.length := by
      apply Finset.sum_congr rfl
      intro slot hslot
      obtain ⟨value, hvalue, heq⟩ := hcounts slot (by
        rw [hlength]
        exact Finset.mem_range.mp hslot)
      simpa only [hvalue, Option.getD_some] using heq
    _ ≤ 2 * edges.length :=
      constructor_quotient_degree_sum_le edges label count.val edges.length le_rfl hlabels

/-- Degree slot zero stays the empty CSR sentinel because every real quotient row is stored at
its one-based count slot. -/
theorem constructor_quotient_degree_zero (edges : List topology.Edge)
    (label : Usize → Usize) (processed : Nat) :
    constructorQuotientDegreeSlot edges label 0 processed = 0 := by
  induction processed with
  | zero => rfl
  | succ processed ih =>
      simp only [constructorQuotientDegreeSlot, ih]
      split
      · rfl
      · split
        · rfl
        · simp
/-- Exact prefix offsets admit a single row owner for every slot in a quotient row. -/
theorem constructor_quotient_row_owner (counts : List Usize) (offsets : Slice Usize)
    (count : Usize) (hlength : offsets.val.length = count.val + 1)
    (hoffsets : ∀ slot, slot < offsets.val.length → ∃ value : Usize,
      offsets.val[slot]? = some value ∧
        value.val = constructorPrefixSum counts (slot + 1)) :
    ∃ rowOf : Nat → Usize, ∀ row : Usize, row.val < count.val → ∀ slot,
      constructorDFSOffset offsets row.val ≤ slot →
      slot < constructorDFSOffset offsets (row.val + 1) → rowOf slot = row := by
  classical
  let owns (slot : Nat) (row : Usize) : Prop :=
    row.val < count.val ∧ constructorDFSOffset offsets row.val ≤ slot ∧
      slot < constructorDFSOffset offsets (row.val + 1)
  let rowOf : Nat → Usize := fun slot =>
    if h : ∃ row, owns slot row then Classical.choose h else 0#usize
  refine ⟨rowOf, ?_⟩
  intro row hrow slot hstart hstop
  have hexists : ∃ candidate, owns slot candidate := ⟨row, hrow, hstart, hstop⟩
  have hchosen : owns slot (Classical.choose hexists) := Classical.choose_spec hexists
  rw [show rowOf slot = Classical.choose hexists by
    simp only [rowOf, dite_eq_left hexists]]
  have hchosenBound : (Classical.choose hexists).val < count.val := hchosen.1
  have offsetMono {left right : Nat} (hleft : left < offsets.val.length)
      (hright : right < offsets.val.length) (hle : left ≤ right) :
      constructorDFSOffset offsets left ≤ constructorDFSOffset offsets right := by
    obtain ⟨leftValue, hleftValue, hleftPrefix⟩ := hoffsets left hleft
    obtain ⟨rightValue, hrightValue, hrightPrefix⟩ := hoffsets right hright
    simp only [constructorDFSOffset, hleftValue, hrightValue, Option.map_some,
      Option.getD_some, hleftPrefix, hrightPrefix]
    exact constructor_prefix_sum_mono counts (by omega)
  apply UScalar.eq_of_val_eq
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hbefore | hafter
  · have hdisjoint := offsetMono
      (left := (Classical.choose hexists).val + 1) (right := row.val)
      (by omega) (by omega) (by omega)
    omega
  · have hdisjoint := offsetMono
      (left := row.val + 1) (right := (Classical.choose hexists).val)
      (by omega) (by omega) (by omega)
    omega



/-- Every checked allocation width in `scene_dfs`, stated only with original input sizes. -/
def ConstructorSceneAllocationFits (carrier : topology.Carrier) : Prop :=
  let n := cellCount carrier
  let m := carrier.edges.val.length
  n + 1 ≤ Usize.max ∧
  (n + 1) * 8 ≤ Usize.max ∧
  (n + 1) * 8 ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val ∧
  m * 2 ≤ Usize.max ∧
  (m * 2) * 8 ≤ Usize.max ∧
  (m * 2) * 8 ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val ∧
  (m * 2) * 16 ≤ Usize.max ∧
  (m * 2) * 16 ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val ∧
  (n - 1) * 16 ≤ Usize.max ∧
  (n - 1) * 16 ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val ∧
  ((n - 1) * 2) * 8 ≤ Usize.max ∧
  ((n - 1) * 2) * 8 ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val

private theorem constructor_scene_carrier_overflow_return :
    WP.spec (do
      let actual ← ok (core.convert.FromSame.from topology.Error.Overflow)
      ok (.Err actual : core.result.Result topology.Carrier topology.Error))
      (fun result => result = .Err topology.Error.Overflow) := by
  have hconvert : WP.spec
      (ok (core.convert.FromSame.from topology.Error.Overflow))
      (fun actual => actual = topology.Error.Overflow) := (WP.spec_ok _).mpr rfl
  apply WP.spec_bind hconvert
  intro actual hactual
  rw [hactual]
  exact (WP.spec_ok _).mpr rfl

/-- If one of the allocation widths checked by `from_edges` does not fit, the literal
selected-carrier call returns exactly `Overflow`; endpoint validation is not reached. -/
theorem constructor_scene_expanded_carrier_overflow (n : Usize)
    (selected : alloc.vec.Vec topology.Edge) (hn : n ≠ 0#usize)
    (hwidth : ¬ constructorEdgesStorageFits n selected.slice) :
    WP.spec (topology.Carrier.from_edges n selected.slice)
      (fun result => result = .Err topology.Error.Overflow) := by
  unfold topology.Carrier.from_edges
  simp only [hn, ite_false]
  cases hadd : Usize.checked_add n 1#usize with
  | none =>
      simp only [lift, bind_ok, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact constructor_scene_carrier_overflow_return
  | some count =>
      have ha := Usize.checked_add_bv_spec n 1#usize
      simp only [hadd] at ha
      have hcount : count.val = n.val + 1 := by
        simpa only [UScalar.ofNatCore_val_eq] using ha.2.1
      cases hmul : Usize.checked_mul (Slice.len selected.slice) 2#usize with
      | none =>
          simp only [lift, bind_ok, core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          exact constructor_scene_carrier_overflow_return
      | some twice =>
          have hm := Usize.checked_mul_bv_spec (Slice.len selected.slice) 2#usize
          simp only [hmul] at hm
          have htwice : twice.val = selected.val.length * 2 := by
            simpa only [Slice.len_val, UScalar.ofNatCore_val_eq,
              alloc.vec.Vec.slice, alloc.vec.Vec.val] using hm.2.1
          simp only [lift, bind_ok, core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch, constructor_check_storage_eq]
          by_cases hc : constructorStorageFits count 8#usize
          · simp only [hc, ite_true, bind_ok]
            by_cases ht : constructorStorageFits twice 8#usize
            · simp only [ht, ite_true, bind_ok]
              by_cases he : constructorStorageFits (Slice.len selected.slice) 16#usize
              · have hc' := hc
                have ht' := ht
                simp only [constructorStorageFits, hcount, UScalar.ofNatCore_val_eq] at hc'
                simp only [constructorStorageFits, htwice, UScalar.ofNatCore_val_eq] at ht'
                exact False.elim (hwidth
                  ⟨by omega, by simpa only [alloc.vec.Vec.slice, alloc.vec.Vec.val] using
                    (show selected.val.length * 2 ≤ Usize.max by omega),
                    hc'.1, hc'.2, by simpa only [alloc.vec.Vec.slice, alloc.vec.Vec.val] using
                    ht'.1, by simpa only [alloc.vec.Vec.slice, alloc.vec.Vec.val] using ht'.2,
                    he⟩)
              · simp only [he, ite_false, bind_ok,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                exact constructor_scene_carrier_overflow_return
            · simp only [ht, ite_false, bind_ok,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              exact constructor_scene_carrier_overflow_return
          · simp only [hc, ite_false, bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            exact constructor_scene_carrier_overflow_return

/-- A tree oriented over the expanded selected carrier is also a tree over the original carrier,
provided every actual selected edge is an original carrier edge. -/
theorem constructor_scene_tree_valid_original (carrier expanded : topology.Carrier)
    (selected : alloc.vec.Vec topology.Edge) (tree : spanning_tree.Tree)
    (hc : CarrierValid carrier) (_hec : CarrierValid expanded)
    (hcount : cellCount expanded = cellCount carrier)
    (hexact : ∀ u v, carrierEdge expanded u v ↔
      ∃ edge ∈ selected.val, (u = edge.u.val ∧ v = edge.v.val) ∨
        (u = edge.v.val ∧ v = edge.u.val))
    (hselected : ∀ edge ∈ selected.val,
      carrierEdge carrier edge.u.val edge.v.val)
    (htree : TreeValid expanded tree) : TreeValid carrier tree := by
  refine ⟨htree.1.trans hcount, ?_, ?_⟩
  · exact htree.2.1
  · intro node hnode hnonroot
    have hnodeExpanded : node < (parents tree).length := by exact hnode
    have hedgeExpanded := htree.2.2 node hnodeExpanded hnonroot
    obtain ⟨edge, hedge, forward | backward⟩ := (hexact node (parentAt (parents tree) node)).mp
      hedgeExpanded
    · rw [forward.2, forward.1]
      exact hselected edge hedge
    · have horiginal := hselected edge hedge
      have hreverse := constructor_carrier_edge_symmetric carrier hc horiginal
      rw [backward.2, backward.1]
      exact hreverse

/-- Adjacency in a parent graph transported to an equal vertex count is adjacency of the
original graph at the corresponding cast vertices. -/
theorem constructor_parentGraph_transport_adj (p : List Nat) {n : Nat}
    (hlength : p.length = n) (source target : Fin n)
    (hadj : (hlength ▸ constructorParentGraph p).Adj source target) :
    (constructorParentGraph p).Adj
      (Fin.cast hlength.symm source) (Fin.cast hlength.symm target) := by
  subst n
  exact hadj

/-- Equality of the oriented parent graph with the expanded carrier graph turns every expanded
carrier edge into an actual published parent edge. -/
theorem constructor_scene_published_has_expanded_edge
    (expanded : topology.Carrier) (tree : spanning_tree.Tree)
    (hc : CarrierValid expanded)
    (hgraph : ∃ hlength : (parents tree).length = cellCount expanded,
      hlength ▸ constructorParentGraph (parents tree) = constructorCarrierGraph expanded)
    {u v : Nat} (hedge : carrierEdge expanded u v) :
    parentEdge (parents tree) u v := by
  obtain ⟨hlength, hgraph⟩ := hgraph
  have hv : v < cellCount expanded :=
    ((hc.2.2.2.2.1 u hedge.1).2.2 v hedge.2).1
  let source : Fin (cellCount expanded) := ⟨u, hedge.1⟩
  let target : Fin (cellCount expanded) := ⟨v, hv⟩
  have hcarrierAdj : (constructorCarrierGraph expanded).Adj source target :=
    (constructor_carrierGraph_adj_iff expanded hc source target).mpr hedge
  have htransported : (hlength ▸ constructorParentGraph (parents tree)).Adj source target := by
    rw [hgraph]
    exact hcarrierAdj
  have hparentAdj : (constructorParentGraph (parents tree)).Adj
      (Fin.cast hlength.symm source) (Fin.cast hlength.symm target) :=
    constructor_parentGraph_transport_adj (parents tree) hlength source target htransported
  simpa only [source, target, Fin.val_cast] using
    (constructor_parentGraph_adj_iff (parents tree)
      (Fin.cast hlength.symm source) (Fin.cast hlength.symm target)).mp hparentAdj

/-- The literal `from_edges` call followed by the literal generated orientation loops publishes
an original-carrier tree, rooted as requested, containing every required edge. -/
theorem constructor_scene_publish_accepts
    (carrier : topology.Carrier) (required : Slice topology.Edge) (n root : Usize)
    (selected : alloc.vec.Vec topology.Edge) (work : spanning_tree.Workspace)
    (hc : CarrierValid carrier) (hn : n.val = cellCount carrier)
    (hroot : root.val < cellCount carrier)
    (hselectedEdges : ∀ edge ∈ selected.val,
      edge.u.val < n.val ∧ edge.v.val < n.val ∧ edge.u ≠ edge.v)
    (hselectedCarrier : ∀ edge ∈ selected.val,
      carrierEdge carrier edge.u.val edge.v.val)
    (hconnected : ∀ v, v < n.val →
      Relation.ReflTransGen (fun u v =>
        ∃ edge ∈ selected.val, (u = edge.u.val ∧ v = edge.v.val) ∨
          (u = edge.v.val ∧ v = edge.u.val)) 0 v)
    (hlength : selected.val.length + 1 = n.val)
    (hprefix : ∀ slot, slot < required.val.length →
      selected.val[slot]? = (required.val[slot]?).map constructorCanonicalEdge)
    (hwidth : constructorEdgesStorageFits n selected.slice)
    (hw : WorkspaceValid work) (hcapacity : n.val ≤ work.path.val.length) :
    WP.spec (do
      let result ← topology.Carrier.from_edges n selected.slice
      let cf ← core.result.Result.Insts.CoreOpsTry.branch result
      match cf with
      | .Continue expanded =>
        let parents ← alloc.vec.from_elem core.clone.CloneUsize root n
        let (work1, index) ← spanning_tree.Tree.scene_dfs_loop8 work n 0#usize
        let (_, seenBack) ← alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice Bool) work1.seen root
        let (_, pathBack) ← alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice Usize) work1.path 0#usize
        let path := pathBack root
        let seen := seenBack true
        let (finalSeen, finalPath, finalParents) ←
          spanning_tree.Tree.scene_dfs_loop9 seen path index expanded parents 1#usize
        ok (core.result.Result.Ok ({ parents := finalParents, root } : spanning_tree.Tree),
          { work1 with seen := finalSeen, path := finalPath })
      | .Break residual => do
        let result ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            spanning_tree.Tree (core.convert.FromSame topology.Error) residual
        ok (result, work)) (fun output =>
      ∃ (published : spanning_tree.Tree),
        output.1 = core.result.Result.Ok published ∧ published.root = root ∧
        TreeValid carrier published ∧ WorkspaceValid output.2 ∧
        output.2.frames = work.frames ∧ output.2.parents = work.parents ∧
        output.2.incoming = work.incoming ∧ output.2.edit_slots = work.edit_slots ∧
        output.2.edit_nodes = work.edit_nodes ∧ output.2.edit_count = work.edit_count ∧
        output.2.edge_capacity = work.edge_capacity ∧
        (∀ slot, slot < required.val.length → ∀ edge,
          required.val[slot]? = some edge →
          parentEdge (parents published) edge.u.val edge.v.val)) := by
  have hnzero : n ≠ 0#usize := by
    intro heq
    have : n.val = 0 := congrArg UScalar.val heq
    rw [hn] at this
    omega
  apply WP.spec_bind (constructor_scene_expanded_carrier_accepts n selected hnzero
    hselectedEdges hconnected hlength hwidth)
  intro result hresult
  obtain ⟨expanded, hresult, hec, hcount, htree, hexact⟩ := hresult
  rw [hresult]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have horientation := constructor_scene_orientation_accepts expanded n root work hec htree
    hcount (by omega) hw (by simpa only [hcount] using hcapacity)
  have hwrapped := WP.spec_bind
    (Pₖ := fun output : core.result.Result spanning_tree.Tree topology.Error ×
        spanning_tree.Workspace =>
      ∃ published, output.1 = core.result.Result.Ok published ∧ published.root = root ∧
        TreeValid carrier published ∧ WorkspaceValid output.2 ∧
        output.2.frames = work.frames ∧ output.2.parents = work.parents ∧
        output.2.incoming = work.incoming ∧ output.2.edit_slots = work.edit_slots ∧
        output.2.edit_nodes = work.edit_nodes ∧ output.2.edit_count = work.edit_count ∧
        output.2.edge_capacity = work.edge_capacity ∧
        ∀ slot, slot < required.val.length → ∀ edge,
          required.val[slot]? = some edge →
          parentEdge (parents published) edge.u.val edge.v.val)
    (k := fun output : spanning_tree.Tree × spanning_tree.Workspace =>
      ok (core.result.Result.Ok output.1, output.2))
    horientation (by
      rintro ⟨published, finalWork⟩ horiented
      obtain ⟨hpublishedRoot, hpublishedExpanded, hgraph, hwork, _hseenLength, _hpathLength,
        hframes, hparents, hincoming, hslots, hnodes, heditCount, hedgeCapacity, _hallSeen⟩ :=
        horiented
      apply (WP.spec_ok _).mpr
      refine ⟨published, rfl, hpublishedRoot,
        constructor_scene_tree_valid_original carrier expanded selected published hc hec
          (by omega) hexact hselectedCarrier hpublishedExpanded,
        hwork, hframes, hparents, hincoming, hslots, hnodes, heditCount, hedgeCapacity, ?_⟩
      intro slot hslot edge hedge
      apply constructor_scene_published_has_expanded_edge expanded published hec hgraph
      exact constructor_scene_expanded_contains_required required selected expanded hprefix hexact
        slot hslot edge hedge)
  simp only [Std.bind_assoc, bind_ok, uncurry] at hwrapped
  apply Eq.mp ?_ hwrapped
  apply congrArg₂ WP.spec
  · congr 1
  · rfl

end Labyrinth
