module
public import LabyrinthCore.ConstructorOrientationInitial
public import LabyrinthCore.ConstructorTreeInterpretation
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- A rooted parent tree carried by a carrier tree uses every carrier edge exactly once. -/
theorem constructor_orientation_parentGraph_eq_carrierGraph
    (carrier : topology.Carrier) (tree : spanning_tree.Tree)
    (hc : CarrierValid carrier) (ht : TreeValid carrier tree)
    (hcarrier : (constructorCarrierGraph carrier).IsTree) :
    ∃ hlength : (parents tree).length = cellCount carrier,
      hlength ▸ constructorParentGraph (parents tree) = constructorCarrierGraph carrier := by
  classical
  have transportAdj {m n : Nat} (h : m = n) (graph : SimpleGraph (Fin m))
      (u v : Fin n) :
      (h ▸ graph).Adj u v ↔
        graph.Adj (Fin.cast h.symm u) (Fin.cast h.symm v) := by
    cases h
    rfl
  have transportIsTree {m n : Nat} (h : m = n) (graph : SimpleGraph (Fin m))
      (htree : graph.IsTree) : (h ▸ graph).IsTree := by
    cases h
    exact htree
  have hlength := ht.1
  refine ⟨hlength, ?_⟩
  let parentGraph : SimpleGraph (Fin (cellCount carrier)) :=
    hlength ▸ constructorParentGraph (parents tree)
  let carrierGraph := constructorCarrierGraph carrier
  have hparentTree : parentGraph.IsTree := by
    exact transportIsTree hlength _ (constructor_treeValid_isTree ht)
  have hsub : parentGraph ≤ carrierGraph := by
    intro u v huv
    let pu : Fin (parents tree).length := Fin.cast hlength.symm u
    let pv : Fin (parents tree).length := Fin.cast hlength.symm v
    have hpTransport : (constructorParentGraph (parents tree)).Adj pu pv := by
      exact (transportAdj hlength _ u v).mp (by simpa only [parentGraph] using huv)
    have hp := (constructor_parentGraph_adj_iff (parents tree) pu pv).mp hpTransport
    obtain ⟨hu, hv, hne, hlookup | hlookup⟩ := hp
    · have hnonroot : pu.val ≠ tree.root.val := by
        intro he
        have hfixed := ht.2.1.2.1
        have heq : (parents tree)[pu.val]? = some pu.val := by simpa only [he] using hfixed
        have huvval : pu.val = pv.val := Option.some.inj (heq.symm.trans hlookup)
        exact hne huvval
      have hedge := ht.2.2 pu.val hu hnonroot
      have hedge' : carrierEdge carrier pu.val pv.val := by
        simpa only [parentAt, hlookup, Option.getD_some] using hedge
      have hedgeUV : carrierEdge carrier u.val v.val := by simpa [pu, pv] using hedge'
      simpa only [carrierGraph] using
        (constructor_carrierGraph_adj_iff carrier hc u v).mpr hedgeUV
    · have hnonroot : pv.val ≠ tree.root.val := by
        intro he
        have hfixed := ht.2.1.2.1
        have heq : (parents tree)[pv.val]? = some pv.val := by simpa only [he] using hfixed
        have huvval : pv.val = pu.val := Option.some.inj (heq.symm.trans hlookup)
        exact hne huvval.symm
      have hedge := ht.2.2 pv.val hv hnonroot
      have hedge' : carrierEdge carrier pv.val pu.val := by
        simpa only [parentAt, hlookup, Option.getD_some] using hedge
      have hedgeUV : carrierEdge carrier v.val u.val := by simpa [pu, pv] using hedge'
      simpa only [carrierGraph] using
        (constructor_carrierGraph_adj_iff carrier hc u v).mpr
          (constructor_carrier_edge_symmetric carrier hc hedgeUV)
  have hparentCard := hparentTree.card_edgeFinset
  have hcarrierTree : carrierGraph.IsTree := by simpa only [carrierGraph] using hcarrier
  have hcarrierCard := hcarrierTree.card_edgeFinset
  have hcard : carrierGraph.edgeFinset.card ≤ parentGraph.edgeFinset.card := by omega
  have heq : parentGraph.edgeFinset = carrierGraph.edgeFinset :=
    Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hsub) hcard
  change parentGraph = carrierGraph
  exact SimpleGraph.edgeFinset_inj.mp heq

/-- Actual loops 8/10/9, including the generated root writes and publication, orient a genuine
expanded carrier tree at the requested root. No abstract DFS is substituted. -/
theorem constructor_scene_orientation_accepts
    (expanded : topology.Carrier) (n root : Usize) (work : spanning_tree.Workspace)
    (hc : CarrierValid expanded) (hcarrier : (constructorCarrierGraph expanded).IsTree)
    (hn : n.val = cellCount expanded) (hroot : root.val < cellCount expanded)
    (hw : WorkspaceValid work) (hcapacity : cellCount expanded ≤ work.path.val.length) :
    WP.spec (do
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
      ok (({ parents := finalParents, root } : spanning_tree.Tree),
        { work1 with seen := finalSeen, path := finalPath })) (fun output =>
      let published := output.1
      let finalWork := output.2
      published.root = root ∧ TreeValid expanded published ∧
      (∃ hlength : (parents published).length = cellCount expanded,
        hlength ▸ constructorParentGraph (parents published) =
          constructorCarrierGraph expanded) ∧
      WorkspaceValid finalWork ∧
      finalWork.seen.val.length = work.seen.val.length ∧
      finalWork.path.val.length = work.path.val.length ∧
      finalWork.frames = work.frames ∧ finalWork.parents = work.parents ∧
      finalWork.incoming = work.incoming ∧ finalWork.edit_slots = work.edit_slots ∧
      finalWork.edit_nodes = work.edit_nodes ∧ finalWork.edit_count = work.edit_count ∧
      finalWork.edge_capacity = work.edge_capacity ∧
      ∀ v, v < cellCount expanded → finalWork.seen.val[v]? = some true) := by
  apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize root n rfl)
  intro fresh hfresh
  have hfreshValues : fresh.val = List.replicate (cellCount expanded) root := by
    simpa only [hn] using hfresh.1
  apply WP.spec_bind (constructor_scene_orientation_clear_spec work n hw (by simpa only [hn]))
  rintro ⟨work1, index⟩ ⟨_hindex, hclear⟩
  obtain ⟨hw1, hframes, hpath, hscratchParents, hincoming, hslots, hnodes,
    hcount, hedgeCapacity, hcleared, _hsuffix⟩ := hclear
  have hrootSeen : root.val < work1.seen.val.length := by
    rw [hw1.1, hpath]
    exact lt_of_lt_of_le hroot hcapacity
  have hzeroPath : 0 < work1.path.val.length := by
    rw [hpath]
    have := hc.1
    omega
  simp only [alloc.vec.Vec.index_mut_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec work1.seen root hrootSeen)
  rintro ⟨oldSeen, seenBack⟩ ⟨_, rfl⟩
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec work1.path 0#usize hzeroPath)
  rintro ⟨oldPath, pathBack⟩ ⟨_, rfl⟩
  have hinitial := constructor_orientation_initial expanded root work1 fresh hc hroot hw1
    (by rw [hpath]; exact hcapacity)
    (fun v hv => hcleared v (by simpa only [hn] using hv)) hfreshValues
  apply WP.spec_bind (constructor_scene_orientation_loop_spec expanded root.val
    work1.path.val.length hc hroot (work1.seen.set root true) (work1.path.set 0#usize root)
    index fresh 1#usize {root.val} (fun _ => 0) hinitial)
  rintro ⟨finalSeen, finalPath, finalParents⟩
    ⟨visited, rank, hfinal, hall, hseen⟩
  apply (WP.spec_ok _).mpr
  let published : spanning_tree.Tree := { parents := finalParents, root }
  let finalWork : spanning_tree.Workspace := { work1 with seen := finalSeen, path := finalPath }
  have hrooted : RootedTree (finalParents.val.map (·.val)) root.val :=
    constructor_orientation_rooted hfinal (fun v hv => by rw [hall]; exact Finset.mem_range.mpr hv)
  have htree : TreeValid expanded published := by
    refine ⟨by simpa [published, parents] using hfinal.parents_length, ?_, ?_⟩
    · simpa [published, parents] using hrooted
    · intro v hv hne
      have hv' : v < cellCount expanded := by
        simpa [published, parents, hfinal.parents_length] using hv
      have hm : v ∈ visited := by rw [hall]; exact Finset.mem_range.mpr hv'
      obtain ⟨value, hlookup, _⟩ := hfinal.parent v hm
      have hedge := hfinal.parent_edge v hm hne value hlookup
      have hreverse := constructor_carrier_edge_symmetric expanded hc hedge
      simpa [published, parents, parentAt, hlookup] using hreverse
  have hworkValid : WorkspaceValid finalWork :=
    constructor_orientation_workspace_valid work1 finalSeen finalPath hw1
      (by simpa [finalWork] using hfinal.seen_length)
      (by simpa [finalWork] using hfinal.path_length)
  change published.root = root ∧ TreeValid expanded published ∧
    (∃ hlength : (parents published).length = cellCount expanded,
      hlength ▸ constructorParentGraph (parents published) =
        constructorCarrierGraph expanded) ∧
    WorkspaceValid finalWork ∧ _
  refine ⟨rfl, htree, constructor_orientation_parentGraph_eq_carrierGraph expanded published hc
    htree hcarrier, hworkValid, ?_⟩
  refine ⟨?_, ?_, hframes, hscratchParents, hincoming, hslots, hnodes, hcount,
    hedgeCapacity, ?_⟩
  · change finalSeen.val.length = work.seen.val.length
    calc
      _ = work1.path.val.length := hfinal.seen_length
      _ = work.path.val.length := by rw [hpath]
      _ = work.seen.val.length := hw.1.symm
  · change finalPath.val.length = work.path.val.length
    exact hfinal.path_length.trans (by rw [hpath])
  · intro v hv
    exact hseen v hv

end Labyrinth
