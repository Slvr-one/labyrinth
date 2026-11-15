module
public import LabyrinthCore.MutationBatchAttach
public import LabyrinthCore.MutationCommit
public import LabyrinthCore.MutationEditPreflight
public import LabyrinthCore.MutationCut
public import LabyrinthCore.MutationEditModel

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

/-- Totality, publication framing, and structural validity for the actual sparse batch
operation. Every internal walk terminates, errors retain the published tree, and every
successful result is a valid tree with exactly the requested edge edit. -/
theorem mutation_edit_edges_tree_valid
    (c : topology.Carrier) (t : spanning_tree.Tree)
    (remove add : Slice topology.Edge) (w : spanning_tree.Workspace)
    (hc : CarrierValid c) (ht : TreeValid c t) (hw : WorkspaceValid w)
    (hcapacity : t.parents.val.length ≤ w.path.val.length)
    (hedgeCapacity : c.edges.val.length ≤ w.edge_capacity.val) :
    spanning_tree.Tree.edit_edges t c remove add w ⦃ out =>
      WorkspaceValid out.2.2 ∧
      out.2.2.path.val.length = w.path.val.length ∧
      (∀ error, out.1 = core.result.Result.Err error → out.2.1 = t) ∧
      (out.1 = core.result.Result.Ok () →
        out.2.1.root = t.root ∧ out.2.1.parents.val.length = t.parents.val.length ∧
        (∀ u v, parentEdge (parents out.2.1) u v ↔
          MutationEditedEdge (parents t) remove add u v) ∧
        (∀ u v, parentEdge (parents out.2.1) u v → carrierEdge c u v) ∧
        TreeValid c out.2.1) ⦄ := by
  classical
  have herrorReturn (error : topology.Error) (work : spanning_tree.Workspace)
      (hvalid : WorkspaceValid work) (hlength : work.path.val.length = w.path.val.length) :
      (do
        let status ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame topology.Error) (core.result.Result.Err error)
        Result.ok (status, t, work)) ⦃ out =>
          WorkspaceValid out.2.2 ∧
          out.2.2.path.val.length = w.path.val.length ∧
          (∀ e, out.1 = core.result.Result.Err e → out.2.1 = t) ∧
          (out.1 = core.result.Result.Ok () →
            out.2.1.root = t.root ∧ out.2.1.parents.val.length = t.parents.val.length ∧
            (∀ u v, parentEdge (parents out.2.1) u v ↔
              MutationEditedEdge (parents t) remove add u v) ∧
            (∀ u v, parentEdge (parents out.2.1) u v → carrierEdge c u v) ∧
            TreeValid c out.2.1) ⦄ := by
    have hconvert : Result.ok (core.convert.FromSame.from error)
        ⦃ actual => actual = core.convert.FromSame.from error ⦄ := (spec_ok _).mpr rfl
    have hresidual :
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame topology.Error) (core.result.Result.Err error) ⦃
            (status : core.result.Result Unit topology.Error) =>
              ∃ actual : topology.Error, status = core.result.Result.Err actual ⦄ := by
      unfold core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      apply spec_bind hconvert
      intro actual _
      exact (spec_ok _).mpr ⟨actual, rfl⟩
    apply spec_bind hresidual
    rintro status ⟨actual, rfl⟩
    apply (spec_ok _).mpr
    exact ⟨hvalid, hlength, fun _ _ => rfl, by simp⟩
  unfold spanning_tree.Tree.edit_edges
  simp only [topology.Carrier.impl.edges, bind_ok]
  have hcells : ¬ alloc.vec.Vec.len t.parents > alloc.vec.Vec.len w.path := by
    change ¬ w.path.val.length < t.parents.val.length
    omega
  have hderefLength :
      (alloc.vec.Vec.deref c.edges).val.length = c.edges.val.length := by
    simp only [alloc.vec.Vec.deref, Slice.from_val]
  have hedges : ¬ Slice.len (alloc.vec.Vec.deref c.edges) > w.edge_capacity := by
    change ¬ w.edge_capacity.val < (alloc.vec.Vec.deref c.edges).val.length
    rw [hderefLength]
    omega
  simp only [spanning_tree.Workspace.ensure, hcells, hedges, ite_false,
    core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply spec_bind (mutation_check_carrier_total c t hc)
  intro checked hchecked
  have hcheckedOk : checked = core.result.Result.Ok () :=
    hchecked.2.mpr (mutation_tree_valid_compatible c t ht)
  rw [hcheckedOk]
  simp only [bind_ok]
  by_cases hlength : Slice.len remove = Slice.len add
  · have hlengthNat : remove.val.length = add.val.length := by simpa using congrArg UScalar.val hlength
    simp only [hlength, bne_self_eq_false, Bool.false_eq_true, ite_false]
    split
    · apply (spec_ok _).mpr
      simp [hw]
    · rename_i hcount
      apply spec_bind (mutation_edit_preflight_total c t remove add hc hlengthNat)
      intro status hstatus
      cases status with
      | Err error =>
        apply spec_bind ((spec_ok _).mpr rfl)
        intro cf hcf
        subst cf
        exact herrorReturn error w hw rfl
      | Ok payload =>
        cases payload
        have hentries := hstatus.mp rfl
        obtain ⟨hremove, hadd⟩ := mutation_edit_entries_edges c t remove add hc hlengthNat hentries
        simp only [bind_ok]
        apply spec_bind (mutation_clear_edits_prepares c t w ht hw)
        rintro cleared ⟨hclearValid, hclearPath, hclearWithin, hclearForest,
          hclearRoot, hclearParents⟩
        apply spec_bind (mutation_cut_loop_preserves_root t remove cleared hclearValid
          (by rw [hclearPath]; exact hcapacity) hclearWithin hclearForest ht.2.1 hremove hclearRoot)
        rintro cut ⟨hcutValid, hcutPath, hcutWithin, hcutForest, hcutRoot, hcutParents⟩
        have hcutParents' : ∀ u, u < (parents t).length →
            mutationVirtualParent cut (alloc.vec.Vec.deref t.parents) u =
              if ∃ edge ∈ remove.val, mutationCutChild t.parents edge = u then u
              else parentAt (parents t) u := by
          intro u hu
          rw [hcutParents u (by simpa only [parents, List.length_map] using hu),
            hclearParents u (by simpa only [parents, List.length_map] using hu)]
        have hparentRawLength : (parents t).length = t.parents.val.length := by
          simp only [parents, List.length_map]
        have hcutGraph : (mutationFunctionalGraph t.parents.val.length
            (mutationVirtualParent cut (alloc.vec.Vec.deref t.parents))).IsAcyclic := by
          rw [← hparentRawLength]
          exact mutation_functional_cut_acyclic (parents t) t.root.val
            (mutationVirtualParent cut (alloc.vec.Vec.deref t.parents))
            (fun u => ∃ edge ∈ remove.val, mutationCutChild t.parents edge = u)
            ht.2.1 hcutParents'
        have hparentLength : t.parents.val.length = cellCount c := by
          simpa only [parents, List.length_map] using ht.1
        have haddIndices : ∀ edge ∈ add.val,
            edge.u.val < t.parents.val.length ∧ edge.v.val < t.parents.val.length := by
          intro edge hedge
          have he := hadd edge hedge
          have hvBound := (hc.2.2.2.2.1 edge.u.val he.1).2.2 edge.v.val he.2
          rw [hparentLength]
          exact ⟨he.1, hvBound.1⟩
        apply spec_bind (mutation_batch_attach_total t add cut hcutValid
          (by rw [hcutPath, hclearPath]; exact hcapacity) hcutWithin hcutForest
          (by simpa only [parents, List.length_map] using ht.2.1.1) hcutRoot hcutGraph haddIndices)
        rintro ⟨attached, attachedStatus⟩
          ⟨hattachedValid, hattachedLength, hattachedWithin, hattachedForest,
            hattachedRoot, hattachedGraph, hattachedEdges⟩
        cases attachedStatus with
        | Err error =>
          dsimp only at hattachedValid hattachedLength
          apply spec_bind ((spec_ok _).mpr rfl)
          intro cf hcf
          subst cf
          exact herrorReturn error attached hattachedValid (by
            rw [hattachedLength, hcutPath, hclearPath])
        | Ok payload =>
          cases payload
          apply spec_bind ((spec_ok _).mpr rfl)
          intro cf hcf
          subst cf
          change (do
            let (v, v1, v2, v3, v4, v5, v6, v7, i4, i5) ←
              spanning_tree.Tree.edit_edges_loop3 t.parents attached 0#usize
            Result.ok
              (core.result.Result.Ok (),
                spanning_tree.Tree.mk v t.root,
                spanning_tree.Workspace.mk v1 v2 v3 v4 v5 v6 v7 i4 i5)) ⦃ _ ⦄
          apply spec_bind (mutation_commit_total t.parents attached hattachedValid
            (by rw [hattachedLength, hcutPath, hclearPath]; exact hcapacity)
            (mutation_overlay_active_bound t.parents.val.length attached
              hattachedValid hattachedWithin))
          rintro committed ⟨result, rfl, hresultLength, hresultParents⟩
          apply (spec_ok _).mpr
          have hcutEdges := mutation_cut_functional_edges_exact t.parents
            (mutationVirtualParent cut (alloc.vec.Vec.deref t.parents)) t.root.val remove
            ht.2.1 hremove (by
              simpa only [parents, List.length_map] using hcutParents')
          have hresultEdges := mutation_committed_edit_edges_exact t.parents result cut attached
            remove add hresultLength hresultParents hcutEdges (hattachedEdges rfl)
          have hfinalEdges : ∀ u v,
              mutationFunctionalEdge t.parents.val.length
                  (mutationVirtualParent attached (alloc.vec.Vec.deref t.parents)) u v ↔
                MutationEditedEdge (parents t) remove add u v := by
            intro u v
            rw [hattachedEdges rfl u v, hcutEdges u v, mutation_added_before_full]
            rfl
          have hfinalTree := mutation_functional_edit_isTree c t remove add
            (mutationVirtualParent attached (alloc.vec.Vec.deref t.parents))
            hc ht hlengthNat hentries hfinalEdges hattachedGraph
          have hresultParentLength :
              (result.val.map (fun x : Usize => x.val)).length =
                t.parents.val.length := by
            simpa only [List.length_map] using hresultLength
          have hresultRooted :
              RootedTree (result.val.map (fun x : Usize => x.val)) t.root.val := by
            apply mutation_functional_connected_rooted
              (result.val.map (fun x : Usize => x.val)) t.root.val
              (mutationVirtualParent attached (alloc.vec.Vec.deref t.parents))
            · rw [hresultParentLength]
              simpa only [parents, List.length_map] using ht.2.1.1
            · intro u hu
              rw [hresultParentLength] at hu ⊢
              exact mutation_functional_forest_bounds t.parents.val.length
                (mutationVirtualParent attached (alloc.vec.Vec.deref t.parents))
                hattachedForest u hu
            · exact hattachedRoot
            · intro u hu
              have hresult : u < result.val.length := by simpa only [List.length_map] using hu
              simpa [parentAt, hresult] using hresultParents u (by
                rw [← hresultParentLength]
                exact hu)
            · rw [hresultParentLength]
              exact hfinalTree.connected
          have hresultCarrier : ∀ u v,
              parentEdge (parents (spanning_tree.Tree.mk result t.root)) u v →
                carrierEdge c u v := by
            intro u v hedge
            apply mutation_edited_edge_carrier c t remove add hc ht hadd u v
            exact (hresultEdges u v).mp (by simpa only [parents] using hedge)
          have hresultValid : TreeValid c (spanning_tree.Tree.mk result t.root) := by
            refine ⟨?_, hresultRooted, ?_⟩
            · simpa only [parents, List.length_map, hresultLength] using ht.1
            · intro u hu hnonroot
              have hu' : u < (result.val.map (fun x : Usize => x.val)).length := by
                simpa only [parents] using hu
              have hnonroot' : u ≠ t.root.val := by simpa only using hnonroot
              have hparentMem :
                  parentAt (result.val.map (fun x : Usize => x.val)) u ∈
                    result.val.map (fun x : Usize => x.val) := by
                simp only [parentAt, List.getElem?_eq_getElem hu', Option.getD_some]
                exact List.getElem_mem hu'
              have hparentBound : parentAt (result.val.map (fun x : Usize => x.val)) u <
                  (result.val.map (fun x : Usize => x.val)).length :=
                hresultRooted.2.2.1 _ hparentMem
              have huResult : u < result.val.length := by
                simpa only [List.length_map] using hu'
              have hparentGet :
                  (result.val.map (fun x : Usize => x.val))[u]? =
                    some (parentAt (result.val.map (fun x : Usize => x.val)) u) := by
                simp [parentAt, huResult]
              have hedge : parentEdge (result.val.map (fun x : Usize => x.val)) u
                  (parentAt (result.val.map (fun x : Usize => x.val)) u) :=
                ⟨hu', hparentBound,
                  mutation_rooted_nonroot_parent_ne _ t.root.val u
                    hresultRooted hu' hnonroot',
                  Or.inl hparentGet⟩
              apply hresultCarrier u (parentAt (result.val.map (fun x : Usize => x.val)) u)
              simpa only [parents] using hedge
          refine ⟨hattachedValid,
            by simpa only using hattachedLength.trans (hcutPath ▸ hclearPath ▸ rfl),
            by simp, ?_⟩
          intro _
          exact ⟨by simp, by simp [hresultLength],
            by simpa only [parents] using hresultEdges, hresultCarrier, hresultValid⟩
  · have hne : (Slice.len remove != Slice.len add) = true := by simp [hlength]
    simp only [hne, ite_true, spec_ok]
    simp [hw]


/-- The original total/frame view, retained for callers that do not need the structural
success refinement. -/
theorem mutation_edit_edges_total_frame
    (c : topology.Carrier) (t : spanning_tree.Tree)
    (remove add : Slice topology.Edge) (w : spanning_tree.Workspace)
    (hc : CarrierValid c) (ht : TreeValid c t) (hw : WorkspaceValid w)
    (hcapacity : t.parents.val.length ≤ w.path.val.length)
    (hedgeCapacity : c.edges.val.length ≤ w.edge_capacity.val) :
    spanning_tree.Tree.edit_edges t c remove add w ⦃ out =>
      WorkspaceValid out.2.2 ∧
      out.2.2.path.val.length = w.path.val.length ∧
      (∀ error, out.1 = core.result.Result.Err error → out.2.1 = t) ∧
      (out.1 = core.result.Result.Ok () →
        out.2.1.root = t.root ∧ out.2.1.parents.val.length = t.parents.val.length ∧
        (∀ u v, parentEdge (parents out.2.1) u v ↔
          MutationEditedEdge (parents t) remove add u v) ∧
        ∀ u v, parentEdge (parents out.2.1) u v → carrierEdge c u v) ⦄ := by
  apply spec_mono
    (mutation_edit_edges_tree_valid c t remove add w hc ht hw hcapacity hedgeCapacity)
  intro out h
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro hok
  have hs := h.2.2.2 hok
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩
end Labyrinth
