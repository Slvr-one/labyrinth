module
public import LabyrinthCore.MutationAttachSpec
public import LabyrinthCore.MutationFunctionalGraph

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

 def mutationAddedBefore (add : Slice topology.Edge) (stop u v : Nat) : Prop :=
  ∃ j, j < stop ∧ ∃ edge, add.val[j]? = some edge ∧
    ((u = edge.u.val ∧ v = edge.v.val) ∨ (v = edge.u.val ∧ u = edge.v.val))

 def MutationSeparate (n : Nat) (next : Nat → Nat) (u v : Nat) : Prop :=
  ∃ a b, MutationVirtualRootWitness next n u a ∧
    MutationVirtualRootWitness next n v b ∧ a ≠ b

 theorem mutation_attach_virtual_acceptance
    (t : spanning_tree.Tree) (edge : topology.Edge) (w : spanning_tree.Workspace)
    (hw : WorkspaceValid w) (hcapacity : t.parents.val.length ≤ w.path.val.length)
    (hwithin : MutationOverlayWithin t.parents.val.length w)
    (hu : edge.u.val < t.parents.val.length) (hv : edge.v.val < t.parents.val.length)
    (hforest : MutationFunctionalForest t.parents.val.length
      (mutationVirtualParent w (alloc.vec.Vec.deref t.parents))) :
    spanning_tree.Tree.attach_virtual t edge w ⦃ out =>
      out.1 = core.result.Result.Ok () ↔
        MutationSeparate t.parents.val.length
          (mutationVirtualParent w (alloc.vec.Vec.deref t.parents)) edge.u.val edge.v.val ⦄ := by
  let n := t.parents.val.length
  let next := mutationVirtualParent w (alloc.vec.Vec.deref t.parents)
  have hbounded := mutation_functional_forest_bounds n next hforest
  have hiter : ∀ j u, u < n → next^[j] u < n := by
    intro j
    induction j with
    | zero => exact fun _ h => h
    | succ j ih =>
      intro u h
      rw [Function.iterate_succ_apply']
      exact hbounded _ (ih u h)
  unfold spanning_tree.Tree.attach_virtual
  apply spec_bind (mutation_virtual_root_total t edge.u w hw hcapacity)
  rintro first ⟨hfirst, hfirstError, hfirstCases⟩
  obtain ⟨rootU, rfl⟩ : ∃ rootU, first = core.result.Result.Ok rootU := by
    rcases hfirstCases with h | h
    · exact h
    · exact ((hfirstError.mp h) (hforest edge.u.val hu)).elim
  have hrootU := hfirst rootU rfl
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply spec_bind (mutation_virtual_root_total t edge.v w hw hcapacity)
  rintro second ⟨hsecond, hsecondError, hsecondCases⟩
  obtain ⟨rootV, rfl⟩ : ∃ rootV, second = core.result.Result.Ok rootV := by
    rcases hsecondCases with h | h
    · exact h
    · exact ((hsecondError.mp h) (hforest edge.v.val hv)).elim
  have hrootV := hsecond rootV rfl
  have hseparate : MutationSeparate n next edge.u.val edge.v.val ↔ rootU ≠ rootV := by
    constructor
    · rintro ⟨a, b, ha, hb, hne⟩ he
      apply hne
      have hau := mutation_virtual_root_unique next n edge.u.val a rootU.val ha hrootU
      have hbv := mutation_virtual_root_unique next n edge.v.val b rootV.val hb hrootV
      exact hau.trans ((congrArg UScalar.val he).trans hbv.symm)
    · intro hne
      exact ⟨rootU.val, rootV.val, hrootU, hrootV, fun he => hne (UScalar.eq_of_val_eq he)⟩
  simp only [bind_ok]
  by_cases heq : rootU = rootV
  · simp only [heq, ite_true]
    apply (spec_ok _).mpr
    change core.result.Result.Err topology.Error.InvalidTransition =
      (core.result.Result.Ok () : core.result.Result Unit topology.Error) ↔
      MutationSeparate n next edge.u.val edge.v.val
    rw [hseparate]
    simp [heq]
  simp only [heq, ite_false]
  have hpath (inside outside component : Usize) (hi : inside.val < n)
      (hcomponent : MutationVirtualRootWitness next n inside.val component.val) :
      (do
        let (work1, cell, count) ← spanning_tree.Tree.attach_virtual_loop0 t.parents w
          (alloc.vec.Vec.len t.parents) component inside 0#usize
        if cell ≥ alloc.vec.Vec.len t.parents then
          Result.ok (core.result.Result.Err topology.Error.InvalidTree, work1)
        else if count ≥ alloc.vec.Vec.len t.parents then
          Result.ok (core.result.Result.Err topology.Error.InvalidTree, work1)
        else
          let (_, back) ← alloc.vec.Vec.index_mut_usize work1.path count
          let count1 ← count + 1#usize
          let work2 ← spanning_tree.Tree.attach_virtual_loop1 {work1 with path := back cell}
            count1 1#usize
          let work3 ← spanning_tree.Workspace.set_parent work2 inside outside
          Result.ok (core.result.Result.Ok (), work3)) ⦃ out =>
        out.1 = core.result.Result.Ok () ↔
          MutationSeparate n next edge.u.val edge.v.val ⦄ := by
    obtain ⟨steps, _, hreach, _, _⟩ := hcomponent
    obtain ⟨k, hk, hreachk, hminimal, hdistinct⟩ :=
      mutation_functional_first_reach next n inside.val component.val hbounded hi ⟨steps, hreach⟩
    apply spec_mono (mutation_attach_path_total t.parents w inside outside component k
      hw hcapacity hwithin (fun j _ => hiter j inside.val hi) hreachk hminimal hdistinct hk)
    rintro out ⟨hok, _⟩
    exact ⟨fun _ => hseparate.mpr heq, fun _ => hok⟩
  by_cases hglobal : rootU = t.root
  · simp only [hglobal, ite_true, bind_ok, alloc.vec.Vec.index_mut_slice_index]
    exact hpath edge.v edge.u rootV hv hrootV
  · simp only [hglobal, ite_false, bind_ok, alloc.vec.Vec.index_mut_slice_index]
    exact hpath edge.u edge.v rootU hu hrootU

 theorem mutation_batch_attach_total (t : spanning_tree.Tree) (add : Slice topology.Edge)
    (w : spanning_tree.Workspace) (hw : WorkspaceValid w)
    (hcapacity : t.parents.val.length ≤ w.path.val.length)
    (hwithin : MutationOverlayWithin t.parents.val.length w)
    (hforest : MutationFunctionalForest t.parents.val.length
      (mutationVirtualParent w (alloc.vec.Vec.deref t.parents)))
    (hroot : t.root.val < t.parents.val.length)
    (hfixed : mutationVirtualParent w (alloc.vec.Vec.deref t.parents) t.root.val = t.root.val)
    (hacyclic : (mutationFunctionalGraph t.parents.val.length
      (mutationVirtualParent w (alloc.vec.Vec.deref t.parents))).IsAcyclic)
    (hindices : ∀ edge ∈ add.val,
      edge.u.val < t.parents.val.length ∧ edge.v.val < t.parents.val.length) :
    spanning_tree.Tree.edit_edges_loop2 t.parents t.root add w 0#usize
      (core.result.Result.Ok ()) ⦃ out =>
        WorkspaceValid out.1 ∧ out.1.path.val.length = w.path.val.length ∧
        MutationOverlayWithin t.parents.val.length out.1 ∧
        MutationFunctionalForest t.parents.val.length
          (mutationVirtualParent out.1 (alloc.vec.Vec.deref t.parents)) ∧
        mutationVirtualParent out.1 (alloc.vec.Vec.deref t.parents) t.root.val = t.root.val ∧
        (mutationFunctionalGraph t.parents.val.length
          (mutationVirtualParent out.1 (alloc.vec.Vec.deref t.parents))).IsAcyclic ∧
        (out.2 = core.result.Result.Ok () → ∀ u v,
          mutationFunctionalEdge t.parents.val.length
            (mutationVirtualParent out.1 (alloc.vec.Vec.deref t.parents)) u v ↔
          mutationFunctionalEdge t.parents.val.length
            (mutationVirtualParent w (alloc.vec.Vec.deref t.parents)) u v ∨
          mutationAddedBefore add add.val.length u v) ⦄ := by
  let exactEdges := fun (scratch : spanning_tree.Workspace) stop => ∀ u v,
    mutationFunctionalEdge t.parents.val.length
      (mutationVirtualParent scratch (alloc.vec.Vec.deref t.parents)) u v ↔
    mutationFunctionalEdge t.parents.val.length
      (mutationVirtualParent w (alloc.vec.Vec.deref t.parents)) u v ∨
    mutationAddedBefore add stop u v
  unfold spanning_tree.Tree.edit_edges_loop2
  apply loop.spec_decr_nat
    (fun state : spanning_tree.Workspace × Usize × core.result.Result Unit topology.Error =>
      add.val.length - state.2.1.val)
    (fun state : spanning_tree.Workspace × Usize × core.result.Result Unit topology.Error =>
      WorkspaceValid state.1 ∧ state.1.path.val.length = w.path.val.length ∧
      MutationOverlayWithin t.parents.val.length state.1 ∧
      MutationFunctionalForest t.parents.val.length
        (mutationVirtualParent state.1 (alloc.vec.Vec.deref t.parents)) ∧
      mutationVirtualParent state.1 (alloc.vec.Vec.deref t.parents) t.root.val = t.root.val ∧
      (mutationFunctionalGraph t.parents.val.length
        (mutationVirtualParent state.1 (alloc.vec.Vec.deref t.parents))).IsAcyclic ∧
      state.2.1.val ≤ add.val.length ∧
      (state.2.2 = core.result.Result.Ok () → exactEdges state.1 state.2.1.val))
    _
  · rintro ⟨scratch, i, status⟩ ⟨hvalid, hlength, hins, htree, hrootFixed, hgraph, hi, hexact⟩
    dsimp only at hvalid hlength hins htree hrootFixed hgraph hi hexact ⊢
    unfold spanning_tree.Tree.edit_edges_loop2.body
    by_cases hlt : i < Slice.len add
    · have hltNat : i.val < add.val.length := hlt
      simp only [hlt, ite_true]
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false]
        apply (spec_ok _).mpr
        exact ⟨hvalid, hlength, hins, htree, hrootFixed, hgraph, by simp⟩
      | Ok payload =>
        cases payload
        simp only [core.result.Result.is_ok, bind_ok, ite_true]
        apply spec_bind (Slice.index_usize_spec add i hltNat)
        intro edge hedge
        have hedgeGet : add.val[i.val]? = some edge := by
          rw [List.getElem?_eq_getElem hltNat, ← hedge]
        obtain ⟨hu, hv⟩ := hindices edge (List.mem_of_getElem? hedgeGet)
        apply spec_bind (spec_and
          (mutation_attach_virtual_preserves t edge scratch hvalid
            (by rw [hlength]; exact hcapacity) hins hu hv htree hroot hrootFixed)
          (mutation_attach_virtual_acceptance t edge scratch hvalid
            (by rw [hlength]; exact hcapacity) hins hu hv htree))
        rintro ⟨nextStatus, nextWork⟩
          ⟨⟨hnextValid, hnextLen, hnextWithin, hnextForest,
            hnextFixed, herrorFrame, hnewEdges⟩, hacceptance⟩
        dsimp only at hnextValid hnextLen hnextWithin hnextForest hnextFixed herrorFrame hnewEdges hacceptance
        have hnextGraph : (mutationFunctionalGraph t.parents.val.length
            (mutationVirtualParent nextWork (alloc.vec.Vec.deref t.parents))).IsAcyclic := by
          cases nextStatus with
          | Err error =>
            have hframe : nextWork = scratch := herrorFrame error rfl
            rw [hframe]
            exact hgraph
          | Ok payload =>
            cases payload
            obtain ⟨a, b, ha, hb, hne⟩ := hacceptance.mp rfl
            exact mutation_functional_attach_acyclic t.parents.val.length
              (mutationVirtualParent scratch (alloc.vec.Vec.deref t.parents))
              (mutationVirtualParent nextWork (alloc.vec.Vec.deref t.parents))
              ⟨edge.u.val, hu⟩ ⟨edge.v.val, hv⟩ a b ha hb hne hgraph (hnewEdges rfl)
        change (do
          let next ← i + 1#usize
          Result.ok (ControlFlow.cont (nextWork, next, nextStatus))) ⦃ _ ⦄
        apply spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
        intro next hnext
        have hn : next.val = i.val + 1 := by simpa using hnext
        apply (spec_ok _).mpr
        refine ⟨⟨hnextValid, hnextLen.trans hlength, hnextWithin, hnextForest,
          hnextFixed, hnextGraph, (by change next.val ≤ add.val.length; omega), ?_⟩,
          (by change add.val.length - next.val < add.val.length - i.val; omega)⟩
        intro hok u v
        have hsplit : mutationAddedBefore add next.val u v ↔
            mutationAddedBefore add i.val u v ∨
            (u = edge.u.val ∧ v = edge.v.val) ∨ (v = edge.u.val ∧ u = edge.v.val) := by
          constructor
          · rintro ⟨j, hj, earlier, hearlier, he⟩
            by_cases hji : j = i.val
            · have heq : earlier = edge := by
                rw [hji, hedgeGet] at hearlier
                exact (Option.some.inj hearlier).symm
              exact Or.inr (by simpa only [heq] using he)
            · exact Or.inl ⟨j, by omega, earlier, hearlier, he⟩
          · rintro (hold | hnew)
            · obtain ⟨j, hj, earlier, hearlier, he⟩ := hold
              exact ⟨j, by omega, earlier, hearlier, he⟩
            · exact ⟨i.val, by omega, edge, hedgeGet, hnew⟩
        change _ ↔ _ ∨ mutationAddedBefore add next.val u v
        rw [hnewEdges hok u v, hexact rfl u v, hsplit]
        tauto
    · have he : i.val = add.val.length := by
        have hnot : ¬ i.val < add.val.length := hlt
        omega
      simp only [hlt, ite_false]
      apply (spec_ok _).mpr
      refine ⟨hvalid, hlength, hins, htree, hrootFixed, hgraph, ?_⟩
      intro hok
      simpa only [exactEdges, he] using hexact hok
  · refine ⟨hw, rfl, hwithin, hforest, hfixed, hacyclic, by simp, ?_⟩
    intro _ u v
    simp [mutationAddedBefore]

end Labyrinth
