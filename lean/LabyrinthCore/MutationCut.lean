module
public import LabyrinthCore.MutationWorkspaceBounds
public import LabyrinthCore.MutationForest

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

 theorem mutation_functional_forest_congr (n : Nat) (before after : Nat → Nat)
    (hf : MutationFunctionalForest n before)
    (heq : ∀ u, u < n → after u = before u) : MutationFunctionalForest n after := by
  have hb := mutation_functional_forest_bounds n before hf
  have hiter : ∀ k u, u < n → after^[k] u = before^[k] u ∧ before^[k] u < n := by
    intro k
    induction k with
    | zero => exact fun _ hu => ⟨rfl, hu⟩
    | succ k ih =>
      intro u hu
      obtain ⟨he, hbound⟩ := ih u hu
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', he, heq _ hbound]
      exact ⟨rfl, hb _ hbound⟩
  intro start hstart
  obtain ⟨root, k, hk, hreach, hfixed, hbound⟩ := hf start hstart
  have hr : root < n := by simpa only [hreach] using (hiter k start hstart).2
  exact ⟨root, k, hk, (hiter k start hstart).1.trans hreach,
    (heq root hr).trans hfixed,
    fun j hj => by rw [(hiter j start hstart).1]; exact hbound j hj⟩

 def mutationCutChild (v : alloc.vec.Vec Usize) (edge : topology.Edge) : Nat :=
  if parentAt (v.val.map (·.val)) edge.u.val = edge.v.val then edge.u.val else edge.v.val

 theorem mutation_cut_loop_total
    (v : alloc.vec.Vec Usize) (remove : Slice topology.Edge) (w : spanning_tree.Workspace)
    (hw : WorkspaceValid w) (hcapacity : v.val.length ≤ w.path.val.length)
    (hwithin : MutationOverlayWithin v.val.length w)
    (hforest : MutationFunctionalForest v.val.length
      (mutationVirtualParent w (alloc.vec.Vec.deref v)))
    (hindices : ∀ edge ∈ remove.val, edge.u.val < v.val.length ∧ edge.v.val < v.val.length) :
    spanning_tree.Tree.edit_edges_loop1 v remove w 0#usize ⦃ out =>
      WorkspaceValid out ∧ out.path = w.path ∧ MutationOverlayWithin v.val.length out ∧
      MutationFunctionalForest v.val.length (mutationVirtualParent out (alloc.vec.Vec.deref v)) ∧
      ∀ u, u < v.val.length → mutationVirtualParent out (alloc.vec.Vec.deref v) u =
        if ∃ edge ∈ remove.val, mutationCutChild v edge = u then u
        else mutationVirtualParent w (alloc.vec.Vec.deref v) u ⦄ := by
  classical
  let touched := fun stop u => ∃ j, j < stop ∧ ∃ edge,
    remove.val[j]? = some edge ∧ mutationCutChild v edge = u
  let exactParents := fun (scratch : spanning_tree.Workspace) stop =>
    ∀ u, u < v.val.length → mutationVirtualParent scratch (alloc.vec.Vec.deref v) u =
      if touched stop u then u else mutationVirtualParent w (alloc.vec.Vec.deref v) u
  unfold spanning_tree.Tree.edit_edges_loop1
  apply loop.spec_decr_nat
    (fun state : spanning_tree.Workspace × Usize => remove.val.length - state.2.val)
    (fun state : spanning_tree.Workspace × Usize =>
      WorkspaceValid state.1 ∧ state.1.path = w.path ∧
      MutationOverlayWithin v.val.length state.1 ∧
      MutationFunctionalForest v.val.length (mutationVirtualParent state.1 (alloc.vec.Vec.deref v)) ∧
      state.2.val ≤ remove.val.length ∧ exactParents state.1 state.2.val)
    _
  · rintro ⟨scratch, i⟩ ⟨hvalid, hpath, hins, htree, hi, hexact⟩
    dsimp only at hvalid hpath hins htree hi hexact ⊢
    unfold spanning_tree.Tree.edit_edges_loop1.body
    by_cases hlt : i < Slice.len remove
    · have hltNat : i.val < remove.val.length := hlt
      simp only [hlt, ite_true]
      apply spec_bind (Slice.index_usize_spec remove i hltNat)
      intro edge hedge
      have hedgeGet : remove.val[i.val]? = some edge := by
        rw [List.getElem?_eq_getElem hltNat]
        exact congrArg some hedge.symm
      have hedgeMem : edge ∈ remove.val := List.mem_of_getElem? hedgeGet
      obtain ⟨hu, hv⟩ := hindices edge hedgeMem
      simp only [alloc.vec.Vec.index_slice_index]
      apply spec_bind (alloc.vec.Vec.index_usize_spec v edge.u hu)
      intro parent hparent
      have hp : parent.val = parentAt (v.val.map (·.val)) edge.u.val := by
        rw [hparent]
        exact (mutation_parent_get v edge.u hu).symm
      have hchoose : (if parent = edge.v then Result.ok edge.u else Result.ok edge.v) ⦃ child =>
          child.val = mutationCutChild v edge ∧ child.val < v.val.length ⦄ := by
        by_cases he : parent = edge.v
        · have hev : parent.val = edge.v.val := congrArg UScalar.val he
          simp [he, mutationCutChild, ← hp, hev, hu]
        · have hne : parent.val ≠ edge.v.val := fun h => he (UScalar.eq_of_val_eq h)
          simp [he, mutationCutChild, ← hp, hne, hv]
      apply spec_bind hchoose
      rintro child ⟨hchild, hchildBound⟩
      apply spec_bind (spec_and
        (mutation_workspace_set_parent_exact scratch child child (alloc.vec.Vec.deref v) hvalid
          (by rw [hpath]; omega))
        (mutation_set_parent_within v.val.length scratch child child hvalid hchildBound
          (by simpa only [hpath] using hcapacity) hins))
      rintro nextWork ⟨⟨hnextValid, hnextPath, _, _, _, _, hupdate⟩, ⟨_, _, hnextWithin⟩⟩
      apply spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      intro next hnext
      have hnextVal : next.val = i.val + 1 := by simpa using hnext
      have hforestNext : MutationFunctionalForest v.val.length
          (mutationVirtualParent nextWork (alloc.vec.Vec.deref v)) := by
        apply mutation_functional_forest_congr v.val.length
          (fun u => if u = child.val then child.val else mutationVirtualParent scratch (alloc.vec.Vec.deref v) u)
        · exact mutation_functional_cut_preserves _ _ _ htree
        · intro u hu
          exact hupdate u (by rw [hpath]; omega)
      simp only [spec_ok]
      refine ⟨⟨hnextValid, hnextPath.trans hpath, hnextWithin, hforestNext, by omega, ?_⟩, by omega⟩
      intro u hu
      have hsplit : touched next.val u ↔ u = child.val ∨ touched i.val u := by
        constructor
        · rintro ⟨j, hj, earlier, hearlier, hwhich⟩
          by_cases he : j = i.val
          · have heq : earlier = edge := by
              rw [he, hedgeGet] at hearlier
              exact (Option.some.inj hearlier).symm
            exact Or.inl (by simpa only [heq, ← hchild] using hwhich.symm)
          · exact Or.inr ⟨j, by omega, earlier, hearlier, hwhich⟩
        · rintro (he | hprior)
          · exact ⟨i.val, by omega, edge, hedgeGet, hchild.symm.trans he.symm⟩
          · obtain ⟨j, hj, earlier, hearlier, hwhich⟩ := hprior
            exact ⟨j, by omega, earlier, hearlier, hwhich⟩
      rw [hupdate u (by rw [hpath]; omega), hexact u hu]
      simp only [hsplit]
      by_cases he : u = child.val <;> simp [he]
    · have heq : i.val = remove.val.length := by
        have hge : remove.val.length ≤ i.val := Nat.le_of_not_lt hlt
        omega
      simp only [hlt, ite_false, spec_ok]
      refine ⟨hvalid, hpath, hins, htree, ?_⟩
      intro u hu
      have htouched : touched i.val u ↔ ∃ edge ∈ remove.val, mutationCutChild v edge = u := by
        constructor
        · rintro ⟨j, _, edge, hedge, hwhich⟩
          exact ⟨edge, List.mem_of_getElem? hedge, hwhich⟩
        · rintro ⟨edge, hedge, hwhich⟩
          obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hedge
          exact ⟨j, by omega, edge, by simp [hj, hget], hwhich⟩
      simpa only [exactParents, htouched] using hexact u hu
  · refine ⟨hw, rfl, hwithin, hforest, by simp, ?_⟩
    intro u hu
    simp [touched]

 theorem mutation_parent_iterate_follow (p : List Nat) (k u : Nat) :
    (parentAt p)^[k] u = follow p k u := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih => simpa only [Function.iterate_succ_apply, follow] using ih (parentAt p u)

 theorem mutation_rooted_functional_forest (p : List Nat) (root : Nat)
    (ht : RootedTree p root) : MutationFunctionalForest p.length (parentAt p) := by
  apply mutation_functional_forest_of_reaches (parentAt p) p.length
  · exact mutation_parentAt_bound p ht.2.2.1
  · intro u hu
    exact ⟨root, p.length, (mutation_parent_iterate_follow p p.length u).trans (ht.2.2.2 u hu),
      mutation_rooted_fixed p root ht⟩

 theorem mutation_clear_edits_prepares
    (c : topology.Carrier) (t : spanning_tree.Tree) (w : spanning_tree.Workspace)
    (ht : TreeValid c t) (hw : WorkspaceValid w) :
    spanning_tree.Workspace.clear_edits w ⦃ out =>
      WorkspaceValid out ∧ out.path = w.path ∧ MutationOverlayWithin t.parents.val.length out ∧
      MutationFunctionalForest t.parents.val.length
        (mutationVirtualParent out (alloc.vec.Vec.deref t.parents)) ∧
      mutationVirtualParent out (alloc.vec.Vec.deref t.parents) t.root.val = t.root.val ∧
      ∀ u, u < t.parents.val.length →
        mutationVirtualParent out (alloc.vec.Vec.deref t.parents) u = parentAt (parents t) u ⦄ := by
  apply spec_mono (mutation_clear_edits_within t.parents.val.length w hw)
  rintro out ⟨hvalid, hpath, hwithin, hparent⟩
  have heq : ∀ u, u < t.parents.val.length →
      mutationVirtualParent out (alloc.vec.Vec.deref t.parents) u = parentAt (parents t) u := by
    intro u hu
    rw [hparent]
    simp [parentAt, parents, hu]
  have hforest : MutationFunctionalForest t.parents.val.length
      (mutationVirtualParent out (alloc.vec.Vec.deref t.parents)) := by
    apply mutation_functional_forest_congr t.parents.val.length (parentAt (parents t))
    · simpa only [parents, List.length_map] using mutation_rooted_functional_forest
        (parents t) t.root.val ht.2.1
    · exact heq
  have hrbound : t.root.val < t.parents.val.length := by
    simpa only [parents, List.length_map] using ht.2.1.1
  exact ⟨hvalid, hpath, hwithin, hforest,
    (heq t.root.val hrbound).trans (mutation_rooted_fixed (parents t) t.root.val ht.2.1), heq⟩

 theorem mutation_cut_child_nonroot (v : alloc.vec.Vec Usize) (root : Usize)
    (edge : topology.Edge) (ht : RootedTree (v.val.map (·.val)) root.val)
    (hedge : parentEdge (v.val.map (·.val)) edge.u.val edge.v.val) :
    mutationCutChild v edge ≠ root.val := by
  have hfixed := mutation_rooted_fixed (v.val.map (·.val)) root.val ht
  obtain ⟨hu, hv, hne, hp⟩ := hedge
  unfold mutationCutChild
  split
  · rename_i hparent
    intro he
    rw [he, hfixed] at hparent
    exact hne (he.trans hparent)
  · rename_i hparent
    intro he
    rcases hp with hp | hp
    · exact hparent (by simp [parentAt, hp])
    · have hvp : parentAt (v.val.map (·.val)) edge.v.val = edge.u.val := by simp [parentAt, hp]
      rw [he, hfixed] at hvp
      exact hne (hvp.symm.trans he.symm)

 theorem mutation_cut_loop_preserves_root
    (t : spanning_tree.Tree) (remove : Slice topology.Edge) (w : spanning_tree.Workspace)
    (hw : WorkspaceValid w) (hcapacity : t.parents.val.length ≤ w.path.val.length)
    (hwithin : MutationOverlayWithin t.parents.val.length w)
    (hforest : MutationFunctionalForest t.parents.val.length
      (mutationVirtualParent w (alloc.vec.Vec.deref t.parents)))
    (ht : RootedTree (parents t) t.root.val)
    (hremove : ∀ edge ∈ remove.val, parentEdge (parents t) edge.u.val edge.v.val)
    (hroot : mutationVirtualParent w (alloc.vec.Vec.deref t.parents) t.root.val = t.root.val) :
    spanning_tree.Tree.edit_edges_loop1 t.parents remove w 0#usize ⦃ out =>
      WorkspaceValid out ∧ out.path = w.path ∧ MutationOverlayWithin t.parents.val.length out ∧
      MutationFunctionalForest t.parents.val.length
        (mutationVirtualParent out (alloc.vec.Vec.deref t.parents)) ∧
      mutationVirtualParent out (alloc.vec.Vec.deref t.parents) t.root.val = t.root.val ∧
      ∀ u, u < t.parents.val.length → mutationVirtualParent out (alloc.vec.Vec.deref t.parents) u =
        if ∃ edge ∈ remove.val, mutationCutChild t.parents edge = u then u
        else mutationVirtualParent w (alloc.vec.Vec.deref t.parents) u ⦄ := by
  apply spec_mono (mutation_cut_loop_total t.parents remove w hw hcapacity hwithin hforest (by
    intro edge hedge
    obtain ⟨hu, hv, _⟩ := hremove edge hedge
    exact ⟨by simpa only [parents, List.length_map] using hu,
      by simpa only [parents, List.length_map] using hv⟩))
  rintro out ⟨hvalid, hpath, hins, htree, hexact⟩
  refine ⟨hvalid, hpath, hins, htree, ?_, hexact⟩
  have hr : t.root.val < t.parents.val.length := by simpa only [parents, List.length_map] using ht.1
  have hnot : ¬ ∃ edge ∈ remove.val, mutationCutChild t.parents edge = t.root.val := by
    rintro ⟨edge, hedge, hchild⟩
    exact mutation_cut_child_nonroot t.parents t.root edge ht (hremove edge hedge) hchild
  simpa only [hnot, ite_false, hroot] using hexact t.root.val hr

 theorem mutation_rooted_no_two_cycle (p : List Nat) (root u v : Nat)
    (ht : RootedTree p root) (hu : u < p.length) (hne : u ≠ v)
    (huv : parentAt p u = v) : parentAt p v ≠ u := by
  intro hvu
  have hstay : ∀ k x, x = u ∨ x = v → follow p k x = u ∨ follow p k x = v := by
    intro k
    induction k with
    | zero => exact fun _ h => h
    | succ k ih =>
      intro x hx
      rcases hx with rfl | rfl
      · simpa only [follow, huv] using ih v (Or.inr rfl)
      · simpa only [follow, hvu] using ih u (Or.inl rfl)
  have hroot := ht.2.2.2 u hu
  have hfixed := mutation_rooted_fixed p root ht
  rcases hstay p.length u (Or.inl rfl) with he | he
  · have hr : root = u := hroot.symm.trans he
    rw [hr, huv] at hfixed
    exact hne hfixed.symm
  · have hr : root = v := hroot.symm.trans he
    rw [hr, hvu] at hfixed
    exact hne hfixed

 theorem mutation_cut_child_represents (v : alloc.vec.Vec Usize) (edge : topology.Edge)
    (he : parentEdge (v.val.map (·.val)) edge.u.val edge.v.val) :
    (mutationCutChild v edge = edge.u.val ∧
      parentAt (v.val.map (·.val)) (mutationCutChild v edge) = edge.v.val) ∨
    (mutationCutChild v edge = edge.v.val ∧
      parentAt (v.val.map (·.val)) (mutationCutChild v edge) = edge.u.val) := by
  unfold mutationCutChild
  split
  · rename_i h
    exact Or.inl ⟨rfl, h⟩
  · rename_i h
    right
    refine ⟨rfl, ?_⟩
    rcases he.2.2.2 with hp | hp
    · exact (h (by simp [parentAt, hp])).elim
    · simp [parentAt, hp]

 def mutationRemoval (remove : Slice topology.Edge) (u v : Nat) : Prop :=
  ∃ edge ∈ remove.val,
    (edge.u.val = u ∧ edge.v.val = v) ∨ (edge.v.val = u ∧ edge.u.val = v)

 theorem mutation_removal_symmetric (remove : Slice topology.Edge) (u v : Nat) :
    mutationRemoval remove u v ↔ mutationRemoval remove v u := by
  constructor
  · rintro ⟨edge, hedge, ⟨hu, hv⟩ | ⟨hu, hv⟩⟩
    · exact ⟨edge, hedge, Or.inr ⟨hv, hu⟩⟩
    · exact ⟨edge, hedge, Or.inl ⟨hv, hu⟩⟩
  · rintro ⟨edge, hedge, ⟨hv, hu⟩ | ⟨hv, hu⟩⟩
    · exact ⟨edge, hedge, Or.inr ⟨hu, hv⟩⟩
    · exact ⟨edge, hedge, Or.inl ⟨hu, hv⟩⟩

 theorem mutation_cut_child_membership (published : alloc.vec.Vec Usize)
    (root u v : Nat) (remove : Slice topology.Edge)
    (ht : RootedTree (published.val.map (·.val)) root)
    (hremove : ∀ edge ∈ remove.val, parentEdge (published.val.map (·.val)) edge.u.val edge.v.val)
    (hu : u < published.val.length) (hne : u ≠ v)
    (hparent : parentAt (published.val.map (·.val)) u = v) :
    (∃ edge ∈ remove.val, mutationCutChild published edge = u) ↔ mutationRemoval remove u v := by
  constructor
  · rintro ⟨edge, hedge, hchild⟩
    rcases mutation_cut_child_represents published edge (hremove edge hedge) with hrep | hrep
    · exact ⟨edge, hedge, Or.inl ⟨hrep.1.symm.trans hchild,
        hrep.2.symm.trans ((congrArg (parentAt (published.val.map (·.val))) hchild).trans hparent)⟩⟩
    · exact ⟨edge, hedge, Or.inr ⟨hrep.1.symm.trans hchild,
        hrep.2.symm.trans ((congrArg (parentAt (published.val.map (·.val))) hchild).trans hparent)⟩⟩
  · rintro ⟨edge, hedge, hends | hends⟩
    · exact ⟨edge, hedge, by simp [mutationCutChild, hends.1, hends.2, hparent]⟩
    · have hreverse := mutation_rooted_no_two_cycle (published.val.map (·.val)) root u v ht
        (by simpa only [List.length_map] using hu) hne hparent
      exact ⟨edge, hedge, by simp [mutationCutChild, hends.1, hends.2, hreverse]⟩

 theorem mutation_cut_edges_exact (published : alloc.vec.Vec Usize) (after : List Nat)
    (root : Nat) (remove : Slice topology.Edge)
    (ht : RootedTree (published.val.map (·.val)) root)
    (hremove : ∀ edge ∈ remove.val, parentEdge (published.val.map (·.val)) edge.u.val edge.v.val)
    (hlen : after.length = published.val.length)
    (hparents : ∀ u, u < published.val.length → parentAt after u =
      if ∃ edge ∈ remove.val, mutationCutChild published edge = u then u
      else parentAt (published.val.map (·.val)) u) :
    ∀ u v, parentEdge after u v ↔
      parentEdge (published.val.map (·.val)) u v ∧ ¬ mutationRemoval remove u v := by
  classical
  have hdir : ∀ u v, u < published.val.length → u ≠ v →
      (parentAt after u = v ↔
        parentAt (published.val.map (·.val)) u = v ∧ ¬ mutationRemoval remove u v) := by
    intro u v hu hne
    rw [hparents u hu]
    by_cases htouched : ∃ edge ∈ remove.val, mutationCutChild published edge = u
    · simp only [htouched, ite_true]
      constructor
      · intro he
        exact (hne he).elim
      · rintro ⟨hparent, hnot⟩
        exact (hnot ((mutation_cut_child_membership published root u v remove ht hremove hu hne hparent).mp htouched)).elim
    · simp only [htouched, ite_false]
      constructor
      · intro hparent
        refine ⟨hparent, ?_⟩
        intro hremoved
        exact htouched ((mutation_cut_child_membership published root u v remove ht hremove hu hne hparent).mpr hremoved)
      · exact And.left
  intro u v
  by_cases hu : u < published.val.length
  · by_cases hv : v < published.val.length
    · by_cases hne : u ≠ v
      · have huAfter : u < after.length := by omega
        have hvAfter : v < after.length := by omega
        have huBefore : u < (published.val.map (·.val)).length := by simpa using hu
        have hvBefore : v < (published.val.map (·.val)).length := by simpa using hv
        have ha : parentEdge after u v ↔ parentAt after u = v ∨ parentAt after v = u := by
          simp [parentEdge, parentAt, huAfter, hvAfter, hne]
        have hb : parentEdge (published.val.map (·.val)) u v ↔
            parentAt (published.val.map (·.val)) u = v ∨ parentAt (published.val.map (·.val)) v = u := by
          simp [parentEdge, parentAt, huBefore, hvBefore, hne]
        rw [ha, hb, hdir u v hu hne, hdir v u hv hne.symm,
          ← mutation_removal_symmetric remove u v]
        tauto
      · have heq : u = v := Classical.not_not.mp hne
        simp [heq, parentEdge]
    · simp [parentEdge, hlen, hv]
  · simp [parentEdge, hlen, hu]

end Labyrinth
