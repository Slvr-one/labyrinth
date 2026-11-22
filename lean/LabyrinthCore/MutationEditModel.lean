module
public import LabyrinthCore.MutationBatchAttach
public import LabyrinthCore.MutationCommit
public import LabyrinthCore.MutationCut
public import LabyrinthCore.MutationRerootSpec
public import LabyrinthCore.MutationEditPreflight
public import Mathlib.Data.Finset.Card

@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

def mutationAddition (add : Slice topology.Edge) (u v : Nat) : Prop :=
  ∃ edge ∈ add.val,
    (edge.u.val = u ∧ edge.v.val = v) ∨ (edge.v.val = u ∧ edge.u.val = v)

def MutationEditedEdge (before : List Nat) (remove add : Slice topology.Edge)
    (u v : Nat) : Prop :=
  (parentEdge before u v ∧ ¬ mutationRemoval remove u v) ∨ mutationAddition add u v

theorem mutation_added_before_full (add : Slice topology.Edge) (u v : Nat) :
    mutationAddedBefore add add.val.length u v ↔ mutationAddition add u v := by
  constructor
  · rintro ⟨j, _, edge, hedge, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩
    · exact ⟨edge, List.mem_of_getElem? hedge, Or.inl ⟨hu.symm, hv.symm⟩⟩
    · exact ⟨edge, List.mem_of_getElem? hedge, Or.inr ⟨hu.symm, hv.symm⟩⟩
  · rintro ⟨edge, hedge, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩
    · obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hedge
      exact ⟨j, hj, edge, by simp [hj, hget], Or.inl ⟨hu.symm, hv.symm⟩⟩
    · obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hedge
      exact ⟨j, hj, edge, by simp [hj, hget], Or.inr ⟨hu.symm, hv.symm⟩⟩
/-- A concrete parent vector whose parent function is `next` has exactly the
functional undirected edge relation. -/
theorem mutation_parent_edge_functional_exact (p : List Nat) (n : Nat)
    (next : Nat → Nat) (hlen : p.length = n)
    (hnext : ∀ u, u < n → parentAt p u = next u) :
    ∀ u v, parentEdge p u v ↔ mutationFunctionalEdge n next u v := by
  intro u v
  by_cases hu : u < n
  · by_cases hv : v < n
    · by_cases hne : u ≠ v
      · have hup : u < p.length := by omega
        have hvp : v < p.length := by omega
        have hedge : parentEdge p u v ↔ parentAt p u = v ∨ parentAt p v = u := by
          simp [parentEdge, parentAt, hup, hvp, hne]
        rw [hedge, hnext u hu, hnext v hv]
        simp only [mutationFunctionalEdge, hu, hv, true_and]
        exact ⟨fun h => ⟨hne, h⟩, And.right⟩
      · have he : u = v := Classical.not_not.mp hne
        simp [he, parentEdge, mutationFunctionalEdge]
    · have hvp : ¬ v < p.length := by omega
      simp [parentEdge, mutationFunctionalEdge, hv, hvp]
  · have hup : ¬ u < p.length := by omega
    simp [parentEdge, mutationFunctionalEdge, hu, hup]

/-- Cutting the requested parent edges in the sparse overlay removes exactly
those undirected edges and no others. -/
theorem mutation_cut_functional_edges_exact
    (published : alloc.vec.Vec Usize) (after : Nat → Nat) (root : Nat)
    (remove : Slice topology.Edge)
    (ht : RootedTree (published.val.map (·.val)) root)
    (hremove : ∀ edge ∈ remove.val,
      parentEdge (published.val.map (·.val)) edge.u.val edge.v.val)
    (hparents : ∀ u, u < published.val.length → after u =
      if ∃ edge ∈ remove.val, mutationCutChild published edge = u then u
      else parentAt (published.val.map (·.val)) u) :
    ∀ u v, mutationFunctionalEdge published.val.length after u v ↔
      parentEdge (published.val.map (·.val)) u v ∧ ¬ mutationRemoval remove u v := by
  classical
  have hdir : ∀ u v, u < published.val.length → u ≠ v →
      (after u = v ↔ parentAt (published.val.map (·.val)) u = v ∧
        ¬ mutationRemoval remove u v) := by
    intro u v hu hne
    rw [hparents u hu]
    by_cases htouched : ∃ edge ∈ remove.val, mutationCutChild published edge = u
    · simp only [htouched, ite_true]
      constructor
      · intro he
        exact (hne he).elim
      · rintro ⟨hparent, hnot⟩
        exact (hnot ((mutation_cut_child_membership published root u v remove ht hremove
          hu hne hparent).mp htouched)).elim
    · simp only [htouched, ite_false]
      constructor
      · intro hparent
        refine ⟨hparent, ?_⟩
        intro hremoved
        exact htouched ((mutation_cut_child_membership published root u v remove ht hremove
          hu hne hparent).mpr hremoved)
      · exact And.left
  intro u v
  by_cases hu : u < published.val.length
  · by_cases hv : v < published.val.length
    · by_cases hne : u ≠ v
      · rw [show mutationFunctionalEdge published.val.length after u v ↔
              after u = v ∨ after v = u by simp [mutationFunctionalEdge, hu, hv, hne],
            show parentEdge (published.val.map (·.val)) u v ↔
              parentAt (published.val.map (·.val)) u = v ∨
                parentAt (published.val.map (·.val)) v = u by
              simp [parentEdge, parentAt, hu, hv, hne],
            hdir u v hu hne, hdir v u hv hne.symm,
            ← mutation_removal_symmetric remove u v]
        tauto
      · have he : u = v := Classical.not_not.mp hne
        simp [he, mutationFunctionalEdge, parentEdge]
    · simp [mutationFunctionalEdge, parentEdge, hv]
  · simp [mutationFunctionalEdge, parentEdge, hu]

/-- Committing the sparse overlay publishes exactly its functional undirected edges. -/
theorem mutation_committed_parent_edges_exact
    (published result : alloc.vec.Vec Usize) (work : spanning_tree.Workspace)
    (hlen : result.val.length = published.val.length)
    (hparents : ∀ u, u < published.val.length →
      (result.val[u]?.getD 0#usize).val =
        mutationVirtualParent work (alloc.vec.Vec.deref published) u) :
    ∀ u v, parentEdge (result.val.map (·.val)) u v ↔
      mutationFunctionalEdge published.val.length
        (mutationVirtualParent work (alloc.vec.Vec.deref published)) u v := by
  apply mutation_parent_edge_functional_exact
  · simpa only [List.length_map] using hlen
  · intro u hu
    have hresult : u < result.val.length := by omega
    simpa [parentAt, hresult] using hparents u (by omega)

/-- The committed parent vector refines the complete remove/add edge model. -/
theorem mutation_committed_edit_edges_exact
    (published result : alloc.vec.Vec Usize) (cut attached : spanning_tree.Workspace)
    (remove add : Slice topology.Edge)
    (hlen : result.val.length = published.val.length)
    (hparents : ∀ u, u < published.val.length →
      (result.val[u]?.getD 0#usize).val =
        mutationVirtualParent attached (alloc.vec.Vec.deref published) u)
    (hcut : ∀ u v,
      mutationFunctionalEdge published.val.length
          (mutationVirtualParent cut (alloc.vec.Vec.deref published)) u v ↔
        parentEdge (published.val.map (·.val)) u v ∧ ¬ mutationRemoval remove u v)
    (hattached : ∀ u v,
      mutationFunctionalEdge published.val.length
          (mutationVirtualParent attached (alloc.vec.Vec.deref published)) u v ↔
        mutationFunctionalEdge published.val.length
          (mutationVirtualParent cut (alloc.vec.Vec.deref published)) u v ∨
        mutationAddedBefore add add.val.length u v) :
    ∀ u v, parentEdge (result.val.map (·.val)) u v ↔
      MutationEditedEdge (published.val.map (·.val)) remove add u v := by
  intro u v
  rw [mutation_committed_parent_edges_exact published result attached hlen hparents u v,
    hattached u v, hcut u v, mutation_added_before_full]
  rfl

/-- Every edge admitted by the batch refinement remains an edge of the carrier. -/
theorem mutation_edited_edge_carrier
    (c : topology.Carrier) (t : spanning_tree.Tree) (remove add : Slice topology.Edge)
    (hc : CarrierValid c) (ht : TreeValid c t)
    (hadd : ∀ edge ∈ add.val, carrierEdge c edge.u.val edge.v.val)
    (u v : Nat) (hedge : MutationEditedEdge (parents t) remove add u v) :
    carrierEdge c u v := by
  rcases hedge with ⟨hold, _⟩ | ⟨edge, hedge, huv | hvu⟩
  · exact mutation_tree_edge_carrier c t hc ht u v hold
  · simpa only [huv.1, huv.2] using hadd edge hedge
  · apply (mutation_carrier_symmetric c hc v u).mp
    simpa only [hvu.1, hvu.2] using hadd edge hedge


theorem mutation_addition_symmetric (add : Slice topology.Edge) (u v : Nat) :
    mutationAddition add u v ↔ mutationAddition add v u := by
  constructor
  · rintro ⟨edge, hedge, huv | hvu⟩
    · exact ⟨edge, hedge, Or.inr ⟨huv.2, huv.1⟩⟩
    · exact ⟨edge, hedge, Or.inl ⟨hvu.2, hvu.1⟩⟩
  · rintro ⟨edge, hedge, hvu | huv⟩
    · exact ⟨edge, hedge, Or.inr ⟨hvu.2, hvu.1⟩⟩
    · exact ⟨edge, hedge, Or.inl ⟨huv.2, huv.1⟩⟩

theorem mutation_canonical_swap (u v : Usize) :
    mutationCanonicalEdge { u := u, v := v } =
      mutationCanonicalEdge { u := v, v := u } := by
  unfold mutationCanonicalEdge
  by_cases huv : u ≤ v
  · by_cases heq : u = v
    · subst v
      simp
    · have hvu : ¬ v ≤ u := fun h => heq (le_antisymm huv h)
      simp [huv, hvu]
  · have hvu : v ≤ u := le_of_not_ge huv
    simp [huv, hvu]

theorem mutation_canonical_eq_of_fin_edge_eq {n : Nat} (a b : topology.Edge)
    (hau : a.u.val < n) (hav : a.v.val < n)
    (hbu : b.u.val < n) (hbv : b.v.val < n)
    (h : s((⟨a.u.val, hau⟩ : Fin n), ⟨a.v.val, hav⟩) =
      s((⟨b.u.val, hbu⟩ : Fin n), ⟨b.v.val, hbv⟩)) :
    mutationCanonicalEdge a = mutationCanonicalEdge b := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have heu : a.u = b.u :=
      UScalar.eq_of_val_eq (congrArg (fun x : Fin n => x.val) hu)
    have hev : a.v = b.v :=
      UScalar.eq_of_val_eq (congrArg (fun x : Fin n => x.val) hv)
    cases a
    cases b
    simp_all
  · have heu : a.u = b.v :=
      UScalar.eq_of_val_eq (congrArg (fun x : Fin n => x.val) hu)
    have hev : a.v = b.u :=
      UScalar.eq_of_val_eq (congrArg (fun x : Fin n => x.val) hv)
    cases a
    cases b
    simp_all only
    exact mutation_canonical_swap _ _

/-- Successful edit preflight makes both undirected input edge lists duplicate-free.
The duplicate check is performed on canonical endpoints, so reversed duplicates are
excluded as well. -/
theorem mutation_edit_entries_canonical_nodup
    (c : topology.Carrier) (t : spanning_tree.Tree)
    (remove add : Slice topology.Edge)
    (hlength : remove.val.length = add.val.length)
    (hentries : ∀ j, j < remove.val.length → MutationEditEntryValid c t remove add j) :
    (remove.val.map mutationCanonicalEdge).Nodup ∧
      (add.val.map mutationCanonicalEdge).Nodup := by
  constructor
  · rw [List.nodup_iff_getElem?_ne_getElem?]
    intro i j hij hj heq
    have hjRemove : j < remove.val.length := by simpa using hj
    have hi : i < remove.val.length := lt_trans hij hjRemove
    obtain ⟨removal, addition, hr, ha, hvalid⟩ := hentries j hjRemove
    dsimp only at hvalid
    have hrj : removal = remove.val[j] := by
      rw [List.getElem?_eq_getElem hjRemove] at hr
      exact (Option.some.inj hr).symm
    have hiMap : i < (remove.val.map mutationCanonicalEdge).length := by simpa
    have heq' :
        mutationCanonicalEdge remove.val[i] = mutationCanonicalEdge remove.val[j] := by
      rw [List.getElem?_eq_getElem hiMap, List.getElem?_eq_getElem hj] at heq
      simpa only [List.getElem_map] using Option.some.inj heq
    have hcanonical :
        mutationCanonicalEdge remove.val[i] = mutationCanonicalEdge removal :=
      heq'.trans (congrArg mutationCanonicalEdge hrj.symm)
    exact hvalid.2.2.2.2.2.2.1 ⟨i, hij, Or.inl
      ⟨remove.val[i], by simp [hi], congrArg topology.Edge.u hcanonical,
        congrArg topology.Edge.v hcanonical⟩⟩
  · rw [List.nodup_iff_getElem?_ne_getElem?]
    intro i j hij hj heq
    have hjAdd : j < add.val.length := by simpa using hj
    have hi : i < add.val.length := lt_trans hij hjAdd
    have hjRemove : j < remove.val.length := by simpa [hlength] using hjAdd
    obtain ⟨removal, addition, hr, ha, hvalid⟩ := hentries j hjRemove
    dsimp only at hvalid
    have haj : addition = add.val[j] := by
      rw [List.getElem?_eq_getElem hjAdd] at ha
      exact (Option.some.inj ha).symm
    have hiMap : i < (add.val.map mutationCanonicalEdge).length := by simpa
    have heq' :
        mutationCanonicalEdge add.val[i] = mutationCanonicalEdge add.val[j] := by
      rw [List.getElem?_eq_getElem hiMap, List.getElem?_eq_getElem hj] at heq
      simpa only [List.getElem_map] using Option.some.inj heq
    have hcanonical :
        mutationCanonicalEdge add.val[i] = mutationCanonicalEdge addition :=
      heq'.trans (congrArg mutationCanonicalEdge haj.symm)
    exact hvalid.2.2.2.2.2.2.1 ⟨i, hij, Or.inr
      ⟨add.val[i], by simp [hi], congrArg topology.Edge.u hcanonical,
        congrArg topology.Edge.v hcanonical⟩⟩

noncomputable def mutationRemovalFinset (n : Nat) (remove : Slice topology.Edge) :
    Finset (Sym2 (Fin n)) :=
  (Sym2.fromRel (r := fun u v : Fin n => mutationRemoval remove u.val v.val)
    ⟨fun u v h => (mutation_removal_symmetric remove u.val v.val).mp h⟩).toFinite.toFinset

noncomputable def mutationAdditionFinset (n : Nat) (add : Slice topology.Edge) :
    Finset (Sym2 (Fin n)) :=
  (Sym2.fromRel (r := fun u v : Fin n => mutationAddition add u.val v.val)
    ⟨fun u v h => (mutation_addition_symmetric add u.val v.val).mp h⟩).toFinite.toFinset

@[simp] theorem mutation_removalFinset_mem (n : Nat) (remove : Slice topology.Edge)
    (u v : Fin n) :
    s(u, v) ∈ mutationRemovalFinset n remove ↔ mutationRemoval remove u.val v.val := by
  simp [mutationRemovalFinset]

@[simp] theorem mutation_additionFinset_mem (n : Nat) (add : Slice topology.Edge)
    (u v : Fin n) :
    s(u, v) ∈ mutationAdditionFinset n add ↔ mutationAddition add u.val v.val := by
  simp [mutationAdditionFinset]

theorem mutation_removalFinset_card (n : Nat) (remove : Slice topology.Edge)
    (hbounds : ∀ edge ∈ remove.val, edge.u.val < n ∧ edge.v.val < n)
    (hnodup : (remove.val.map mutationCanonicalEdge).Nodup) :
    (mutationRemovalFinset n remove).card = remove.val.length := by
  classical
  let indexed : Fin remove.val.length → Sym2 (Fin n) := fun i =>
    let bounds := hbounds remove.val[i] (List.getElem_mem i.isLt)
    s((⟨remove.val[i].u.val, bounds.1⟩ : Fin n),
      (⟨remove.val[i].v.val, bounds.2⟩ : Fin n))
  have hcard := Finset.card_bij
    (s := Finset.univ) (t := mutationRemovalFinset n remove)
    (fun i _ => indexed i)
    (fun i _ => by
      simp only [indexed, mutation_removalFinset_mem]
      exact ⟨remove.val[i], List.getElem_mem i.isLt, Or.inl ⟨rfl, rfl⟩⟩)
    (fun i _ j _ hij => by
      have hi := hbounds remove.val[i] (List.getElem_mem i.isLt)
      have hj := hbounds remove.val[j] (List.getElem_mem j.isLt)
      have hcanonical := mutation_canonical_eq_of_fin_edge_eq remove.val[i] remove.val[j]
        hi.1 hi.2 hj.1 hj.2 (by simpa only [indexed] using hij)
      have hiMap : i.val < (remove.val.map mutationCanonicalEdge).length := by simp
      have hjMap : j.val < (remove.val.map mutationCanonicalEdge).length := by simp
      apply Fin.ext
      exact (hnodup.getElem_inj_iff (hi := hiMap) (hj := hjMap)).mp
        (by simpa only [List.getElem_map, Fin.getElem_fin] using hcanonical))
    (fun edge hedge => by
      induction edge using Sym2.inductionOn with
      | _ u v =>
        obtain ⟨actual, hactual, hends | hends⟩ :=
          mutation_removalFinset_mem n remove u v |>.mp hedge
        · obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hactual
          refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
          rw [show indexed ⟨j, hj⟩ =
              s((⟨remove.val[j].u.val,
                  (hbounds remove.val[j] (List.getElem_mem hj)).1⟩ : Fin n),
                (⟨remove.val[j].v.val,
                  (hbounds remove.val[j] (List.getElem_mem hj)).2⟩ : Fin n)) by rfl,
            Sym2.eq_iff]
          left
          constructor
          · apply Fin.ext
            simpa [hget] using hends.1
          · apply Fin.ext
            simpa [hget] using hends.2
        · obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hactual
          refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
          rw [show indexed ⟨j, hj⟩ =
              s((⟨remove.val[j].u.val,
                  (hbounds remove.val[j] (List.getElem_mem hj)).1⟩ : Fin n),
                (⟨remove.val[j].v.val,
                  (hbounds remove.val[j] (List.getElem_mem hj)).2⟩ : Fin n)) by rfl,
            Sym2.eq_iff]
          right
          constructor
          · apply Fin.ext
            simpa [hget] using hends.2
          · apply Fin.ext
            simpa [hget] using hends.1)
  simpa using hcard.symm

theorem mutation_additionFinset_card (n : Nat) (add : Slice topology.Edge)
    (hbounds : ∀ edge ∈ add.val, edge.u.val < n ∧ edge.v.val < n)
    (hnodup : (add.val.map mutationCanonicalEdge).Nodup) :
    (mutationAdditionFinset n add).card = add.val.length := by
  classical
  let indexed : Fin add.val.length → Sym2 (Fin n) := fun i =>
    let bounds := hbounds add.val[i] (List.getElem_mem i.isLt)
    s((⟨add.val[i].u.val, bounds.1⟩ : Fin n),
      (⟨add.val[i].v.val, bounds.2⟩ : Fin n))
  have hcard := Finset.card_bij
    (s := Finset.univ) (t := mutationAdditionFinset n add)
    (fun i _ => indexed i)
    (fun i _ => by
      simp only [indexed, mutation_additionFinset_mem]
      exact ⟨add.val[i], List.getElem_mem i.isLt, Or.inl ⟨rfl, rfl⟩⟩)
    (fun i _ j _ hij => by
      have hi := hbounds add.val[i] (List.getElem_mem i.isLt)
      have hj := hbounds add.val[j] (List.getElem_mem j.isLt)
      have hcanonical := mutation_canonical_eq_of_fin_edge_eq add.val[i] add.val[j]
        hi.1 hi.2 hj.1 hj.2 (by simpa only [indexed] using hij)
      have hiMap : i.val < (add.val.map mutationCanonicalEdge).length := by simp
      have hjMap : j.val < (add.val.map mutationCanonicalEdge).length := by simp
      apply Fin.ext
      exact (hnodup.getElem_inj_iff (hi := hiMap) (hj := hjMap)).mp
        (by simpa only [List.getElem_map, Fin.getElem_fin] using hcanonical))
    (fun edge hedge => by
      induction edge using Sym2.inductionOn with
      | _ u v =>
        obtain ⟨actual, hactual, hends | hends⟩ :=
          mutation_additionFinset_mem n add u v |>.mp hedge
        · obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hactual
          refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
          rw [show indexed ⟨j, hj⟩ =
              s((⟨add.val[j].u.val,
                  (hbounds add.val[j] (List.getElem_mem hj)).1⟩ : Fin n),
                (⟨add.val[j].v.val,
                  (hbounds add.val[j] (List.getElem_mem hj)).2⟩ : Fin n)) by rfl,
            Sym2.eq_iff]
          left
          constructor
          · apply Fin.ext
            simpa [hget] using hends.1
          · apply Fin.ext
            simpa [hget] using hends.2
        · obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hactual
          refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
          rw [show indexed ⟨j, hj⟩ =
              s((⟨add.val[j].u.val,
                  (hbounds add.val[j] (List.getElem_mem hj)).1⟩ : Fin n),
                (⟨add.val[j].v.val,
                  (hbounds add.val[j] (List.getElem_mem hj)).2⟩ : Fin n)) by rfl,
            Sym2.eq_iff]
          right
          constructor
          · apply Fin.ext
            simpa [hget] using hends.2
          · apply Fin.ext
            simpa [hget] using hends.1)
  simpa using hcard.symm

theorem mutation_parentEdge_symmetric (p : List Nat) (u v : Nat) :
    parentEdge p u v ↔ parentEdge p v u := by
  unfold parentEdge
  tauto

theorem mutation_removal_canonical_edge (remove : Slice topology.Edge)
    (edge : topology.Edge) :
    mutationRemoval remove (mutationCanonicalEdge edge).u.val
        (mutationCanonicalEdge edge).v.val ↔
      mutationRemoval remove edge.u.val edge.v.val := by
  unfold mutationCanonicalEdge
  split
  · rfl
  · exact mutation_removal_symmetric remove edge.v.val edge.u.val

theorem mutation_removal_parent_edge (p : List Nat) (remove : Slice topology.Edge)
    (hremove : ∀ edge ∈ remove.val, parentEdge p edge.u.val edge.v.val)
    (u v : Nat) (h : mutationRemoval remove u v) :
    parentEdge p u v := by
  obtain ⟨edge, hedge, hends | hends⟩ := h
  · simpa only [hends.1, hends.2] using hremove edge hedge
  · apply (mutation_parentEdge_symmetric p v u).mp
    simpa only [hends.1, hends.2] using hremove edge hedge

theorem mutation_addition_existing_removed
    (c : topology.Carrier) (t : spanning_tree.Tree)
    (remove add : Slice topology.Edge)
    (hlength : remove.val.length = add.val.length)
    (hentries : ∀ j, j < remove.val.length → MutationEditEntryValid c t remove add j)
    (u v : Nat) (hadd : mutationAddition add u v)
    (hold : parentEdge (parents t) u v) :
    mutationRemoval remove u v := by
  obtain ⟨edge, hedge, hends | hends⟩ := hadd
  · obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hedge
    obtain ⟨removal, addition, hr, ha, hvalid⟩ := hentries j (by omega)
    dsimp only at hvalid
    have heq : addition = edge := by
      rw [List.getElem?_eq_getElem (by omega), hget] at ha
      exact (Option.some.inj ha).symm
    subst addition
    obtain ⟨removed, hremoved, hcu, hcv⟩ :=
      hvalid.2.2.2.2.2.2.2 ((mutation_canonical_parent_edge (parents t) edge).mpr
        (by simpa only [hends.1, hends.2] using hold))
    have hremovedCanonical :
        mutationRemoval remove (mutationCanonicalEdge removed).u.val
          (mutationCanonicalEdge removed).v.val :=
      (mutation_removal_canonical_edge remove removed).mpr
        ⟨removed, hremoved, Or.inl ⟨rfl, rfl⟩⟩
    have hcanonicalRemoval :
        mutationRemoval remove (mutationCanonicalEdge edge).u.val
          (mutationCanonicalEdge edge).v.val := by
      simpa only [hcu, hcv] using hremovedCanonical
    have hedgeRemoval := (mutation_removal_canonical_edge remove edge).mp hcanonicalRemoval
    simpa only [hends.1, hends.2] using hedgeRemoval
  · obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hedge
    obtain ⟨removal, addition, hr, ha, hvalid⟩ := hentries j (by omega)
    dsimp only at hvalid
    have heq : addition = edge := by
      rw [List.getElem?_eq_getElem (by omega), hget] at ha
      exact (Option.some.inj ha).symm
    subst addition
    obtain ⟨removed, hremoved, hcu, hcv⟩ :=
      hvalid.2.2.2.2.2.2.2 ((mutation_canonical_parent_edge (parents t) edge).mpr
        (by
          have hreverse := (mutation_parentEdge_symmetric (parents t) u v).mp hold
          simpa only [hends.1, hends.2] using hreverse))
    have hremovedCanonical :
        mutationRemoval remove (mutationCanonicalEdge removed).u.val
          (mutationCanonicalEdge removed).v.val :=
      (mutation_removal_canonical_edge remove removed).mpr
        ⟨removed, hremoved, Or.inl ⟨rfl, rfl⟩⟩
    have hcanonicalRemoval :
        mutationRemoval remove (mutationCanonicalEdge edge).u.val
          (mutationCanonicalEdge edge).v.val := by
      simpa only [hcu, hcv] using hremovedCanonical
    have hedgeRemoval := (mutation_removal_canonical_edge remove edge).mp hcanonicalRemoval
    apply (mutation_removal_symmetric remove v u).mp
    simpa only [hends.1, hends.2] using hedgeRemoval

/-- Successful preflight plus equal edit counts and the checked acyclic attachment
equations make the final functional graph a genuine tree. -/
theorem mutation_functional_edit_isTree
    (c : topology.Carrier) (t : spanning_tree.Tree)
    (remove add : Slice topology.Edge) (next : Nat → Nat)
    (hc : CarrierValid c) (ht : TreeValid c t)
    (hlength : remove.val.length = add.val.length)
    (hentries : ∀ j, j < remove.val.length → MutationEditEntryValid c t remove add j)
    (hedges : ∀ u v, mutationFunctionalEdge t.parents.val.length next u v ↔
      MutationEditedEdge (parents t) remove add u v)
    (hacyclic : (mutationFunctionalGraph t.parents.val.length next).IsAcyclic) :
    (mutationFunctionalGraph t.parents.val.length next).IsTree := by
  classical
  let n := (parents t).length
  let old := constructorParentGraph (parents t)
  let final := mutationFunctionalGraph n next
  let removed := mutationRemovalFinset n remove
  let added := mutationAdditionFinset n add
  have hroot : t.root.val < n := by simpa [n] using ht.2.1.1
  let _ : Nonempty (Fin n) := ⟨⟨t.root.val, hroot⟩⟩
  have hn : n = t.parents.val.length := by simp [n, parents]
  obtain ⟨hremove, hadd⟩ :=
    mutation_edit_entries_edges c t remove add hc hlength hentries
  obtain ⟨hnodupRemove, hnodupAdd⟩ :=
    mutation_edit_entries_canonical_nodup c t remove add hlength hentries
  have hremoveBounds : ∀ edge ∈ remove.val,
      edge.u.val < n ∧ edge.v.val < n := by
    intro edge hedge
    have he := hremove edge hedge
    exact ⟨he.1, he.2.1⟩
  have hparentLength : n = cellCount c := by
    simpa only [n] using ht.1
  have haddBounds : ∀ edge ∈ add.val,
      edge.u.val < n ∧ edge.v.val < n := by
    intro edge hedge
    have he := hadd edge hedge
    have hv := (hc.2.2.2.2.1 edge.u.val he.1).2.2 edge.v.val he.2
    rw [hparentLength]
    exact ⟨he.1, hv.1⟩
  have hremovedCard : removed.card = remove.val.length := by
    exact mutation_removalFinset_card n remove hremoveBounds hnodupRemove
  have haddedCard : added.card = add.val.length := by
    exact mutation_additionFinset_card n add haddBounds hnodupAdd
  have hedges' : ∀ u v, mutationFunctionalEdge n next u v ↔
      MutationEditedEdge (parents t) remove add u v := by
    intro u v
    simpa only [n, parents, List.length_map] using hedges u v
  have hremoveSubset : removed ⊆ old.edgeFinset := by
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset]
      change (constructorParentGraph (parents t)).Adj u v
      rw [constructor_parentGraph_adj_iff]
      exact mutation_removal_parent_edge (parents t) remove hremove u.val v.val
        (mutation_removalFinset_mem n remove u v |>.mp hedge)
  have hdisjoint : Disjoint (old.edgeFinset \ removed) added := by
    rw [Finset.disjoint_left]
    intro edge hold haddition
    induction edge using Sym2.inductionOn with
    | _ u v =>
      have hold' := Finset.mem_sdiff.mp hold
      have hparent : parentEdge (parents t) u.val v.val := by
        exact constructor_parentGraph_adj_iff (parents t) u v |>.mp
          (SimpleGraph.mem_edgeFinset.mp hold'.1)
      have hremoved := mutation_addition_existing_removed c t remove add hlength hentries
        u.val v.val (mutation_additionFinset_mem n add u v |>.mp haddition) hparent
      exact hold'.2 (mutation_removalFinset_mem n remove u v |>.mpr hremoved)
  have hcounts : removed.card = added.card := by
    rw [hremovedCard, haddedCard, hlength]
  have hedgeFinsets :
      final.edgeFinset = (old.edgeFinset \ removed) ∪ added := by
    ext edge
    induction edge using Sym2.inductionOn with
    | _ u v =>
      simp only [final, old, removed, added, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, mutation_functional_graph_adj, hedges',
        MutationEditedEdge, constructor_parentGraph_adj_iff, Finset.mem_union,
        Finset.mem_sdiff, mutation_removalFinset_mem, mutation_additionFinset_mem]
  have hacyclicFinal : final.IsAcyclic := by
    change (mutationFunctionalGraph n next).IsAcyclic
    rw [hn]
    exact hacyclic
  have htree := mutation_batch_graph_connected old final removed added
    (constructor_rooted_isTree ht.2.1) hremoveSubset hdisjoint hcounts
    hedgeFinsets hacyclicFinal
  change (mutationFunctionalGraph t.parents.val.length next).IsTree
  rw [← hn]
  exact htree
end Labyrinth
