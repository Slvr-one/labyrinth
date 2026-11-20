module
public import LabyrinthCore.MutationPreflight

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

 def MutationEditEntryValid (c : topology.Carrier) (t : spanning_tree.Tree)
    (remove add : Slice topology.Edge) (index : Nat) : Prop :=
  ∃ removal addition, remove.val[index]? = some removal ∧ add.val[index]? = some addition ∧
    let r := mutationCanonicalEdge removal
    let a := mutationCanonicalEdge addition
    r.u.val < t.parents.val.length ∧ r.v.val < t.parents.val.length ∧
    a.u.val < t.parents.val.length ∧ a.v.val < t.parents.val.length ∧
    parentEdge (parents t) r.u.val r.v.val ∧ carrierEdge c a.u.val a.v.val ∧
    (¬ ∃ j, j < index ∧ mutationDuplicateAt remove add r.u r.v a.u a.v j) ∧
    (parentEdge (parents t) a.u.val a.v.val → ∃ edge ∈ remove.val,
      (mutationCanonicalEdge edge).u = a.u ∧ (mutationCanonicalEdge edge).v = a.v)

 theorem mutation_check_edit_total (c : topology.Carrier) (t : spanning_tree.Tree)
    (remove add : Slice topology.Edge) (index : Usize) (hc : CarrierValid c)
    (hr : index.val < remove.val.length) (ha : index.val < add.val.length) :
    spanning_tree.Tree.check_edit t c remove add index ⦃ result =>
      result = core.result.Result.Ok () ↔ MutationEditEntryValid c t remove add index.val ⦄ := by
  unfold spanning_tree.Tree.check_edit
  apply spec_bind (Slice.index_usize_spec remove index hr)
  intro removal hremoval
  have hrget : remove.val[index.val]? = some removal := by
    rw [List.getElem?_eq_getElem hr, ← hremoval]
  apply spec_bind (mutation_edge_new_total removal.u removal.v)
  intro r hcanonicalR
  have hrCanonical : r = mutationCanonicalEdge removal := hcanonicalR
  apply spec_bind (Slice.index_usize_spec add index ha)
  intro addition haddition
  have haget : add.val[index.val]? = some addition := by
    rw [List.getElem?_eq_getElem ha, ← haddition]
  apply spec_bind (mutation_edge_new_total addition.u addition.v)
  intro a hcanonicalA
  have haCanonical : a = mutationCanonicalEdge addition := hcanonicalA
  have hvalid : MutationEditEntryValid c t remove add index.val ↔
      r.u.val < t.parents.val.length ∧ r.v.val < t.parents.val.length ∧
      a.u.val < t.parents.val.length ∧ a.v.val < t.parents.val.length ∧
      parentEdge (parents t) r.u.val r.v.val ∧ carrierEdge c a.u.val a.v.val ∧
      (¬ ∃ j, j < index.val ∧ mutationDuplicateAt remove add r.u r.v a.u a.v j) ∧
      (parentEdge (parents t) a.u.val a.v.val → ∃ edge ∈ remove.val,
        (mutationCanonicalEdge edge).u = a.u ∧ (mutationCanonicalEdge edge).v = a.v) := by
    constructor
    · rintro ⟨actualRemoval, actualAddition, hactualR, hactualA, hproperties⟩
      have heqR : actualRemoval = removal :=
        Option.some.inj (hactualR.symm.trans hrget)
      have heqA : actualAddition = addition :=
        Option.some.inj (hactualA.symm.trans haget)
      simpa only [heqR, heqA, ← hrCanonical, ← haCanonical] using hproperties
    · intro hproperties
      refine ⟨removal, addition, hrget, haget, ?_⟩
      simpa only [hrCanonical, haCanonical] using hproperties
  by_cases hru : r.u ≥ alloc.vec.Vec.len t.parents
  · simp only [hru, ite_true]
    apply (spec_ok _).mpr
    rw [hvalid]
    have hn : ¬ r.u.val < t.parents.val.length := Nat.not_lt.mpr hru
    simp [hn]
  simp only [hru, ite_false]
  by_cases hrv : r.v ≥ alloc.vec.Vec.len t.parents
  · simp only [hrv, ite_true]
    apply (spec_ok _).mpr
    rw [hvalid]
    have hn : ¬ r.v.val < t.parents.val.length := Nat.not_lt.mpr hrv
    simp [hn]
  simp only [hrv, ite_false]
  by_cases hau : a.u ≥ alloc.vec.Vec.len t.parents
  · simp only [hau, ite_true]
    apply (spec_ok _).mpr
    rw [hvalid]
    have hn : ¬ a.u.val < t.parents.val.length := Nat.not_lt.mpr hau
    simp [hn]
  simp only [hau, ite_false]
  by_cases hav : a.v ≥ alloc.vec.Vec.len t.parents
  · simp only [hav, ite_true]
    apply (spec_ok _).mpr
    rw [hvalid]
    have hn : ¬ a.v.val < t.parents.val.length := Nat.not_lt.mpr hav
    simp [hn]
  simp only [hav, ite_false]
  have hru' : r.u.val < t.parents.val.length := Nat.lt_of_not_ge hru
  have hrv' : r.v.val < t.parents.val.length := Nat.lt_of_not_ge hrv
  have hau' : a.u.val < t.parents.val.length := Nat.lt_of_not_ge hau
  have hav' : a.v.val < t.parents.val.length := Nat.lt_of_not_ge hav
  apply spec_bind (mutation_has_edge_total t r)
  intro removalPresent hremovalPresent
  cases removalPresent with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    apply (spec_ok _).mpr
    rw [hvalid]
    have hn : ¬ parentEdge (parents t) r.u.val r.v.val := by simpa using hremovalPresent.symm
    simp [hn]
  | true =>
    have hrem := hremovalPresent.mp rfl
    simp only [ite_true]
    apply spec_bind (mutation_carrier_contains_total c a hc)
    intro allowed hallowed
    cases allowed with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      apply (spec_ok _).mpr
      rw [hvalid]
      have hn : ¬ carrierEdge c a.u.val a.v.val := by simpa using hallowed.symm
      simp [hn]
    | true =>
      have hadd := hallowed.mp rfl
      simp only [ite_true]
      apply spec_bind (mutation_duplicate_scan_total remove add index r.u r.v a.u a.v
        (by omega) (by omega))
      intro duplicate hduplicate
      cases duplicate with
      | true =>
        simp only [ite_true]
        apply (spec_ok _).mpr
        rw [hvalid]
        simp [hduplicate.mp rfl]
      | false =>
        have hdistinct : ¬ ∃ j, j < index.val ∧ mutationDuplicateAt remove add r.u r.v a.u a.v j := by
          simpa using hduplicate.symm
        simp only [Bool.false_eq_true, ite_false]
        apply spec_bind (mutation_has_edge_total t a)
        intro additionPresent hadditionPresent
        cases additionPresent with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          apply (spec_ok _).mpr
          rw [hvalid]
          have hn : ¬ parentEdge (parents t) a.u.val a.v.val := by simpa using hadditionPresent.symm
          simp [hru', hrv', hau', hav', hrem, hadd, hdistinct, hn]
        | true =>
          have hexisting := hadditionPresent.mp rfl
          simp only [ite_true]
          apply spec_bind (mutation_removed_scan_total remove a.u a.v 0#usize (by simp)
            (by simp))
          rintro found ⟨hfound, hprefix, hmatch⟩
          have hexists : (∃ edge ∈ remove.val,
              (mutationCanonicalEdge edge).u = a.u ∧ (mutationCanonicalEdge edge).v = a.v) ↔
              found.val < remove.val.length := by
            constructor
            · rintro ⟨edge, hedge, he⟩
              obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hedge
              by_contra hn
              have hfull : found.val = remove.val.length := by omega
              have hne := hprefix j (by omega) edge (by simp [hj, hget])
              exact hne.elim (fun h => h he.1) (fun h => h he.2)
            · intro hf
              obtain ⟨edge, hget, he⟩ := hmatch hf
              exact ⟨edge, List.mem_of_getElem? hget, he⟩
          by_cases hfull : found = Slice.len remove
          · simp only [hfull, ite_true]
            apply (spec_ok _).mpr
            rw [hvalid]
            have hn : ¬ found.val < remove.val.length := by rw [hfull]; simp
            simp [hru', hrv', hau', hav', hrem, hadd, hdistinct, hexisting, hexists, hn]
          · simp only [hfull, ite_false]
            apply (spec_ok _).mpr
            rw [hvalid]
            have hshort : found.val < remove.val.length := by
              have hne : found.val ≠ remove.val.length := fun he => hfull (UScalar.eq_of_val_eq he)
              omega
            simp [hru', hrv', hau', hav', hrem, hadd, hdistinct, hexisting, hexists, hshort]

 theorem mutation_edit_preflight_total
    (c : topology.Carrier) (t : spanning_tree.Tree)
    (remove add : Slice topology.Edge) (hc : CarrierValid c)
    (hlength : remove.val.length = add.val.length) :
    spanning_tree.Tree.edit_edges_loop0 t.parents t.root c remove add 0#usize
      (core.result.Result.Ok ()) ⦃ result =>
        result = core.result.Result.Ok () ↔
          ∀ j, j < remove.val.length → MutationEditEntryValid c t remove add j ⦄ := by
  unfold spanning_tree.Tree.edit_edges_loop0
  apply loop.spec_decr_nat
    (fun state : Usize × core.result.Result Unit topology.Error =>
      remove.val.length - state.1.val)
    (fun state : Usize × core.result.Result Unit topology.Error =>
      state.1.val ≤ remove.val.length ∧
        (state.2 = core.result.Result.Ok () ↔
          ∀ j, j < state.1.val → MutationEditEntryValid c t remove add j))
    _
  · rintro ⟨index, status⟩ ⟨hindex, hprefix⟩
    dsimp only at hindex hprefix ⊢
    unfold spanning_tree.Tree.edit_edges_loop0.body
    by_cases hlt : index < Slice.len remove
    · have hltNat : index.val < remove.val.length := hlt
      simp only [hlt, ite_true]
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false]
        apply (spec_ok _).mpr
        constructor
        · intro h
          cases h
        · intro hall
          have hbad := hprefix.mpr (fun j hj => hall j (by omega))
          cases hbad
      | Ok payload =>
        cases payload
        have hprevious := hprefix.mp rfl
        simp only [core.result.Result.is_ok, bind_ok, ite_true]
        apply spec_bind (mutation_check_edit_total c t remove add index hc hltNat
          (by omega))
        intro nextStatus hnextStatus
        apply spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        intro next hnext
        have hn : next.val = index.val + 1 := by simpa using hnext
        apply (spec_ok _).mpr
        dsimp only
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [hnextStatus]
        constructor
        · intro hcurrent j hj
          by_cases heq : j = index.val
          · simpa only [heq] using hcurrent
          · exact hprevious j (by omega)
        · intro hall
          exact hall index.val (by omega)
    · have heq : index.val = remove.val.length := by
        have hnot : ¬ index.val < remove.val.length := hlt
        omega
      simp only [hlt, ite_false]
      apply (spec_ok _).mpr
      simpa only [heq] using hprefix
  · exact ⟨by simp, by simp⟩

 theorem mutation_canonical_parent_edge (p : List Nat) (edge : topology.Edge) :
    parentEdge p (mutationCanonicalEdge edge).u.val (mutationCanonicalEdge edge).v.val ↔
      parentEdge p edge.u.val edge.v.val := by
  unfold mutationCanonicalEdge
  split
  · rfl
  · simp only
    unfold parentEdge
    constructor
    · rintro ⟨hv, hu, hne, hp⟩
      exact ⟨hu, hv, Ne.symm hne, hp.symm⟩
    · rintro ⟨hu, hv, hne, hp⟩
      exact ⟨hv, hu, Ne.symm hne, hp.symm⟩

 theorem mutation_canonical_carrier_edge (c : topology.Carrier) (edge : topology.Edge)
    (hc : CarrierValid c) :
    carrierEdge c (mutationCanonicalEdge edge).u.val (mutationCanonicalEdge edge).v.val ↔
      carrierEdge c edge.u.val edge.v.val := by
  unfold mutationCanonicalEdge
  split
  · rfl
  · exact mutation_carrier_symmetric c hc edge.v.val edge.u.val

 theorem mutation_edit_entries_edges (c : topology.Carrier) (t : spanning_tree.Tree)
    (remove add : Slice topology.Edge) (hc : CarrierValid c)
    (hlength : remove.val.length = add.val.length)
    (hentries : ∀ j, j < remove.val.length → MutationEditEntryValid c t remove add j) :
    (∀ edge ∈ remove.val, parentEdge (parents t) edge.u.val edge.v.val) ∧
    (∀ edge ∈ add.val, carrierEdge c edge.u.val edge.v.val) := by
  constructor
  · intro edge hedge
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hedge
    obtain ⟨removal, addition, hr, _, hvalid⟩ := hentries j hj
    have heq : removal = edge := by
      have hactual : remove.val[j]? = some edge := by simp [hj, hget]
      exact Option.some.inj (hr.symm.trans hactual)
    apply (mutation_canonical_parent_edge (parents t) edge).mp
    simpa only [heq] using hvalid.2.2.2.2.1
  · intro edge hedge
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hedge
    obtain ⟨removal, addition, _, ha, hvalid⟩ := hentries j (by omega)
    have heq : addition = edge := by
      have hactual : add.val[j]? = some edge := by simp [hj, hget]
      exact Option.some.inj (ha.symm.trans hactual)
    apply (mutation_canonical_carrier_edge c edge hc).mp
    simpa only [heq] using hvalid.2.2.2.2.2.1

end Labyrinth
