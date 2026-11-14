module
public import LabyrinthCore.ConstructorPrefixOffsets
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core
open scoped BigOperators

namespace Labyrinth

/-- The generated edge counter increments exactly the two distinct endpoint degree slots. -/
theorem constructor_count_edge_accepts (counts : Slice Usize) (n : Usize) (edge : topology.Edge)
    (hu : edge.u.val < n.val) (hv : edge.v.val < n.val) (hne : edge.u ≠ edge.v)
    (hcapacity : n.val + 1 ≤ counts.val.length)
    (degreeU degreeV : Usize)
    (hdegreeU : counts.val[edge.u.val + 1]? = some degreeU)
    (hdegreeV : counts.val[edge.v.val + 1]? = some degreeV)
    (hwidthU : degreeU.val < Usize.max) (hwidthV : degreeV.val < Usize.max) :
    WP.spec (topology.count_edge counts n edge) (fun result =>
      result.1 = .Ok () ∧ result.2.val.length = counts.val.length ∧
      ∃ nextU nextV : Usize,
        nextU.val = degreeU.val + 1 ∧ nextV.val = degreeV.val + 1 ∧
        result.2.val[edge.u.val + 1]? = some nextU ∧
        result.2.val[edge.v.val + 1]? = some nextV ∧
        ∀ j, j ≠ edge.u.val + 1 → j ≠ edge.v.val + 1 → result.2.val[j]? = counts.val[j]?) := by
  have hnotU : ¬ edge.u ≥ n := by simpa using hu
  have hnotV : ¬ edge.v ≥ n := by simpa using hv
  have hneqVal : edge.u.val ≠ edge.v.val := fun he => hne ((UScalar.eq_equiv _ _).mpr he)
  unfold topology.count_edge
  simp only [hnotU, hnotV, hne, ite_false]
  apply WP.spec_bind (Usize.add_spec (x := edge.u) (y := 1#usize) (by
    have := counts.property
    simp only [UScalar.ofNatCore_val_eq]
    omega))
  intro uSlot hus
  have huSlot : uSlot.val = edge.u.val + 1 := by simpa using hus
  have huBound : uSlot.val < counts.val.length := by omega
  apply WP.spec_bind (Slice.index_usize_spec counts uSlot huBound)
  intro actualU hau
  have huLookup : counts.val[uSlot.val]? = some actualU := by
    rw [List.getElem?_eq_getElem huBound, hau]
  rw [huSlot, hdegreeU] at huLookup
  have huEq : actualU = degreeU := Option.some.inj huLookup.symm
  rw [huEq]
  obtain ⟨nextU, hcheckedU, hnextU⟩ := constructor_checked_add_some degreeU 1#usize (by
    simp only [UScalar.ofNatCore_val_eq]
    omega)
  simp only [hcheckedU, lift, bind_ok, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch]
  apply WP.spec_bind (Slice.update_spec counts uSlot nextU huBound)
  intro updated huUpdated
  subst updated
  apply WP.spec_bind (Usize.add_spec (x := edge.v) (y := 1#usize) (by
    have := counts.property
    simp only [UScalar.ofNatCore_val_eq]
    omega))
  intro vSlot hvs
  have hvSlot : vSlot.val = edge.v.val + 1 := by simpa using hvs
  have hvBound : vSlot.val < (counts.set uSlot nextU).val.length := by
    simp only [Slice.set_val_eq, List.length_set]
    omega
  apply WP.spec_bind (Slice.index_usize_spec (counts.set uSlot nextU) vSlot hvBound)
  intro actualV hav
  have hvLookup : (counts.set uSlot nextU).val[vSlot.val]? = some actualV := by
    rw [List.getElem?_eq_getElem hvBound, hav]
  have hslots : uSlot.val ≠ vSlot.val := by omega
  have hvEq : actualV = degreeV := by
    have h := hvLookup
    simp only [Slice.set_val_eq] at h
    rw [List.getElem?_set_ne hslots, hvSlot, hdegreeV] at h
    exact Option.some.inj h.symm
  rw [hvEq]
  obtain ⟨nextV, hcheckedV, hnextV⟩ := constructor_checked_add_some degreeV 1#usize (by
    simp only [UScalar.ofNatCore_val_eq]
    omega)
  simp only [hcheckedV, bind_ok]
  apply WP.spec_bind (Slice.update_spec (counts.set uSlot nextU) vSlot nextV hvBound)
  intro final hfinal
  subst final
  apply (WP.spec_ok _).mpr
  refine ⟨rfl, by simp, nextU, nextV, by simpa using hnextU, by simpa using hnextV, ?_, ?_, ?_⟩
  · have hub : edge.u.val + 1 < counts.val.length := by omega
    simp only [Slice.set_val_eq, huSlot, hvSlot]
    rw [List.getElem?_set_ne (show edge.v.val + 1 ≠ edge.u.val + 1 by omega),
      List.getElem?_set_eq_of_lt nextU hub]
  · have hvb : edge.v.val + 1 < counts.val.length := by omega
    simp [hvSlot, hvb]
  · intro j hju hjv
    have hjus : j ≠ uSlot.val := by omega
    have hjvs : j ≠ vSlot.val := by omega
    simp [Ne.symm hjus, Ne.symm hjvs]

def constructorDegreeSlot (edges : List topology.Edge) (slot : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 =>
    let previous := constructorDegreeSlot edges slot count
    match edges[count]? with
    | none => previous
    | some edge =>
      if slot = edge.u.val + 1 ∨ slot = edge.v.val + 1 then previous + 1 else previous

theorem constructor_degree_slot_le (edges : List topology.Edge) (slot count : Nat) :
    constructorDegreeSlot edges slot count ≤ count := by
  induction count with
  | zero => exact le_rfl
  | succ count ih =>
    simp only [constructorDegreeSlot]
    split
    · omega
    · split <;> omega

/-- The whole generated degree-count phase accepts every bounded non-self edge sequence
and computes the exact incidence count at every CSR slot. Duplicate-edge rejection is later. -/
theorem constructor_degrees_spec (n : Usize) (edges : Slice topology.Edge)
    (counts : alloc.vec.Vec Usize)
    (hcapacity : n.val + 1 = counts.val.length)
    (hzero : counts.val = List.replicate counts.val.length 0#usize)
    (hedges : ∀ edge ∈ edges.val, edge.u.val < n.val ∧ edge.v.val < n.val ∧ edge.u ≠ edge.v) :
    WP.spec (topology.Carrier.from_edges_loop0 n edges counts 0#usize (.Ok ())) (fun result =>
      result.2 = .Ok () ∧ result.1.val.length = counts.val.length ∧
      ∀ j, j < counts.val.length → ∃ value : Usize, result.1.val[j]? = some value ∧
        value.val = constructorDegreeSlot edges.val j edges.val.length) := by
  let invariant : alloc.vec.Vec Usize × Usize × core.result.Result Unit topology.Error → Prop :=
    fun state => state.1.val.length = counts.val.length ∧ state.2.1.val ≤ edges.val.length ∧
      state.2.2 = .Ok () ∧ ∀ j, j < counts.val.length → ∃ value : Usize,
        state.1.val[j]? = some value ∧ value.val = constructorDegreeSlot edges.val j state.2.1.val
  unfold topology.Carrier.from_edges_loop0
  apply loop.spec_decr_nat
    (fun state : alloc.vec.Vec Usize × Usize × core.result.Result Unit topology.Error =>
      edges.val.length - state.2.1.val) invariant
  · rintro ⟨current, index, status⟩ hinv
    obtain ⟨hlen, hindex, hstatus, hcounts⟩ := hinv
    dsimp only at hlen hindex hstatus hcounts
    subst status
    unfold topology.Carrier.from_edges_loop0.body
    by_cases hmore : index < Slice.len edges
    · have hi : index.val < edges.val.length := by simpa using hmore
      simp only [hmore, ite_true, core.result.Result.is_ok, bind_ok,
        alloc.vec.Vec.deref_mut, lift]
      apply WP.spec_bind (Slice.index_usize_spec edges index hi)
      intro edge hedge
      have hlookup : edges.val[index.val]? = some edge := by
        rw [List.getElem?_eq_getElem hi, hedge]
      have hmem : edge ∈ edges.val := by rw [hedge]; exact List.getElem_mem hi
      obtain ⟨hu, hv, hne⟩ := hedges edge hmem
      obtain ⟨degreeU, hdu, hduval⟩ := hcounts (edge.u.val + 1) (by omega)
      obtain ⟨degreeV, hdv, hdvval⟩ := hcounts (edge.v.val + 1) (by omega)
      have hwidthU : degreeU.val < Usize.max := by
        have hb := constructor_degree_slot_le edges.val (edge.u.val + 1) index.val
        have := edges.property
        omega
      have hwidthV : degreeV.val < Usize.max := by
        have hb := constructor_degree_slot_le edges.val (edge.v.val + 1) index.val
        have := edges.property
        omega
      apply WP.spec_bind (constructor_count_edge_accepts current.slice n edge hu hv hne
        (by change n.val + 1 ≤ current.val.length; omega)
        degreeU degreeV hdu hdv hwidthU hwidthV)
      rintro ⟨status', updated⟩ ⟨hs', hlen', nextU, nextV, hnextU, hnextV, hlookU, hlookV, hunchanged⟩
      dsimp only at hs' hlen' hnextU hnextV hlookU hlookV hunchanged
      rw [hs']
      apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
        have := edges.property
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro index' hi'
      have hindex' : index'.val = index.val + 1 := by simpa using hi'
      apply (WP.spec_ok _).mpr
      dsimp only [invariant]
      refine ⟨⟨hlen'.trans hlen, by omega, rfl, ?_⟩, by omega⟩
      intro j hj
      rw [hindex']
      simp only [constructorDegreeSlot, hlookup]
      by_cases hju : j = edge.u.val + 1
      · subst j
        refine ⟨nextU, hlookU, ?_⟩
        simp only [true_or, ite_true]
        omega
      · by_cases hjv : j = edge.v.val + 1
        · subst j
          refine ⟨nextV, hlookV, ?_⟩
          simp only [or_true, ite_true]
          omega
        · obtain ⟨value, hvalue, hval⟩ := hcounts j hj
          exact ⟨value, (hunchanged j hju hjv).trans hvalue,
            by simpa only [hju, hjv, false_or, ite_false] using hval⟩
    · have he : index.val = edges.val.length := by
        have : ¬ index.val < edges.val.length := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      exact ⟨rfl, hlen, by simpa only [he] using hcounts⟩
  · refine ⟨rfl, by simp, rfl, ?_⟩
    intro j hj
    refine ⟨0#usize, ?_, by simp [constructorDegreeSlot]⟩
    rw [hzero]
    simp [hj]

/-- The degree allocation contains two incidences per non-self input edge, for every prefix. -/
theorem constructor_degree_sum (n : Nat) (edges : List topology.Edge)
    (hedges : ∀ edge ∈ edges, edge.u.val < n ∧ edge.v.val < n ∧ edge.u ≠ edge.v)
    (count : Nat) (hcount : count ≤ edges.length) :
    (∑ j ∈ Finset.range (n + 1), constructorDegreeSlot edges j count) = 2 * count := by
  induction count with
  | zero => simp [constructorDegreeSlot]
  | succ count ih =>
    have hi : count < edges.length := by omega
    let edge := edges[count]'hi
    have hlookup : edges[count]? = some edge := List.getElem?_eq_getElem hi
    obtain ⟨hu, hv, hne⟩ := hedges edge (List.getElem_mem hi)
    have hslots : edge.u.val + 1 ≠ edge.v.val + 1 := by
      intro he
      apply hne
      exact (UScalar.eq_equiv _ _).mpr (by omega)
    have hstep (j : Nat) :
        constructorDegreeSlot edges j (count + 1) = constructorDegreeSlot edges j count +
          (if j = edge.u.val + 1 then 1 else 0) + (if j = edge.v.val + 1 then 1 else 0) := by
      simp only [constructorDegreeSlot, hlookup]
      split_ifs <;> omega
    simp only [hstep, Finset.sum_add_distrib]
    rw [ih (by omega)]
    have huMem : edge.u.val + 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hvMem : edge.v.val + 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    simp [huMem, hvMem]
    omega

theorem constructor_prefix_sum_as_sum (values : List Usize) (count : Nat) :
    constructorPrefixSum values count = ∑ j ∈ Finset.range count, (values[j]?.getD 0#usize).val := by
  induction count with
  | zero => simp [constructorPrefixSum]
  | succ count ih => simp only [constructorPrefixSum, Finset.sum_range_succ, ih]

/-- Exact degree counting supplies the numeric width premise of the real prefix-sum operation. -/
theorem constructor_degrees_prefix_sum (n : Nat) (edges : List topology.Edge)
    (counts : Slice Usize) (hlen : counts.val.length = n + 1)
    (hedges : ∀ edge ∈ edges, edge.u.val < n ∧ edge.v.val < n ∧ edge.u ≠ edge.v)
    (hcounts : ∀ j, j < counts.val.length → ∃ value : Usize, counts.val[j]? = some value ∧
      value.val = constructorDegreeSlot edges j edges.length) :
    constructorPrefixSum counts.val counts.val.length = 2 * edges.length := by
  rw [constructor_prefix_sum_as_sum, hlen]
  calc
    (∑ j ∈ Finset.range (n + 1), (counts.val[j]?.getD 0#usize).val) =
        ∑ j ∈ Finset.range (n + 1), constructorDegreeSlot edges j edges.length := by
      apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨value, hv, he⟩ := hcounts j (by rw [hlen]; exact Finset.mem_range.mp hj)
      simpa only [hv, Option.getD_some] using he
    _ = 2 * edges.length := constructor_degree_sum n edges hedges _ le_rfl

/-- Degree validation terminates on arbitrary edge lists. Its successful branch supplies
the endpoint bounds needed by the unchecked adjacency-fill phase; malformed edges return
an ordinary Rust error rather than an Aeneas failure. -/
theorem constructor_degrees_total_spec (n : Usize) (edges : Slice topology.Edge)
    (counts : alloc.vec.Vec Usize)
    (hcapacity : n.val + 1 = counts.val.length)
    (hzero : counts.val = List.replicate counts.val.length 0#usize) :
    WP.spec (topology.Carrier.from_edges_loop0 n edges counts 0#usize (.Ok ())) (fun result =>
      result.2 = .Ok () →
        result.1.val.length = counts.val.length ∧
        (∀ edge ∈ edges.val, edge.u.val < n.val ∧ edge.v.val < n.val ∧ edge.u ≠ edge.v) ∧
        ∀ j, j < counts.val.length → ∃ value : Usize, result.1.val[j]? = some value ∧
          value.val = constructorDegreeSlot edges.val j edges.val.length) := by
  let invariant : alloc.vec.Vec Usize × Usize × core.result.Result Unit topology.Error → Prop :=
    fun state => state.1.val.length = counts.val.length ∧ state.2.1.val ≤ edges.val.length ∧
      (state.2.2 = .Ok () →
        (∀ i edge, i < state.2.1.val → edges.val[i]? = some edge →
          edge.u.val < n.val ∧ edge.v.val < n.val ∧ edge.u ≠ edge.v) ∧
        ∀ j, j < counts.val.length → ∃ value : Usize,
          state.1.val[j]? = some value ∧ value.val = constructorDegreeSlot edges.val j state.2.1.val)
  unfold topology.Carrier.from_edges_loop0
  apply loop.spec_decr_nat
    (fun state : alloc.vec.Vec Usize × Usize × core.result.Result Unit topology.Error =>
      edges.val.length - state.2.1.val) invariant
  · rintro ⟨current, index, status⟩ hinv
    obtain ⟨hlen, hindex, hsuccess⟩ := hinv
    dsimp only at hlen hindex hsuccess
    unfold topology.Carrier.from_edges_loop0.body
    by_cases hmore : index < Slice.len edges
    · have hi : index.val < edges.val.length := by simpa using hmore
      simp only [hmore, ite_true]
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false]
        apply (WP.spec_ok _).mpr
        intro h
        cases h
      | Ok value =>
        cases value
        obtain ⟨hprefix, hcounts⟩ := hsuccess rfl
        simp only [core.result.Result.is_ok, bind_ok, ite_true,
          alloc.vec.Vec.deref_mut, lift]
        apply WP.spec_bind (Slice.index_usize_spec edges index hi)
        intro edge hedge
        have hlookup : edges.val[index.val]? = some edge := by
          rw [List.getElem?_eq_getElem hi, hedge]
        have hstep : WP.spec (topology.count_edge current.slice n edge) (fun result =>
            result.2.val.length = current.val.length ∧
            (result.1 = .Ok () →
              (edge.u.val < n.val ∧ edge.v.val < n.val ∧ edge.u ≠ edge.v) ∧
              ∀ j, j < counts.val.length → ∃ value : Usize,
                result.2.val[j]? = some value ∧
                value.val = constructorDegreeSlot edges.val j (index.val + 1))) := by
          by_cases hu : edge.u.val < n.val
          · have hnotU : ¬ edge.u ≥ n := by simpa using hu
            by_cases hv : edge.v.val < n.val
            · have hnotV : ¬ edge.v ≥ n := by simpa using hv
              by_cases hne : edge.u ≠ edge.v
              · obtain ⟨degreeU, hdu, hduval⟩ := hcounts (edge.u.val + 1) (by omega)
                obtain ⟨degreeV, hdv, hdvval⟩ := hcounts (edge.v.val + 1) (by omega)
                have hwidthU : degreeU.val < Usize.max := by
                  have hb := constructor_degree_slot_le edges.val (edge.u.val + 1) index.val
                  have := edges.property
                  omega
                have hwidthV : degreeV.val < Usize.max := by
                  have hb := constructor_degree_slot_le edges.val (edge.v.val + 1) index.val
                  have := edges.property
                  omega
                apply WP.spec_mono (constructor_count_edge_accepts current.slice n edge
                  hu hv hne (by change n.val + 1 ≤ current.val.length; omega)
                  degreeU degreeV hdu hdv hwidthU hwidthV)
                rintro ⟨status', updated⟩ ⟨_, hlen', nextU, nextV, hnextU, hnextV,
                  hlookU, hlookV, hunchanged⟩
                refine ⟨hlen', fun _ => ⟨⟨hu, hv, hne⟩, ?_⟩⟩
                intro j hj
                simp only [constructorDegreeSlot, hlookup]
                by_cases hju : j = edge.u.val + 1
                · subst j
                  refine ⟨nextU, hlookU, ?_⟩
                  simp only [true_or, ite_true]
                  omega
                · by_cases hjv : j = edge.v.val + 1
                  · subst j
                    refine ⟨nextV, hlookV, ?_⟩
                    simp only [or_true, ite_true]
                    omega
                  · obtain ⟨value, hvalue, hval⟩ := hcounts j hj
                    exact ⟨value, (hunchanged j hju hjv).trans hvalue,
                      by simpa only [hju, hjv, false_or, ite_false] using hval⟩
              · have he : edge.u = edge.v := not_ne_iff.mp hne
                simp only [topology.count_edge, hnotV, he, ite_false, ite_true, WP.spec_ok]
                exact ⟨rfl, fun h => by cases h⟩
            · have hbadV : edge.v ≥ n := by simpa using hv
              simp only [topology.count_edge, hnotU, hbadV, ite_false, ite_true, WP.spec_ok]
              exact ⟨rfl, fun h => by cases h⟩
          · have hbadU : edge.u ≥ n := by simpa using hu
            simp only [topology.count_edge, hbadU, ite_true, WP.spec_ok]
            exact ⟨rfl, fun h => by cases h⟩
        apply WP.spec_bind hstep
        rintro ⟨status', updated⟩ ⟨hlen', hsuccess'⟩
        apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
          have := edges.property
          simp only [UScalar.ofNatCore_val_eq]
          omega))
        intro next hn
        have hnext : next.val = index.val + 1 := by simpa using hn
        apply (WP.spec_ok _).mpr
        dsimp only [invariant]
        refine ⟨⟨hlen'.trans hlen, by omega, ?_⟩, by omega⟩
        intro hok
        obtain ⟨hedgeValid, hcounts'⟩ := hsuccess' hok
        refine ⟨?_, ?_⟩
        · intro i other hib hother
          by_cases he : i = index.val
          · subst i
            have heq : other = edge := Option.some.inj (hother.symm.trans hlookup)
            simpa only [heq] using hedgeValid
          · exact hprefix i other (by omega) hother
        · change ∀ j, j < counts.val.length → ∃ value : Usize,
            updated.val[j]? = some value ∧
              value.val = constructorDegreeSlot edges.val j next.val
          simpa only [hnext] using hcounts'
    · have he : index.val = edges.val.length := by
        have : ¬ index.val < edges.val.length := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      intro hok
      obtain ⟨hprefix, hcounts⟩ := hsuccess hok
      refine ⟨hlen, ?_, by simpa only [he] using hcounts⟩
      intro edge hedge
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hedge
      exact hprefix i edge (by omega) (by simp [hi, hget])
  · refine ⟨rfl, by simp, fun _ => ⟨?_, ?_⟩⟩
    · intro i edge hi _
      simp at hi
    · intro j hj
      refine ⟨0#usize, ?_, by simp [constructorDegreeSlot]⟩
      rw [hzero]
      simp [hj]

end Labyrinth
