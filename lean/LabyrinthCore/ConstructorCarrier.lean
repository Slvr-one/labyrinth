module
public import LabyrinthCore.Constructors
public import LabyrinthCore.ConstructorCSR
public import LabyrinthCore.ConstructorConnected
public import LabyrinthCore.ConstructorCarrierModel
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- Validity of the supplied CSR representation, with no evaluation/output premise. -/
def constructorCsrInputValid (offsets neighbors : alloc.vec.Vec Usize) : Prop :=
  2 ≤ offsets.val.length ∧ offsets.val[0]? = some 0#usize ∧
  offsets.val[offsets.val.length - 1]? = some (alloc.vec.Vec.len neighbors) ∧
  constructorRawRows (alloc.vec.Vec.deref offsets) (alloc.vec.Vec.deref neighbors) ∧
  constructorAllRows offsets neighbors (offsets.val.length - 1) ∧
  ∀ v, v < offsets.val.length - 1 →
    Relation.ReflTransGen (constructorCsrAdjacent offsets neighbors) 0 v

/-- Exactly the two additional allocation widths checked by `Carrier.from_csr`. -/
def constructorCsrStorageFits (offsets neighbors : alloc.vec.Vec Usize) : Prop :=
  (offsets.val.length - 1) * 8 ≤ Usize.max ∧
  (offsets.val.length - 1) * 8 ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val ∧
  (neighbors.val.length / 2) * 16 ≤ Usize.max ∧
  (neighbors.val.length / 2) * 16 ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val

/-- The actual CSR constructor terminates and accepts every valid representable connected
simple reciprocal CSR, yielding the full public carrier invariant and preserving row order. -/
theorem constructor_carrier_from_csr_accepts (offsets neighbors : alloc.vec.Vec Usize)
    (hinput : constructorCsrInputValid offsets neighbors)
    (hwidth : constructorCsrStorageFits offsets neighbors) :
    WP.spec (topology.Carrier.from_csr offsets neighbors) (fun result =>
      ∃ carrier, result = .Ok carrier ∧ CarrierValid carrier ∧
        carrier.offsets = offsets ∧ carrier.neighbors = neighbors) := by
  obtain ⟨hsize, hfirst, hlast, hrows, hentries, hconnected⟩ := hinput
  obtain ⟨hnodeMax, hnodeStorage, hedgeMax, hedgeStorage⟩ := hwidth
  have hsmall : ¬ alloc.vec.Vec.len offsets < 2#usize := by simpa using (not_lt.mpr hsize)
  unfold topology.Carrier.from_csr
  simp only [hsmall, ite_false]
  apply WP.spec_bind (Usize.sub_spec (x := alloc.vec.Vec.len offsets) (y := 1#usize) (by
    change 1 ≤ offsets.val.length
    omega))
  intro n hn
  have hnval : n.val = offsets.val.length - 1 := by simpa using hn.1
  simp only [alloc.vec.Vec.index_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec offsets 0#usize (by
    change 0 < offsets.val.length
    omega))
  intro first hf
  have hfirstLookup : offsets.val[0]? = some first := by
    rw [List.getElem?_eq_getElem (show 0 < offsets.val.length by omega)]
    exact congrArg some (by simpa using hf.symm)
  have hzero : first = 0#usize := Option.some.inj (hfirstLookup.symm.trans hfirst)
  simp only [bne_iff_ne, ne_eq, hzero, not_true_eq_false, ite_false]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec offsets n (by
    change n.val < offsets.val.length
    omega))
  intro last hl
  have hlastLookup : offsets.val[n.val]? = some last := by
    rw [List.getElem?_eq_getElem (show n.val < offsets.val.length by omega), hl]
  rw [hnval, hlast] at hlastLookup
  have hlastEq : last = alloc.vec.Vec.len neighbors := Option.some.inj hlastLookup.symm
  simp only [hlastEq, not_true_eq_false, ite_false]
  apply WP.spec_bind (constructor_csr_offsets_spec offsets neighbors n (by omega))
  intro valid hv
  have hraw := hrows
  simp only [constructorRawRows, alloc.vec.Vec.deref, Slice.from_val] at hraw
  have hvtrue : valid = true := hv.mpr (by
    intro i hi
    obtain ⟨lo, stop, hlo, hstop, hordered, hstorage⟩ := hraw i (by omega)
    simpa only [constructorOffsetOK, hlo, hstop, Option.getD_some] using
      And.intro hordered hstorage)
  simp only [hvtrue, ite_true]
  apply WP.spec_bind (constructor_csr_all_rows_spec offsets neighbors n hsize hnval hrows)
  rintro ⟨unused, status⟩ hstatus
  have hstatusOk : status = .Ok () := hstatus.2.mpr (by simpa only [hnval] using hentries)
  rw [hstatusOk]
  have hbranch : WP.spec
      (core.result.Result.Insts.CoreOpsTry.branch
        (.Ok () : core.result.Result Unit topology.Error))
      (fun cf => cf = .Continue ()) := (WP.spec_ok _).mpr rfl
  apply WP.spec_bind hbranch
  intro cf hcf
  subst cf
  have hnodeFits : constructorStorageFits n 8#usize := by
    simp only [constructorStorageFits, hnval, UScalar.ofNatCore_val_eq]
    exact ⟨hnodeMax, hnodeStorage⟩
  apply WP.spec_bind (constructor_check_storage_spec n 8#usize)
  intro storage hs
  have hsok : storage = .Ok () := by simpa only [hnodeFits, ite_true] using hs
  simp only [hsok, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneBool false n rfl)
  intro seen hseen
  apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize n rfl)
  intro stack hstack
  simp only [alloc.vec.Vec.index_mut_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec seen 0#usize (by
    change 0 < seen.val.length
    rw [hseen.1, List.length_replicate]
    omega))
  rintro ⟨old, back⟩ ⟨_, rfl⟩
  apply WP.spec_bind (constructor_csr_connectivity_accepts offsets neighbors n unused seen stack
    hnval (by omega) hseen.1 hstack.1 hrows hentries)
  intro reached hr
  have hreached : reached = n := hr.2.mpr (by simpa only [hnval] using hconnected)
  simp only [hreached, not_true_eq_false, ite_false]
  apply WP.spec_bind (Usize.div_spec (x := alloc.vec.Vec.len neighbors) (y := 2#usize) (by simp))
  intro edgeCount hec
  have hecval : edgeCount.val = neighbors.val.length / 2 := by simpa using hec
  have hedgeFits : constructorStorageFits edgeCount 16#usize := by
    simp only [constructorStorageFits, hecval, UScalar.ofNatCore_val_eq]
    exact ⟨hedgeMax, hedgeStorage⟩
  apply WP.spec_bind (constructor_check_storage_spec edgeCount 16#usize)
  intro edgeStorage hes
  have hesok : edgeStorage = .Ok () := by simpa only [hedgeFits, ite_true] using hes
  simp only [hesok, bind_ok,
    topology.Edge.new, le_refl, ite_true]
  apply WP.spec_bind (Usize.div_spec (x := alloc.vec.Vec.len neighbors) (y := 2#usize) (by simp))
  intro edgeCount' hec'
  have hecval' : edgeCount'.val = neighbors.val.length / 2 := by simpa using hec'
  apply WP.spec_bind (alloc.vec.from_elem_spec topology.Edge.Insts.CoreCloneClone
    ({ u := 0#usize, v := 0#usize } : topology.Edge) edgeCount' rfl)
  intro edgeStorage' hallocated
  have hcapacity : edgeStorage'.val.length =
      (constructorCanonicalPairs offsets neighbors n.val).length := by
    rw [hallocated.1, List.length_replicate, hecval', hnval,
      constructor_csr_canonical_count offsets neighbors hfirst hlast hrows hentries]
  apply WP.spec_bind (constructor_canonical_all_rows_spec offsets neighbors n edgeStorage'
    hnval hrows hcapacity)
  intro canonical hcanonical
  apply (WP.spec_ok _).mpr
  refine ⟨_, rfl, ?_, rfl, rfl⟩
  apply constructor_carrier_valid_of_rows _ hsize hfirst hlast hrows hentries hconnected
  simpa only [edgePairs, hnval] using hcanonical

/-- Totality includes malformed inputs: every indexing and allocation path is justified by
the checks performed by the extracted constructor itself. Successful results retain the
input CSR and satisfy both its acceptance predicate and the public carrier invariant. -/
theorem constructor_carrier_from_csr_spec (offsets neighbors : alloc.vec.Vec Usize) :
    WP.spec (topology.Carrier.from_csr offsets neighbors) (fun result =>
      match result with
      | .Ok carrier => CarrierValid carrier ∧
          carrier.offsets = offsets ∧ carrier.neighbors = neighbors ∧
          constructorCsrInputValid offsets neighbors ∧
          constructorCsrStorageFits offsets neighbors
      | .Err _ => True) := by
  unfold topology.Carrier.from_csr
  by_cases hsmall : alloc.vec.Vec.len offsets < 2#usize
  · simp only [hsmall, ite_true, WP.spec_ok]
  · simp only [hsmall, ite_false]
    have hsize : 2 ≤ offsets.val.length := by
      have hbound : 1 < offsets.val.length := by simpa using hsmall
      omega
    apply WP.spec_bind (Usize.sub_spec (x := alloc.vec.Vec.len offsets) (y := 1#usize) (by
      change 1 ≤ offsets.val.length
      omega))
    intro n hn
    have hnval : n.val = offsets.val.length - 1 := by simpa using hn.1
    simp only [alloc.vec.Vec.index_slice_index]
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec offsets 0#usize (by
      change 0 < offsets.val.length
      omega))
    intro first hf
    have hfirstLookup : offsets.val[0]? = some first := by
      rw [List.getElem?_eq_getElem (show 0 < offsets.val.length by omega)]
      exact congrArg some (by simpa using hf.symm)
    by_cases hzero : first = 0#usize
    · simp only [bne_iff_ne, ne_eq, hzero, not_true_eq_false, ite_false]
      have hfirst : offsets.val[0]? = some 0#usize := by simpa only [hzero] using hfirstLookup
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec offsets n (by
        change n.val < offsets.val.length
        omega))
      intro last hl
      have hlastLookup : offsets.val[n.val]? = some last := by
        rw [List.getElem?_eq_getElem (show n.val < offsets.val.length by omega), hl]
      by_cases hlastEq : last = alloc.vec.Vec.len neighbors
      · simp only [hlastEq, not_true_eq_false, ite_false]
        have hlast : offsets.val[offsets.val.length - 1]? =
            some (alloc.vec.Vec.len neighbors) := by
          simpa only [hnval, hlastEq] using hlastLookup
        apply WP.spec_bind (constructor_csr_offsets_spec offsets neighbors n (by omega))
        intro valid hv
        cases valid with
        | false => simp only [Bool.false_eq_true, ite_false, WP.spec_ok]
        | true =>
          simp only [ite_true]
          have hraw := hv.mp rfl
          have hrows : constructorRawRows (alloc.vec.Vec.deref offsets)
              (alloc.vec.Vec.deref neighbors) := by
            simp only [constructorRawRows, alloc.vec.Vec.deref, Slice.from_val]
            intro i hi
            have hil : i < offsets.val.length := by
              change i < offsets.val.length - 1 at hi
              omega
            have hin : i + 1 < offsets.val.length := by
              change i < offsets.val.length - 1 at hi
              omega
            refine ⟨offsets.val[i], offsets.val[i + 1],
              List.getElem?_eq_getElem hil, List.getElem?_eq_getElem hin, ?_⟩
            have h := hraw i (by
              change i < offsets.val.length - 1 at hi
              omega)
            simpa only [constructorOffsetOK, List.getElem?_eq_getElem hil,
              List.getElem?_eq_getElem hin, Option.getD_some] using h
          apply WP.spec_bind (constructor_csr_all_rows_spec offsets neighbors n hsize hnval hrows)
          rintro ⟨unused, status⟩ hstatus
          cases status with
          | Err error =>
            have hbranch : WP.spec
                (core.result.Result.Insts.CoreOpsTry.branch
                  (.Err error : core.result.Result Unit topology.Error))
                (fun cf => cf = .Break (.Err error)) := (WP.spec_ok _).mpr rfl
            apply WP.spec_bind hbranch
            intro cf hcf
            subst cf
            unfold core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            have hconvert : WP.spec (ok (core.convert.FromSame.from error))
                (fun actual => actual = core.convert.FromSame.from error) :=
              (WP.spec_ok _).mpr rfl
            apply WP.spec_bind hconvert
            intro actual _
            apply (WP.spec_ok _).mpr
            trivial
          | Ok value =>
            cases value
            have hentries : constructorAllRows offsets neighbors (offsets.val.length - 1) :=
              by simpa only [hnval] using hstatus.2.mp rfl
            have hbranch : WP.spec
                (core.result.Result.Insts.CoreOpsTry.branch
                  (.Ok () : core.result.Result Unit topology.Error))
                (fun cf => cf = .Continue ()) := (WP.spec_ok _).mpr rfl
            apply WP.spec_bind hbranch
            intro cf hcf
            subst cf
            apply WP.spec_bind (constructor_check_storage_spec n 8#usize)
            intro storage hs
            by_cases hnodeFits : constructorStorageFits n 8#usize
            · have hsok : storage = .Ok () := by simpa only [hnodeFits, ite_true] using hs
              simp only [hsok, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
              apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneBool false n rfl)
              intro seen hseen
              apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize n rfl)
              intro stack hstack
              simp only [alloc.vec.Vec.index_mut_slice_index]
              apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec seen 0#usize (by
                change 0 < seen.val.length
                rw [hseen.1, List.length_replicate]
                omega))
              rintro ⟨old, back⟩ ⟨_, rfl⟩
              apply WP.spec_bind (constructor_csr_connectivity_accepts offsets neighbors n
                unused seen stack hnval (by omega) hseen.1 hstack.1 hrows hentries)
              intro reached hr
              by_cases hreached : reached = n
              · simp only [hreached, not_true_eq_false, ite_false]
                have hconnected : ∀ v, v < offsets.val.length - 1 →
                    Relation.ReflTransGen (constructorCsrAdjacent offsets neighbors) 0 v :=
                  by simpa only [hnval] using hr.2.mp hreached
                apply WP.spec_bind (Usize.div_spec
                  (x := alloc.vec.Vec.len neighbors) (y := 2#usize) (by simp))
                intro edgeCount hec
                have hecval : edgeCount.val = neighbors.val.length / 2 := by simpa using hec
                apply WP.spec_bind (constructor_check_storage_spec edgeCount 16#usize)
                intro edgeStorage hes
                by_cases hedgeFits : constructorStorageFits edgeCount 16#usize
                · have hesok : edgeStorage = .Ok () := by
                    simpa only [hedgeFits, ite_true] using hes
                  simp only [hesok, bind_ok,
                    topology.Edge.new, le_refl, ite_true]
                  apply WP.spec_bind (Usize.div_spec
                    (x := alloc.vec.Vec.len neighbors) (y := 2#usize) (by simp))
                  intro edgeCount' hec'
                  have hecval' : edgeCount'.val = neighbors.val.length / 2 := by simpa using hec'
                  apply WP.spec_bind (alloc.vec.from_elem_spec topology.Edge.Insts.CoreCloneClone
                    ({ u := 0#usize, v := 0#usize } : topology.Edge) edgeCount' rfl)
                  intro edges he
                  have hcapacity : edges.val.length =
                      (constructorCanonicalPairs offsets neighbors n.val).length := by
                    rw [he.1, List.length_replicate, hecval', hnval,
                      constructor_csr_canonical_count offsets neighbors hfirst hlast hrows hentries]
                  apply WP.spec_bind (constructor_canonical_all_rows_spec offsets neighbors n
                    edges hnval hrows hcapacity)
                  intro canonical hcanonical
                  apply (WP.spec_ok _).mpr
                  refine ⟨?_, rfl, rfl,
                    ⟨hsize, hfirst, hlast, hrows, hentries, hconnected⟩, ?_⟩
                  · apply constructor_carrier_valid_of_rows _ hsize hfirst hlast hrows
                      hentries hconnected
                    simpa only [edgePairs, hnval] using hcanonical
                  · simpa only [constructorCsrStorageFits, constructorStorageFits,
                      hnval, hecval, UScalar.ofNatCore_val_eq, and_assoc] using
                      And.intro hnodeFits hedgeFits
                · have heserr : edgeStorage = .Err .Overflow := by
                    simpa only [hedgeFits, ite_false] using hes
                  simp only [heserr, bind_ok,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                  have hconvert : WP.spec (ok (core.convert.FromSame.from topology.Error.Overflow))
                      (fun actual => actual = core.convert.FromSame.from topology.Error.Overflow) :=
                    (WP.spec_ok _).mpr rfl
                  apply WP.spec_bind hconvert
                  intro actual _
                  apply (WP.spec_ok _).mpr
                  trivial
              · simp only [hreached, not_false_eq_true, ite_true, WP.spec_ok]
            · have hserr : storage = .Err .Overflow := by
                simpa only [hnodeFits, ite_false] using hs
              simp only [hserr, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              have hconvert : WP.spec (ok (core.convert.FromSame.from topology.Error.Overflow))
                  (fun actual => actual = core.convert.FromSame.from topology.Error.Overflow) :=
                (WP.spec_ok _).mpr rfl
              apply WP.spec_bind hconvert
              intro actual _
              apply (WP.spec_ok _).mpr
              trivial
      · simp only [hlastEq, not_false_eq_true, ite_true, WP.spec_ok]
    · simp only [bne_iff_ne, ne_eq, hzero, not_false_eq_true, ite_true, WP.spec_ok]

end Labyrinth
