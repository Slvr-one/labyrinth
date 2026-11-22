module
public import LabyrinthCore.ConstructorCarrierEdges
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- What an accepted edge-list carrier says about its input, with no connectivity premise:
every input edge is in range and non-self, the carrier has `n` cells, and its adjacency is exactly
the undirected adjacency of the input edges. -/
def ConstructorEdgeRows (n : Usize) (edges : Slice topology.Edge) (c : topology.Carrier) : Prop :=
  CarrierValid c ∧ cellCount c = n.val ∧
  (∀ edge ∈ edges.val, edge.u.val < n.val ∧ edge.v.val < n.val ∧ edge.u ≠ edge.v) ∧
  ∀ u v, carrierEdge c u v ↔
    ∃ edge ∈ edges.val, (u = edge.u.val ∧ v = edge.v.val) ∨ (u = edge.v.val ∧ v = edge.u.val)

private theorem constructor_edges_rows_error_return (n : Usize) (edges : Slice topology.Edge)
    (error : topology.Error) :
    WP.spec (do
      let actual ← ok (core.convert.FromSame.from error)
      ok (.Err actual : core.result.Result topology.Carrier topology.Error))
      (fun result => match result with
        | .Ok carrier => ConstructorEdgeRows n edges carrier
        | .Err _ => True) := by
  have hconvert : WP.spec (ok (core.convert.FromSame.from error))
      (fun actual => actual = core.convert.FromSame.from error) := (WP.spec_ok _).mpr rfl
  apply WP.spec_bind hconvert
  intro actual _
  apply (WP.spec_ok _).mpr
  trivial

/-- Row soundness on representable allocations. -/
theorem constructor_carrier_from_edges_rows_aux (n : Usize) (edges : Slice topology.Edge)
    (hwidth : constructorEdgesStorageFits n edges) :
    WP.spec (topology.Carrier.from_edges n edges) (fun result =>
      match result with
      | .Ok carrier => ConstructorEdgeRows n edges carrier
      | .Err _ => True) := by
  obtain ⟨hadd, htwice, hcountMax, hcountStorage, hneighborMax, hneighborStorage,
    hedgeStorage⟩ := hwidth
  unfold topology.Carrier.from_edges
  by_cases hn : n = 0#usize
  · simp only [hn, ite_true, WP.spec_ok]
  · simp only [hn, ite_false]
    obtain ⟨count, hchecked, hcount⟩ := constructor_checked_add_some n 1#usize (by
      simpa only [UScalar.ofNatCore_val_eq] using hadd)
    obtain ⟨twice, hmul, htwiceValue⟩ := constructor_checked_mul_some (Slice.len edges)
      2#usize (by simpa using htwice)
    have hcountValue : count.val = n.val + 1 := by
      simpa only [UScalar.ofNatCore_val_eq] using hcount
    have htwiceNat : twice.val = edges.val.length * 2 := by
      simpa using htwiceValue
    have hcountFits : constructorStorageFits count 8#usize := by
      simpa only [constructorStorageFits, hcountValue, UScalar.ofNatCore_val_eq] using
        And.intro hcountMax hcountStorage
    have hneighborFits : constructorStorageFits twice 8#usize := by
      simpa only [constructorStorageFits, htwiceNat, UScalar.ofNatCore_val_eq] using
        And.intro hneighborMax hneighborStorage
    simp only [hchecked, hmul, lift, bind_ok, core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch, constructor_check_storage_eq,
      hcountFits, hneighborFits, hedgeStorage, ite_true]
    apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize count rfl)
    intro counts hcountsInit
    have hcountsLength : counts.val.length = n.val + 1 := by
      rw [hcountsInit.1, List.length_replicate, hcountValue]
    apply WP.spec_bind (constructor_degrees_total_spec n edges counts
      hcountsLength.symm (by rw [hcountsInit.1, List.length_replicate]))
    rintro ⟨degrees, status⟩ hdegrees
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
      exact constructor_edges_rows_error_return n edges _
    | Ok value =>
      cases value
      obtain ⟨hdegreesLength, hedges, hdegreesContents⟩ := hdegrees rfl
      have hdegreeLen : degrees.val.length = n.val + 1 := hdegreesLength.trans hcountsLength
      have hsum : constructorPrefixSum degrees.val degrees.val.length = 2 * edges.val.length :=
        constructor_degrees_prefix_sum n.val edges.val degrees.slice hdegreeLen hedges
          (by
            intro j hj
            exact hdegreesContents j (by change j < degrees.val.length at hj; omega))
      have hbranch : WP.spec
          (core.result.Result.Insts.CoreOpsTry.branch
            (.Ok () : core.result.Result Unit topology.Error))
          (fun cf => cf = .Continue ()) := (WP.spec_ok _).mpr rfl
      apply WP.spec_bind hbranch
      intro cf hcf
      subst cf
      apply WP.spec_bind (constructor_prefix_offsets_spec degrees.slice (by
        change 0 < degrees.val.length
        omega) (by
        change constructorPrefixSum degrees.val degrees.val.length ≤ Usize.max
        rw [hsum]
        omega))
      rintro ⟨prefixStatus, summed⟩ ⟨hprefixStatus, hsummedLength, hsummed⟩
      change prefixStatus = .Ok () at hprefixStatus
      rw [hprefixStatus]
      have hbranchPrefix : WP.spec
          (core.result.Result.Insts.CoreOpsTry.branch
            (.Ok () : core.result.Result Unit topology.Error))
          (fun cf => cf = .Continue ()) := (WP.spec_ok _).mpr rfl
      apply WP.spec_bind hbranchPrefix
      intro cf hcf
      subst cf
      apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize n rfl)
      intro cursor hcursor
      let offsets : alloc.vec.Vec Usize := ⟨summed⟩
      have hoffsetsLength : offsets.val.length = n.val + 1 := hsummedLength.trans hdegreeLen
      have hcursorLength : cursor.val.length = n.val := by
        rw [hcursor.1, List.length_replicate]
      apply WP.spec_bind (constructor_cursors_spec n offsets cursor (by
        rw [hoffsetsLength]
        omega) hcursorLength)
      intro initialized hinitialized
      have hinitializedLength : initialized.val.length = n.val := by
        rw [hinitialized, List.length_take, hoffsetsLength, Nat.min_eq_left (by omega)]
      apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize twice rfl)
      intro neighbors hneighbors
      let starts : Nat → Nat := fun cell => (offsets.val[cell]?.getD 0#usize).val
      have hnumericCounts : ∀ j, j < degrees.val.length →
          (degrees.val[j]?.getD 0#usize).val =
            constructorDegreeSlot edges.val j edges.val.length := by
        intro j hj
        obtain ⟨value, hv, he⟩ := hdegreesContents j (by omega)
        simpa only [hv, Option.getD_some] using he
      have hnumericOffsets : ∀ j, j ≤ n.val →
          (offsets.val[j]?.getD 0#usize).val = constructorPrefixSum degrees.val (j + 1) := by
        intro j hj
        obtain ⟨value, hv, he⟩ := hsummed j (by change j < degrees.val.length; omega)
        change summed.val[j]? = some value at hv
        change (summed.val[j]?.getD 0#usize).val = _
        change value.val = constructorPrefixSum degrees.val (j + 1) at he
        simpa only [hv, Option.getD_some] using he
      obtain ⟨_, hlast, hrows, hmono⟩ := constructor_degree_offsets_layout n.val edges.val
        degrees.val offsets.val hdegreeLen hedges hnumericCounts hnumericOffsets
      have hcapacity : ∀ cell, cell < n.val →
          starts cell + constructorDegreeSlot edges.val (cell + 1) edges.val.length ≤
            neighbors.val.length := by
        intro cell hcn
        have hrow := hrows cell hcn
        have hbound := hmono (cell + 1) n.val (by omega) le_rfl
        rw [hneighbors.1, List.length_replicate, htwiceNat]
        dsimp only [starts]
        omega
      have hseparated : ∀ u v, u < n.val → v < n.val → u ≠ v →
          starts u + constructorDegreeSlot edges.val (u + 1) edges.val.length ≤ starts v ∨
          starts v + constructorDegreeSlot edges.val (v + 1) edges.val.length ≤ starts u := by
        intro u v hu hv hne
        by_cases huv : u < v
        · left
          have hrow := hrows u hu
          have hbound := hmono (u + 1) v (by omega) (by omega)
          dsimp only [starts]
          omega
        · right
          have hrow := hrows v hv
          have hbound := hmono (v + 1) u (by omega) (by omega)
          dsimp only [starts]
          omega
      apply WP.spec_bind (constructor_fill_edges_spec edges initialized neighbors starts
        (by simpa only [hinitializedLength] using hedges) (by
          intro cell hc
          have hcn : cell < n.val := by omega
          have hco : cell < offsets.val.length := by omega
          let value := offsets.val[cell]'hco
          refine ⟨value, ?_, ?_⟩
          · rw [hinitialized]
            simp only [List.getElem?_take, hcn, ite_true]
            exact List.getElem?_eq_getElem hco
          · dsimp only [starts, value]
            rw [List.getElem?_eq_getElem hco]
            rfl) (fun cell hc => hcapacity cell (by omega)))
      intro filled hfilled
      apply WP.spec_mono (constructor_carrier_from_csr_spec offsets filled)
      intro result hresult
      cases result with
      | Err error => trivial
      | Ok carrier =>
        obtain ⟨hvalid, hoff, hneigh, _, _⟩ := hresult
        refine ⟨hvalid, ?_, hedges, ?_⟩
        · unfold cellCount
          rw [hoff]
          omega
        · intro u v
          rw [constructor_carrier_edge_iff, hoff, hneigh]
          exact constructor_filled_csr_adjacent edges.val starts neighbors.val n.val offsets filled
            hedges hcapacity hseparated hoffsetsLength (fun _ _ => rfl)
            (fun cell hc => (hrows cell hc).symm) hfilled u v

/-- **Row soundness of `Carrier::from_edges`, with no connectivity premise.** On every `Ok`
result the carrier is valid, has `n` cells, every input edge is in range and not a loop, and the
carrier's adjacency is exactly the undirected adjacency of the input edges: each row entry comes
from an input edge and each input edge appears in both rows. -/
theorem constructor_carrier_from_edges_rows_spec (n : Usize) (edges : Slice topology.Edge) :
    WP.spec (topology.Carrier.from_edges n edges) (fun result =>
      match result with
      | .Ok carrier => ConstructorEdgeRows n edges carrier
      | .Err _ => True) := by
  by_cases hwidth : constructorEdgesStorageFits n edges
  · exact constructor_carrier_from_edges_rows_aux n edges hwidth
  · unfold topology.Carrier.from_edges
    by_cases hn : n = 0#usize
    · simp only [hn, ite_true, WP.spec_ok]
    · simp only [hn, ite_false]
      cases hadd : Usize.checked_add n 1#usize with
      | none =>
        simp only [lift, bind_ok, core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        exact constructor_edges_rows_error_return n edges _
      | some count =>
        have ha := Usize.checked_add_bv_spec n 1#usize
        simp only [hadd] at ha
        have hcount : count.val = n.val + 1 := by
          simpa only [UScalar.ofNatCore_val_eq] using ha.2.1
        cases hmul : Usize.checked_mul (Slice.len edges) 2#usize with
        | none =>
          simp only [lift, bind_ok, core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          exact constructor_edges_rows_error_return n edges _
        | some twice =>
          have hm := Usize.checked_mul_bv_spec (Slice.len edges) 2#usize
          simp only [hmul] at hm
          have htwice : twice.val = edges.val.length * 2 := by
            simpa using hm.2.1
          simp only [lift, bind_ok, core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch, constructor_check_storage_eq]
          by_cases hc : constructorStorageFits count 8#usize
          · simp only [hc, ite_true, bind_ok]
            by_cases ht : constructorStorageFits twice 8#usize
            · simp only [ht, ite_true, bind_ok]
              by_cases he : constructorStorageFits (Slice.len edges) 16#usize
              · have hc' := hc
                have ht' := ht
                simp only [constructorStorageFits, hcount, UScalar.ofNatCore_val_eq] at hc'
                simp only [constructorStorageFits, htwice, UScalar.ofNatCore_val_eq] at ht'
                exact False.elim (hwidth ⟨by omega, by omega, hc'.1, hc'.2, ht'.1, ht'.2, he⟩)
              · simp only [he, ite_false, bind_ok,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                exact constructor_edges_rows_error_return n edges _
            · simp only [ht, ite_false, bind_ok,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              exact constructor_edges_rows_error_return n edges _
          · simp only [hc, ite_false, bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            exact constructor_edges_rows_error_return n edges _


end Labyrinth
