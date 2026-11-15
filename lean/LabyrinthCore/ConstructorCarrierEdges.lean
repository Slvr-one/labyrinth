module
public import LabyrinthCore.ConstructorCarrier
public import LabyrinthCore.ConstructorCursor
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

private theorem constructor_edges_error_return (error : topology.Error) :
    WP.spec (do
      let actual ← ok (core.convert.FromSame.from error)
      ok (.Err actual : core.result.Result topology.Carrier topology.Error))
      (fun result => match result with
        | .Ok carrier => CarrierValid carrier
        | .Err _ => True) := by
  have hconvert : WP.spec (ok (core.convert.FromSame.from error))
      (fun actual => actual = core.convert.FromSame.from error) := (WP.spec_ok _).mpr rfl
  apply WP.spec_bind hconvert
  intro actual _
  apply (WP.spec_ok _).mpr
  trivial

/-- Widths of the allocations explicitly checked by the edge-list constructor. -/
def constructorEdgesStorageFits (n : Usize) (edges : Slice topology.Edge) : Prop :=
  n.val + 1 ≤ Usize.max ∧ edges.val.length * 2 ≤ Usize.max ∧
  (n.val + 1) * 8 ≤ Usize.max ∧
  (n.val + 1) * 8 ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val ∧
  (edges.val.length * 2) * 8 ≤ Usize.max ∧
  (edges.val.length * 2) * 8 ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val ∧
  constructorStorageFits (Slice.len edges) 16#usize

/-- The actual edge-list constructor is total on representable allocations, including
malformed endpoint lists. Every accepted result satisfies the full carrier invariant. -/
theorem constructor_carrier_from_edges_spec (n : Usize) (edges : Slice topology.Edge)
    (hwidth : constructorEdgesStorageFits n edges) :
    WP.spec (topology.Carrier.from_edges n edges) (fun result =>
      match result with
      | .Ok carrier => CarrierValid carrier
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
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, WP.spec_ok]
    | Ok value =>
      cases value
      obtain ⟨hdegreesLength, hedges, hdegreesContents⟩ := hdegrees rfl
      have hdegreeLen : degrees.val.length = n.val + 1 := hdegreesLength.trans hcountsLength
      have hsum : constructorPrefixSum degrees.val degrees.val.length = 2 * edges.val.length :=
        constructor_degrees_prefix_sum n.val edges.val degrees.slice hdegreeLen hedges
          hdegreesContents
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        alloc.vec.Vec.deref_mut, lift]
      apply WP.spec_bind (constructor_prefix_offsets_spec degrees.slice (by
        change 0 < degrees.val.length
        omega) (by
        change constructorPrefixSum degrees.val degrees.val.length ≤ Usize.max
        rw [hsum]
        omega))
      rintro ⟨prefixStatus, summed⟩ ⟨hprefixStatus, hsummedLength, hsummed⟩
      simp only [hprefixStatus, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
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
        simpa only [hv, Option.getD_some] using he
      obtain ⟨_, hlast, hrows, hmono⟩ := constructor_degree_offsets_layout n.val edges.val
        degrees.val offsets.val hdegreeLen hedges hnumericCounts hnumericOffsets
      have hcapacity : ∀ cell, cell < initialized.val.length →
          starts cell + constructorDegreeSlot edges.val (cell + 1) edges.val.length ≤
            neighbors.val.length := by
        intro cell hc
        have hcn : cell < n.val := by omega
        have hrow := hrows cell hcn
        have hbound := hmono (cell + 1) n.val (by omega) le_rfl
        rw [hneighbors.1, List.length_replicate, htwiceNat]
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
            rfl) hcapacity)
      intro filled _
      apply WP.spec_mono (constructor_carrier_from_csr_spec offsets filled)
      intro result hresult
      cases result with
      | Err error => trivial
      | Ok carrier => exact hresult.1

/-- Totality and soundness include failed size/overflow/storage checks, not just
the allocation-representable branch. -/
theorem constructor_carrier_from_edges_total_spec (n : Usize) (edges : Slice topology.Edge) :
    WP.spec (topology.Carrier.from_edges n edges) (fun result =>
      match result with
      | .Ok carrier => CarrierValid carrier
      | .Err _ => True) := by
  by_cases hwidth : constructorEdgesStorageFits n edges
  · exact constructor_carrier_from_edges_spec n edges hwidth
  · unfold topology.Carrier.from_edges
    by_cases hn : n = 0#usize
    · simp only [hn, ite_true, WP.spec_ok]
    · simp only [hn, ite_false]
      cases hadd : Usize.checked_add n 1#usize with
      | none =>
        simp only [lift, bind_ok, core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        exact constructor_edges_error_return _
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
          exact constructor_edges_error_return _
        | some twice =>
          have hm := Usize.checked_mul_bv_spec (Slice.len edges) 2#usize
          simp only [hmul] at hm
          have htwice : twice.val = edges.val.length * 2 := by
            simpa using hm.2.1
          simp only [lift, bind_ok, core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch, constructor_check_storage_eq]
          by_cases hc : constructorStorageFits count 8#usize
          · simp only [hc, ite_true, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            by_cases ht : constructorStorageFits twice 8#usize
            · simp only [ht, ite_true, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
              by_cases he : constructorStorageFits (Slice.len edges) 16#usize
              · have hc' := hc
                have ht' := ht
                simp only [constructorStorageFits, hcount, UScalar.ofNatCore_val_eq] at hc'
                simp only [constructorStorageFits, htwice, UScalar.ofNatCore_val_eq] at ht'
                exact False.elim (hwidth ⟨by omega, by omega, hc'.1, hc'.2, ht'.1, ht'.2, he⟩)
              · simp only [he, ite_false, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                exact constructor_edges_error_return _
            · simp only [ht, ite_false, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              exact constructor_edges_error_return _
          · simp only [hc, ite_false, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            exact constructor_edges_error_return _

/-- Input-only absence of parallel undirected edges, independent of CSR storage. -/
def constructorEdgesSimple (edges : List topology.Edge) : Prop :=
  ∀ (i j : Nat) (edge other : topology.Edge) (cell : Nat) (value : Usize),
    edges[i]? = some edge → edges[j]? = some other →
    ((cell = edge.u.val ∧ value = edge.v) ∨ (cell = edge.v.val ∧ value = edge.u)) →
    ((cell = other.u.val ∧ value = other.v) ∨ (cell = other.v.val ∧ value = other.u)) →
    i = j

theorem constructor_filled_rank_unique (edges : List topology.Edge) (starts : Nat → Nat)
    (initial : List Usize) (n cell left right : Nat) (value : Usize)
    (hedges : ∀ edge ∈ edges, edge.u.val < n ∧ edge.v.val < n ∧ edge.u ≠ edge.v)
    (hcapacity : ∀ cell, cell < n →
      starts cell + constructorDegreeSlot edges (cell + 1) edges.length ≤ initial.length)
    (hseparated : ∀ u v, u < n → v < n → u ≠ v →
      starts u + constructorDegreeSlot edges (u + 1) edges.length ≤ starts v ∨
      starts v + constructorDegreeSlot edges (v + 1) edges.length ≤ starts u)
    (hsimple : constructorEdgesSimple edges)
    (hl : left < constructorDegreeSlot edges (cell + 1) edges.length)
    (hr : right < constructorDegreeSlot edges (cell + 1) edges.length)
    (hleft : (constructorFilledNeighbors edges starts initial edges.length)[starts cell + left]? =
      some value)
    (hright : (constructorFilledNeighbors edges starts initial edges.length)[starts cell + right]? =
      some value) :
    left = right := by
  obtain ⟨i, edge, hi, hedge, hcell, hdegree⟩ :=
    constructor_degree_rank_witness edges cell edges.length left hl
  obtain ⟨j, other, hj, hother, hcell', hdegree'⟩ :=
    constructor_degree_rank_witness edges cell edges.length right hr
  have hfilled := constructor_filled_incidence edges starts initial n edges.length
    hedges hcapacity hseparated le_rfl
  have hincidence (index : Nat) (e : topology.Edge)
      (hindex : index < edges.length) (he : edges[index]? = some e)
      (hc : cell = e.u.val ∨ cell = e.v.val) (rank : Nat)
      (hd : constructorDegreeSlot edges (cell + 1) index = rank)
      (hlookup : (constructorFilledNeighbors edges starts initial edges.length)[starts cell + rank]? =
        some value) :
      (cell = e.u.val ∧ value = e.v) ∨ (cell = e.v.val ∧ value = e.u) := by
    obtain ⟨hu, hv⟩ := hfilled index e hindex he
    rcases hc with hc | hc
    · rw [← hc, hd] at hu
      exact Or.inl ⟨hc, Option.some.inj (hlookup.symm.trans hu)⟩
    · rw [← hc, hd] at hv
      exact Or.inr ⟨hc, Option.some.inj (hlookup.symm.trans hv)⟩
  have hij := hsimple i j edge other cell value hedge hother
    (hincidence i edge hi hedge hcell left hdegree hleft)
    (hincidence j other hj hother hcell' right hdegree' hright)
  rw [hij] at hdegree
  exact hdegree.symm.trans hdegree'

/-- Input endpoint bounds and simplicity transfer through every filled slot to all
of the actual CSR validator's entry obligations, including reciprocity. -/
theorem constructor_filled_csr_all_rows (edges : List topology.Edge) (starts : Nat → Nat)
    (initial : List Usize) (n : Nat) (offsets neighbors : alloc.vec.Vec Usize)
    (hedges : ∀ edge ∈ edges, edge.u.val < n ∧ edge.v.val < n ∧ edge.u ≠ edge.v)
    (hcapacity : ∀ cell, cell < n →
      starts cell + constructorDegreeSlot edges (cell + 1) edges.length ≤ initial.length)
    (hseparated : ∀ u v, u < n → v < n → u ≠ v →
      starts u + constructorDegreeSlot edges (u + 1) edges.length ≤ starts v ∨
      starts v + constructorDegreeSlot edges (v + 1) edges.length ≤ starts u)
    (hsimple : constructorEdgesSimple edges)
    (hlen : offsets.val.length = n + 1)
    (hstarts : ∀ cell, cell < n → (offsets.val[cell]?.getD 0#usize).val = starts cell)
    (hstops : ∀ cell, cell < n → (offsets.val[cell + 1]?.getD 0#usize).val =
      starts cell + constructorDegreeSlot edges (cell + 1) edges.length)
    (hfilled : neighbors.val = constructorFilledNeighbors edges starts initial edges.length) :
    constructorAllRows offsets neighbors n := by
  have hadj := constructor_filled_csr_adjacent edges starts initial n offsets neighbors
    hedges hcapacity hseparated hlen hstarts hstops hfilled
  have hsymm (u v : Nat) (h : constructorCsrAdjacent offsets neighbors u v) :
      constructorCsrAdjacent offsets neighbors v u := by
    obtain ⟨edge, he, hc⟩ := (hadj u v).mp h
    apply (hadj v u).mpr
    refine ⟨edge, he, ?_⟩
    rcases hc with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Or.inr ⟨hv, hu⟩
    · exact Or.inl ⟨hv, hu⟩
  intro cell hc index hlo hhi
  rw [hstarts cell.val hc] at hlo
  rw [hstops cell.val hc] at hhi
  have hrank : index - starts cell.val <
      constructorDegreeSlot edges (cell.val + 1) edges.length := by omega
  obtain ⟨i, edge, hi, hedge, hcell, hdegree⟩ :=
    constructor_degree_rank_witness edges cell.val edges.length (index - starts cell.val) hrank
  obtain ⟨hu, hv⟩ := constructor_filled_incidence edges starts initial n edges.length
    hedges hcapacity hseparated le_rfl i edge hi hedge
  have hindex : starts cell.val + (index - starts cell.val) = index := by omega
  have hvalue : ∃ value : Usize, neighbors.val[index]? = some value := by
    rcases hcell with hcell | hcell
    · rw [← hcell, hdegree, hindex] at hu
      exact ⟨edge.v, by simpa only [hfilled] using hu⟩
    · rw [← hcell, hdegree, hindex] at hv
      exact ⟨edge.u, by simpa only [hfilled] using hv⟩
  obtain ⟨value, hlookup⟩ := hvalue
  have hforward : constructorCsrAdjacent offsets neighbors cell.val value.val := by
    refine ⟨by omega, index, ?_, ?_, value, hlookup, rfl⟩
    · rw [hstarts cell.val hc]
      exact hlo
    · rw [hstops cell.val hc]
      exact hhi
  obtain ⟨input, hinput, hincidence⟩ := (hadj cell.val value.val).mp hforward
  obtain ⟨hinputU, hinputV, hinputNe⟩ := hedges input hinput
  have hbounded : value.val < offsets.val.length - 1 := by
    rcases hincidence with ⟨_, hv⟩ | ⟨_, hv⟩ <;> omega
  have hne : value ≠ cell := by
    intro he
    have hev := congrArg UScalar.val he
    have hinputNat : input.u.val ≠ input.v.val :=
      fun h => hinputNe ((UScalar.eq_equiv _ _).mpr h)
    rcases hincidence with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> omega
  refine ⟨value, hlookup, hbounded, hne, ?_, ?_⟩
  · intro earlier helo heilt hsame
    rw [hstarts cell.val hc] at helo
    have hbefore : earlier - starts cell.val <
        constructorDegreeSlot edges (cell.val + 1) edges.length := by omega
    have hearlier : starts cell.val + (earlier - starts cell.val) = earlier := by omega
    have hsameRank := constructor_filled_rank_unique edges starts initial n cell.val
      (earlier - starts cell.val) (index - starts cell.val) value
      hedges hcapacity hseparated hsimple hbefore hrank
      (by simpa only [hearlier, hfilled] using hsame)
      (by simpa only [hindex, hfilled] using hlookup)
    omega
  · obtain ⟨_, slot, hslotLo, hslotHi, actual, hactual, hactualVal⟩ := hsymm _ _ hforward
    have heq : actual = cell := (UScalar.eq_equiv _ _).mpr hactualVal
    exact ⟨slot, hslotLo, hslotHi, by simpa only [heq] using hactual⟩

/-- A connected simple input edge list survives the whole fill-to-CSR validation
boundary. Its reachability witnesses refer only to the original input edges. -/
theorem constructor_carrier_from_filled_csr_accepts
    (edges : List topology.Edge) (starts : Nat → Nat) (initial : List Usize) (n : Nat)
    (offsets neighbors : alloc.vec.Vec Usize)
    (hn : 0 < n)
    (hedges : ∀ edge ∈ edges, edge.u.val < n ∧ edge.v.val < n ∧ edge.u ≠ edge.v)
    (hcapacity : ∀ cell, cell < n →
      starts cell + constructorDegreeSlot edges (cell + 1) edges.length ≤ initial.length)
    (hseparated : ∀ u v, u < n → v < n → u ≠ v →
      starts u + constructorDegreeSlot edges (u + 1) edges.length ≤ starts v ∨
      starts v + constructorDegreeSlot edges (v + 1) edges.length ≤ starts u)
    (hsimple : constructorEdgesSimple edges)
    (hlen : offsets.val.length = n + 1)
    (hfirst : offsets.val[0]? = some 0#usize)
    (hlast : offsets.val[n]? = some (alloc.vec.Vec.len neighbors))
    (hrows : constructorRawRows (alloc.vec.Vec.deref offsets) (alloc.vec.Vec.deref neighbors))
    (hstarts : ∀ cell, cell < n → (offsets.val[cell]?.getD 0#usize).val = starts cell)
    (hstops : ∀ cell, cell < n → (offsets.val[cell + 1]?.getD 0#usize).val =
      starts cell + constructorDegreeSlot edges (cell + 1) edges.length)
    (hfilled : neighbors.val = constructorFilledNeighbors edges starts initial edges.length)
    (hconnected : ∀ v, v < n →
      Relation.ReflTransGen (fun u v =>
        ∃ edge ∈ edges, (u = edge.u.val ∧ v = edge.v.val) ∨
          (u = edge.v.val ∧ v = edge.u.val)) 0 v)
    (hwidth : constructorCsrStorageFits offsets neighbors) :
    WP.spec (topology.Carrier.from_csr offsets neighbors) (fun result =>
      ∃ carrier, result = .Ok carrier ∧ CarrierValid carrier ∧
        carrier.offsets = offsets ∧ carrier.neighbors = neighbors) := by
  apply constructor_carrier_from_csr_accepts offsets neighbors _ hwidth
  refine ⟨by omega, hfirst, ?_, hrows, ?_, ?_⟩
  · have he : offsets.val.length - 1 = n := by omega
    simpa only [he] using hlast
  · have hall := constructor_filled_csr_all_rows edges starts initial n offsets neighbors
      hedges hcapacity hseparated hsimple hlen hstarts hstops hfilled
    have he : offsets.val.length - 1 = n := by omega
    simpa only [he] using hall
  · intro v hv
    have hvn : v < n := by omega
    have hp := hconnected v hvn
    clear hv hvn
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hedge ih =>
      exact ih.tail ((constructor_filled_csr_adjacent edges starts initial n offsets neighbors
        hedges hcapacity hseparated hlen hstarts hstops hfilled _ _).mpr hedge)

/-- Every nonempty connected simple bounded input edge list is accepted by the
actual edge-list constructor on representable allocations. -/
theorem constructor_carrier_from_edges_accepts (n : Usize) (edges : Slice topology.Edge)
    (hn : n ≠ 0#usize)
    (hedges : ∀ edge ∈ edges.val,
      edge.u.val < n.val ∧ edge.v.val < n.val ∧ edge.u ≠ edge.v)
    (hsimple : constructorEdgesSimple edges.val)
    (hconnected : ∀ v, v < n.val →
      Relation.ReflTransGen (fun u v =>
        ∃ edge ∈ edges.val, (u = edge.u.val ∧ v = edge.v.val) ∨
          (u = edge.v.val ∧ v = edge.u.val)) 0 v)
    (hwidth : constructorEdgesStorageFits n edges) :
    WP.spec (topology.Carrier.from_edges n edges) (fun result =>
      ∃ carrier, result = .Ok carrier ∧ CarrierValid carrier) := by
  obtain ⟨hadd, htwice, hcountMax, hcountStorage, hneighborMax, hneighborStorage,
    hedgeStorage⟩ := hwidth
  obtain ⟨count, hchecked, hcount⟩ := constructor_checked_add_some n 1#usize (by
    simpa only [UScalar.ofNatCore_val_eq] using hadd)
  obtain ⟨twice, hmul, htwiceValue⟩ := constructor_checked_mul_some (Slice.len edges)
    2#usize (by simpa using htwice)
  have hcountValue : count.val = n.val + 1 := by
    simpa only [UScalar.ofNatCore_val_eq] using hcount
  have htwiceNat : twice.val = edges.val.length * 2 := by
    simpa using htwiceValue
  have hnpos : 0 < n.val := by
    have hne : n.val ≠ 0 := by
      intro he
      exact hn ((UScalar.eq_equiv _ _).mpr (by simpa using he))
    omega
  have hcountFits : constructorStorageFits count 8#usize := by
    simpa only [constructorStorageFits, hcountValue, UScalar.ofNatCore_val_eq] using
      And.intro hcountMax hcountStorage
  have hneighborFits : constructorStorageFits twice 8#usize := by
    simpa only [constructorStorageFits, htwiceNat, UScalar.ofNatCore_val_eq] using
      And.intro hneighborMax hneighborStorage
  unfold topology.Carrier.from_edges
  simp only [hn, ite_false, hchecked, hmul, lift, bind_ok, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch, constructor_check_storage_eq,
    hcountFits, hneighborFits, hedgeStorage, ite_true]
  apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize count rfl)
  intro counts hcountsInit
  have hcountsLength : counts.val.length = n.val + 1 := by
    rw [hcountsInit.1, List.length_replicate, hcountValue]
  apply WP.spec_bind (constructor_degrees_spec n edges counts hcountsLength.symm
    (by rw [hcountsInit.1, List.length_replicate]) hedges)
  rintro ⟨degrees, status⟩ ⟨hstatus, hdegreesLength, hdegreesContents⟩
  have hdegreeLen : degrees.val.length = n.val + 1 := hdegreesLength.trans hcountsLength
  have hsum : constructorPrefixSum degrees.val degrees.val.length = 2 * edges.val.length :=
    constructor_degrees_prefix_sum n.val edges.val degrees.slice hdegreeLen hedges
      hdegreesContents
  simp only [hstatus, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
    alloc.vec.Vec.deref_mut, lift]
  apply WP.spec_bind (constructor_prefix_offsets_spec degrees.slice (by
    change 0 < degrees.val.length
    omega) (by
    change constructorPrefixSum degrees.val degrees.val.length ≤ Usize.max
    rw [hsum]
    omega))
  rintro ⟨prefixStatus, summed⟩ ⟨hprefixStatus, hsummedLength, hsummed⟩
  simp only [hprefixStatus, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
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
  have hneighborsLength : neighbors.val.length = edges.val.length * 2 := by
    rw [hneighbors.1, List.length_replicate, htwiceNat]
  let starts : Nat → Nat := fun cell => (offsets.val[cell]?.getD 0#usize).val
  have hnumericCounts : ∀ j, j < degrees.val.length →
      (degrees.val[j]?.getD 0#usize).val = constructorDegreeSlot edges.val j edges.val.length := by
    intro j hj
    obtain ⟨value, hv, he⟩ := hdegreesContents j (by omega)
    simpa only [hv, Option.getD_some] using he
  have hnumericOffsets : ∀ j, j ≤ n.val →
      (offsets.val[j]?.getD 0#usize).val = constructorPrefixSum degrees.val (j + 1) := by
    intro j hj
    obtain ⟨value, hv, he⟩ := hsummed j (by change j < degrees.val.length; omega)
    change summed.val[j]? = some value at hv
    change (summed.val[j]?.getD 0#usize).val = _
    simpa only [hv, Option.getD_some] using he
  obtain ⟨hfirstNat, hlastNat, hrows, hmono⟩ := constructor_degree_offsets_layout n.val edges.val
    degrees.val offsets.val hdegreeLen hedges hnumericCounts hnumericOffsets
  have hcapacity : ∀ cell, cell < n.val →
      starts cell + constructorDegreeSlot edges.val (cell + 1) edges.val.length ≤
        neighbors.val.length := by
    intro cell hc
    have hrow := hrows cell hc
    have hbound := hmono (cell + 1) n.val (by omega) le_rfl
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
        rfl) (by simpa only [hinitializedLength] using hcapacity))
  intro filled hfilled
  have hfilledLength : filled.val.length = edges.val.length * 2 := by
    rw [hfilled, constructor_filled_neighbors_length, hneighborsLength]
  have hfirst : offsets.val[0]? = some 0#usize := by
    have hi : 0 < offsets.val.length := by omega
    have hlook := List.getElem?_eq_getElem (l := offsets.val) hi
    have hval : (offsets.val[0]'hi).val = 0 := by
      simpa only [hlook, Option.getD_some] using hfirstNat
    have heq : offsets.val[0] = 0#usize := (UScalar.eq_equiv _ _).mpr (by simpa using hval)
    simpa only [heq] using hlook
  have hlast : offsets.val[n.val]? = some (alloc.vec.Vec.len filled) := by
    have hi : n.val < offsets.val.length := by omega
    have hlook := List.getElem?_eq_getElem (l := offsets.val) hi
    have hval : (offsets.val[n.val]'hi).val = 2 * edges.val.length := by
      simpa only [hlook, Option.getD_some] using hlastNat
    have heq : offsets.val[n.val] = alloc.vec.Vec.len filled := (UScalar.eq_equiv _ _).mpr (by
      change (offsets.val[n.val]'hi).val = filled.val.length
      omega)
    simpa only [heq] using hlook
  have hraw : constructorRawRows (alloc.vec.Vec.deref offsets)
      (alloc.vec.Vec.deref filled) := by
    intro cell hc
    change cell < offsets.val.length - 1 at hc
    have hcn : cell < n.val := by omega
    have hloBound : cell < offsets.val.length := by omega
    have hhiBound : cell + 1 < offsets.val.length := by omega
    have hlo : (offsets.val[cell]'hloBound).val =
        (offsets.val[cell]?.getD 0#usize).val := by rw [List.getElem?_eq_getElem hloBound]; rfl
    have hhi : (offsets.val[cell + 1]'hhiBound).val =
        (offsets.val[cell + 1]?.getD 0#usize).val := by rw [List.getElem?_eq_getElem hhiBound]; rfl
    refine ⟨offsets.val[cell], offsets.val[cell + 1],
      List.getElem?_eq_getElem hloBound, List.getElem?_eq_getElem hhiBound, ?_, ?_⟩
    · have hm := hmono cell (cell + 1) (by omega) (by omega)
      omega
    · have hm := hmono (cell + 1) n.val (by omega) le_rfl
      change (offsets.val[cell + 1]'hhiBound).val ≤ filled.val.length
      omega
  have hcsrWidth : constructorCsrStorageFits offsets filled := by
    have he := hedgeStorage
    simp [constructorStorageFits] at he
    simp only [constructorCsrStorageFits, hoffsetsLength, Nat.add_sub_cancel,
      hfilledLength, Nat.mul_div_cancel]
    exact ⟨by omega, by omega, he.1, he.2⟩
  apply WP.spec_mono (constructor_carrier_from_filled_csr_accepts edges.val starts
    neighbors.val n.val offsets filled hnpos hedges hcapacity hseparated hsimple
    hoffsetsLength hfirst hlast hraw (fun _ _ => rfl)
    (fun cell hc => (hrows cell hc).symm) hfilled hconnected hcsrWidth)
  rintro result ⟨carrier, hr, hc, _, _⟩
  exact ⟨carrier, hr, hc⟩

end Labyrinth
