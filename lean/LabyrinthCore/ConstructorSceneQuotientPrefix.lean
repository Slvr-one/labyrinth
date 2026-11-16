module
public import LabyrinthCore.ConstructorSceneAcceptance
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

private theorem constructor_scene_prefix_overflow_return
    (post : core.result.Result (alloc.vec.Vec Usize × Usize) topology.Error → Prop) :
    WP.spec (do
      let error ← ok (core.convert.FromSame.from topology.Error.Overflow)
      ok (core.result.Result.Err error))
      (fun output => output = .Err topology.Error.Overflow ∨ post output) := by
  have hconvert : WP.spec
      (ok (core.convert.FromSame.from topology.Error.Overflow))
      (fun actual => actual = topology.Error.Overflow) := (WP.spec_ok _).mpr rfl
  apply WP.spec_bind hconvert
  intro actual hactual
  rw [hactual]
  exact (WP.spec_ok _).mpr (Or.inl rfl)

/-- The actual quotient-degree, checked-prefix and adjacency-storage segment is total for
arbitrary representable input widths. Every rejected branch is exactly `Overflow`; success
records the literal degree counts, prefix sums, final adjacency count and all three storage
guards. No RNG or caller workspace occurs in this pre-DFS segment. -/
theorem constructor_scene_quotient_prefix_total
    (carrier : topology.Carrier) (components : alloc.vec.Vec Usize)
    (componentCount : Usize) (label : Usize → Usize)
    (hc : CarrierValid carrier)
    (hcomponents : components.val.length = cellCount carrier)
    (hlabels : ∀ node : Usize, node.val < components.val.length →
      components.val[node.val]? = some (label node))
    (hbounded : ∀ node : Usize, node.val < components.val.length →
      (label node).val < componentCount.val) :
    WP.spec (do
      let optionCount ← lift (Usize.checked_add componentCount 1#usize)
      let countResult ← core.option.Option.ok_or optionCount topology.Error.Overflow
      let countFlow ← core.result.Result.Insts.CoreOpsTry.branch countResult
      match countFlow with
      | .Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
      | .Continue count =>
        let storageResult ← topology.check_storage count 8#usize
        let storageFlow ← core.result.Result.Insts.CoreOpsTry.branch storageResult
        match storageFlow with
        | .Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
        | .Continue _ =>
          let offsets ← alloc.vec.from_elem core.clone.CloneUsize 0#usize count
          let edges ← topology.Carrier.impl.edges carrier
          let (degreeStatus, counts) ← spanning_tree.Tree.scene_dfs_loop3 0#usize (.Ok ())
            components componentCount offsets edges
          let degreeFlow ← core.result.Result.Insts.CoreOpsTry.branch degreeStatus
          match degreeFlow with
          | .Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
          | .Continue _ =>
            let (countSlice, countBack) ← lift (alloc.vec.Vec.deref_mut counts)
            let (prefixStatus, prefixed) ← topology.prefix_offsets countSlice
            let prefixFlow ← core.result.Result.Insts.CoreOpsTry.branch prefixStatus
            match prefixFlow with
            | .Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
            | .Continue _ =>
              let prefixedCounts := countBack prefixed
              let adjacencyCount ← alloc.vec.Vec.index
                (core.slice.index.SliceIndexUsizeSlice Usize) prefixedCounts componentCount
              let adjacencyStorage8 ← topology.check_storage adjacencyCount 8#usize
              let adjacencyFlow8 ← core.result.Result.Insts.CoreOpsTry.branch adjacencyStorage8
              match adjacencyFlow8 with
              | .Break residual =>
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
              | .Continue _ =>
                let adjacencyStorage16 ← topology.check_storage adjacencyCount 16#usize
                let adjacencyFlow16 ← core.result.Result.Insts.CoreOpsTry.branch adjacencyStorage16
                match adjacencyFlow16 with
                | .Break residual =>
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
                | .Continue _ => ok (.Ok (prefixedCounts, adjacencyCount)))
      (fun output =>
        output = .Err topology.Error.Overflow ∨
        ∃ offsets adjacencyCount,
          output = .Ok (offsets, adjacencyCount) ∧
            ConstructorScenePrefixSuccess carrier componentCount label offsets adjacencyCount) := by
  have hedges : ∀ edge ∈ carrier.edges.val,
      edge.u.val < components.val.length ∧ edge.v.val < components.val.length ∧
      (label edge.u).val < componentCount.val ∧
      (label edge.v).val < componentCount.val := by
    intro edge hedge
    have hpairs : (edge.u.val, edge.v.val) ∈ edgePairs carrier := by
      change (edge.u.val, edge.v.val) ∈
        carrier.edges.val.map (fun source => (source.u.val, source.v.val))
      exact List.mem_map.mpr ⟨edge, hedge, rfl⟩
    have hcarrier := (hc.2.2.2.2.2.2.2 edge.u.val edge.v.val).mp hpairs
    have hv := ((hc.2.2.2.2.1 edge.u.val hcarrier.2.1).2.2 edge.v.val hcarrier.2.2).1
    have huComponents : edge.u.val < components.val.length := by
      rw [hcomponents]
      exact hcarrier.2.1
    have hvComponents : edge.v.val < components.val.length := by
      rw [hcomponents]
      exact hv
    exact ⟨huComponents, hvComponents, hbounded edge.u huComponents,
      hbounded edge.v hvComponents⟩
  cases hcount : Usize.checked_add componentCount 1#usize with
  | none =>
      simp only [lift, bind_ok, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact constructor_scene_prefix_overflow_return _
  | some count =>
      have hcountSpec := Usize.checked_add_bv_spec componentCount 1#usize
      simp only [hcount] at hcountSpec
      have hcountValue : count.val = componentCount.val + 1 := by
        simpa only [UScalar.ofNatCore_val_eq] using hcountSpec.2.1
      simp only [lift, bind_ok, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch]
      apply WP.spec_bind (constructor_check_storage_spec count 8#usize)
      intro countStorage hcountStorage
      by_cases hcountFits : constructorStorageFits count 8#usize
      · have hcountStorageOk : countStorage = .Ok () := by
          simpa only [hcountFits, ite_true] using hcountStorage
        simp only [hcountStorageOk, bind_ok]
        apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize count rfl)
        intro offsets hoffsets
        simp only [topology.Carrier.impl.edges, bind_ok]
        have hoffsetsLength : offsets.val.length = componentCount.val + 1 := by
          rw [hoffsets.1, List.length_replicate, hcountValue]
        have hoffsetsZero : ∀ j, j < offsets.val.length →
            offsets.val[j]? = some 0#usize := by
          intro j hj
          have hj' : j < count.val := by
            simpa only [hoffsets.1, List.length_replicate] using hj
          simp [hoffsets.1, hj']
        apply WP.spec_bind (constructor_quotient_degrees_spec components componentCount
          (alloc.vec.Vec.deref carrier.edges) offsets label hoffsetsLength hoffsetsZero hlabels
          (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using hedges))
        rintro ⟨degreeStatus, counts⟩ hdegrees
        have hdegreeOk : degreeStatus = .Ok () := hdegrees.1
        have hdegreeCounts : ∀ slot, slot < counts.val.length → ∃ value : Usize,
            counts.val[slot]? = some value ∧ value.val =
              constructorQuotientDegreeSlot carrier.edges.val label slot
                carrier.edges.val.length := by
          intro slot hslot
          have hslotOffsets : slot < offsets.val.length := by
            rw [← hdegrees.2.1]
            exact hslot
          simpa only [alloc.vec.Vec.deref, Slice.from_val] using
            hdegrees.2.2 slot hslotOffsets
        simp [hdegreeOk, alloc.vec.Vec.deref_mut]
        apply WP.spec_bind (constructor_prefix_offsets_total_spec counts.slice (by
          change 0 < counts.val.length
          rw [hdegrees.2.1, hoffsetsLength]
          omega))
        rintro ⟨prefixStatus, prefixed⟩ hprefix
        change prefixed.val.length = counts.val.length ∧
          (prefixStatus = .Ok () → ∀ j, j < counts.val.length → ∃ value : Usize,
            prefixed.val[j]? = some value ∧
              value.val = constructorPrefixSum counts.val (j + 1)) ∧
          (prefixStatus = .Ok () ∨ prefixStatus = .Err topology.Error.Overflow) at hprefix
        rcases hprefix.2.2 with hprefixOk | hprefixOverflow
        · have hprefixOk' : prefixStatus = .Ok () := by simpa only using hprefixOk
          subst prefixStatus
          simp only [uncurry, bind_ok]
          have hprefixedLength : prefixed.val.length = componentCount.val + 1 := by
            rw [hprefix.1]
            rw [hdegrees.2.1, hoffsetsLength]
          apply WP.spec_bind (alloc.vec.Vec.index_usize_spec
            ({ slice := prefixed } : alloc.vec.Vec Usize) componentCount (by
              change componentCount.val < prefixed.val.length
              omega))
          intro adjacencyCount hadjacency
          have hadjacencyLookup : prefixed.val[componentCount.val]? = some adjacencyCount := by
            rw [List.getElem?_eq_getElem (by omega)]
            simpa only [alloc.vec.Vec.val] using congrArg some hadjacency.symm
          obtain ⟨last, hlast, hlastValue⟩ :=
            hprefix.2.1 rfl componentCount.val (by omega)
          have hadjacencyValue :
              adjacencyCount.val = constructorPrefixSum counts.val counts.val.length := by
            have heq : adjacencyCount = last :=
              Option.some.inj (hadjacencyLookup.symm.trans hlast)
            subst last
            have hlength : counts.val.length = componentCount.val + 1 := by
              rw [hdegrees.2.1, hoffsetsLength]
            simpa only [hlength] using hlastValue
          apply WP.spec_bind (constructor_check_storage_spec adjacencyCount 8#usize)
          intro storage8 hstorage8
          by_cases hfits8 : constructorStorageFits adjacencyCount 8#usize
          · have hstorage8Ok : storage8 = .Ok () := by
              simpa only [hfits8, ite_true] using hstorage8
            simp only [hstorage8Ok, bind_ok]
            apply WP.spec_bind (constructor_check_storage_spec adjacencyCount 16#usize)
            intro storage16 hstorage16
            by_cases hfits16 : constructorStorageFits adjacencyCount 16#usize
            · have hstorage16Ok : storage16 = .Ok () := by
                simpa only [hfits16, ite_true] using hstorage16
              simp only [hstorage16Ok, bind_ok]
              apply (WP.spec_ok _).mpr
              refine Or.inr ⟨({ slice := prefixed } : alloc.vec.Vec Usize),
                adjacencyCount, rfl, count, counts.val, ?_, ?_, ?_, ?_,
                ?_, ?_, ?_, hfits8, hfits16⟩
              · rw [hdegrees.2.1, hoffsetsLength, hcountValue]
              · rw [hdegrees.2.1, hoffsetsLength]
              · exact hdegreeCounts
              · exact hprefixedLength.trans (by rw [hdegrees.2.1, hoffsetsLength])
              · intro slot hslot
                change slot < prefixed.val.length at hslot
                have hslotCounts : slot < counts.val.length := by
                  rw [← hprefix.1]
                  exact hslot
                simpa only [alloc.vec.Vec.val] using hprefix.2.1 rfl slot hslotCounts
              · exact hadjacencyValue
              · exact hcountFits
            · have hstorage16Error : storage16 = .Err .Overflow := by
                simpa only [hfits16, ite_false] using hstorage16
              simp only [hstorage16Error, bind_ok,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              exact constructor_scene_prefix_overflow_return _
          · have hstorage8Error : storage8 = .Err .Overflow := by
              simpa only [hfits8, ite_false] using hstorage8
            simp only [hstorage8Error, bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            exact constructor_scene_prefix_overflow_return _
        · have hprefixOverflow' : prefixStatus = .Err topology.Error.Overflow := by
            simpa only using hprefixOverflow
          subst prefixStatus
          simp only [uncurry, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          exact constructor_scene_prefix_overflow_return _
      · have hcountStorageError : countStorage = .Err .Overflow := by
          simpa only [hcountFits, ite_false] using hcountStorage
        simp only [hcountStorageError, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        exact constructor_scene_prefix_overflow_return _


theorem constructor_scene_quotient_prefix_accepts
    (carrier : topology.Carrier) (components : alloc.vec.Vec Usize)
    (componentCount : Usize) (label : Usize → Usize)
    (hc : CarrierValid carrier)
    (hcomponents : components.val.length = cellCount carrier)
    (hlabels : ∀ node : Usize, node.val < components.val.length →
      components.val[node.val]? = some (label node))
    (hbounded : ∀ node : Usize, node.val < components.val.length →
      (label node).val < componentCount.val)
    (hcountBound : componentCount.val ≤ cellCount carrier)
    (hallocation : ConstructorSceneAllocationFits carrier) :
    WP.spec (do
      let optionCount ← lift (Usize.checked_add componentCount 1#usize)
      let countResult ← core.option.Option.ok_or optionCount topology.Error.Overflow
      let countFlow ← core.result.Result.Insts.CoreOpsTry.branch countResult
      match countFlow with
      | .Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
      | .Continue count =>
        let storageResult ← topology.check_storage count 8#usize
        let storageFlow ← core.result.Result.Insts.CoreOpsTry.branch storageResult
        match storageFlow with
        | .Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
        | .Continue _ =>
          let offsets ← alloc.vec.from_elem core.clone.CloneUsize 0#usize count
          let edges ← topology.Carrier.impl.edges carrier
          let (degreeStatus, counts) ← spanning_tree.Tree.scene_dfs_loop3 0#usize (.Ok ())
            components componentCount offsets edges
          let degreeFlow ← core.result.Result.Insts.CoreOpsTry.branch degreeStatus
          match degreeFlow with
          | .Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
          | .Continue _ =>
            let (countSlice, countBack) ← lift (alloc.vec.Vec.deref_mut counts)
            let (prefixStatus, prefixed) ← topology.prefix_offsets countSlice
            let prefixFlow ← core.result.Result.Insts.CoreOpsTry.branch prefixStatus
            match prefixFlow with
            | .Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
            | .Continue _ =>
              let prefixedCounts := countBack prefixed
              let adjacencyCount ← alloc.vec.Vec.index
                (core.slice.index.SliceIndexUsizeSlice Usize) prefixedCounts componentCount
              let adjacencyStorage8 ← topology.check_storage adjacencyCount 8#usize
              let adjacencyFlow8 ← core.result.Result.Insts.CoreOpsTry.branch adjacencyStorage8
              match adjacencyFlow8 with
              | .Break residual =>
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
              | .Continue _ =>
                let adjacencyStorage16 ← topology.check_storage adjacencyCount 16#usize
                let adjacencyFlow16 ← core.result.Result.Insts.CoreOpsTry.branch adjacencyStorage16
                match adjacencyFlow16 with
                | .Break residual =>
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    (alloc.vec.Vec Usize × Usize) (core.convert.FromSame topology.Error) residual
                | .Continue _ => ok (.Ok (prefixedCounts, adjacencyCount)))
      (fun output => ∃ offsets adjacencyCount,
        output = .Ok (offsets, adjacencyCount) ∧
          ConstructorScenePrefixSuccess carrier componentCount label offsets adjacencyCount) := by
  rcases hallocation with
    ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, _ha9, _ha10, _ha11, _ha12⟩
  have hcomponentCountSucc : componentCount.val + 1 ≤ Usize.max := by omega
  obtain ⟨count, hcount, hcountValueRaw⟩ :=
    constructor_checked_add_some componentCount 1#usize (by
      simpa only [UScalar.ofNatCore_val_eq] using hcomponentCountSucc)
  have hcountValue : count.val = componentCount.val + 1 := by
    simpa only [UScalar.ofNatCore_val_eq] using hcountValueRaw
  have hcountFits : constructorStorageFits count 8#usize := by
    simp only [constructorStorageFits, hcountValue, UScalar.ofNatCore_val_eq]
    constructor <;> omega
  have hedges : ∀ edge ∈ carrier.edges.val,
      edge.u.val < components.val.length ∧ edge.v.val < components.val.length ∧
      (label edge.u).val < componentCount.val ∧
      (label edge.v).val < componentCount.val := by
    intro edge hedge
    have hpairs : (edge.u.val, edge.v.val) ∈ edgePairs carrier :=
      List.mem_map.mpr ⟨edge, hedge, rfl⟩
    have hcarrier := (hc.2.2.2.2.2.2.2 edge.u.val edge.v.val).mp hpairs
    have hv := ((hc.2.2.2.2.1 edge.u.val hcarrier.2.1).2.2 edge.v.val hcarrier.2.2).1
    have huComponents : edge.u.val < components.val.length := by omega
    have hvComponents : edge.v.val < components.val.length := by omega
    exact ⟨huComponents, hvComponents, hbounded edge.u huComponents,
      hbounded edge.v hvComponents⟩
  simp only [hcount, lift, bind_ok, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch, constructor_check_storage_eq,
    hcountFits, ite_true]
  apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize count rfl)
  intro offsets hoffsets
  simp only [topology.Carrier.impl.edges, bind_ok]
  have hoffsetsLength : offsets.val.length = componentCount.val + 1 := by
    rw [hoffsets.1, List.length_replicate, hcountValue]
  have hoffsetsZero : ∀ j, j < offsets.val.length →
      offsets.val[j]? = some 0#usize := by
    intro j hj
    have hj' : j < count.val := by simpa only [hoffsets.1, List.length_replicate] using hj
    simp [hoffsets.1, hj']
  apply WP.spec_bind (constructor_quotient_degrees_spec components componentCount
    (alloc.vec.Vec.deref carrier.edges) offsets label hoffsetsLength hoffsetsZero hlabels
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using hedges))
  rintro ⟨degreeStatus, counts⟩ hdegrees
  have hdegreeOk : degreeStatus = .Ok () := hdegrees.1
  have hdegreeCounts : ∀ slot, slot < counts.val.length → ∃ value : Usize,
      counts.val[slot]? = some value ∧ value.val =
        constructorQuotientDegreeSlot carrier.edges.val label slot carrier.edges.val.length := by
    intro slot hslot
    have hslotOffsets : slot < offsets.val.length := by
      rw [← hdegrees.2.1]
      exact hslot
    simpa only [alloc.vec.Vec.deref, Slice.from_val] using
      hdegrees.2.2 slot hslotOffsets
  simp [hdegreeOk, alloc.vec.Vec.deref_mut]
  have hprefixWidth : constructorPrefixSum counts.val counts.val.length ≤ Usize.max := by
    have hsum := constructor_quotient_prefix_sum_le carrier.edges.val label componentCount
      counts.val (by rw [hdegrees.2.1, hoffsetsLength]) (fun edge hedge =>
        ⟨hbounded edge.u (hedges edge hedge).1,
          hbounded edge.v (hedges edge hedge).2.1⟩) hdegreeCounts
    omega
  apply WP.spec_bind (constructor_prefix_offsets_spec counts.slice (by
    change 0 < counts.val.length
    rw [hdegrees.2.1, hoffsetsLength]
    omega) hprefixWidth)
  rintro ⟨prefixStatus, prefixed⟩ hprefix
  change prefixStatus = .Ok () ∧ prefixed.val.length = counts.val.length ∧
    (∀ j, j < counts.val.length → ∃ value : Usize,
      prefixed.val[j]? = some value ∧
        value.val = constructorPrefixSum counts.val (j + 1)) at hprefix
  have hprefixOk : prefixStatus = .Ok () := hprefix.1
  subst prefixStatus
  simp only [uncurry, bind_ok]
  have hprefixedLength : prefixed.val.length = componentCount.val + 1 := by
    rw [hprefix.2.1, hdegrees.2.1, hoffsetsLength]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec
    ({ slice := prefixed } : alloc.vec.Vec Usize) componentCount (by
      change componentCount.val < prefixed.val.length
      omega))
  intro adjacencyCount hadjacency
  have hadjacencyLookup : prefixed.val[componentCount.val]? = some adjacencyCount := by
    rw [List.getElem?_eq_getElem (by omega)]
    simpa only [alloc.vec.Vec.val] using congrArg some hadjacency.symm
  obtain ⟨last, hlast, hlastValue⟩ := hprefix.2.2 componentCount.val (by omega)
  have hadjacencyValue :
      adjacencyCount.val = constructorPrefixSum counts.val counts.val.length := by
    have heq : adjacencyCount = last := Option.some.inj (hadjacencyLookup.symm.trans hlast)
    subst last
    have hlength : counts.val.length = componentCount.val + 1 := by
      rw [hdegrees.2.1, hoffsetsLength]
    simpa only [hlength] using hlastValue
  have hadjacencyBound : adjacencyCount.val ≤ 2 * carrier.edges.val.length := by
    rw [hadjacencyValue]
    exact constructor_quotient_prefix_sum_le carrier.edges.val label componentCount counts.val
      (by rw [hdegrees.2.1, hoffsetsLength]) (fun edge hedge =>
        ⟨hbounded edge.u (hedges edge hedge).1,
          hbounded edge.v (hedges edge hedge).2.1⟩) hdegreeCounts
  have hfits8 : constructorStorageFits adjacencyCount 8#usize := by
    simp only [constructorStorageFits, UScalar.ofNatCore_val_eq]
    constructor <;> omega
  have hfits16 : constructorStorageFits adjacencyCount 16#usize := by
    simp only [constructorStorageFits, UScalar.ofNatCore_val_eq]
    constructor <;> omega
  simp only [hfits8, hfits16, ite_true, bind_ok]
  apply (WP.spec_ok _).mpr
  refine ⟨({ slice := prefixed } : alloc.vec.Vec Usize),
    adjacencyCount, rfl, count, counts.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hfits8, hfits16⟩
  · rw [hdegrees.2.1, hoffsetsLength, hcountValue]
  · rw [hdegrees.2.1, hoffsetsLength]
  · exact hdegreeCounts
  · exact hprefixedLength.trans (by rw [hdegrees.2.1, hoffsetsLength])
  · intro slot hslot
    change slot < prefixed.val.length at hslot
    have hslotCounts : slot < counts.val.length := by
      rw [← hprefix.2.1]
      exact hslot
    simpa only [alloc.vec.Vec.val] using hprefix.2.2 slot hslotCounts
  · exact hadjacencyValue
  · exact hcountFits
end Labyrinth
