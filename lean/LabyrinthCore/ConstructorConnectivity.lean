module
public import LabyrinthCore.ConstructorSearch
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- Every generated connectivity-row scan terminates, closes the active row (every row neighbour
is visited), and keeps the depth/reached balance. The final visited set is not bounded by the
row, so exact discovery is not stated. -/
theorem constructor_connectivity_row_spec
    (offsets neighbors : alloc.vec.Vec Usize) (cell lo hi : Usize)
    (seen : alloc.vec.Vec Bool) (stack : alloc.vec.Vec Usize) (depth reached : Usize)
    (visited : Finset Nat)
    (hcell : cell.val < offsets.val.length - 1)
    (hlo : offsets.val[cell.val]? = some lo)
    (hhi : offsets.val[cell.val + 1]? = some hi)
    (hordered : lo.val ≤ hi.val) (hstorage : hi.val ≤ neighbors.val.length)
    (hentries : ∀ j, lo.val ≤ j → j < hi.val → ∀ value : Usize,
      neighbors.val[j]? = some value → value.val < offsets.val.length - 1)
    (hstate : constructorSearchState (offsets.val.length - 1)
      (constructorCsrAdjacent offsets neighbors) seen stack depth reached (some cell.val) visited)
    (hsource : cell.val ∈ visited) :
    WP.spec (topology.Carrier.from_csr_loop2_loop0 offsets neighbors cell seen stack depth reached lo)
      (fun output => ∃ finalVisited : Finset Nat,
        constructorSearchState (offsets.val.length - 1) (constructorCsrAdjacent offsets neighbors)
          output.1 output.2.1 output.2.2.1 output.2.2.2 none finalVisited ∧
        visited ⊆ finalVisited ∧
        output.2.2.2.val + depth.val = reached.val + output.2.2.1.val) := by
  let invariant : alloc.vec.Vec Bool × alloc.vec.Vec Usize × Usize × Usize × Usize → Prop :=
    fun state => ∃ discovered : Finset Nat,
      constructorSearchState (offsets.val.length - 1) (constructorCsrAdjacent offsets neighbors)
        state.1 state.2.1 state.2.2.1 state.2.2.2.1 (some cell.val) discovered ∧
      visited ⊆ discovered ∧
      state.2.2.2.1.val + depth.val = reached.val + state.2.2.1.val ∧
      lo.val ≤ state.2.2.2.2.val ∧ state.2.2.2.2.val ≤ hi.val ∧
      ∀ j, lo.val ≤ j → j < state.2.2.2.2.val → ∀ value : Usize,
        neighbors.val[j]? = some value → value.val ∈ discovered
  unfold topology.Carrier.from_csr_loop2_loop0
  apply loop.spec_decr_nat
    (fun state : alloc.vec.Vec Bool × alloc.vec.Vec Usize × Usize × Usize × Usize =>
      hi.val - state.2.2.2.2.val) invariant
  · rintro ⟨currentSeen, currentStack, currentDepth, currentReached, index⟩ hinv
    obtain ⟨discovered, hs, hsubset, hbalance, hlow, hupp, hprefix⟩ := hinv
    dsimp only at hs hsubset hbalance hlow hupp hprefix
    unfold topology.Carrier.from_csr_loop2_loop0.body
    apply WP.spec_bind (Usize.add_spec (x := cell) (y := 1#usize) (by
      have := offsets.property
      simp only [UScalar.ofNatCore_val_eq]
      omega))
    intro rowNext hn
    have hnext : rowNext.val = cell.val + 1 := by simpa using hn
    simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
    apply WP.spec_bind (alloc.vec.Vec.index_usize_spec offsets rowNext (by
      change rowNext.val < offsets.val.length
      omega))
    intro rowEnd he
    have hendLookup : offsets.val[rowNext.val]? = some rowEnd := by
      rw [List.getElem?_eq_getElem (show rowNext.val < offsets.val.length by omega), he]
    rw [hnext, hhi] at hendLookup
    have hend : rowEnd = hi := Option.some.inj hendLookup.symm
    rw [hend]
    by_cases hmore : index < hi
    · have hiIndex : index.val < hi.val := by simpa using hmore
      have hbound : index.val < neighbors.val.length := by omega
      simp only [hmore, ite_true]
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec neighbors index hbound)
      intro value hv
      have hlookup : neighbors.val[index.val]? = some value := by
        rw [List.getElem?_eq_getElem hbound, hv]
      have hvbound := hentries index.val hlow hiIndex value hlookup
      have hvseen : value.val < currentSeen.val.length := by
        rw [hs.seen_length]
        exact hvbound
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec currentSeen value hvseen)
      intro marked hm
      have hmlookup : currentSeen.val[value.val]? = some marked := by
        rw [List.getElem?_eq_getElem hvseen, hm]
      have hmarked : marked = decide (value.val ∈ discovered) :=
        Option.some.inj (hmlookup.symm.trans (hs.seen_eq value.val hvbound))
      by_cases hvisited : value.val ∈ discovered
      · have hmtrue : marked = true := by simpa only [hvisited, decide_true] using hmarked
        simp only [hmtrue, ite_true, bind_ok]
        apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
          have := neighbors.property
          simp only [UScalar.ofNatCore_val_eq]
          omega))
        intro index' hi'
        have hindex' : index'.val = index.val + 1 := by simpa using hi'
        apply (WP.spec_ok _).mpr
        dsimp only [invariant]
        refine ⟨⟨discovered, hs, hsubset, hbalance, by omega, by omega, ?_⟩, by omega⟩
        intro j hjl hjh other hother
        by_cases heq : j = index.val
        · subst j
          have heq : other = value := Option.some.inj (hother.symm.trans hlookup)
          simpa only [heq] using hvisited
        · exact hprefix j hjl (by omega) other hother
      · have hmfalse : marked = false := by simpa only [hvisited, decide_false] using hmarked
        simp only [hmfalse, Bool.false_eq_true, ite_false]
        have hboundedInsert : insert value.val discovered ⊆ Finset.range (offsets.val.length - 1) := by
          intro v hv
          rcases Finset.mem_insert.mp hv with rfl | hv
          · exact Finset.mem_range.mpr hvbound
          · exact hs.bounded hv
        have hcard := Finset.card_le_card hboundedInsert
        rw [Finset.card_range, Finset.card_insert_of_notMem hvisited] at hcard
        have hreached := hs.reached_eq
        have hdepth := hs.depth_le
        have hstack : currentDepth.val < currentStack.val.length := by
          rw [hs.stack_length]
          omega
        simp only [Aeneas.Std.bind_assoc]
        apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec currentSeen value hvseen)
        rintro ⟨oldSeen, backSeen⟩ ⟨_, rfl⟩
        change WP.spec (Std.bind
          (Std.bind (currentStack.index_mut_usize currentDepth) (fun pair => do
            let nextDepth ← currentDepth + 1#usize
            let nextReached ← currentReached + 1#usize
            ok (currentSeen.set value true, pair.2 value, nextDepth, nextReached)))
          (fun state => do
            let nextIndex ← index + 1#usize
            ok (cont (state.1, state.2.1, state.2.2.1, state.2.2.2, nextIndex)))) _
        rw [Aeneas.Std.bind_assoc]
        apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec currentStack currentDepth hstack)
        rintro ⟨oldStack, backStack⟩ ⟨_, rfl⟩
        dsimp only
        rw [Aeneas.Std.bind_assoc]
        apply WP.spec_bind (Usize.add_spec (x := currentDepth) (y := 1#usize) (by
          have := offsets.property
          simp only [UScalar.ofNatCore_val_eq]
          omega))
        intro depth' hd'
        have hdepth' : depth'.val = currentDepth.val + 1 := by simpa using hd'
        rw [Aeneas.Std.bind_assoc]
        apply WP.spec_bind (Usize.add_spec (x := currentReached) (y := 1#usize) (by
          have := offsets.property
          simp only [UScalar.ofNatCore_val_eq]
          omega))
        intro reached' hr'
        have hreached' : reached'.val = currentReached.val + 1 := by simpa using hr'
        simp only [bind_ok]
        apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
          have := neighbors.property
          simp only [UScalar.ofNatCore_val_eq]
          omega))
        intro index' hi'
        have hindex' : index'.val = index.val + 1 := by simpa using hi'
        have hedge : constructorCsrAdjacent offsets neighbors cell.val value.val := by
          refine ⟨hcell, index.val, ?_, ?_, value, hlookup, rfl⟩
          · simpa only [hlo, Option.getD_some] using hlow
          · simpa only [hhi, Option.getD_some] using hiIndex
        have hpath := (hs.reachable cell.val (hsubset hsource)).tail hedge
        have hnewState := constructor_search_push hs hvbound hvisited hpath hdepth' hreached'
        apply (WP.spec_ok _).mpr
        dsimp only [invariant]
        refine ⟨⟨insert value.val discovered, hnewState, ?_, by omega, by omega, by omega, ?_⟩,
          by omega⟩
        · intro v hv
          exact Finset.mem_insert_of_mem (hsubset hv)
        · intro j hjl hjh other hother
          by_cases heq : j = index.val
          · subst j
            have heq : other = value := Option.some.inj (hother.symm.trans hlookup)
            rw [heq]
            exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hprefix j hjl (by omega) other hother)
    · have heq : index.val = hi.val := by
        have : ¬ index.val < hi.val := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      refine ⟨discovered, constructor_search_finish_row hs ?_, hsubset, hbalance⟩
      intro v hedge
      obtain ⟨_, j, hjl, hjh, value, hv, hval⟩ := hedge
      simp only [hlo, hhi, Option.getD_some] at hjl hjh
      rw [← hval]
      exact hprefix j hjl (by omega) value hv
  · refine ⟨visited, hstate, Finset.Subset.refl _, rfl, le_rfl, hordered, ?_⟩
    intro j hjl hjh
    dsimp only at hjh
    omega

/-- The complete generated work-stack traversal terminates and returns `n` exactly when every
vertex is reachable from vertex 0; the size of the root component is not stated.
Its decreasing measure accounts for both newly discovered vertices and pending stack entries. -/
theorem constructor_connectivity_spec
    (offsets neighbors : alloc.vec.Vec Usize) (unused : Usize)
    (seen : alloc.vec.Vec Bool) (stack : alloc.vec.Vec Usize) (depth reached : Usize)
    (visited : Finset Nat)
    (hrows : constructorRawRows (alloc.vec.Vec.deref offsets) (alloc.vec.Vec.deref neighbors))
    (hentries : constructorAllRows offsets neighbors (offsets.val.length - 1))
    (hstate : constructorSearchState (offsets.val.length - 1)
      (constructorCsrAdjacent offsets neighbors) seen stack depth reached none visited) :
    WP.spec (topology.Carrier.from_csr_loop2 offsets neighbors unused seen stack depth reached)
      (fun result => result.val ≤ offsets.val.length - 1 ∧
        (result.val = offsets.val.length - 1 ↔
          ∀ v, v < offsets.val.length - 1 →
            Relation.ReflTransGen (constructorCsrAdjacent offsets neighbors) 0 v)) := by
  let invariant :
      Usize × alloc.vec.Vec Bool × alloc.vec.Vec Usize × Usize × Usize → Prop :=
    fun state => ∃ discovered : Finset Nat,
      constructorSearchState (offsets.val.length - 1) (constructorCsrAdjacent offsets neighbors)
        state.2.1 state.2.2.1 state.2.2.2.1 state.2.2.2.2 none discovered
  let measure :
      Usize × alloc.vec.Vec Bool × alloc.vec.Vec Usize × Usize × Usize → Nat :=
    fun state => 2 * (offsets.val.length - 1 - state.2.2.2.2.val) + state.2.2.2.1.val
  have hraw := hrows
  simp only [constructorRawRows, alloc.vec.Vec.deref, Slice.from_val] at hraw
  unfold topology.Carrier.from_csr_loop2
  apply loop.spec_decr_nat measure invariant
  · rintro ⟨previousCell, currentSeen, currentStack, currentDepth, currentReached⟩ hinv
    obtain ⟨discovered, hs⟩ := hinv
    dsimp only at hs
    unfold topology.Carrier.from_csr_loop2.body
    by_cases hmore : currentDepth > 0#usize
    · have hpositive : 0 < currentDepth.val := by simpa using hmore
      simp only [hmore, ite_true, alloc.vec.Vec.index_slice_index]
      apply WP.spec_bind (Usize.sub_spec (x := currentDepth) (y := 1#usize) (by
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro popped hp
      have hpopped : popped.val = currentDepth.val - 1 := by simpa using hp.1
      have hcountBound := constructor_search_card_bound hs
      have hdepthBound := hs.depth_le
      have hpoppedBound : popped.val < currentStack.val.length := by
        rw [hs.stack_length]
        omega
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec currentStack popped hpoppedBound)
      intro cell hc
      have hcellLookup : currentStack.val[popped.val]? = some cell := by
        rw [List.getElem?_eq_getElem hpoppedBound, hc]
      obtain ⟨cell', hcell', hmem'⟩ := hs.pending popped.val (by omega)
      have heq : cell' = cell := Option.some.inj (hcell'.symm.trans hcellLookup)
      subst cell'
      have hcell : cell.val < offsets.val.length - 1 :=
        Finset.mem_range.mp (hs.bounded hmem')
      have hpoppedState : constructorSearchState (offsets.val.length - 1)
          (constructorCsrAdjacent offsets neighbors) currentSeen currentStack popped currentReached
          (some cell.val) discovered := by
        refine ⟨hs.seen_length, hs.stack_length, by omega, hs.reached_eq,
          hs.bounded, hs.root_mem, hs.seen_eq, ?_, hs.reachable, ?_⟩
        · intro i hi
          exact hs.pending i (by omega)
        · intro v hv
          rcases hs.covered v hv with ha | hclosed | ⟨i, hi, queued, hqueued, hvalue⟩
          · cases ha
          · exact Or.inr (Or.inl hclosed)
          · by_cases hstill : i < popped.val
            · exact Or.inr (Or.inr ⟨i, hstill, queued, hqueued, hvalue⟩)
            · have hiPop : i = popped.val := by omega
              rw [hiPop, hcellLookup] at hqueued
              have hsame : queued = cell := (Option.some.inj hqueued).symm
              subst queued
              exact Or.inl (congrArg some hvalue)
      obtain ⟨lo, hi, hlo, hhi, hordered, hstorage⟩ := hraw cell.val hcell
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec offsets cell (by
        change cell.val < offsets.val.length
        omega))
      intro start hstart
      have hstartLookup : offsets.val[cell.val]? = some start := by
        rw [List.getElem?_eq_getElem (show cell.val < offsets.val.length by omega), hstart]
      have hstartEq : start = lo := Option.some.inj (hstartLookup.symm.trans hlo)
      rw [hstartEq]
      have hrowBounds : ∀ j, lo.val ≤ j → j < hi.val → ∀ value : Usize,
          neighbors.val[j]? = some value → value.val < offsets.val.length - 1 := by
        intro j hjl hjh value hv
        have hentry := hentries cell hcell j
          (by simpa only [hlo, Option.getD_some] using hjl)
          (by simpa only [hhi, Option.getD_some] using hjh)
        obtain ⟨actual, ha, habound, _⟩ := hentry
        have he : actual = value := Option.some.inj (ha.symm.trans hv)
        simpa only [he] using habound
      apply WP.spec_bind (constructor_connectivity_row_spec offsets neighbors cell lo hi
        currentSeen currentStack popped currentReached discovered hcell hlo hhi hordered hstorage
        hrowBounds hpoppedState hmem')
      rintro ⟨seen', stack', depth', reached'⟩ ⟨found, hfound, hsubset, hbalance⟩
      dsimp only at hfound hbalance
      apply (WP.spec_ok _).mpr
      refine ⟨⟨found, hfound⟩, ?_⟩
      have hfoundBound := constructor_search_card_bound hfound
      have hcard := Finset.card_le_card hsubset
      have hbefore := hs.reached_eq
      have hafter := hfound.reached_eq
      dsimp only [measure]
      omega
    · have hzero : currentDepth.val = 0 := by
        have : ¬ 0 < currentDepth.val := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      exact ⟨constructor_search_card_bound hs, (constructor_search_exhausted hs hzero).2⟩
  · exact ⟨visited, hstate⟩

end Labyrinth
