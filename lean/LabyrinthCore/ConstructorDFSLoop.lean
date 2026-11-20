module
public import LabyrinthCore.ConstructorDFSState
public import LabyrinthCore.ConstructorDFSFuel
public import LabyrinthCore.ConstructorDFSStep
public import LabyrinthCore.ConstructorDFSDiscovery
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

abbrev ConstructorDFSLoopState (R : Type*) := R × alloc.vec.Vec Bool ×
  alloc.vec.Vec spanning_tree.Frame × alloc.vec.Vec Usize × alloc.vec.Vec Usize ×
  Usize × Usize × core.result.Result Unit topology.Error

abbrev ConstructorDFSLoopResult (R : Type*) := R × alloc.vec.Vec Bool ×
  alloc.vec.Vec spanning_tree.Frame × alloc.vec.Vec Usize × alloc.vec.Vec Usize ×
  Usize × core.result.Result Unit topology.Error

def constructorDFSLoopInvariant {R : Type*} (offsets neighbors : Slice Usize)
    (root capacity : Nat) : ConstructorDFSLoopState R → Prop :=
  fun (_, seen, frames, parents, incoming, reached, depth, status) =>
    status = .Ok () ∧ ∃ visited rank,
      ConstructorDFSInvariant offsets neighbors root capacity seen frames parents incoming
        reached.val depth.val visited rank

def constructorDFSLoopMeasure {R : Type*} (offsets neighbors : Slice Usize) :
    ConstructorDFSLoopState R → Nat :=
  fun (_, _, frames, _, _, reached, depth, _) =>
    constructorDFSMeasure (constructorDFSVertexCount offsets) neighbors.val.length
      reached.val depth.val frames.val

def constructorDFSLoopOutput {R : Type*} (offsets neighbors : Slice Usize)
    (root capacity : Nat) : ConstructorDFSLoopResult R → Prop :=
  fun (_, seen, frames, parents, incoming, reached, status) =>
    status = .Ok () ∧ ∃ visited rank,
      ConstructorDFSInvariant offsets neighbors root capacity seen frames parents incoming
        reached.val 0 visited rank

theorem constructor_dfs_row_lookup (offsets : Slice Usize) (cell : Usize)
    (hc : cell.val < constructorDFSVertexCount offsets) :
    ∃ lo hi : Usize, offsets.val[cell.val]? = some lo ∧
      offsets.val[cell.val + 1]? = some hi ∧
      lo.val = constructorDFSOffset offsets cell.val ∧
      hi.val = constructorDFSOffset offsets (cell.val + 1) := by
  have hb : cell.val + 1 < offsets.val.length := by
    unfold constructorDFSVertexCount at hc
    omega
  have hb0 : cell.val < offsets.val.length := by omega
  refine ⟨offsets.val[cell.val], offsets.val[cell.val + 1],
    List.getElem?_eq_getElem hb0, List.getElem?_eq_getElem hb, ?_, ?_⟩
  · simp [constructorDFSOffset, List.getElem?_eq_getElem hb0]
  · simp [constructorDFSOffset, List.getElem?_eq_getElem hb]

/-- The three production branches preserve the ranked frontier and strictly decrease fuel. -/
theorem constructor_dfs_loop_body_spec {R : Type*} (adapter : tree.Rng R)
    (hrng : constructorLegalRng adapter) (offsets neighbors : Slice Usize)
    (root capacity : Nat) (hinput : ConstructorDFSInput offsets neighbors root)
    (state : ConstructorDFSLoopState R)
    (hstate : constructorDFSLoopInvariant offsets neighbors root capacity state) :
    WP.spec
      (spanning_tree.depth_first_loop1.body adapter offsets neighbors state.1 state.2.1
        state.2.2.1 state.2.2.2.1 state.2.2.2.2.1 state.2.2.2.2.2.1
        state.2.2.2.2.2.2.1 state.2.2.2.2.2.2.2)
      (fun output => match output with
        | cont next => constructorDFSLoopInvariant offsets neighbors root capacity next ∧
            constructorDFSLoopMeasure offsets neighbors next <
              constructorDFSLoopMeasure offsets neighbors state
        | done result => constructorDFSLoopOutput offsets neighbors root capacity result) := by
  rcases state with ⟨rng, seen, frames, parents, incoming, reached, depth, status⟩
  obtain ⟨rfl, visited, rank, hinv⟩ := hstate
  dsimp only
  by_cases hz : depth.val = 0
  · have he : depth = 0#usize := (UScalar.eq_equiv _ _).mpr (by simpa using hz)
    subst depth
    apply WP.spec_mono (constructor_dfs_done_step_spec adapter offsets neighbors rng seen frames
      parents incoming reached (.Ok ()))
    intro output he
    rw [he]
    exact ⟨rfl, visited, rank, by simpa using hinv⟩
  · have hd : 0 < depth.val := by omega
    have hdb : depth.val ≤ capacity := Nat.le_trans hinv.depth_bound
      (Nat.le_trans (constructor_dfs_reached_bound hinv) hinv.capacity_bound)
    let index : Usize := UScalar.ofNatCore (depth.val - 1) (by
      have hmax := depth.hmax
      omega)
    have hi : index.val + 1 = depth.val := by simp only [index, UScalar.ofNatCore_val_eq]; omega
    have hib : index.val < frames.val.length := by rw [hinv.frames_length]; omega
    let frame := frames.val[index.val]
    have hf : frames.val[index.val]? = some frame := List.getElem?_eq_getElem hib
    have hframe := (hinv.frame index.val (by omega) frame hf).2
    by_cases hempty : frame.remaining.val = 0
    · have he : frame.remaining = 0#usize :=
        (UScalar.eq_equiv _ _).mpr (by simpa using hempty)
      apply WP.spec_mono (constructor_dfs_pop_step_spec adapter offsets neighbors rng seen frames
        parents incoming reached depth index frame hi hib hf he)
      intro output heq
      rw [heq]
      have hold : ConstructorDFSInvariant offsets neighbors root capacity seen frames parents incoming
          reached.val (index.val + 1) visited rank := by simpa only [hi] using hinv
      refine ⟨⟨rfl, visited, rank, constructor_dfs_invariant_pop hold frame hf hempty⟩, ?_⟩
      change constructorDFSMeasure _ _ _ index.val frames.val <
        constructorDFSMeasure _ _ _ depth.val frames.val
      rw [← hi]
      exact constructor_dfs_measure_pop _ _ _ _ frames.val frame hf hempty
    · have hpos : 0 < frame.remaining.val := by omega
      obtain ⟨lo, rowEnd, hlo, hhi, hloval, hhival⟩ :=
        constructor_dfs_row_lookup offsets frame.cell hframe.cell
      have hcell : frame.cell.val + 1 < offsets.val.length := by
        have hc := hframe.cell
        unfold constructorDFSVertexCount at hc
        omega
      have hnext : lo.val ≤ frame.next.val ∧ frame.next.val < rowEnd.val := by
        simpa only [hloval, hhival] using hframe.next hpos
      have hstorage : rowEnd.val ≤ neighbors.val.length := by
        rw [hhival]
        exact constructor_dfs_offset_bound offsets neighbors root hinput _ (by have := hframe.cell; omega)
      have hnb : frame.next.val < neighbors.val.length := by omega
      let neighbor := neighbors.val[frame.next.val]
      have hn : neighbors.val[frame.next.val]? = some neighbor := List.getElem?_eq_getElem hnb
      have hnv : neighbor.val < constructorDFSVertexCount offsets :=
        hinput.bounded neighbor (List.getElem_mem hnb)
      have hns : neighbor.val < seen.val.length := by rw [hinv.seen_length]; have := hinv.capacity_bound; omega
      by_cases hm : neighbor.val ∈ visited
      · have hseen := (hinv.seen_iff neighbor.val hnv).mpr hm
        apply WP.spec_mono (constructor_dfs_seen_step_spec adapter offsets neighbors rng seen frames
          parents incoming reached depth index frame lo rowEnd neighbor hi hib hf hcell hlo hhi
          hnext hstorage hpos hn hns hseen)
        rintro output ⟨advanced, rfl, hc, hr, ha⟩
        have hanext : advanced.next.val = if frame.next.val + 1 =
            constructorDFSOffset offsets (frame.cell.val + 1)
            then constructorDFSOffset offsets frame.cell.val else frame.next.val + 1 := by
          simpa only [hloval, hhival] using ha
        refine ⟨⟨rfl, visited, rank,
          constructor_dfs_invariant_seen hinv index frame advanced (by omega) hf hpos hc hr
            hanext neighbor hn hm⟩, ?_⟩
        simpa only [constructorDFSLoopMeasure, alloc.vec.Vec.set, alloc.vec.Vec.from_val] using
          (constructor_dfs_measure_scan (constructorDFSVertexCount offsets) neighbors.val.length
            reached.val depth.val frames.val index frame advanced hi hib hf hpos hr)
      · have hreached := constructor_dfs_unseen_reached_lt hinv neighbor.val hnv hm
        have hroom : depth.val < capacity := by have := hinv.depth_bound; have := hinv.capacity_bound; omega
        have hfalse : seen.val[neighbor.val]? = some false := by
          cases hb : seen.val[neighbor.val] with
          | false => exact List.getElem?_eq_getElem hns |>.trans (congrArg some hb)
          | true =>
            have ht : seen.val[neighbor.val]? = some true :=
              (List.getElem?_eq_getElem hns).trans (congrArg some hb)
            exact False.elim (hm ((hinv.seen_iff neighbor.val hnv).mp ht))
        obtain ⟨childLo, childHi, hclo, hchi, hcloval, hchival⟩ :=
          constructor_dfs_row_lookup offsets neighbor hnv
        have hchild : neighbor.val + 1 < offsets.val.length := by
          unfold constructorDFSVertexCount at hnv
          omega
        have hordered : childLo.val ≤ childHi.val := by
          rw [hcloval, hchival]
          exact hinput.ordered neighbor.val hnv
        have hrmax : reached.val < Usize.max := by
          have hnmax : constructorDFSVertexCount offsets < Usize.max := by
            have h := offsets.property
            unfold constructorDFSVertexCount
            omega
          omega
        apply WP.spec_mono (constructor_dfs_discovery_step_spec adapter hrng offsets neighbors rng
          seen frames parents incoming reached depth index frame lo rowEnd neighbor childLo childHi
          hi (by rw [hinv.frames_length]; exact hroom) hf hcell hlo hhi hnext hstorage hpos hn hns hfalse
          (by rw [hinv.parents_length]; have := hinv.capacity_bound; omega)
          (by rw [hinv.incoming_length]; have := hinv.capacity_bound; omega) hrmax
          hchild hclo hchi hordered)
        rintro output ⟨advanced, child, rng', depth', reached', hc, hr, ha, hcc, hcr,
          _hemptyChild, hcn, hd', hr', rfl⟩
        have hanext : advanced.next.val = if frame.next.val + 1 =
            constructorDFSOffset offsets (frame.cell.val + 1)
            then constructorDFSOffset offsets frame.cell.val else frame.next.val + 1 := by
          simpa only [hloval, hhival] using ha
        have hchildValid : ConstructorDFSFrameValid offsets child := by
          refine ⟨by simpa only [hcc] using hnv, ?_, ?_⟩
          · rw [hcc, hcr, hcloval, hchival]
          · intro hpositive
            have hnonempty : childLo.val < childHi.val := by omega
            simpa only [hcc, hcloval, hchival] using hcn hnonempty
        have hchildRemaining : child.remaining.val =
            constructorDFSOffset offsets (neighbor.val + 1) -
              constructorDFSOffset offsets neighbor.val := by
          simpa only [hcloval, hchival] using hcr
        have hinv' := constructor_dfs_invariant_discover hinv index depth frame advanced child neighbor
          (by omega) rfl hroom hf hpos hc hr hanext hnv hm hn hcc hchildValid hchildRemaining
        refine ⟨⟨rfl, insert neighbor.val visited,
          (fun v => if v = neighbor.val then reached.val else rank v), ?_⟩, ?_⟩
        · simpa only [hd', hr'] using hinv'
        · change constructorDFSMeasure _ _ reached'.val depth'.val
            (((frames.set index advanced).set depth child).val) <
            constructorDFSMeasure _ _ reached.val depth.val frames.val
          rw [hd', hr']
          have hslots : child.remaining.val ≤ neighbors.val.length := by
            have hb := constructor_dfs_offset_bound offsets neighbors root hinput
              (neighbor.val + 1) (by omega)
            omega
          simpa only [alloc.vec.Vec.set, alloc.vec.Vec.from_val] using
            (constructor_dfs_measure_discover (constructorDFSVertexCount offsets) neighbors.val.length
              reached.val depth.val frames.val index depth frame advanced child hi rfl
              (by rw [hinv.frames_length]; exact hroom) hf hpos hr hslots hreached)

/-- Universal totality of the actual stack loop under legal cyclic choices. -/
theorem constructor_dfs_loop_spec {R : Type*} (adapter : tree.Rng R)
    (hrng : constructorLegalRng adapter) (offsets neighbors : Slice Usize)
    (root capacity : Nat) (hinput : ConstructorDFSInput offsets neighbors root)
    (rng : R) (seen : alloc.vec.Vec Bool) (frames : alloc.vec.Vec spanning_tree.Frame)
    (parents incoming : alloc.vec.Vec Usize) (reached depth : Usize)
    (visited : Finset Nat) (rank : Nat → Nat)
    (hinv : ConstructorDFSInvariant offsets neighbors root capacity seen frames parents incoming
      reached.val depth.val visited rank) :
    WP.spec (spanning_tree.depth_first_loop1 adapter offsets neighbors rng seen frames parents incoming
      reached depth (.Ok ())) (constructorDFSLoopOutput offsets neighbors root capacity) := by
  unfold spanning_tree.depth_first_loop1
  apply loop.spec_decr_nat (constructorDFSLoopMeasure offsets neighbors)
    (constructorDFSLoopInvariant offsets neighbors root capacity)
  · rintro ⟨stateRng, stateSeen, stateFrames, stateParents, stateIncoming,
      stateReached, stateDepth, stateStatus⟩ hs
    apply WP.spec_mono (constructor_dfs_loop_body_spec adapter hrng offsets neighbors root capacity hinput
      (stateRng, stateSeen, stateFrames, stateParents, stateIncoming,
        stateReached, stateDepth, stateStatus) hs)
    intro result hresult
    cases result <;> exact hresult
  · exact ⟨rfl, visited, rank, hinv⟩

end Labyrinth
