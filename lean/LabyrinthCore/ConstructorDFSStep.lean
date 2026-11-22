module
public import LabyrinthCore.ConstructorDFS
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- A generated DFS iteration scans the current row cyclically exactly once per remaining
entry. A previously seen neighbor changes neither parents nor RNG nor discovery count. -/
theorem constructor_dfs_seen_step_spec {R : Type*} (adapter : tree.Rng R)
    (offsets neighbors : Slice Usize) (rng : R)
    (seen : alloc.vec.Vec Bool) (frames : alloc.vec.Vec spanning_tree.Frame)
    (parents incoming : alloc.vec.Vec Usize) (reached depth slot : Usize)
    (frame : spanning_tree.Frame) (lo hi neighbor : Usize)
    (hslot : slot.val + 1 = depth.val) (hslotBound : slot.val < frames.val.length)
    (hframe : frames.val[slot.val]? = some frame)
    (hcell : frame.cell.val + 1 < offsets.val.length)
    (hlo : offsets.val[frame.cell.val]? = some lo)
    (hhi : offsets.val[frame.cell.val + 1]? = some hi)
    (hnext : lo.val ≤ frame.next.val ∧ frame.next.val < hi.val)
    (hstorage : hi.val ≤ neighbors.val.length) (hremaining : 0 < frame.remaining.val)
    (hneighbor : neighbors.val[frame.next.val]? = some neighbor)
    (hneighborBound : neighbor.val < seen.val.length)
    (hseen : seen.val[neighbor.val]? = some true) :
    WP.spec (spanning_tree.depth_first_loop1.body adapter offsets neighbors rng seen frames
      parents incoming reached depth (.Ok ())) (fun output =>
        ∃ advanced : spanning_tree.Frame,
          output = cont (rng, seen, frames.set slot advanced, parents, incoming, reached, depth,
            core.result.Result.Ok ()) ∧
          advanced.cell = frame.cell ∧ advanced.remaining.val = frame.remaining.val - 1 ∧
          advanced.next.val = if frame.next.val + 1 = hi.val then lo.val else frame.next.val + 1) := by
  unfold spanning_tree.depth_first_loop1.body
  have hdepth : depth > 0#usize := by
    change 0 < depth.val
    omega
  have hrem : frame.remaining ≠ 0#usize := by
    intro he
    have hz : frame.remaining.val = 0 := by simp only [he, UScalar.ofNatCore_val_eq]
    omega
  simp only [hdepth, ite_true, core.result.Result.is_ok, bind_ok,
    alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
  apply WP.spec_bind (Usize.sub_spec (x := depth) (y := 1#usize) (by
    simp only [UScalar.ofNatCore_val_eq]
    omega))
  intro actualSlot has
  have hslotEq : actualSlot = slot := (UScalar.eq_equiv _ _).mpr (by
    have h := has.1
    simp only [UScalar.ofNatCore_val_eq] at h
    omega)
  rw [hslotEq]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec frames slot hslotBound)
  intro actualFrame haf
  have hframeLookup : frames.val[slot.val]? = some actualFrame := by
    rw [List.getElem?_eq_getElem hslotBound, haf]
  have hframeEq : actualFrame = frame := Option.some.inj (hframeLookup.symm.trans hframe)
  have hframeValue : frame = frames.val[slot.val] := hframeEq.symm.trans haf
  rw [hframeEq]
  simp only [hrem, ite_false]
  apply WP.spec_bind (Slice.index_usize_spec neighbors frame.next (by
    change frame.next.val < neighbors.val.length
    omega))
  intro actualNeighbor han
  have hneighborLookup : neighbors.val[frame.next.val]? = some actualNeighbor := by
    rw [List.getElem?_eq_getElem (show frame.next.val < neighbors.val.length by omega), han]
  have hneighborEq : actualNeighbor = neighbor := Option.some.inj (hneighborLookup.symm.trans hneighbor)
  rw [hneighborEq]
  apply WP.spec_bind (Usize.add_spec (x := frame.next) (y := 1#usize) (by
    have hh : hi.val ≤ Usize.max := by scalar_tac
    simp only [UScalar.ofNatCore_val_eq]
    omega))
  intro next hn
  have hnval : next.val = frame.next.val + 1 := by simpa using hn
  apply WP.spec_bind (Usize.add_spec (x := frame.cell) (y := 1#usize) (by
    have := offsets.property
    simp only [UScalar.ofNatCore_val_eq]
    omega))
  intro nextCell hnc
  have hncval : nextCell.val = frame.cell.val + 1 := by simpa using hnc
  apply WP.spec_bind (Slice.index_usize_spec offsets nextCell (by
    change nextCell.val < offsets.val.length
    omega))
  intro rowEnd hre
  have hreLookup : offsets.val[nextCell.val]? = some rowEnd := by
    rw [List.getElem?_eq_getElem (show nextCell.val < offsets.val.length by omega), hre]
  rw [hncval, hhi] at hreLookup
  have hreEq : rowEnd = hi := Option.some.inj hreLookup.symm
  rw [hreEq]
  have hwrap : WP.spec
      (if next = hi then Slice.index_usize offsets frame.cell else ok next)
      (fun chosen => chosen.val = if frame.next.val + 1 = hi.val then lo.val else frame.next.val + 1) := by
    by_cases he : next = hi
    · simp only [he, ite_true]
      apply WP.spec_mono (Slice.index_usize_spec offsets frame.cell (by
        change frame.cell.val < offsets.val.length
        omega))
      intro start hstart
      have hlookup : offsets.val[frame.cell.val]? = some start := by
        rw [List.getElem?_eq_getElem (show frame.cell.val < offsets.val.length by omega), hstart]
      have hstartEq : start = lo := Option.some.inj (hlookup.symm.trans hlo)
      have hwrapEq : frame.next.val + 1 = hi.val := by rw [← hnval, he]
      simp only [hstartEq, hwrapEq, ite_true]
    · simp only [he, ite_false]
      apply (WP.spec_ok _).mpr
      have hnowrap : frame.next.val + 1 ≠ hi.val := by
        intro hnhi
        exact he ((UScalar.eq_equiv _ _).mpr (hnval.trans hnhi))
      simpa only [hnowrap, ite_false] using hnval
  apply WP.spec_bind hwrap
  intro cyclic hcyclic
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec frames slot hslotBound)
  rintro ⟨old, back⟩ ⟨hold, rfl⟩
  have holdEq : old = frame := hold.trans hframeValue.symm
  rw [holdEq]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec
    (frames.set slot { frame with next := cyclic }) slot (by simpa using hslotBound))
  rintro ⟨updated, backUpdated⟩ ⟨hupdated, rfl⟩
  have hupdatedEq : updated = { frame with next := cyclic } := by
    simpa [alloc.vec.Vec.set] using hupdated
  rw [hupdatedEq]
  apply WP.spec_bind (Usize.sub_spec (x := frame.remaining) (y := 1#usize) (by
    simp only [UScalar.ofNatCore_val_eq]
    omega))
  intro remaining hr
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec seen neighbor hneighborBound)
  intro marked hm
  have hmLookup : seen.val[neighbor.val]? = some marked := by
    rw [List.getElem?_eq_getElem hneighborBound, hm]
  have hmtrue : marked = true := Option.some.inj (hmLookup.symm.trans hseen)
  simp only [hmtrue, ite_true]
  apply (WP.spec_ok _).mpr
  let advanced : spanning_tree.Frame := { frame with next := cyclic, remaining := remaining }
  have hwrite : (frames.set slot { frame with next := cyclic }).set slot advanced =
      frames.set slot advanced := by
    apply alloc.vec.Vec.ext
    simp
  refine ⟨advanced, ?_, rfl, ?_, hcyclic⟩
  · change cont (rng, seen, (frames.set slot { frame with next := cyclic }).set slot advanced,
      parents, incoming, reached, depth, core.result.Result.Ok ()) = _
    rw [hwrite]
  · simpa only [advanced, UScalar.ofNatCore_val_eq] using hr.1

/-- Exhausted frames are popped without changing any discovery data or random state. -/
theorem constructor_dfs_pop_step_spec {R : Type*} (adapter : tree.Rng R)
    (offsets neighbors : Slice Usize) (rng : R)
    (seen : alloc.vec.Vec Bool) (frames : alloc.vec.Vec spanning_tree.Frame)
    (parents incoming : alloc.vec.Vec Usize) (reached depth slot : Usize)
    (frame : spanning_tree.Frame)
    (hslot : slot.val + 1 = depth.val) (hslotBound : slot.val < frames.val.length)
    (hframe : frames.val[slot.val]? = some frame) (hempty : frame.remaining = 0#usize) :
    WP.spec (spanning_tree.depth_first_loop1.body adapter offsets neighbors rng seen frames
      parents incoming reached depth (.Ok ())) (fun output =>
        output = cont (rng, seen, frames, parents, incoming, reached, slot,
          core.result.Result.Ok ())) := by
  unfold spanning_tree.depth_first_loop1.body
  have hdepth : depth > 0#usize := by change 0 < depth.val; omega
  simp only [hdepth, ite_true, core.result.Result.is_ok, bind_ok,
    alloc.vec.Vec.index_slice_index]
  apply WP.spec_bind (Usize.sub_spec (x := depth) (y := 1#usize) (by
    simp only [UScalar.ofNatCore_val_eq]
    omega))
  intro actualSlot has
  have hslotEq : actualSlot = slot := (UScalar.eq_equiv _ _).mpr (by
    have h := has.1
    simp only [UScalar.ofNatCore_val_eq] at h
    omega)
  rw [hslotEq]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec frames slot hslotBound)
  intro actualFrame haf
  have hlookup : frames.val[slot.val]? = some actualFrame := by
    rw [List.getElem?_eq_getElem hslotBound, haf]
  have he : actualFrame = frame := Option.some.inj (hlookup.symm.trans hframe)
  simp only [he, hempty, ite_true]
  exact (WP.spec_ok _).mpr rfl

/-- The production loop returns immediately once its active stack is empty. -/
theorem constructor_dfs_done_step_spec {R : Type*} (adapter : tree.Rng R)
    (offsets neighbors : Slice Usize) (rng : R)
    (seen : alloc.vec.Vec Bool) (frames : alloc.vec.Vec spanning_tree.Frame)
    (parents incoming : alloc.vec.Vec Usize) (reached : Usize)
    (status : core.result.Result Unit topology.Error) :
    WP.spec (spanning_tree.depth_first_loop1.body adapter offsets neighbors rng seen frames
      parents incoming reached 0#usize status) (fun output =>
        output = done (rng, seen, frames, parents, incoming, reached, status)) := by
  simp [spanning_tree.depth_first_loop1.body]

end Labyrinth
