module
public import LabyrinthCore.ConstructorDFS
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- An unseen neighbor is descended into immediately: the generated body records the parent,
incoming original adjacency index, discovery mark, and one freshly chosen child frame. -/
theorem constructor_dfs_discovery_step_spec {R : Type*} (adapter : tree.Rng R)
    (hrng : constructorLegalRng adapter) (offsets neighbors : Slice Usize) (rng : R)
    (seen : alloc.vec.Vec Bool) (frames : alloc.vec.Vec spanning_tree.Frame)
    (parents incoming : alloc.vec.Vec Usize) (reached depth slot : Usize)
    (frame : spanning_tree.Frame) (lo hi neighbor childLo childHi : Usize)
    (hslot : slot.val + 1 = depth.val) (hdepthBound : depth.val < frames.val.length)
    (hframe : frames.val[slot.val]? = some frame)
    (hcell : frame.cell.val + 1 < offsets.val.length)
    (hlo : offsets.val[frame.cell.val]? = some lo)
    (hhi : offsets.val[frame.cell.val + 1]? = some hi)
    (hnext : lo.val ≤ frame.next.val ∧ frame.next.val < hi.val)
    (hstorage : hi.val ≤ neighbors.val.length) (hremaining : 0 < frame.remaining.val)
    (hneighbor : neighbors.val[frame.next.val]? = some neighbor)
    (hseenBound : neighbor.val < seen.val.length) (hseen : seen.val[neighbor.val]? = some false)
    (hparentBound : neighbor.val < parents.val.length)
    (hincomingBound : neighbor.val < incoming.val.length) (hreached : reached.val < Usize.max)
    (hchild : neighbor.val + 1 < offsets.val.length)
    (hchildLo : offsets.val[neighbor.val]? = some childLo)
    (hchildHi : offsets.val[neighbor.val + 1]? = some childHi)
    (hchildOrdered : childLo.val ≤ childHi.val) :
    WP.spec (spanning_tree.depth_first_loop1.body adapter offsets neighbors rng seen frames
      parents incoming reached depth (.Ok ())) (fun output =>
        ∃ advanced child : spanning_tree.Frame, ∃ rng' : R, ∃ depth' reached' : Usize,
          advanced.cell = frame.cell ∧ advanced.remaining.val = frame.remaining.val - 1 ∧
          advanced.next.val = (if frame.next.val + 1 = hi.val then lo.val else frame.next.val + 1) ∧
          child.cell = neighbor ∧ child.remaining.val = childHi.val - childLo.val ∧
          (childLo.val = childHi.val → child.next = childLo ∧ rng' = rng) ∧
          (childLo.val < childHi.val → childLo.val ≤ child.next.val ∧ child.next.val < childHi.val) ∧
          depth'.val = depth.val + 1 ∧ reached'.val = reached.val + 1 ∧
          output = cont (rng', seen.set neighbor true, (frames.set slot advanced).set depth child,
            parents.set neighbor frame.cell, incoming.set neighbor frame.next, reached', depth',
            core.result.Result.Ok ())) := by
  have hslotBound : slot.val < frames.val.length := by omega
  unfold spanning_tree.depth_first_loop1.body
  have hdepth : depth > 0#usize := by change 0 < depth.val; omega
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
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec seen neighbor hseenBound)
  intro marked hm
  have hmLookup : seen.val[neighbor.val]? = some marked := by
    rw [List.getElem?_eq_getElem hseenBound, hm]
  have hmfalse : marked = false := Option.some.inj (hmLookup.symm.trans hseen)
  simp only [hmfalse, Bool.false_eq_true, ite_false]
  apply WP.spec_bind (constructor_enter_spec adapter hrng offsets neighbor childLo childHi rng
    hchild hchildLo hchildHi hchildOrdered)
  rintro ⟨status, rng'⟩ ⟨child, hstatus, hchildCell, hchildRemaining, hchildEmpty, hchildNext⟩
  dsimp only at hstatus hchildEmpty
  rw [hstatus]
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec parents neighbor hparentBound)
  rintro ⟨oldParent, backParent⟩ ⟨_, rfl⟩
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec incoming neighbor hincomingBound)
  rintro ⟨oldIncoming, backIncoming⟩ ⟨_, rfl⟩
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec seen neighbor hseenBound)
  rintro ⟨oldSeen, backSeen⟩ ⟨_, rfl⟩
  let advanced : spanning_tree.Frame := { frame with next := cyclic, remaining := remaining }
  have hwrite : (frames.set slot { frame with next := cyclic }).set slot advanced =
      frames.set slot advanced := by
    apply alloc.vec.Vec.ext
    simp
  rw [hwrite]
  change WP.spec (do
    let (_, backFrame) ← (frames.set slot advanced).index_mut_usize depth
    let depth' ← depth + 1#usize
    let reached' ← reached + 1#usize
    ok (cont (rng', seen.set neighbor true, backFrame child, parents.set neighbor frame.cell,
      incoming.set neighbor frame.next, reached', depth', core.result.Result.Ok ()))) _
  apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec (frames.set slot advanced) depth (by
    simpa using hdepthBound))
  rintro ⟨oldChild, backChild⟩ ⟨_, rfl⟩
  apply WP.spec_bind (Usize.add_spec (x := depth) (y := 1#usize) (by
    have := frames.property
    simp only [UScalar.ofNatCore_val_eq]
    omega))
  intro depth' hd'
  apply WP.spec_bind (Usize.add_spec (x := reached) (y := 1#usize) (by
    simp only [UScalar.ofNatCore_val_eq]
    omega))
  intro reached' hr'
  apply (WP.spec_ok _).mpr
  exact ⟨advanced, child, rng', depth', reached', rfl,
    by simpa only [advanced, UScalar.ofNatCore_val_eq] using hr.1,
    hcyclic, hchildCell, hchildRemaining, hchildEmpty, hchildNext,
    by simpa using hd', by simpa using hr', rfl⟩

end Labyrinth
