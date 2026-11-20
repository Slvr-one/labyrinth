module
public import LabyrinthCore.ConstructorDFSInvariant
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

theorem constructor_dfs_frame_advance (offsets : Slice Usize)
    (frame advanced : spanning_tree.Frame) (h : ConstructorDFSFrameValid offsets frame)
    (hpos : 0 < frame.remaining.val) (hc : advanced.cell = frame.cell)
    (hr : advanced.remaining.val = frame.remaining.val - 1)
    (hn : advanced.next.val = if frame.next.val + 1 =
      constructorDFSOffset offsets (frame.cell.val + 1)
      then constructorDFSOffset offsets frame.cell.val else frame.next.val + 1) :
    ConstructorDFSFrameValid offsets advanced := by
  have hb := h.next hpos
  refine ⟨by simpa only [hc] using h.cell, ?_, ?_⟩
  · rw [hc, hr]
    exact Nat.le_trans (Nat.sub_le _ _) h.remaining
  · intro _
    rw [hc, hn]
    split <;> omega

/-- Popping a fully scanned row preserves the owed-slot frontier. -/
theorem constructor_dfs_invariant_pop
    {offsets neighbors : Slice Usize} {root capacity : Nat}
    {seen : alloc.vec.Vec Bool} {frames : alloc.vec.Vec spanning_tree.Frame}
    {parents incoming : alloc.vec.Vec Usize} {reached depth : Nat}
    {visited : Finset Nat} {rank : Nat → Nat}
    (h : ConstructorDFSInvariant offsets neighbors root capacity seen frames parents incoming
      reached (depth + 1) visited rank)
    (frame : spanning_tree.Frame) (hf : frames.val[depth]? = some frame)
    (hz : frame.remaining.val = 0) :
    ConstructorDFSInvariant offsets neighbors root capacity seen frames parents incoming
      reached depth visited rank := by
  refine { h with
    depth_bound := by have := h.depth_bound; omega
    frame := ?_
    frontier := ?_ }
  · intro i hi value hl
    exact h.frame i (by omega) value hl
  · intro u hu slot value hlo hhi hl hn
    obtain ⟨i, active, hi, ha, hc, hp⟩ := h.frontier u hu slot value hlo hhi hl hn
    have hne : i ≠ depth := by
      intro he
      subst i
      have heq : active = frame := Option.some.inj (ha.symm.trans hf)
      subst active
      exact constructor_dfs_pending_empty offsets frame hz slot hp
    exact ⟨i, active, by omega, ha, hc, hp⟩

/-- A scan of an already discovered neighbor removes no still-owed discovery slot. -/
theorem constructor_dfs_invariant_seen
    {offsets neighbors : Slice Usize} {root capacity : Nat}
    {seen : alloc.vec.Vec Bool} {frames : alloc.vec.Vec spanning_tree.Frame}
    {parents incoming : alloc.vec.Vec Usize} {reached depth : Nat}
    {visited : Finset Nat} {rank : Nat → Nat}
    (h : ConstructorDFSInvariant offsets neighbors root capacity seen frames parents incoming
      reached depth visited rank)
    (index : Usize) (frame advanced : spanning_tree.Frame)
    (hi : index.val < depth) (hf : frames.val[index.val]? = some frame)
    (hpos : 0 < frame.remaining.val) (hc : advanced.cell = frame.cell)
    (hr : advanced.remaining.val = frame.remaining.val - 1)
    (hn : advanced.next.val = if frame.next.val + 1 =
      constructorDFSOffset offsets (frame.cell.val + 1)
      then constructorDFSOffset offsets frame.cell.val else frame.next.val + 1)
    (neighbor : Usize) (hl : neighbors.val[frame.next.val]? = some neighbor)
    (hm : neighbor.val ∈ visited) :
    ConstructorDFSInvariant offsets neighbors root capacity seen (frames.set index advanced)
      parents incoming reached depth visited rank := by
  have hib : index.val < frames.val.length := by
    have := h.depth_bound
    have := constructor_dfs_reached_bound h
    have := h.capacity_bound
    rw [h.frames_length]
    omega
  have hfv := (h.frame index.val hi frame hf).2
  refine { h with
    frames_length := by simpa [alloc.vec.Vec.set] using h.frames_length
    frame := ?_
    frontier := ?_ }
  · intro i hactive value hlookup
    by_cases he : i = index.val
    · subst i
      have heq : value = advanced := by
        have hx : (frames.set index advanced).val[index.val]? = some advanced := by
          simp [alloc.vec.Vec.set, hib]
        exact Option.some.inj (hlookup.symm.trans hx)
      subst value
      exact ⟨by simpa only [hc] using (h.frame index.val hi frame hf).1,
        constructor_dfs_frame_advance offsets frame advanced hfv hpos hc hr hn⟩
    · have hold : frames.val[i]? = some value := by
        simpa [alloc.vec.Vec.set, he, Ne.symm he] using hlookup
      exact h.frame i hactive value hold
  · intro u hu slot value hlo hhi hlookup hnot
    obtain ⟨i, active, hactive, ha, hcell, hp⟩ :=
      h.frontier u hu slot value hlo hhi hlookup hnot
    by_cases he : i = index.val
    · subst i
      have heq : active = frame := Option.some.inj (ha.symm.trans hf)
      subst active
      have hslot : slot ≠ frame.next.val := by
        intro hs
        rw [hs, hl] at hlookup
        have heq : neighbor = value := Option.some.inj hlookup
        exact hnot (by simpa only [← heq] using hm)
      refine ⟨index.val, advanced, hi, ?_, by rw [hc]; exact hcell, ?_⟩
      · simp [alloc.vec.Vec.set, hib]
      · exact constructor_dfs_pending_advance offsets frame advanced slot (hfv.next hpos)
          hc hr hn hp hslot
    · refine ⟨i, active, hactive, ?_, hcell, hp⟩
      simpa [alloc.vec.Vec.set, he, Ne.symm he] using ha

/-- The discovery writes extend the ranked forest and install precisely the entered child row. -/
theorem constructor_dfs_invariant_discover
    {offsets neighbors : Slice Usize} {root capacity : Nat}
    {seen : alloc.vec.Vec Bool} {frames : alloc.vec.Vec spanning_tree.Frame}
    {parents incoming : alloc.vec.Vec Usize} {reached depth : Nat}
    {visited : Finset Nat} {rank : Nat → Nat}
    (h : ConstructorDFSInvariant offsets neighbors root capacity seen frames parents incoming
      reached depth visited rank)
    (index push : Usize) (frame advanced child : spanning_tree.Frame) (neighbor : Usize)
    (hi : index.val < depth) (hp : push.val = depth)
    (hroom : depth < capacity) (hf : frames.val[index.val]? = some frame)
    (hpos : 0 < frame.remaining.val) (hc : advanced.cell = frame.cell)
    (hr : advanced.remaining.val = frame.remaining.val - 1)
    (hn : advanced.next.val = if frame.next.val + 1 =
      constructorDFSOffset offsets (frame.cell.val + 1)
      then constructorDFSOffset offsets frame.cell.val else frame.next.val + 1)
    (hv : neighbor.val < constructorDFSVertexCount offsets) (hunseen : neighbor.val ∉ visited)
    (hl : neighbors.val[frame.next.val]? = some neighbor)
    (hchild : child.cell = neighbor) (hchildValid : ConstructorDFSFrameValid offsets child)
    (hchildRemaining : child.remaining.val =
      constructorDFSOffset offsets (neighbor.val + 1) - constructorDFSOffset offsets neighbor.val) :
    ConstructorDFSInvariant offsets neighbors root capacity (seen.set neighbor true)
      ((frames.set index advanced).set push child) (parents.set neighbor frame.cell)
      (incoming.set neighbor frame.next) (reached + 1) (depth + 1)
      (insert neighbor.val visited) (fun v => if v = neighbor.val then reached else rank v) := by
  have hvc : neighbor.val < capacity := by have := h.capacity_bound; omega
  have hib : index.val < frames.val.length := by rw [h.frames_length]; omega
  have hpb : push.val < frames.val.length := by rw [h.frames_length, hp]; exact hroom
  have hrootne : root ≠ neighbor.val := by
    intro he
    exact hunseen (he ▸ h.root_mem)
  have hfm := (h.frame index.val hi frame hf).1
  have hfv := (h.frame index.val hi frame hf).2
  have holdNe (v : Nat) (hm : v ∈ visited) : v ≠ neighbor.val := by
    intro he
    exact hunseen (he ▸ hm)
  have hlookup (i : Nat) (hactive : i < depth) :
      ((frames.set index advanced).set push child).val[i]? =
        (frames.set index advanced).val[i]? := by
    have hne : i ≠ push.val := by omega
    simp [alloc.vec.Vec.set, Ne.symm hne]
  refine {
    seen_length := ?_
    frames_length := ?_
    parents_length := ?_
    incoming_length := ?_
    capacity_bound := h.capacity_bound
    visited_bound := ?_
    count := ?_
    seen_iff := ?_
    root_mem := ?_
    root_parent := ?_
    depth_bound := ?_
    parent := ?_
    rank_bound := ?_
    rank_decreases := ?_
    witness := ?_
    frame := ?_
    frontier := ?_ }
  · simpa [alloc.vec.Vec.set] using h.seen_length
  · simpa [alloc.vec.Vec.set] using h.frames_length
  · simpa [alloc.vec.Vec.set] using h.parents_length
  · simpa [alloc.vec.Vec.set] using h.incoming_length
  · intro v hm
    rcases Finset.mem_insert.mp hm with he | hm
    · exact Finset.mem_range.mpr (he ▸ hv)
    · exact h.visited_bound hm
  · rw [Finset.card_insert_of_notMem hunseen, h.count]
  · intro v hb
    by_cases he : v = neighbor.val
    · subst v
      simp [alloc.vec.Vec.set, h.seen_length, hvc]
    · simpa [alloc.vec.Vec.set, he, Ne.symm he] using h.seen_iff v hb
  · exact Finset.mem_insert_of_mem h.root_mem
  · obtain ⟨value, hvp, he⟩ := h.root_parent
    exact ⟨value, by simpa [alloc.vec.Vec.set, hrootne, Ne.symm hrootne] using hvp, he⟩
  · have := h.depth_bound
    omega
  · intro v hm
    rcases Finset.mem_insert.mp hm with he | hm
    · subst v
      refine ⟨frame.cell, ?_, Finset.mem_insert_of_mem hfm⟩
      simp [alloc.vec.Vec.set, h.parents_length, hvc]
    · obtain ⟨value, hval, hmem⟩ := h.parent v hm
      exact ⟨value, by simpa [alloc.vec.Vec.set, holdNe v hm, Ne.symm (holdNe v hm)] using hval,
        Finset.mem_insert_of_mem hmem⟩
  · intro v hm
    rcases Finset.mem_insert.mp hm with he | hm
    · subst v
      simp
    · have hb := h.rank_bound v hm
      simp only [holdNe v hm, ite_false]
      omega
  · intro v hm hne value hval
    rcases Finset.mem_insert.mp hm with he | hm
    · subst v
      have heq : value = frame.cell := by
        have hx : (parents.set neighbor frame.cell).val[neighbor.val]? = some frame.cell := by
          simp [alloc.vec.Vec.set, h.parents_length, hvc]
        exact Option.some.inj (hval.symm.trans hx)
      subst value
      simpa [holdNe frame.cell.val hfm] using h.rank_bound frame.cell.val hfm
    · have hvne := holdNe v hm
      have hold : parents.val[v]? = some value := by
        simpa [alloc.vec.Vec.set, hvne, Ne.symm hvne] using hval
      obtain ⟨actual, ha, hmem⟩ := h.parent v hm
      have heq : actual = value := Option.some.inj (ha.symm.trans hold)
      have hpne : value.val ≠ neighbor.val := holdNe value.val (heq ▸ hmem)
      simpa only [hvne, hpne, ite_false] using h.rank_decreases v hm hne value hold
  · intro v hm hne
    rcases Finset.mem_insert.mp hm with he | hm
    · subst v
      refine ⟨frame.cell, frame.next, neighbor, ?_, ?_, (hfv.next hpos).1,
        (hfv.next hpos).2, hl, rfl⟩
      · simp [alloc.vec.Vec.set, h.parents_length, hvc]
      · simp [alloc.vec.Vec.set, h.incoming_length, hvc]
    · obtain ⟨parent, slot, value, hpa, hin, hlo, hhi, hval, he⟩ := h.witness v hm hne
      exact ⟨parent, slot, value,
        by simpa [alloc.vec.Vec.set, holdNe v hm, Ne.symm (holdNe v hm)] using hpa,
        by simpa [alloc.vec.Vec.set, holdNe v hm, Ne.symm (holdNe v hm)] using hin,
        hlo, hhi, hval, he⟩
  · intro i hactive value hval
    by_cases he : i = depth
    · have hlookupPush : ((frames.set index advanced).set push child).val[i]? = some child := by
        rw [he, ← hp]
        simp only [alloc.vec.Vec.set, alloc.vec.Vec.from_val]
        apply List.getElem?_set_self
        simpa using hpb
      have heq : value = child := Option.some.inj (hval.symm.trans hlookupPush)
      subst value
      exact ⟨by simp [hchild], hchildValid⟩
    · have hid : i < depth := by omega
      rw [hlookup i hid] at hval
      by_cases hei : i = index.val
      · subst i
        have hx : (frames.set index advanced).val[index.val]? = some advanced := by
          simp [alloc.vec.Vec.set, hib]
        have heq : value = advanced := Option.some.inj (hval.symm.trans hx)
        subst value
        exact ⟨by rw [hc]; exact Finset.mem_insert_of_mem hfm,
          constructor_dfs_frame_advance offsets frame advanced hfv hpos hc hr hn⟩
      · have hold : frames.val[i]? = some value := by
          simpa [alloc.vec.Vec.set, hei, Ne.symm hei] using hval
        obtain ⟨hm, hvalid⟩ := h.frame i hid value hold
        exact ⟨Finset.mem_insert_of_mem hm, hvalid⟩
  · intro u hu slot value hlo hhi hval hnot
    have hnotOld : value.val ∉ visited := fun hm => hnot (Finset.mem_insert_of_mem hm)
    have hnotNew : value.val ≠ neighbor.val := by
      intro he
      apply hnot
      rw [he]
      exact Finset.mem_insert_self ..
    rcases Finset.mem_insert.mp hu with he | hm
    · subst u
      refine ⟨depth, child, by omega, ?_, by simp only [hchild], ?_⟩
      · rw [← hp]
        simp only [alloc.vec.Vec.set, alloc.vec.Vec.from_val]
        apply List.getElem?_set_self
        simpa using hpb
      · have hrow : constructorDFSOffset offsets neighbor.val <
            constructorDFSOffset offsets (neighbor.val + 1) := by omega
        have hposChild : 0 < child.remaining.val := by omega
        exact constructor_dfs_pending_full offsets child (hchildValid.next hposChild)
          (by simpa only [hchild] using hchildRemaining) slot
          (by simpa only [hchild] using And.intro hlo hhi)
    · obtain ⟨i, active, hactive, ha, hcell, hpend⟩ :=
        h.frontier u hm slot value hlo hhi hval hnotOld
      by_cases he : i = index.val
      · subst i
        have heq : active = frame := Option.some.inj (ha.symm.trans hf)
        subst active
        have hsne : slot ≠ frame.next.val := by
          intro he
          rw [he, hl] at hval
          exact hnotNew (congrArg (fun x : Usize => x.val) (Option.some.inj hval).symm)
        refine ⟨index.val, advanced, by omega, ?_, by rw [hc]; exact hcell,
          constructor_dfs_pending_advance offsets frame advanced slot (hfv.next hpos)
            hc hr hn hpend hsne⟩
        rw [hlookup index.val hi]
        simp [alloc.vec.Vec.set, hib]
      · refine ⟨i, active, by omega, ?_, hcell, hpend⟩
        rw [hlookup i hactive]
        simpa [alloc.vec.Vec.set, he, Ne.symm he] using ha

end Labyrinth
