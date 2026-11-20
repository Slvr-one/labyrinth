module
public import LabyrinthCore.Model

public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

 theorem mutation_empty_slot_has_capacity
    (w : spanning_tree.Workspace) (hw : WorkspaceValid w)
    (cell : Usize) (hc : cell.val < w.path.val.length)
    (hempty : w.edit_slots.val[cell.val]? = some core.num.Usize.MAX) :
    w.edit_count.val < w.path.val.length := by
  classical
  rcases hw with ⟨_, _, _, _, _, _, hcount, _, hforward, _⟩
  by_contra hnot
  have hfull : w.edit_count.val = w.path.val.length := by omega
  choose nodes hnodes hbounds slots hslots hindices using
    (fun k : Fin w.path.val.length => hforward k.val (by omega))
  let f : Fin w.path.val.length → Fin w.path.val.length :=
    fun k => ⟨(nodes k).val, hbounds k⟩
  have hinjective : Function.Injective f := by
    intro a b hab
    have hnodesEq : (nodes a).val = (nodes b).val :=
      congrArg (fun x : Fin w.path.val.length => x.val) hab
    have hslotsA := hslots a
    rw [hnodesEq, hslots b] at hslotsA
    have hslotsEq : slots b = slots a := Option.some.inj hslotsA
    apply Fin.ext
    rw [← hindices a, ← hindices b]
    exact congrArg UScalar.val hslotsEq.symm
  have hsurjective : Function.Surjective f := Finite.surjective_of_injective hinjective
  obtain ⟨index, hindex⟩ := hsurjective ⟨cell.val, hc⟩
  have hnodeEq : (nodes index).val = cell.val :=
    congrArg (fun x : Fin w.path.val.length => x.val) hindex
  have hslot := hslots index
  rw [hnodeEq, hempty] at hslot
  have hslotEq : core.num.Usize.MAX = slots index := Option.some.inj hslot
  have hindexMax : index.val = Usize.max := by
    rw [← hindices index, ← hslotEq]
    rfl
  have hcap := w.path.property
  have hi := index.isLt
  omega

 theorem mutation_empty_slot_not_active
    (w : spanning_tree.Workspace) (hw : WorkspaceValid w)
    (cell : Usize)
    (hempty : w.edit_slots.val[cell.val]? = some core.num.Usize.MAX)
    (i : Nat) (hi : i < w.edit_count.val) :
    w.edit_nodes.val[i]? ≠ some cell := by
  rcases hw with ⟨_, _, _, _, _, _, hcount, _, hforward, _⟩
  obtain ⟨node, hnode, _, slot, hslot, hindex⟩ := hforward i hi
  intro heq
  rw [heq] at hnode
  have hnodeEq : cell = node := Option.some.inj hnode
  rw [← hnodeEq, hempty] at hslot
  have hslotEq : core.num.Usize.MAX = slot := Option.some.inj hslot
  have hiMax : i = Usize.max := by
    rw [← hindex, ← hslotEq]
    rfl
  have hcap := w.path.property
  omega

end Labyrinth
