module
public import LabyrinthCore.MutationVirtualRoot

public section

open Aeneas Aeneas.Std Aeneas.Std.WP labyrinth_core

namespace Labyrinth

 theorem mutation_workspace_active_slot_injective
    (w : spanning_tree.Workspace) (hw : WorkspaceValid w)
    (a b : Nat) (slot : Usize)
    (ha : a < w.path.val.length) (hb : b < w.path.val.length)
    (hslot : slot ≠ core.num.Usize.MAX)
    (hgetA : w.edit_slots.val[a]? = some slot)
    (hgetB : w.edit_slots.val[b]? = some slot) : a = b := by
  obtain ⟨sa, hsa, hca⟩ := hw.2.2.2.2.2.2.2.2.2 a ha
  obtain ⟨sb, hsb, hcb⟩ := hw.2.2.2.2.2.2.2.2.2 b hb
  have hea : sa = slot := Option.some.inj (hsa.symm.trans hgetA)
  have heb : sb = slot := Option.some.inj (hsb.symm.trans hgetB)
  have hnotmax : slot.val ≠ Usize.max := fun he => hslot (UScalar.eq_of_val_eq he)
  rw [hea] at hca
  rw [heb] at hcb
  obtain ⟨_, na, hna, hva⟩ := hca.resolve_left hnotmax
  obtain ⟨_, nb, hnb, hvb⟩ := hcb.resolve_left hnotmax
  have he : na = nb := Option.some.inj (hna.symm.trans hnb)
  exact hva.symm.trans ((congrArg UScalar.val he).trans hvb)

 theorem mutation_workspace_set_parent_exact
    (w : spanning_tree.Workspace) (cell parent : Usize) (published : Slice Usize)
    (hw : WorkspaceValid w) (hc : cell.val < w.path.val.length) :
    spanning_tree.Workspace.set_parent w cell parent ⦃ out =>
      WorkspaceValid out ∧ out.path = w.path ∧ out.seen = w.seen ∧
      out.frames = w.frames ∧ out.incoming = w.incoming ∧
      out.edge_capacity = w.edge_capacity ∧
      ∀ u, u < w.path.val.length →
        mutationVirtualParent out published u =
          if u = cell.val then parent.val else mutationVirtualParent w published u ⦄ := by
  apply spec_mono (mutation_workspace_set_parent_total w cell parent hw hc)
  rintro out ⟨hout, hpath, hseen, hframes, hincoming, hedge,
    ⟨updated, hupdated, hupdatedCount, hupdatedParent⟩, hslots, hparents⟩
  refine ⟨hout, hpath, hseen, hframes, hincoming, hedge, ?_⟩
  intro u hu
  by_cases heq : u = cell.val
  · have hnotmax : updated ≠ core.num.Usize.MAX := by
      intro he
      have hcount := hout.2.2.2.2.2.2.1
      have hmax := out.path.property
      have heval : updated.val = Usize.max := by rw [he]; rfl
      omega
    simp [mutationVirtualParent, heq, hupdated, hnotmax, hupdatedParent]
  · obtain ⟨slot, hslot, hcases⟩ := hw.2.2.2.2.2.2.2.2.2 u hu
    have hslotOut : out.edit_slots.val[u]? = some slot := (hslots u heq).trans hslot
    by_cases hmax : slot = core.num.Usize.MAX
    · simp [mutationVirtualParent, heq, hslot, hslotOut, hmax]
    · have hnotmax : slot.val ≠ Usize.max := fun he => hmax (UScalar.eq_of_val_eq he)
      have hactive : slot.val < w.edit_count.val := (hcases.resolve_left hnotmax).1
      have hother : w.edit_slots.val[cell.val]? ≠ some slot := by
        intro hcell
        exact heq (mutation_workspace_active_slot_injective w hw u cell.val slot hu hc
          hmax hslot hcell)
      have hparent := hparents slot hactive hother
      simp [mutationVirtualParent, heq, hslot, hslotOut, hmax, hparent]

end Labyrinth
