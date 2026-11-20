module
public import LabyrinthCore.Model
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- The extracted DFS publication loop copies precisely the initialized parent prefix. -/
theorem constructor_dfs_copy_spec (work : spanning_tree.Workspace)
    (parents : alloc.vec.Vec Usize)
    (hcapacity : parents.val.length ≤ work.parents.val.length) :
    WP.spec (spanning_tree.Tree.dfs_loop work parents 0#usize) (fun output =>
      output.1 = work ∧ output.2.val = work.parents.val.take parents.val.length) := by
  let size := parents.val.length
  let invariant : alloc.vec.Vec Usize × Usize → Prop := fun state =>
    state.1.val.length = size ∧ state.2.val ≤ size ∧
    ∀ j, j < state.2.val → state.1.val[j]? = work.parents.val[j]?
  unfold spanning_tree.Tree.dfs_loop
  apply loop.spec_decr_nat (fun state : alloc.vec.Vec Usize × Usize => size - state.2.val)
    invariant
  · rintro ⟨current, index⟩ hi
    obtain ⟨hlen, hindex, hprefix⟩ := hi
    dsimp only at hlen hindex hprefix
    unfold spanning_tree.Tree.dfs_loop.body
    by_cases hmore : index < alloc.vec.Vec.len current
    · have hib : index.val < current.val.length := by simpa using hmore
      simp only [hmore, ite_true, alloc.vec.Vec.index_slice_index,
        alloc.vec.Vec.index_mut_slice_index]
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec work.parents index (by
        change index.val < work.parents.val.length
        dsimp only [size] at hlen hindex
        omega))
      intro value hv
      apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec current index hib)
      rintro ⟨old, back⟩ hb
      obtain ⟨_, rfl⟩ := hb
      change WP.spec (do
        let next ← index + 1#usize
        ok (cont (current.set index value, next))) _
      apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by
        have := current.property
        simp only [UScalar.ofNatCore_val_eq]
        omega))
      intro next hn
      have hnext : next.val = index.val + 1 := by simpa using hn
      apply (WP.spec_ok _).mpr
      dsimp only [invariant]
      refine ⟨⟨by simpa using hlen, by omega, ?_⟩, by omega⟩
      intro j hj
      by_cases he : j = index.val
      · subst j
        have hlookup : work.parents.val[index.val]? = some value := by
          rw [List.getElem?_eq_getElem (show index.val < work.parents.val.length by
            dsimp only [size] at hlen
            omega), hv]
        simp [alloc.vec.Vec.set, hib, hlookup]
      · have hjold : j < index.val := by omega
        simpa [alloc.vec.Vec.set, he, Ne.symm he] using hprefix j hjold
    · have hdone : index.val = size := by
        have : ¬ index.val < current.val.length := by simpa using hmore
        omega
      simp only [hmore, ite_false]
      apply (WP.spec_ok _).mpr
      change work = work ∧ current.val = work.parents.val.take parents.val.length
      refine ⟨rfl, ?_⟩
      apply List.ext_getElem
      · simp only [List.length_take]
        exact hlen.trans (Nat.min_eq_left hcapacity).symm
      · intro j hjcurrent hjtake
        have hsrc : j < work.parents.val.length := by
          dsimp only [size] at hlen
          omega
        have hlook := hprefix j (by omega)
        rw [List.getElem?_eq_getElem hjcurrent, List.getElem?_eq_getElem hsrc] at hlook
        simpa only [List.getElem_take] using Option.some.inj hlook
  · exact ⟨rfl, by simp, fun _ hj => by simp at hj⟩

end Labyrinth
