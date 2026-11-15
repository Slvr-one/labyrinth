module
public import LabyrinthCore.Model
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- This is the exact addressable-allocation bound used by extracted Rust. -/
def constructorStorageFits (count bytes : Usize) : Prop :=
  count.val * bytes.val ≤ Usize.max ∧
  count.val * bytes.val ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val

instance (count bytes : Usize) : Decidable (constructorStorageFits count bytes) :=
  inferInstanceAs (Decidable (count.val * bytes.val ≤ Usize.max ∧
    count.val * bytes.val ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val))

theorem constructor_checked_mul_some
    (x y : Usize) (h : x.val * y.val ≤ Usize.max) :
    ∃ z, Usize.checked_mul x y = some z ∧ z.val = x.val * y.val := by
  have hm := Usize.checked_mul_bv_spec x y
  cases he : Usize.checked_mul x y with
  | none => simp only [he] at hm; omega
  | some z =>
    simp only [he] at hm
    exact ⟨z, rfl, hm.2.1⟩

theorem constructor_check_storage_eq (count bytes : Usize) :
    topology.check_storage count bytes =
      ok (if constructorStorageFits count bytes then .Ok () else .Err .Overflow) := by
  have hm := Usize.checked_mul_bv_spec count bytes
  cases he : Usize.checked_mul count bytes with
  | none =>
    simp only [he] at hm
    have hn : ¬ constructorStorageFits count bytes := fun h => by
      have := h.1
      omega
    simp [topology.check_storage, he, hn, lift, core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | some z =>
    simp only [he] at hm
    have hz := hm.2.1
    have hf : constructorStorageFits count bytes ↔
        z.val ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val := by
      unfold constructorStorageFits
      omega
    simp only [topology.check_storage, he, lift, bind_ok, core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch, hf]
    have hlt : (IScalar.hcast .Usize core.num.Isize.MAX) < z ↔
        ¬ z.val ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val := by
      simp only [UScalar.lt_equiv, not_le]
    simp only [hlt, ite_not]
    split <;> rfl

/-- Totality of the extracted allocation guard, including its exact rejection criterion. -/
theorem constructor_check_storage_spec (count bytes : Usize) :
    WP.spec (topology.check_storage count bytes)
      (fun r => r = if constructorStorageFits count bytes then .Ok () else .Err .Overflow) := by
  rw [constructor_check_storage_eq]
  simp

private theorem constructor_initialized_workspace_valid
    (n edges : Usize)
    (seen : alloc.vec.Vec Bool) (frames : alloc.vec.Vec spanning_tree.Frame)
    (zero slots : alloc.vec.Vec Usize)
    (hs : seen.val = List.replicate n.val false)
    (hf : frames.val = List.replicate n.val
      { cell := 0#usize, next := 0#usize, remaining := 0#usize })
    (hz : zero.val = List.replicate n.val 0#usize)
    (he : slots.val = List.replicate n.val core.num.Usize.MAX) :
    WorkspaceValid {
      seen, frames, path := zero, parents := zero, incoming := zero,
      edit_slots := slots, edit_nodes := zero, edit_count := 0#usize,
      edge_capacity := edges } := by
  simp only [WorkspaceValid, hs, hf, hz, he, List.length_replicate]
  simp only [UScalar.ofNatCore_val_eq, List.take_zero, List.map_nil, List.nodup_nil,
    Nat.zero_le, Nat.not_lt_zero, false_implies, forall_const,
    true_and]
  intro node hn
  refine ⟨core.num.Usize.MAX, ?_, Or.inl rfl⟩
  simp [hn]

/-- Totality and scratch invariants of the actual workspace constructor for every size. -/
theorem constructor_workspace_new_spec (cells edges : Usize) :
    WP.spec (spanning_tree.Workspace.new cells edges) (fun r =>
      match r with
      | .Ok w => WorkspaceValid w ∧ w.path.val.length = cells.val ∧
          w.edge_capacity = edges
      | .Err _ => True) := by
  unfold spanning_tree.Workspace.new
  simp only [constructor_check_storage_eq]
  cases Usize.checked_mul edges 2#usize <;>
    simp only [lift, bind_ok,
      core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] <;>
    split_ifs <;> simp_all
  all_goals
    apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneBool false cells rfl)
    intro seen hs
    apply WP.spec_bind (alloc.vec.from_elem_spec
      spanning_tree.Frame.Insts.CoreCloneClone
      { cell := 0#usize, next := 0#usize, remaining := 0#usize } cells rfl)
    intro frames hf
    apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize cells rfl)
    intro zero hz
    apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize core.num.Usize.MAX cells rfl)
    intro slots he
    apply (WP.spec_ok _).mpr
    exact ⟨constructor_initialized_workspace_valid cells edges seen frames zero slots
      hs.1 hf.1 hz.1 he.1, by simp [hz.1], rfl⟩

/-- Independent numerical precondition, not a hypothesis that the operation succeeds. -/
def constructorWorkspaceFits (cells edges : Usize) : Prop :=
  cells ≠ 0#usize ∧
  constructorStorageFits cells 8#usize ∧
  constructorStorageFits cells 24#usize ∧
  constructorStorageFits edges 16#usize ∧
  edges.val * 2 ≤ Usize.max ∧
  edges.val * 2 * 8 ≤ Usize.max ∧
  edges.val * 2 * 8 ≤ (IScalar.hcast .Usize core.num.Isize.MAX).val

/-- Every representable, nonempty workspace request is accepted with valid initialized scratch. -/
theorem constructor_workspace_new_accepts (cells edges : Usize)
    (h : constructorWorkspaceFits cells edges) :
    WP.spec (spanning_tree.Workspace.new cells edges) (fun r =>
      ∃ w, r = .Ok w ∧ WorkspaceValid w ∧ w.path.val.length = cells.val ∧
        w.edge_capacity = edges) := by
  obtain ⟨hn, h8, h24, h16, h2, h28, hlim⟩ := h
  obtain ⟨twice, hmul, htwice⟩ := constructor_checked_mul_some edges 2#usize (by simpa using h2)
  have htwiceFits : constructorStorageFits twice 8#usize := by
    simp only [constructorStorageFits, htwice, UScalar.ofNatCore_val_eq]
    exact ⟨h28, hlim⟩
  unfold spanning_tree.Workspace.new
  simp only [hn, ite_false, constructor_check_storage_eq, h8, h24, h16,
    ite_true, hmul, lift, bind_ok, htwiceFits,
    core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch]
  apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneBool false cells rfl)
  intro seen hs
  apply WP.spec_bind (alloc.vec.from_elem_spec
    spanning_tree.Frame.Insts.CoreCloneClone
    { cell := 0#usize, next := 0#usize, remaining := 0#usize } cells rfl)
  intro frames hf
  apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize cells rfl)
  intro zero hz
  apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize core.num.Usize.MAX cells rfl)
  intro slots he
  apply (WP.spec_ok _).mpr
  exact ⟨_, rfl, constructor_initialized_workspace_valid cells edges seen frames zero slots
    hs.1 hf.1 hz.1 he.1, by simp [hz.1], rfl⟩

end Labyrinth
