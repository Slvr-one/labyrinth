module
public import LabyrinthCore.SceneInvSwept

/-! The scene invariant, part 12: the workspace `Scene::new` hands to the scene.

`Tree::scene_dfs` keeps its workspace's edge capacity and path length: the quotient depth-first
search rewrites only the search tables, the selection loop passes the workspace through, and the
final expanded search rewrites the path entry by entry. It also returns a tree only after
`Workspace::ensure` accepted, so the carrier's cells fit the path. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

theorem clear_edits_frame (w : spanning_tree.Workspace) :
    OkPost (spanning_tree.Workspace.clear_edits w)
      (fun w' => w'.edge_capacity = w.edge_capacity ∧ w'.path = w.path) := by
  unfold spanning_tree.Workspace.clear_edits spanning_tree.Workspace.clear_edits_loop
  refine okPost_bind (okPost_loop (fun s : spanning_tree.Workspace × Std.Usize =>
      s.1.edge_capacity = w.edge_capacity ∧ s.1.path = w.path)
    (fun r => r.2.2.2.2.2.2.2 = w.edge_capacity ∧ r.2.2.1 = w.path) _ ?_ _ ⟨rfl, rfl⟩)
    (fun r hr => okPost_ok hr)
  rintro ⟨s, i⟩ hs
  unfold spanning_tree.Workspace.clear_edits_loop.body
  capacity_walk

theorem depth_first_loop0_frame (root n : Std.Usize) (w : spanning_tree.Workspace)
    (i : Std.Usize) :
    OkPost (spanning_tree.depth_first_loop0 root w n i)
      (fun w' => w'.edge_capacity = w.edge_capacity ∧ w'.path = w.path) := by
  unfold spanning_tree.depth_first_loop0
  refine okPost_loop (fun s : spanning_tree.Workspace × Std.Usize =>
      s.1.edge_capacity = w.edge_capacity ∧ s.1.path = w.path) _ _ ?_ _ ⟨rfl, rfl⟩
  rintro ⟨s, j⟩ hs
  unfold spanning_tree.depth_first_loop0.body
  capacity_walk

/-- `depth_first` keeps the workspace's edge capacity and path. -/
theorem depth_first_frame {R : Type _} (adapter : tree.Rng R) (offsets neighbors : Slice Std.Usize)
    (root : Std.Usize) (rng : R) (w : spanning_tree.Workspace) :
    OkPost (spanning_tree.depth_first adapter offsets neighbors root rng w)
      (fun out => out.2.2.edge_capacity = w.edge_capacity ∧ out.2.2.path = w.path) := by
  unfold spanning_tree.depth_first
  repeat' (first
    | (exact okPost_ok (by simp_all))
    | (refine okPost_bind (clear_edits_frame _) (fun _ _ => ?_))
    | (refine okPost_bind (depth_first_loop0_frame _ _ _ _) (fun _ _ => ?_))
    | (refine okPost_bind (okPost_trivial _) (fun _ _ => ?_))
    | split)

/-- The selection loop of `scene_dfs` passes the workspace through. -/
theorem scene_dfs_loop7_frame (w : spanning_tree.Workspace) (i cc : Std.Usize)
    (witnesses : alloc.vec.Vec topology.Edge) (qr : Std.Usize) (sel : alloc.vec.Vec topology.Edge)
    (cnt : Std.Usize) :
    OkPost (spanning_tree.Tree.scene_dfs_loop7 w i cc witnesses qr sel cnt) (fun r => r.1 = w) := by
  unfold spanning_tree.Tree.scene_dfs_loop7
  refine okPost_loop (fun s : spanning_tree.Workspace × Std.Usize × alloc.vec.Vec topology.Edge ×
      Std.Usize => s.1 = w) (fun r : spanning_tree.Workspace × alloc.vec.Vec topology.Edge =>
      r.1 = w) _ ?_ _ rfl
  rintro ⟨s, j, sl, c⟩ hs
  simp only at hs
  subst hs
  unfold spanning_tree.Tree.scene_dfs_loop7.body
  dsimp only
  by_cases hlt : j < cc
  · simp only [hlt, ↓reduceIte]
    refine okPost_bind (P := fun t : spanning_tree.Workspace × alloc.vec.Vec topology.Edge ×
        Std.Usize => t.1 = s) ?_
      (fun t ht => okPost_bind (okPost_trivial _) (fun _ _ => okPost_ok ht))
    split
    · repeat' (first
        | (exact okPost_ok rfl)
        | (refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)))
    · exact okPost_ok rfl
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok rfl

theorem scene_dfs_loop8_frame (w : spanning_tree.Workspace) (n i : Std.Usize) :
    OkPost (spanning_tree.Tree.scene_dfs_loop8 w n i)
      (fun r => r.1.edge_capacity = w.edge_capacity ∧ r.1.path = w.path) := by
  unfold spanning_tree.Tree.scene_dfs_loop8
  refine okPost_loop (fun s : spanning_tree.Workspace × Std.Usize =>
      s.1.edge_capacity = w.edge_capacity ∧ s.1.path = w.path) _ _ ?_ _ ⟨rfl, rfl⟩
  rintro ⟨s, j⟩ hs
  unfold spanning_tree.Tree.scene_dfs_loop8.body
  capacity_walk

theorem index_mut_back_len {α : Type _} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    {back : α → alloc.vec.Vec α}
    (h : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i = ok (x, back))
    (y : α) : (back y).val.length = v.val.length := by
  rw [index_mut_ok_set v i x back h]
  simp [alloc.vec.Vec.set_val_eq]

/-- The inner loop of the final search writes the stack entry by entry. -/
theorem scene_dfs_loop9_loop0_len (v : alloc.vec.Vec Bool) (v1 : alloc.vec.Vec Std.Usize)
    (i : Std.Usize) (parents : alloc.vec.Vec Std.Usize) (depth cell : Std.Usize)
    (row : Slice Std.Usize) :
    OkPost (spanning_tree.Tree.scene_dfs_loop9_loop0 v v1 i parents depth cell row)
      (fun r => r.2.1.val.length = v1.val.length) := by
  unfold spanning_tree.Tree.scene_dfs_loop9_loop0
  refine okPost_loop (fun s : alloc.vec.Vec Bool × alloc.vec.Vec Std.Usize × Std.Usize ×
      alloc.vec.Vec Std.Usize × Std.Usize => s.2.1.val.length = v1.val.length) _ _ ?_ _ rfl
  rintro ⟨a, b, j, p, d⟩ hb
  simp only at hb
  unfold spanning_tree.Tree.scene_dfs_loop9_loop0.body
  dsimp only
  by_cases hlt : j < Slice.len row
  · simp only [hlt, ↓reduceIte]
    refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
    refine okPost_bind (okPost_trivial _) (fun bb _ => ?_)
    refine okPost_bind (P := fun t : alloc.vec.Vec Bool × alloc.vec.Vec Std.Usize ×
        alloc.vec.Vec Std.Usize × Std.Usize => t.2.1.val.length = v1.val.length) ?_
      (fun t ht => okPost_bind (okPost_trivial _) (fun _ _ => okPost_ok ht))
    split
    · exact okPost_ok hb
    · refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
      refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
      refine okPost_bind_eq (okPost_trivial _) (fun xb hm _ => ?_)
      obtain ⟨x, back⟩ := xb
      refine okPost_bind (okPost_trivial _) (fun _ _ => okPost_ok ?_)
      show (back _).val.length = v1.val.length
      rw [index_mut_back_len hm, hb]
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok hb

/-- The final search of `scene_dfs` keeps the stack's length. -/
theorem scene_dfs_loop9_len (v : alloc.vec.Vec Bool) (v1 : alloc.vec.Vec Std.Usize)
    (i : Std.Usize) (expanded : topology.Carrier) (parents : alloc.vec.Vec Std.Usize)
    (depth : Std.Usize) :
    OkPost (spanning_tree.Tree.scene_dfs_loop9 v v1 i expanded parents depth)
      (fun r => r.2.1.val.length = v1.val.length) := by
  unfold spanning_tree.Tree.scene_dfs_loop9
  refine okPost_loop (fun s : alloc.vec.Vec Bool × alloc.vec.Vec Std.Usize × Std.Usize ×
      alloc.vec.Vec Std.Usize × Std.Usize => s.2.1.val.length = v1.val.length) _ _ ?_ _ rfl
  rintro ⟨a, b, j, p, d⟩ hb
  simp only at hb
  unfold spanning_tree.Tree.scene_dfs_loop9.body
  dsimp only
  by_cases hlt : d > 0#usize
  · simp only [hlt, ↓reduceIte]
    refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
    refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
    refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
    refine okPost_bind (scene_dfs_loop9_loop0_len _ _ _ _ _ _ _) (fun t ht => okPost_ok ?_)
    rw [← hb]; exact ht
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok hb

/-- **`scene_dfs` keeps the workspace's edge capacity and path length**, and returns a tree only
when the carrier's cells fit the path. -/
theorem scene_dfs_frame {R : Type _} (adapter : tree.Rng R) (carrier : topology.Carrier)
    (required : Slice topology.Edge) (root : Std.Usize) (rng : R) (work : spanning_tree.Workspace) :
    OkPost (spanning_tree.Tree.scene_dfs adapter carrier required root rng work) (fun out =>
      out.2.2.edge_capacity = work.edge_capacity ∧
      out.2.2.path.val.length = work.path.val.length ∧
      (∀ t, out.1 = .Ok t → cellCount carrier ≤ work.path.val.length)) := by
  unfold spanning_tree.Tree.scene_dfs
  refine okPost_bind_eq (okPost_trivial _) (fun n hn _ => ?_)
  have hnv : n.val = cellCount carrier := by
    unfold topology.Carrier.len at hn
    obtain ⟨h1, _⟩ := usize_sub_ok _ _ _ hn
    have e : (alloc.vec.Vec.len carrier.offsets).val = carrier.offsets.val.length := by simp
    have e1 : (1#usize : Std.Usize).val = 1 := by simp
    simp only [cellCount]
    omega
  dsimp only
  split
  · exact okPost_ok ⟨rfl, rfl, fun t h => by simp at h⟩
  · refine okPost_bind (okPost_trivial _) (fun s _ => ?_)
    refine okPost_bind_eq (okPost_trivial _) (fun r hr _ => ?_)
    cases r with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok]
      exact okPost_ok ⟨rfl, rfl, fun t h => by simp at h⟩
    | Ok u =>
      have hle : cellCount carrier ≤ work.path.val.length := by
        unfold spanning_tree.Workspace.ensure at hr
        simp only at hr
        split at hr
        · simp at hr
        · rename_i hgt
          have : ¬ alloc.vec.Vec.len work.path < n := by simpa using hgt
          have : ¬ (alloc.vec.Vec.len work.path).val < n.val := fun h' => this (by scalar_tac)
          have e : (alloc.vec.Vec.len work.path).val = work.path.val.length := by
            simp
          omega
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      repeat' (first
        | (exact okPost_ok ⟨rfl, rfl, fun _ _ => hle⟩)
        | (refine okPost_bind (depth_first_frame _ _ _ _ _ _) ?_;
            rintro ⟨r6, rng1, work1⟩ ⟨hc1, hp1⟩)
        | (refine okPost_bind (scene_dfs_loop7_frame _ _ _ _ _ _ _) ?_;
            rintro ⟨work2, sel2⟩ hw2)
        | (refine okPost_bind (scene_dfs_loop8_frame _ _ _) ?_;
            rintro ⟨work3, i3⟩ ⟨hc3, hp3⟩)
        | (refine okPost_bind (scene_dfs_loop9_len _ _ _ _ _ _) ?_;
            rintro ⟨v2, v3, par⟩ hl3)
        | (refine okPost_bind_eq (okPost_trivial (alloc.vec.Vec.index_mut _ _ _))
            (fun xb hm _ => ?_); obtain ⟨_, _⟩ := xb; have := index_mut_back_len hm)
        | (refine okPost_bind_eq (okPost_trivial _) (fun _ _ _ => ?_))
        | split)
      all_goals
        refine okPost_ok ⟨?_, ?_, fun _ _ => hle⟩ <;>
          simp_all

end Labyrinth
