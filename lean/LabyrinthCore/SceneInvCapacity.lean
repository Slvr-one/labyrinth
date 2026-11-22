module
public import LabyrinthCore.SceneInvFresh

/-! The scene invariant, part 3: `Tree::edit_edges` never changes the workspace's edge capacity.
Every write to the workspace is a field update of its edit tables or its path; the capacity is
copied through. So an edit keeps `EditCapacity` on every path, accepted or rejected. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- Walk a computation whose every step keeps a workspace's capacity. -/
macro "capacity_walk" : tactic => `(tactic| repeat (first
  | (exact okPost_ok (by simp_all))
  | (refine okPost_bind (okPost_trivial _) (fun _ _ => ?_))
  | split
  | dsimp only))

theorem set_parent_capacity (w : spanning_tree.Workspace) (cell parent : Std.Usize) :
    OkPost (spanning_tree.Workspace.set_parent w cell parent)
      (fun w' => w'.edge_capacity = w.edge_capacity) := by
  unfold spanning_tree.Workspace.set_parent
  capacity_walk

theorem clear_edits_capacity (w : spanning_tree.Workspace) :
    OkPost (spanning_tree.Workspace.clear_edits w) (fun w' => w'.edge_capacity = w.edge_capacity) := by
  unfold spanning_tree.Workspace.clear_edits spanning_tree.Workspace.clear_edits_loop
  refine okPost_bind (okPost_loop (fun s : spanning_tree.Workspace × Std.Usize =>
      s.1.edge_capacity = w.edge_capacity) (fun r => r.2.2.2.2.2.2.2 = w.edge_capacity) _ ?_ _ rfl)
    (fun r hr => okPost_ok hr)
  rintro ⟨s, i⟩ hs
  unfold spanning_tree.Workspace.clear_edits_loop.body
  capacity_walk

theorem edit_edges_loop1_capacity (v : alloc.vec.Vec Std.Usize) (remove : Slice topology.Edge)
    (w : spanning_tree.Workspace) (i : Std.Usize) :
    OkPost (spanning_tree.Tree.edit_edges_loop1 v remove w i)
      (fun w' => w'.edge_capacity = w.edge_capacity) := by
  unfold spanning_tree.Tree.edit_edges_loop1
  refine okPost_loop (fun s : spanning_tree.Workspace × Std.Usize =>
    s.1.edge_capacity = w.edge_capacity) _ _ ?_ _ rfl
  rintro ⟨s, j⟩ hs
  unfold spanning_tree.Tree.edit_edges_loop1.body
  repeat (first
    | (exact okPost_ok (by simp_all))
    | (refine okPost_bind (set_parent_capacity _ _ _) (fun _ _ => ?_))
    | (refine okPost_bind (okPost_trivial _) (fun _ _ => ?_))
    | split
    | dsimp only)

theorem attach_virtual_loop0_capacity (v : alloc.vec.Vec Std.Usize) (w : spanning_tree.Workspace)
    (n root inside k : Std.Usize) :
    OkPost (spanning_tree.Tree.attach_virtual_loop0 v w n root inside k)
      (fun r => r.1.edge_capacity = w.edge_capacity) := by
  unfold spanning_tree.Tree.attach_virtual_loop0
  refine okPost_loop (fun s : spanning_tree.Workspace × Std.Usize × Std.Usize =>
    s.1.edge_capacity = w.edge_capacity) _ _ ?_ _ rfl
  rintro ⟨s, c, k⟩ hs
  unfold spanning_tree.Tree.attach_virtual_loop0.body
  capacity_walk

theorem attach_virtual_loop1_capacity (w : spanning_tree.Workspace) (count j : Std.Usize) :
    OkPost (spanning_tree.Tree.attach_virtual_loop1 w count j)
      (fun r => r.edge_capacity = w.edge_capacity) := by
  unfold spanning_tree.Tree.attach_virtual_loop1
  refine okPost_loop (fun s : spanning_tree.Workspace × Std.Usize =>
    s.1.edge_capacity = w.edge_capacity) _ _ ?_ _ rfl
  rintro ⟨s, k⟩ hs
  unfold spanning_tree.Tree.attach_virtual_loop1.body
  repeat (first
    | (exact okPost_ok (by simp_all))
    | (refine okPost_bind (set_parent_capacity _ _ _) (fun _ _ => ?_))
    | (refine okPost_bind (okPost_trivial _) (fun _ _ => ?_))
    | split)

theorem attach_virtual_capacity (t : spanning_tree.Tree) (e : topology.Edge)
    (w : spanning_tree.Workspace) :
    OkPost (spanning_tree.Tree.attach_virtual t e w)
      (fun r => r.2.edge_capacity = w.edge_capacity) := by
  unfold spanning_tree.Tree.attach_virtual
  repeat (first
    | (exact okPost_ok (by simp_all))
    | (refine okPost_bind (set_parent_capacity _ _ _) (fun _ _ => ?_))
    | (refine okPost_bind (attach_virtual_loop0_capacity _ _ _ _ _ _) (fun r hr => ?_);
        obtain ⟨w1, cell, count⟩ := r; simp only at hr;
        show OkPost (if cell ≥ alloc.vec.Vec.len t.parents then _ else _) _)
    | (refine okPost_bind (attach_virtual_loop1_capacity _ _ _) (fun _ _ => ?_))
    | (refine okPost_bind (okPost_trivial _) (fun _ _ => ?_))
    | split)

theorem edit_edges_loop2_capacity (v : alloc.vec.Vec Std.Usize) (root : Std.Usize)
    (add : Slice topology.Edge) (w : spanning_tree.Workspace) (i : Std.Usize)
    (st : core.result.Result Unit topology.Error) :
    OkPost (spanning_tree.Tree.edit_edges_loop2 v root add w i st)
      (fun r => r.1.edge_capacity = w.edge_capacity) := by
  unfold spanning_tree.Tree.edit_edges_loop2
  refine okPost_loop (fun s : spanning_tree.Workspace × Std.Usize ×
    (core.result.Result Unit topology.Error) => s.1.edge_capacity = w.edge_capacity) _ _ ?_ _ rfl
  rintro ⟨s, j, st1⟩ hs
  unfold spanning_tree.Tree.edit_edges_loop2.body
  repeat (first
    | (exact okPost_ok (by simp_all))
    | (refine okPost_bind (attach_virtual_capacity _ _ _) (fun _ _ => ?_))
    | (refine okPost_bind (okPost_trivial _) (fun _ _ => ?_))
    | split
    | dsimp only)

theorem edit_edges_loop3_capacity (v : alloc.vec.Vec Std.Usize) (w : spanning_tree.Workspace)
    (i : Std.Usize) :
    OkPost (spanning_tree.Tree.edit_edges_loop3 v w i)
      (fun r => r.2.2.2.2.2.2.2.2.2 = w.edge_capacity) := by
  unfold spanning_tree.Tree.edit_edges_loop3
  refine okPost_loop (fun _ => True) _ _ ?_ _ trivial
  rintro ⟨v1, j⟩ -
  unfold spanning_tree.Tree.edit_edges_loop3.body
  capacity_walk

/-- **`Tree::edit_edges` keeps the workspace's edge capacity**, whatever it returns. -/
theorem edit_edges_capacity (t : spanning_tree.Tree) (c : topology.Carrier)
    (remove add : Slice topology.Edge) (w : spanning_tree.Workspace) :
    OkPost (spanning_tree.Tree.edit_edges t c remove add w)
      (fun out => out.2.2.edge_capacity = w.edge_capacity) := by
  unfold spanning_tree.Tree.edit_edges
  repeat (first
    | (exact okPost_ok (by simp_all))
    | (refine okPost_bind (clear_edits_capacity _) (fun _ _ => ?_))
    | (refine okPost_bind (edit_edges_loop1_capacity _ _ _ _) (fun _ _ => ?_))
    | (refine okPost_bind (edit_edges_loop2_capacity _ _ _ _ _ _) (fun _ _ => ?_))
    | (refine okPost_bind (edit_edges_loop3_capacity _ _ _) (fun _ _ => ?_))
    | (refine okPost_bind (okPost_trivial _) (fun _ _ => ?_))
    | split
    | dsimp only)

end Labyrinth
