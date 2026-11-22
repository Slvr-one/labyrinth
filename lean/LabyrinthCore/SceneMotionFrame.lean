module
public import LabyrinthCore.SceneMotionConnected

/-! The motion planner (S7), part 4: what the planner's helpers leave untouched.

The workspace fields that bind it to a scene (`epoch`, `cells`, `edges`, `endpoints`), the
divided steps, the admissibility and lock flags and the split-vertex network (`from`, `to`,
`offsets`, `arcs`) are written only by `new`, `advance` and the first loop of `plan`. Every search
helper (`clear_search`, `residual_path`, `augment`, `flow_path`, `reset_flow`, `tree_path`) and
`route_through`/`plan_route` keep them (`WFrame`). These are partial-correctness frames. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- The workspace fields the search helpers never write. -/
def WFrame (w w' : motion.MotionWorkspace) : Prop :=
  w'.epoch = w.epoch ∧ w'.cells = w.cells ∧ w'.edges = w.edges ∧ w'.endpoints = w.endpoints ∧
  w'.steps = w.steps ∧ w'.admissible = w.admissible ∧ w'.locked = w.locked ∧
  w'.from = w.from ∧ w'.to = w.to ∧ w'.offsets = w.offsets ∧ w'.arcs = w.arcs

theorem wFrame_refl (w : motion.MotionWorkspace) : WFrame w w :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The flattened workspace the generated loops return. -/
abbrev WTup := Std.U64 × Std.Usize × Std.Usize × (alloc.vec.Vec (Array Std.Usize 4#usize)) ×
  (alloc.vec.Vec Std.I32) × (alloc.vec.Vec scene.Route) × Bool × (alloc.vec.Vec topology.Edge) ×
  (alloc.vec.Vec topology.Edge) × (alloc.vec.Vec Bool) × (alloc.vec.Vec Bool) ×
  (alloc.vec.Vec Bool) × (alloc.vec.Vec Std.Usize) × (alloc.vec.Vec Std.Usize) ×
  (alloc.vec.Vec Std.Usize) × (alloc.vec.Vec Std.Usize) × (alloc.vec.Vec Std.U8) ×
  (alloc.vec.Vec Std.Usize) × (alloc.vec.Vec Std.Usize) × (alloc.vec.Vec Std.Usize) ×
  (alloc.vec.Vec Std.Usize)

/-- The workspace a flattened tuple stands for. -/
def ofTup : WTup → motion.MotionWorkspace
  | (a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
      a20, a21) =>
    { epoch := a1, cells := a2, edges := a3, endpoints := a4, steps := a5, routes := a6,
      routes_changed := a7, remove := a8, add := a9, admissible := a10, «protected» := a11,
      locked := a12, «from» := a13, «to» := a14, offsets := a15, arcs := a16, residual := a17,
      parent := a18, queue := a19, first := a20, second := a21 }

/-- One step of a frame proof; later lemmas add alternatives for their callers. -/
syntax "wf_step" : tactic

macro_rules
  | `(tactic| wf_step) => `(tactic| first
      | (exact okPost_ok (by assumption))
      | (dsimp only)
      | split
      | (refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)))

/-! ### `clear_search` -/

theorem clear_search_loop_frame (w0 self : motion.MotionWorkspace) (i : Std.Usize)
    (h : WFrame w0 self) :
    OkPost (motion.MotionWorkspace.clear_search_loop self i) (fun t => WFrame w0 (ofTup t)) := by
  unfold motion.MotionWorkspace.clear_search_loop
  refine okPost_loop (fun x : motion.MotionWorkspace × Std.Usize => WFrame w0 x.1) _ _ ?_
    (self, i) h
  rintro ⟨s, j⟩ hs
  dsimp only at hs ⊢
  unfold motion.MotionWorkspace.clear_search_loop.body
  repeat wf_step

theorem clear_search_frame (w0 self : motion.MotionWorkspace) (source : Std.Usize)
    (h : WFrame w0 self) :
    OkPost (motion.MotionWorkspace.clear_search self source) (WFrame w0) := by
  unfold motion.MotionWorkspace.clear_search
  refine okPost_bind (clear_search_loop_frame w0 self 0#usize h) ?_
  rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21⟩ ht
  repeat wf_step

macro_rules
  | `(tactic| wf_step) => `(tactic|
      refine okPost_bind (clear_search_frame _ _ _ (by assumption)) (fun _ _ => ?_))

/-! ### `augment`, `residual_path`, `flow_path` -/

theorem augment_loop_frame (w0 self : motion.MotionWorkspace) (source node : Std.Usize)
    (h : WFrame w0 self) :
    OkPost (motion.MotionWorkspace.augment_loop self source node) (WFrame w0) := by
  unfold motion.MotionWorkspace.augment_loop
  refine okPost_loop (fun x : motion.MotionWorkspace × Std.Usize => WFrame w0 x.1) _ _ ?_
    (self, node) h
  rintro ⟨s, j⟩ hs
  dsimp only at hs ⊢
  unfold motion.MotionWorkspace.augment_loop.body
  repeat wf_step

theorem augment_frame (w0 self : motion.MotionWorkspace) (source target : Std.Usize)
    (h : WFrame w0 self) :
    OkPost (motion.MotionWorkspace.augment self source target) (WFrame w0) :=
  augment_loop_frame w0 self source target h

theorem residual_path_loop0_frame (w0 self : motion.MotionWorkspace)
    (target read written : Std.Usize) (h : WFrame w0 self) :
    OkPost (motion.MotionWorkspace.residual_path_loop0 self target read written) (WFrame w0) := by
  unfold motion.MotionWorkspace.residual_path_loop0
  refine okPost_loop (fun x : motion.MotionWorkspace × Std.Usize × Std.Usize => WFrame w0 x.1)
    _ _ ?_ (self, read, written) h
  rintro ⟨s, r, wr⟩ hs
  dsimp only at hs ⊢
  unfold motion.MotionWorkspace.residual_path_loop0.body
  repeat wf_step

macro_rules
  | `(tactic| wf_step) => `(tactic|
      refine okPost_bind (residual_path_loop0_frame _ _ _ _ _ (by assumption)) (fun _ _ => ?_))

theorem residual_path_frame (w0 self : motion.MotionWorkspace) (source target : Std.Usize)
    (h : WFrame w0 self) :
    OkPost (motion.MotionWorkspace.residual_path self source target) (fun p => WFrame w0 p.2) := by
  unfold motion.MotionWorkspace.residual_path
  repeat wf_step

theorem flow_path_loop0_frame (w0 self : motion.MotionWorkspace) (target read written : Std.Usize)
    (h : WFrame w0 self) :
    OkPost (motion.MotionWorkspace.flow_path_loop0 self target read written) (WFrame w0) := by
  unfold motion.MotionWorkspace.flow_path_loop0
  refine okPost_loop (fun x : motion.MotionWorkspace × Std.Usize × Std.Usize => WFrame w0 x.1)
    _ _ ?_ (self, read, written) h
  rintro ⟨s, r, wr⟩ hs
  dsimp only at hs ⊢
  unfold motion.MotionWorkspace.flow_path_loop0.body
  repeat wf_step

macro_rules
  | `(tactic| wf_step) => `(tactic|
      refine okPost_bind (flow_path_loop0_frame _ _ _ _ _ (by assumption)) (fun _ _ => ?_))

theorem flow_path_frame (w0 self : motion.MotionWorkspace) (source target : Std.Usize)
    (h : WFrame w0 self) :
    OkPost (motion.MotionWorkspace.flow_path self source target) (fun p => WFrame w0 p.2) := by
  unfold motion.MotionWorkspace.flow_path
  repeat wf_step

/-! ### `reset_flow`, `tree_path` -/

theorem reset_flow_loop0_frame (w0 self : motion.MotionWorkspace) (a : Std.Usize)
    (h : WFrame w0 self) :
    OkPost (motion.MotionWorkspace.reset_flow_loop0 self a) (fun t => WFrame w0 (ofTup t)) := by
  unfold motion.MotionWorkspace.reset_flow_loop0
  refine okPost_loop (fun x : motion.MotionWorkspace × Std.Usize => WFrame w0 x.1) _ _ ?_
    (self, a) h
  rintro ⟨s, j⟩ hs
  dsimp only at hs ⊢
  unfold motion.MotionWorkspace.reset_flow_loop0.body
  repeat wf_step

theorem reset_flow_frame (w0 self : motion.MotionWorkspace) (current : scene.Scene)
    (circle pivot : Std.Usize) (h : WFrame w0 self) :
    OkPost (motion.MotionWorkspace.reset_flow self current circle pivot) (WFrame w0) := by
  unfold motion.MotionWorkspace.reset_flow
  refine okPost_bind (reset_flow_loop0_frame w0 self 0#usize h) ?_
  rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21⟩ ht
  repeat wf_step

theorem tree_path_loop0_frame (w0 self : motion.MotionWorkspace) (current : scene.Scene)
    (target read written : Std.Usize) (h : WFrame w0 self) :
    OkPost (motion.MotionWorkspace.tree_path_loop0 self current target read written)
      (WFrame w0) := by
  unfold motion.MotionWorkspace.tree_path_loop0
  refine okPost_loop (fun x : motion.MotionWorkspace × Std.Usize × Std.Usize => WFrame w0 x.1)
    _ _ ?_ (self, read, written) h
  rintro ⟨s, r, wr⟩ hs
  dsimp only at hs ⊢
  unfold motion.MotionWorkspace.tree_path_loop0.body
  repeat wf_step

macro_rules
  | `(tactic| wf_step) => `(tactic|
      refine okPost_bind (tree_path_loop0_frame _ _ _ _ _ _ (by assumption)) (fun _ _ => ?_))

theorem tree_path_frame (w0 self : motion.MotionWorkspace) (current : scene.Scene)
    (source target : Std.Usize) (h : WFrame w0 self) :
    OkPost (motion.MotionWorkspace.tree_path self current source target)
      (fun p => WFrame w0 p.2) := by
  unfold motion.MotionWorkspace.tree_path
  repeat wf_step

/-! ### `route_through`, `plan_route` -/

macro_rules
  | `(tactic| wf_step) => `(tactic|
      refine okPost_bind (reset_flow_frame _ _ _ _ _ (by assumption)) (fun _ _ => ?_))
macro_rules
  | `(tactic| wf_step) => `(tactic|
      refine okPost_bind (augment_frame _ _ _ _ (by assumption)) (fun _ _ => ?_))
macro_rules
  | `(tactic| wf_step) => `(tactic| (
      refine okPost_bind (residual_path_frame _ _ _ _ (by assumption)) ?_
      rintro ⟨_, _⟩ _))
macro_rules
  | `(tactic| wf_step) => `(tactic| (
      refine okPost_bind (flow_path_frame _ _ _ _ (by assumption)) ?_
      rintro ⟨_, _⟩ _))
macro_rules
  | `(tactic| wf_step) => `(tactic| (
      refine okPost_bind (tree_path_frame _ _ _ _ _ (by assumption)) ?_
      rintro ⟨_, _⟩ _))

/-- Both branches of a conditional, seen through a destructuring `let`. -/
theorem okPost_ite_both {α : Type _} {c : Prop} [Decidable c] {a b : Result α} {P : α → Prop}
    (h1 : OkPost a P) (h2 : OkPost b P) : OkPost (if c then a else b) P := by
  split <;> assumption

macro_rules
  | `(tactic| wf_step) => `(tactic| refine okPost_ite_both ?_ ?_)

theorem route_through_loop0_frame (w0 self : motion.MotionWorkspace) (source target : Std.Usize)
    (units : Std.I32) (possible : Bool) (h : WFrame w0 self) :
    OkPost (motion.MotionWorkspace.route_through_loop0 self source target units possible)
      (fun p => WFrame w0 p.1) := by
  unfold motion.MotionWorkspace.route_through_loop0
  refine okPost_loop (fun x : motion.MotionWorkspace × Std.I32 × Bool => WFrame w0 x.1)
    _ _ ?_ (self, units, possible) h
  rintro ⟨s, u, p⟩ hs
  dsimp only at hs ⊢
  unfold motion.MotionWorkspace.route_through_loop0.body
  repeat wf_step

macro_rules
  | `(tactic| wf_step) => `(tactic| (
      refine okPost_bind (route_through_loop0_frame _ _ _ _ _ _ (by assumption)) ?_
      rintro ⟨_, _⟩ _))

theorem route_through_frame (w0 self : motion.MotionWorkspace) (current : scene.Scene)
    (circle pivot : Std.Usize) (h : WFrame w0 self) :
    OkPost (motion.MotionWorkspace.route_through self current circle pivot)
      (fun p => WFrame w0 p.2) := by
  unfold motion.MotionWorkspace.route_through
  repeat wf_step

macro_rules
  | `(tactic| wf_step) => `(tactic| (
      refine okPost_bind (route_through_frame _ _ _ _ _ (by assumption)) ?_
      rintro ⟨_, _⟩ _))

/-- A flattened workspace followed by more loop state. -/
abbrev WTupX (X : Type) := Std.U64 × Std.Usize × Std.Usize ×
  (alloc.vec.Vec (Array Std.Usize 4#usize)) × (alloc.vec.Vec Std.I32) ×
  (alloc.vec.Vec scene.Route) × Bool × (alloc.vec.Vec topology.Edge) ×
  (alloc.vec.Vec topology.Edge) × (alloc.vec.Vec Bool) × (alloc.vec.Vec Bool) ×
  (alloc.vec.Vec Bool) × (alloc.vec.Vec Std.Usize) × (alloc.vec.Vec Std.Usize) ×
  (alloc.vec.Vec Std.Usize) × (alloc.vec.Vec Std.Usize) × (alloc.vec.Vec Std.U8) ×
  (alloc.vec.Vec Std.Usize) × (alloc.vec.Vec Std.Usize) × (alloc.vec.Vec Std.Usize) ×
  (alloc.vec.Vec Std.Usize) × X

/-- The workspace at the front of a flattened loop state. -/
def ofTupX {X : Type} : WTupX X → motion.MotionWorkspace
  | (a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
      a20, a21, _) =>
    { epoch := a1, cells := a2, edges := a3, endpoints := a4, steps := a5, routes := a6,
      routes_changed := a7, remove := a8, add := a9, admissible := a10, «protected» := a11,
      locked := a12, «from» := a13, «to» := a14, offsets := a15, arcs := a16, residual := a17,
      parent := a18, queue := a19, first := a20, second := a21 }

theorem plan_route_loop_frame (w0 self : motion.MotionWorkspace) (current : scene.Scene)
    (circle : Std.Usize) (found : Bool) (v : Std.Usize)
    (status : core.result.Result Unit topology.Error) (h : WFrame w0 self) :
    OkPost (motion.MotionWorkspace.plan_route_loop self current circle found v status)
      (fun t => WFrame w0 (ofTupX t)) := by
  unfold motion.MotionWorkspace.plan_route_loop
  refine okPost_loop (fun x : motion.MotionWorkspace × Bool × Std.Usize ×
    core.result.Result Unit topology.Error => WFrame w0 x.1) _ _ ?_ (self, found, v, status) h
  rintro ⟨s, f, j, st⟩ hs
  dsimp only at hs ⊢
  unfold motion.MotionWorkspace.plan_route_loop.body
  split
  · split
    · exact okPost_ok hs
    · refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
      split
      · refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
        refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
        refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
        refine okPost_bind (P := fun x : motion.MotionWorkspace × Bool ×
          core.result.Result Unit topology.Error => WFrame w0 x.1) ?_ ?_
        · repeat wf_step
        · rintro ⟨s1, f1, st1⟩ hs1
          repeat wf_step
      · exact okPost_ok hs
  · exact okPost_ok hs

macro_rules
  | `(tactic| wf_step) => `(tactic| (
      refine okPost_bind (plan_route_loop_frame _ _ _ _ _ _ _ (by assumption)) ?_
      rintro ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ _))

theorem plan_route_frame (w0 self : motion.MotionWorkspace) (current : scene.Scene)
    (circle : Std.Usize) (h : WFrame w0 self) :
    OkPost (motion.MotionWorkspace.plan_route self current circle) (fun p => WFrame w0 p.2) := by
  unfold motion.MotionWorkspace.plan_route
  repeat wf_step

/-! ### `plan` -/

theorem fromResidual_ok_err {T : Type} {residual : core.result.Result Never topology.Error}
    {r : core.result.Result T topology.Error}
    (h : core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
      (core.convert.FromSame topology.Error) residual = ok r) : ∃ x, r = .Err x := by
  cases residual with
  | Ok n => cases n
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, ok.injEq] at h
    exact ⟨x, h.symm⟩

/-- Both branches of a conditional, each knowing its condition. -/
theorem okPost_ite_cases {α : Type _} {c : Prop} [Decidable c] {a b : Result α} {P : α → Prop}
    (h1 : c → OkPost a P) (h2 : ¬ c → OkPost b P) : OkPost (if c then a else b) P := by
  split
  · exact h1 ‹_›
  · exact h2 ‹_›

/-- An accepted plan proposes as many additions as removals. -/
theorem plan_ok_balanced (w : motion.MotionWorkspace) (current : scene.Scene) :
    OkPost (motion.MotionWorkspace.plan w current) (fun p =>
      p.1 = core.result.Result.Ok () → p.2.remove.val.length = p.2.add.val.length) := by
  unfold motion.MotionWorkspace.plan
  repeat' (first
    | (exact okPost_ok (fun h0 => by
        obtain ⟨x, rfl⟩ := fromResidual_ok_err ‹_ = ok _›; simp at h0))
    | (refine okPost_bind_eq (okPost_trivial _) (fun _ _ _ => ?_))
    | split
    | (dsimp only))
  rename_i t _ _
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21⟩ := t
  refine okPost_ite_cases (fun _ => okPost_ok (fun h0 => by simp at h0)) (fun hne => ?_)
  refine okPost_ok (fun _ => ?_)
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
  exact (congrArg UScalar.val hne).symm

end Labyrinth
