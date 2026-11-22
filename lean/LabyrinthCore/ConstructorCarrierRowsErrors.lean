module
public import LabyrinthCore.SceneGeometryLayoutNew
public import LabyrinthCore.ConstructorCarrierEdgeRows

/-! The error set of `Carrier::from_edges`.

Partial-correctness statements (`OkPost`): every `Err` the constructor returns is one of
`InvalidSize` (no cells), `InvalidIndex` (an edge endpoint, or a row entry, out of range),
`InvalidCarrier` (a loop edge, a repeated or non-reciprocal adjacency, malformed offsets), `Disconnected`
and `Overflow` (a size or storage check). -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- The errors `Carrier::from_edges` and `Carrier::from_csr` can return. -/
def FromEdgesErrSet (e : topology.Error) : Prop :=
  e = .InvalidSize ∨ e = .InvalidIndex ∨ e = .InvalidCarrier ∨ e = .Disconnected ∨
    e = .Overflow

/-- A result whose error, if any, is in `FromEdgesErrSet`. -/
def ErrClosed {α : Type _} (r : core.result.Result α topology.Error) : Prop :=
  ∀ e, r = .Err e → FromEdgesErrSet e

theorem errClosed_ok {α : Type _} (v : α) : ErrClosed (.Ok v : core.result.Result α topology.Error) :=
  fun _ h => by cases h

theorem errClosed_err {α : Type _} {e : topology.Error} (he : FromEdgesErrSet e) :
    ErrClosed (.Err e : core.result.Result α topology.Error) :=
  fun _ h => by cases h; exact he

theorem errSet_size : FromEdgesErrSet .InvalidSize := by simp [FromEdgesErrSet]
theorem errSet_index : FromEdgesErrSet .InvalidIndex := by simp [FromEdgesErrSet]
theorem errSet_carrier : FromEdgesErrSet .InvalidCarrier := by simp [FromEdgesErrSet]
theorem errSet_disconnected : FromEdgesErrSet .Disconnected := by simp [FromEdgesErrSet]
theorem errSet_overflow : FromEdgesErrSet .Overflow := by simp [FromEdgesErrSet]

theorem okPost_branch_closed {T β : Type _} {Q : β → Prop}
    (r : core.result.Result T topology.Error) (hr : ErrClosed r)
    (k : core.ops.control_flow.ControlFlow (core.result.Result Never topology.Error) T → Result β)
    (hok : ∀ v, r = .Ok v → OkPost (k (.Continue v)) Q)
    (herr : ∀ e, r = .Err e → FromEdgesErrSet e → OkPost (k (.Break (.Err e))) Q) :
    OkPost (Std.bind (core.result.Result.Insts.CoreOpsTry.branch r) k) Q := by
  cases r with
  | Ok v => exact okPost_branch_ok v k (hok v rfl)
  | Err e => exact okPost_branch_err e k (herr e rfl (hr e rfl))

theorem okPost_ok_or {T β : Type _} {Q : β → Prop} (o : Option T)
    (k : core.ops.control_flow.ControlFlow (core.result.Result Never topology.Error) T → Result β)
    (hsome : ∀ v, OkPost (k (.Continue v)) Q) (hnone : OkPost (k (.Break (.Err .Overflow))) Q) :
    OkPost (Std.bind (core.option.Option.ok_or o topology.Error.Overflow) (fun r =>
      Std.bind (core.result.Result.Insts.CoreOpsTry.branch r) k)) Q := by
  cases o with
  | none =>
    simp only [core.option.Option.ok_or, Std.bind_ok]
    exact okPost_branch_err _ k hnone
  | some v =>
    simp only [core.option.Option.ok_or, Std.bind_ok]
    exact okPost_branch_ok v k (hsome v)

theorem check_storage_closed (c b : Std.Usize) :
    OkPost (topology.check_storage c b) ErrClosed := by
  unfold topology.check_storage
  refine okPost_any (fun o => ?_)
  refine okPost_ok_or o _ (fun v => ?_) ?_
  · refine okPost_any (fun i => ?_)
    split
    · exact okPost_ok (errClosed_err errSet_overflow)
    · exact okPost_ok (errClosed_ok _)
  · exact okPost_residual _ (errClosed_err errSet_overflow)

theorem count_edge_closed (offsets : Slice Std.Usize) (n : Std.Usize) (edge : topology.Edge) :
    OkPost (topology.count_edge offsets n edge) (fun p => ErrClosed p.1) := by
  unfold topology.count_edge
  split
  · exact okPost_ok (errClosed_err errSet_index)
  · split
    · exact okPost_ok (errClosed_err errSet_index)
    · split
      · exact okPost_ok (errClosed_err errSet_carrier)
      · refine okPost_any (fun i => okPost_any (fun i1 => okPost_any (fun o => ?_)))
        refine okPost_ok_or o _ (fun val => ?_) ?_
        · refine okPost_any (fun offsets1 => okPost_any (fun i2 => okPost_any (fun i3 =>
            okPost_any (fun o1 => ?_))))
          refine okPost_ok_or o1 _ (fun val1 => ?_) ?_
          · exact okPost_any (fun _ => okPost_ok (errClosed_ok _))
          · exact okPost_bind (okPost_residual _ (errClosed_err errSet_overflow))
              (fun r hr => okPost_ok hr)
        · exact okPost_bind (okPost_residual _ (errClosed_err errSet_overflow))
            (fun r hr => okPost_ok hr)

theorem validate_row_entry_closed (offsets neighbors : Slice Std.Usize)
    (cell index : Std.Usize) :
    OkPost (topology.validate_row_entry offsets neighbors cell index) ErrClosed := by
  unfold topology.validate_row_entry
  refine okPost_any (fun nb => okPost_any (fun i1 => ?_))
  split
  · exact okPost_ok (errClosed_err errSet_index)
  · split
    · exact okPost_ok (errClosed_err errSet_carrier)
    · refine okPost_any (fun j => okPost_any (fun j1 => ?_))
      split
      · exact okPost_ok (errClosed_err errSet_carrier)
      · refine okPost_any (fun j2 => okPost_any (fun j3 => okPost_any (fun i2 =>
          okPost_any (fun i3 => ?_))))
        split
        · exact okPost_ok (errClosed_err errSet_carrier)
        · exact okPost_ok (errClosed_ok _)

theorem csr_row_loop_closed (offsets neighbors : alloc.vec.Vec Std.Usize) (u : Std.Usize)
    (status : core.result.Result Unit topology.Error) (i : Std.Usize) (h : ErrClosed status) :
    OkPost (topology.Carrier.from_csr_loop1_loop0 offsets neighbors u status i) ErrClosed := by
  unfold topology.Carrier.from_csr_loop1_loop0
  refine okPost_loop (fun s : core.result.Result Unit topology.Error × Std.Usize => ErrClosed s.1)
    ErrClosed _ ?_ (status, i) h
  rintro ⟨st, j⟩ hst
  unfold topology.Carrier.from_csr_loop1_loop0.body
  refine okPost_any (fun i1 => okPost_any (fun i2 => ?_))
  by_cases hlt : j < i2
  · simp only [hlt, ↓reduceIte]
    refine okPost_any (fun b => ?_)
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact okPost_ok hst
    · simp only [↓reduceIte]
      exact okPost_bind (validate_row_entry_closed _ _ _ _)
        (fun status1 h1 => okPost_any (fun i3 => okPost_ok h1))
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok hst

theorem csr_rows_closed (offsets neighbors : alloc.vec.Vec Std.Usize) (n u : Std.Usize)
    (status : core.result.Result Unit topology.Error) (h : ErrClosed status) :
    OkPost (topology.Carrier.from_csr_loop1 offsets neighbors n u status)
      (fun p => ErrClosed p.2) := by
  unfold topology.Carrier.from_csr_loop1
  refine okPost_loop
    (fun s : Std.Usize × core.result.Result Unit topology.Error => ErrClosed s.2)
    (fun p : Std.Usize × core.result.Result Unit topology.Error => ErrClosed p.2) _ ?_
    (u, status) h
  rintro ⟨v, st⟩ hst
  unfold topology.Carrier.from_csr_loop1.body
  by_cases hlt : v < n
  · simp only [hlt, ↓reduceIte]
    refine okPost_any (fun b => ?_)
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact okPost_ok hst
    · simp only [↓reduceIte]
      refine okPost_any (fun i => ?_)
      exact okPost_bind (csr_row_loop_closed _ _ _ _ _ hst)
        (fun status1 h1 => okPost_any (fun u1 => okPost_ok h1))
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok hst

theorem from_csr_closed (offsets neighbors : alloc.vec.Vec Std.Usize) :
    OkPost (topology.Carrier.from_csr offsets neighbors) ErrClosed := by
  unfold topology.Carrier.from_csr
  dsimp only
  split
  · exact okPost_ok (errClosed_err errSet_size)
  · refine okPost_any (fun n => okPost_any (fun i2 => ?_))
    split
    · exact okPost_ok (errClosed_err errSet_carrier)
    · refine okPost_any (fun i3 => ?_)
      split
      · exact okPost_ok (errClosed_err errSet_carrier)
      · refine okPost_any (fun valid => ?_)
        split
        · refine okPost_bind (csr_rows_closed _ _ _ _ _ (errClosed_ok _)) ?_
          rintro ⟨u, status⟩ hp
          refine okPost_branch_closed status hp _ (fun _ _ => ?_)
            (fun e _ he => okPost_residual _ (errClosed_err he))
          refine okPost_bind (check_storage_closed _ _) (fun r hr => ?_)
          refine okPost_branch_closed r hr _ (fun _ _ => ?_)
            (fun e _ he => okPost_residual _ (errClosed_err he))
          refine okPost_any (fun seen => okPost_any (fun stack => okPost_any (fun pr => ?_)))
          obtain ⟨old, back⟩ := pr
          refine okPost_any (fun reached => ?_)
          split
          · exact okPost_ok (errClosed_err errSet_disconnected)
          · refine okPost_any (fun i6 => ?_)
            refine okPost_bind (check_storage_closed _ _) (fun r1 hr1 => ?_)
            refine okPost_branch_closed r1 hr1 _ (fun _ _ => ?_)
              (fun e _ he => okPost_residual _ (errClosed_err he))
            exact okPost_any (fun e => okPost_any (fun i8 => okPost_any (fun edges =>
              okPost_any (fun edges1 => okPost_ok (errClosed_ok _)))))
        · exact okPost_ok (errClosed_err errSet_carrier)

theorem edges_count_loop_closed (n : Std.Usize) (edges : Slice topology.Edge)
    (offsets : alloc.vec.Vec Std.Usize) (i : Std.Usize)
    (status : core.result.Result Unit topology.Error) (h : ErrClosed status) :
    OkPost (topology.Carrier.from_edges_loop0 n edges offsets i status)
      (fun p => ErrClosed p.2) := by
  unfold topology.Carrier.from_edges_loop0
  refine okPost_loop (fun s : alloc.vec.Vec Std.Usize × Std.Usize ×
      core.result.Result Unit topology.Error => ErrClosed s.2.2)
    (fun p : alloc.vec.Vec Std.Usize × core.result.Result Unit topology.Error => ErrClosed p.2)
    _ ?_ (offsets, i, status) h
  rintro ⟨offs, j, st⟩ hst
  unfold topology.Carrier.from_edges_loop0.body
  dsimp only
  by_cases hlt : j < Slice.len edges
  · simp only [hlt, ↓reduceIte]
    refine okPost_any (fun b => ?_)
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact okPost_ok hst
    · simp only [↓reduceIte]
      refine okPost_any (fun pr => ?_)
      obtain ⟨s, back⟩ := pr
      refine okPost_any (fun e => ?_)
      refine okPost_bind (count_edge_closed _ _ _) ?_
      rintro ⟨status1, s1⟩ h1
      exact okPost_any (fun i2 => okPost_ok h1)
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok hst

theorem prefix_offsets_closed (offsets : Slice Std.Usize) :
    OkPost (topology.prefix_offsets offsets) (fun p => ErrClosed p.1) := by
  unfold topology.prefix_offsets topology.prefix_offsets_loop
  refine okPost_loop (fun s : Slice Std.Usize × Std.Usize × core.result.Result Unit topology.Error =>
      ErrClosed s.2.2)
    (fun p : core.result.Result Unit topology.Error × Slice Std.Usize => ErrClosed p.1) _ ?_ (offsets, 1#usize, .Ok ())
    (errClosed_ok _)
  rintro ⟨offs, j, st⟩ hst
  unfold topology.prefix_offsets_loop.body
  dsimp only
  by_cases hlt : j < Slice.len offs
  · simp only [hlt, ↓reduceIte]
    refine okPost_any (fun b => ?_)
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact okPost_ok hst
    · simp only [↓reduceIte]
      refine okPost_any (fun i2 => okPost_any (fun i3 => okPost_any (fun i4 =>
        okPost_any (fun o => ?_))))
      cases o with
      | none => exact okPost_any (fun i5 => okPost_ok (errClosed_err errSet_overflow))
      | some sum => exact okPost_any (fun s => okPost_any (fun i5 => okPost_ok hst))
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok hst

/-- **The error set of `Carrier::from_edges`**: it returns one of `InvalidSize`, `InvalidIndex`,
`InvalidCarrier`, `Disconnected` and `Overflow`, and no other error. -/
theorem from_edges_error_set (n : Std.Usize) (edges : Slice topology.Edge) :
    OkPost (topology.Carrier.from_edges n edges) ErrClosed := by
  unfold topology.Carrier.from_edges
  split
  · exact okPost_ok (errClosed_err errSet_size)
  · refine okPost_any (fun o => ?_)
    refine okPost_ok_or o _ (fun val => ?_) (okPost_residual _ (errClosed_err errSet_overflow))
    refine okPost_any (fun o1 => ?_)
    refine okPost_ok_or o1 _ (fun val1 => ?_) (okPost_residual _ (errClosed_err errSet_overflow))
    refine okPost_bind (check_storage_closed _ _) (fun r2 hr2 => ?_)
    refine okPost_branch_closed r2 hr2 _ (fun _ _ => ?_)
      (fun e _ he => okPost_residual _ (errClosed_err he))
    refine okPost_bind (check_storage_closed _ _) (fun r3 hr3 => ?_)
    refine okPost_branch_closed r3 hr3 _ (fun _ _ => ?_)
      (fun e _ he => okPost_residual _ (errClosed_err he))
    refine okPost_bind (check_storage_closed _ _) (fun r4 hr4 => ?_)
    refine okPost_branch_closed r4 hr4 _ (fun _ _ => ?_)
      (fun e _ he => okPost_residual _ (errClosed_err he))
    refine okPost_any (fun offsets => ?_)
    refine okPost_bind (edges_count_loop_closed _ _ _ _ _ (errClosed_ok _)) ?_
    rintro ⟨offsets1, status⟩ hs
    refine okPost_branch_closed status hs _ (fun _ _ => ?_)
      (fun e _ he => okPost_residual _ (errClosed_err he))
    refine okPost_any (fun pr => ?_)
    obtain ⟨s, back⟩ := pr
    refine okPost_bind (prefix_offsets_closed _) ?_
    rintro ⟨r5, s1⟩ h5
    refine okPost_branch_closed r5 h5 _ (fun _ _ => ?_)
      (fun e _ he => okPost_residual _ (errClosed_err he))
    refine okPost_any (fun next => okPost_any (fun next1 => okPost_any (fun neighbors =>
      okPost_any (fun neighbors1 => from_csr_closed _ _))))

end Labyrinth
