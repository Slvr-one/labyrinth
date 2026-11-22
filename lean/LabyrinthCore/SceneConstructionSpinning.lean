module
public import LabyrinthCore.SceneRouteBudget

/-! Scene construction (S2), part 2: `Layout::check_spinning_portals`. The scan writes trial
phases into the two scratch tables, but only at the index `transform` of the ring it is checking,
and zeroes that index again before the next route, whatever the verdict. So when it returns, both
tables are all zero again and the verdict is `Ok` or `InvalidGeometry`. The scan reaches
`Layout::doorway`, whose geometry is not shown to be total here, so the statements are partial
correctness (`OkPost`): they hold of every result the call returns. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- Every entry of the table is zero. -/
def AllZeroPhases (l : List Std.I32) : Prop := ∀ (i : Nat) (x : Std.I32), l[i]? = some x → x.val = 0

/-- Every entry of the table other than the one at `t` is zero. -/
def ZeroOffPhase (t : Nat) (l : List Std.I32) : Prop :=
  ∀ (i : Nat) (x : Std.I32), l[i]? = some x → i ≠ t → x.val = 0

/-- The verdict of the scan: it never carries anything but `InvalidGeometry`. -/
def SpinStatus (st : core.result.Result Unit topology.Error) : Prop :=
  st = core.result.Result.Ok () ∨ st = core.result.Result.Err topology.Error.InvalidGeometry

theorem slice_update_ok {α : Type _} (v : Slice α) (i : Std.Usize) (x : α) (r : Slice α)
    (h : Slice.update v i x = ok r) : r.val = v.val.set i.val x := by
  have hb : i.val < v.length := by
    unfold Slice.update at h
    cases hv : v.val[i.val]? with
    | none => simp [hv] at h
    | some _ =>
      have := (List.getElem?_eq_some_iff.mp hv).1
      simpa [Slice.length] using this
  have hu := Slice.update_spec v i x hb
  rw [h] at hu
  have := (spec_ok (p := fun nv => nv = v.set i x) r).mp hu
  rw [this, Slice.set_val_eq]

theorem allZero_set (t : Nat) (l : List Std.I32) (h : ZeroOffPhase t l) :
    AllZeroPhases (l.set t 0#i32) := by
  intro i x hx
  by_cases hit : i = t
  · subst hit
    rw [List.getElem?_set] at hx
    simp only [ite_true] at hx
    split at hx
    · simp only [Option.some.injEq] at hx
      subst hx; simp
    · simp at hx
  · rw [List.getElem?_set_ne (Ne.symm hit)] at hx
    exact h i x hx hit

theorem zeroOff_set (t : Nat) (l : List Std.I32) (v : Std.I32) (h : ZeroOffPhase t l) :
    ZeroOffPhase t (l.set t v) := by
  intro i x hx hit
  rw [List.getElem?_set_ne (Ne.symm hit)] at hx
  exact h i x hx hit

theorem zeroOff_of_allZero (t : Nat) (l : List Std.I32) (h : AllZeroPhases l) :
    ZeroOffPhase t l := fun i x hx _ => h i x hx

/-! ### The phase loop -/

/-- State of the phase loop for the ring at `transform`. -/
def SpinMidInv (t : Nat) (n m : Nat) (s : (Slice Std.I32) × (Slice Std.I32) ×
    (core.result.Result Unit topology.Error) × Std.I32) : Prop :=
  s.1.val.length = n ∧ s.2.1.val.length = m ∧ ZeroOffPhase t s.1.val ∧ ZeroOffPhase t s.2.1.val ∧
    SpinStatus s.2.2.1

def SpinMidPost (t : Nat) (n m : Nat) (s : (Slice Std.I32) × (Slice Std.I32) ×
    (core.result.Result Unit topology.Error)) : Prop :=
  s.1.val.length = n ∧ s.2.1.val.length = m ∧ ZeroOffPhase t s.1.val ∧ ZeroOffPhase t s.2.1.val ∧
    SpinStatus s.2.2

theorem spin_mid_body_post (L : scene.Layout) (transform start count entrance exit : Std.Usize)
    (n m : Nat)
    (phases next : Slice Std.I32) (status : core.result.Result Unit topology.Error)
    (phase : Std.I32)
    (hinv : SpinMidInv transform.val n m (phases, next, status, phase)) :
    OkPost (scene.Layout.check_spinning_portals_loop0_loop0.body L.cell_grid L.cells L.circles
        L.portals L.bands L.geometry L.carrier L.transforms transform start count entrance exit
        phases next status phase)
      (fun y => match y with
        | .cont s => SpinMidInv transform.val n m s
        | .done y => SpinMidPost transform.val n m y) := by
  obtain ⟨hn, hm, hp, hq, hs⟩ := hinv
  simp only at hn hm hp hq hs
  unfold scene.Layout.check_spinning_portals_loop0_loop0.body
  by_cases hlt : phase < polar.TURN
  · simp only [hlt, ↓reduceIte]
    refine okPost_bind (okPost_trivial _) ?_
    intro b _
    by_cases hb : b = true
    · simp only [hb, ↓reduceIte]
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro s hs1 _
      have hsv := slice_update_ok _ _ _ _ hs1
      refine okPost_bind (okPost_trivial _) ?_
      intro i1 _
      refine okPost_bind (okPost_trivial _) ?_
      intro i2 _
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro s1 hs2 _
      have hsv2 := slice_update_ok _ _ _ _ hs2
      refine okPost_bind (okPost_trivial _) ?_
      intro matched _
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro status1 hst1 _
      refine okPost_bind (okPost_trivial _) ?_
      intro phase1 _
      refine okPost_ok ?_
      have hst : SpinStatus status1 := by
        by_cases hmt : matched = true
        · simp only [hmt, ↓reduceIte, ok.injEq] at hst1
          subst hst1; exact hs
        · simp only [hmt, Bool.false_eq_true, ↓reduceIte, ok.injEq] at hst1
          subst hst1; exact Or.inr rfl
      refine ⟨?_, ?_, ?_, ?_, hst⟩
      · simp [hsv, hn]
      · simp [hsv2, hm]
      · rw [hsv]; exact zeroOff_set _ _ _ hp
      · rw [hsv2]; exact zeroOff_set _ _ _ hq
    · simp only [hb]
      exact okPost_ok ⟨hn, hm, hp, hq, hs⟩
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok ⟨hn, hm, hp, hq, hs⟩

theorem spin_mid_post (L : scene.Layout) (transform start count entrance exit : Std.Usize)
    (n m : Nat)
    (phases next : Slice Std.I32) (status : core.result.Result Unit topology.Error)
    (phase : Std.I32)
    (hinv : SpinMidInv transform.val n m (phases, next, status, phase)) :
    OkPost (scene.Layout.check_spinning_portals_loop0_loop0 L.cell_grid L.cells L.circles
        L.portals L.bands L.geometry L.carrier L.transforms phases next status transform start
        count entrance exit phase)
      (SpinMidPost transform.val n m) := by
  unfold scene.Layout.check_spinning_portals_loop0_loop0
  refine okPost_loop (SpinMidInv transform.val n m) (SpinMidPost transform.val n m) _ ?_
    (phases, next, status, phase) hinv
  rintro ⟨p, q, st, ph⟩ h
  dsimp only
  refine okPost_mono (spin_mid_body_post L transform start count entrance exit n m p q st ph h) ?_
  intro y hy
  cases y <;> exact hy

/-! ### The route loop -/

def SpinInv (n m : Nat) (s : (Slice Std.I32) × (Slice Std.I32) ×
    (core.result.Result Unit topology.Error) × Std.Usize) : Prop :=
  s.1.val.length = n ∧ s.2.1.val.length = m ∧ AllZeroPhases s.1.val ∧ AllZeroPhases s.2.1.val ∧
    SpinStatus s.2.2.1

def SpinPost (n m : Nat) (s : (core.result.Result Unit topology.Error) × (Slice Std.I32) ×
    (Slice Std.I32)) : Prop :=
  s.2.1.val.length = n ∧ s.2.2.val.length = m ∧ AllZeroPhases s.2.1.val ∧
    AllZeroPhases s.2.2.val ∧ SpinStatus s.1

theorem spin_body_post (L : scene.Layout) (routes : Slice scene.Route) (n m : Nat)
    (phases next : Slice Std.I32) (status : core.result.Result Unit topology.Error)
    (r : Std.Usize) (hinv : SpinInv n m (phases, next, status, r)) :
    OkPost (scene.Layout.check_spinning_portals_loop0.body L routes phases next status r)
      (fun y => match y with
        | .cont s => SpinInv n m s
        | .done y => SpinPost n m y) := by
  obtain ⟨hn, hm, hp, hq, hs⟩ := hinv
  simp only at hn hm hp hq hs
  unfold scene.Layout.check_spinning_portals_loop0.body
  by_cases hlt : r < Slice.len routes
  · simp only [hlt, ↓reduceIte]
    refine okPost_bind (okPost_trivial _) ?_
    intro b _
    by_cases hb : b = true
    · simp only [hb, ↓reduceIte]
      refine okPost_bind (okPost_trivial _) ?_
      intro r1 _
      refine okPost_bind (okPost_trivial _) ?_
      intro c _
      refine okPost_bind (okPost_trivial _) ?_
      intro mode _
      refine okPost_bind (okPost_trivial _) ?_
      intro b1 _
      by_cases hb1 : b1 = true
      · simp only [hb1, ↓reduceIte]
        refine okPost_bind (okPost_trivial _) ?_
        intro i1 _
        refine okPost_bind (okPost_trivial _) ?_
        intro ring _
        refine okPost_bind_eq (okPost_trivial _) ?_
        intro transform _ _
        refine okPost_bind (okPost_trivial _) ?_
        intro start _
        refine okPost_bind (okPost_trivial _) ?_
        intro count _
        refine okPost_bind (okPost_trivial _) ?_
        intro entrance _
        refine okPost_bind (okPost_trivial _) ?_
        intro i3 _
        refine okPost_bind (okPost_trivial _) ?_
        intro exit _
        refine okPost_bind (spin_mid_post L transform start count entrance exit n m phases next
          status 0#i32 ⟨hn, hm, zeroOff_of_allZero _ _ hp, zeroOff_of_allZero _ _ hq, hs⟩) ?_
        rintro ⟨p1, q1, st1⟩ ⟨hn1, hm1, hp1, hq1, hs1⟩
        simp only at hn1 hm1 hp1 hq1 hs1
        refine okPost_bind_eq (okPost_trivial _) ?_
        intro s hs2 _
        have hsv := slice_update_ok _ _ _ _ hs2
        refine okPost_bind_eq (okPost_trivial _) ?_
        intro s1 hs3 _
        have hsv2 := slice_update_ok _ _ _ _ hs3
        refine okPost_bind (okPost_trivial _) ?_
        intro r2 _
        refine okPost_ok ⟨?_, ?_, ?_, ?_, hs1⟩
        · simp [hsv, hn1]
        · simp [hsv2, hm1]
        · rw [hsv]; exact allZero_set _ _ hp1
        · rw [hsv2]; exact allZero_set _ _ hq1
      · simp only [hb1, Bool.false_eq_true, ↓reduceIte]
        refine okPost_bind (okPost_trivial _) ?_
        intro r2 _
        exact okPost_ok ⟨hn, hm, hp, hq, hs⟩
    · simp only [hb]
      exact okPost_ok ⟨hn, hm, hp, hq, hs⟩
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok ⟨hn, hm, hp, hq, hs⟩

/-- On return both scratch tables are all zero again (and keep their lengths), and the verdict is
`Ok` or `InvalidGeometry`, for every starting verdict of that kind. The scan only ever returns
`InvalidGeometry` itself: a doorway's own error is read as "not admitted", never forwarded. -/
theorem layout_check_spinning_portals_post (L : scene.Layout) (routes : Slice scene.Route)
    (phases next : Slice Std.I32) (hp : AllZeroPhases phases.val) (hq : AllZeroPhases next.val) :
    OkPost (scene.Layout.check_spinning_portals L routes phases next) (fun y =>
      y.2.1.val.length = phases.val.length ∧ y.2.2.val.length = next.val.length ∧
      AllZeroPhases y.2.1.val ∧ AllZeroPhases y.2.2.val ∧
      (y.1 = core.result.Result.Ok () ∨
        y.1 = core.result.Result.Err topology.Error.InvalidGeometry)) := by
  unfold scene.Layout.check_spinning_portals scene.Layout.check_spinning_portals_loop0
  refine okPost_loop (SpinInv phases.val.length next.val.length)
    (SpinPost phases.val.length next.val.length) _ ?_
    (phases, next, core.result.Result.Ok (), 0#usize) ⟨rfl, rfl, hp, hq, Or.inl rfl⟩
  rintro ⟨p, q, st, r⟩ h
  dsimp only
  refine okPost_mono (spin_body_post L routes _ _ p q st r h) ?_
  intro y hy
  cases y <;> exact hy

end Labyrinth
