module
public import LabyrinthCore.SceneInvPrepare
public import LabyrinthCore.SceneGeometryLayout

/-! A doorway reads only the phases of the transforms it holds.

`Layout::doorway` reads the phase table through `Circle::offset` only: the frame pose and the arc
of a sector of a spinning circle read that ring's phase, and the world position of a pose on a
twisting circle interpolates between the phase of its ring and of the ring outside it (a centre
reads ring `0`, a transition cell reads nothing). Each of those transforms is in the hold set the
doorway records, so two phase tables that agree on the doorway's holds give the same doorway. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

theorem bind_congr_ok {α β : Type _} {m : Result α} {k k' : α → Result β}
    (h : ∀ a, m = ok a → k a = k' a) : Std.bind m k = Std.bind m k' := by
  cases m using Result.cases with
  | ret a => rw [Std.bind_ok, Std.bind_ok]; exact h a rfl
  | vis e k0 =>
    rw [Std.bind_vis, Std.bind_vis]
    cases e with
    | fail err =>
      congr 1
      funext x
      exact x.elim
  | div => rw [Std.bind_div, Std.bind_div]

/-- Two phase tables agree at index `k`. -/
def PhAgree (p p' : Slice Std.I32) (k : Nat) : Prop := p.val[k]? = p'.val[k]?

theorem slice_index_congr (p p' : Slice Std.I32) (i : Std.Usize) (h : PhAgree p p' i.val) :
    Slice.index_usize p i = Slice.index_usize p' i := by
  unfold Slice.index_usize
  have : p[i]? = p'[i]? := by simpa [PhAgree] using h
  rw [this]

theorem offset_congr (c : polar.Circle) (ring : Std.Usize) (p p' : Slice Std.I32)
    (h : PhAgree p p' (c.transform_start.val + ring.val)) :
    polar.Circle.offset c ring p = polar.Circle.offset c ring p' := by
  unfold polar.Circle.offset
  apply bind_congr_ok
  intro i hi
  rw [slice_index_congr p p' i (by rw [usize_add_ok _ _ _ hi]; exact h)]

/-! ### Which transforms a hold set records -/

/-- The hold set records transform `k`. -/
def HoldHas (h : walker.Holds) (k : Nat) : Prop :=
  ∃ j, j < h.count.val ∧ ∃ x : Std.Usize, h.ids.val[j]? = some x ∧ x.val = k

theorem holdHas_iff_mem (h : walker.Holds) (k : Nat) :
    HoldHas h k ↔ ∃ x ∈ h.ids.val.take h.count.val, x.val = k := by
  constructor
  · rintro ⟨j, hj, x, hx, rfl⟩
    exact ⟨x, (mem_take_iff h x).mpr ⟨j, hj, hx⟩ |>.elim (fun y hy => by
      obtain ⟨hy1, hy2⟩ := hy; subst hy2; exact hy1), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨j, hj, hjx⟩ := (mem_take_iff h x).mp ⟨x, hx, rfl⟩
    exact ⟨j, hj, x, hjx, rfl⟩

/-- An accepted insert keeps every recorded transform, records `id`, and stays within four. -/
theorem holds_insert_has (h : walker.Holds) (id : Std.Usize) (hc : h.count.val ≤ 4) :
    OkPost (walker.Holds.insert h id) (fun r => r.1 = core.result.Result.Ok () →
      r.2.count.val ≤ 4 ∧ HoldHas r.2 id.val ∧ ∀ k, HoldHas h k → HoldHas r.2 k) := by
  refine okPost_mono (okPost_of_spec (holds_insert_spec h id hc)) ?_
  rintro r ⟨h1, h2, h3⟩ hok
  by_cases hin : ∃ x ∈ h.ids.val.take h.count.val, x = id
  · rw [h1 hin]
    refine ⟨hc, ?_, fun k hk => hk⟩
    obtain ⟨x, hx, rfl⟩ := hin
    exact (holdHas_iff_mem h x.val).mpr ⟨x, hx, rfl⟩
  · have hno : ∀ x ∈ h.ids.val.take h.count.val, x ≠ id := fun x hx he => hin ⟨x, hx, he⟩
    by_cases h4 : h.count.val = 4
    · rw [h2 hno h4] at hok; simp at hok
    · obtain ⟨c', hc', hr⟩ := h3 hno (by omega)
      rw [hr]
      have hlen : h.ids.val.length = 4 := holds_ids_length h
      refine ⟨by simp only; omega, ⟨h.count.val, by simp only; omega, id, ?_, rfl⟩, ?_⟩
      · simp only [Std.Array.set_val_eq]
        rw [List.getElem?_set_self (by omega)]
      · rintro k ⟨j, hj, x, hx, hxk⟩
        refine ⟨j, by simp only; omega, x, ?_, hxk⟩
        simp only [Std.Array.set_val_eq]
        rw [List.getElem?_set_ne (by omega)]
        exact hx

/-- What one of the ring loops of `Layout::holds` records: every ring from `first` to `last`. -/
def RingsHeld (c : polar.Circle) (h0 : walker.Holds) (first last : Nat)
    (r : (core.result.Result Unit topology.Error) × walker.Holds) : Prop :=
  r.1 = core.result.Result.Ok () → r.2.count.val ≤ 4 ∧ (∀ k, HoldHas h0 k → HoldHas r.2 k) ∧
    ∀ j, first ≤ j → j ≤ last → HoldHas r.2 (c.transform_start.val + j)

/-- The invariant of a ring loop at ring `rg`. -/
def RingsInv (c : polar.Circle) (h0 : walker.Holds) (first : Nat)
    (s : walker.Holds × (core.result.Result Unit topology.Error) × Std.Usize) : Prop :=
  s.2.1 = core.result.Result.Ok () → s.1.count.val ≤ 4 ∧ (∀ k, HoldHas h0 k → HoldHas s.1 k) ∧
    first ≤ s.2.2.val ∧ ∀ j, first ≤ j → j < s.2.2.val → HoldHas s.1 (c.transform_start.val + j)

theorem rings_step (c : polar.Circle) (h0 : walker.Holds) (first : Nat) (res : walker.Holds)
    (rg : Std.Usize)
    (hinv : RingsInv c h0 first (res, core.result.Result.Ok (), rg)) :
    OkPost (do
      let id ← c.transform_start + rg
      let (status1, result1) ← walker.Holds.insert res id
      let ring1 ← rg + 1#usize
      ok (.cont (result1, status1, ring1)) : Result (ControlFlow (walker.Holds ×
        (core.result.Result Unit topology.Error) × Std.Usize)
        ((core.result.Result Unit topology.Error) × walker.Holds)))
      (fun r => ∃ x', r = .cont x' ∧ RingsInv c h0 first x') := by
  obtain ⟨hc, hkeep, hfirst, hall⟩ := hinv rfl
  simp only at hc hkeep hfirst hall
  refine okPost_bind_eq (okPost_trivial _) ?_
  intro id hid _
  have hidv : id.val = c.transform_start.val + rg.val := usize_add_ok _ _ _ hid
  refine okPost_bind (holds_insert_has res id hc) ?_
  rintro ⟨st1, res1⟩ hins
  refine okPost_bind_eq (okPost_trivial _) ?_
  intro rg1 hrg1 _
  have hrg1v : rg1.val = rg.val + 1 := usize_add_ok _ _ _ hrg1
  refine okPost_ok ⟨_, rfl, ?_⟩
  intro hst
  simp only at hst ⊢
  obtain ⟨hc1, hnew, hk1⟩ := hins hst
  refine ⟨hc1, fun k hk => hk1 k (hkeep k hk), by omega, fun j hj1 hj2 => ?_⟩
  by_cases hjr : j = rg.val
  · subst hjr; rw [← hidv]; exact hnew
  · exact hk1 _ (hall j hj1 (by omega))

theorem holds_loop1_has (c : polar.Circle) (last : Std.Usize) (h0 : walker.Holds)
    (first : Std.Usize) (hc : h0.count.val ≤ 4) :
    OkPost (scene.Layout.holds_loop1 h0 c last (core.result.Result.Ok ()) first)
      (RingsHeld c h0 first.val last.val) := by
  unfold scene.Layout.holds_loop1
  refine okPost_loop (RingsInv c h0 first.val) _ _ ?_ _
    (fun _ => ⟨hc, fun k hk => hk, le_refl _, fun j h1 h2 => by simp only at h2; omega⟩)
  rintro ⟨res, st, rg⟩ hinv
  simp only [RingsInv] at hinv
  unfold scene.Layout.holds_loop1.body
  by_cases hle : rg ≤ last
  · simp only [hle, ↓reduceIte]
    cases st with
    | Err x =>
      simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte]
      exact okPost_ok (fun h => by simp at h)
    | Ok u =>
      cases u
      simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte]
      exact okPost_mono (rings_step c h0 first.val res rg hinv)
        (fun r ⟨x', hx, h⟩ => by subst hx; exact h)
  · simp only [hle, ↓reduceIte]
    refine okPost_ok (fun hst => ?_)
    obtain ⟨hc', hkeep, hf, hall⟩ := hinv hst
    have : ¬ rg.val ≤ last.val := hle
    exact ⟨hc', hkeep, fun j h1 h2 => hall j h1 (by omega)⟩

theorem holds_loop2_has (c : polar.Circle) (last : Std.Usize) (h0 : walker.Holds)
    (first : Std.Usize) (hc : h0.count.val ≤ 4) :
    OkPost (scene.Layout.holds_loop2 h0 c last (core.result.Result.Ok ()) first)
      (RingsHeld c h0 first.val last.val) := by
  unfold scene.Layout.holds_loop2
  refine okPost_loop (RingsInv c h0 first.val) _ _ ?_ _
    (fun _ => ⟨hc, fun k hk => hk, le_refl _, fun j h1 h2 => by simp only at h2; omega⟩)
  rintro ⟨res, st, rg⟩ hinv
  simp only [RingsInv] at hinv
  unfold scene.Layout.holds_loop2.body
  by_cases hle : rg ≤ last
  · simp only [hle, ↓reduceIte]
    cases st with
    | Err x =>
      simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte]
      exact okPost_ok (fun h => by simp at h)
    | Ok u =>
      cases u
      simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte]
      exact okPost_mono (rings_step c h0 first.val res rg hinv)
        (fun r ⟨x', hx, h⟩ => by subst hx; exact h)
  · simp only [hle, ↓reduceIte]
    refine okPost_ok (fun hst => ?_)
    obtain ⟨hc', hkeep, hf, hall⟩ := hinv hst
    have : ¬ rg.val ≤ last.val := hle
    exact ⟨hc', hkeep, fun j h1 h2 => hall j h1 (by omega)⟩

theorem holds_loop0_has (c : polar.Circle) (h0 : walker.Holds) (hc : h0.count.val ≤ 4) :
    OkPost (scene.Layout.holds_loop0 h0 c (core.result.Result.Ok ()) 0#usize)
      (RingsHeld c h0 0 0) := by
  unfold scene.Layout.holds_loop0
  refine okPost_loop (RingsInv c h0 0) _ _ ?_ _
    (fun _ => ⟨hc, fun k hk => hk, le_refl _, fun j h1 h2 => by simp at h2⟩)
  rintro ⟨res, st, rg⟩ hinv
  simp only [RingsInv] at hinv
  unfold scene.Layout.holds_loop0.body
  by_cases hle : rg ≤ 0#usize
  · simp only [hle, ↓reduceIte]
    cases st with
    | Err x =>
      simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte]
      exact okPost_ok (fun h => by simp at h)
    | Ok u =>
      cases u
      simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte]
      exact okPost_mono (rings_step c h0 0 res rg hinv)
        (fun r ⟨x', hx, h⟩ => by subst hx; exact h)
  · simp only [hle, ↓reduceIte]
    refine okPost_ok (fun hst => ?_)
    obtain ⟨hc', hkeep, hf, hall⟩ := hinv hst
    have : ¬ rg.val ≤ 0 := by simpa using hle
    exact ⟨hc', hkeep, fun j h1 h2 => hall j h1 (by omega)⟩

/-- A circle whose rings twist (rather than spin rigidly). -/
def IsTwisting (c : polar.Circle) : Prop := ∃ a m, c.spec.mode = polar.MotionMode.Twisting a m

/-- The transforms whose phases the doorway computation may read for one end cell: a sector reads
its ring (a spinning sector through its frame pose and arc, a twisting one through its world
position), and a twisting sector also the ring outside it; a twisting centre reads ring `0`; a
transition cell of a twisting circle is charged with the outermost ring (the interpolation it would
start stops at the band edge). -/
def CellReads (L : scene.Layout) (cell : Nat) (k : Nat) : Prop :=
  (∃ circle ring sector c, L.cells.val[cell]? = some (scene.Cell.Sector circle ring sector) ∧
    L.circles.val[circle.val]? = some c ∧ ring.val < c.spec.sectors.val.length ∧
    (k = c.transform_start.val + ring.val ∨
      (IsTwisting c ∧ ring.val + 1 < c.spec.sectors.val.length ∧
        k = c.transform_start.val + (ring.val + 1)))) ∨
  (∃ circle c, L.cells.val[cell]? = some (scene.Cell.Center circle) ∧
    L.circles.val[circle.val]? = some c ∧ IsTwisting c ∧ k = c.transform_start.val + 0) ∨
  (∃ portal pt c, L.cells.val[cell]? = some (scene.Cell.Transition portal) ∧
    L.portals.val[portal.val]? = some pt ∧ L.circles.val[pt.spec.circle.val]? = some c ∧
    IsTwisting c ∧ k = c.transform_start.val + (c.spec.sectors.val.length - 1))

theorem circle_of_post (L : scene.Layout) (cell : Std.Usize) :
    OkPost (scene.Layout.circle_of L cell) (fun o => ∀ cl, L.cells.val[cell.val]? = some cl →
      (∀ k, (cl = scene.Cell.Center k ∨ ∃ r s, cl = scene.Cell.Sector k r s) → o = some k) ∧
      (∀ portal pt, cl = scene.Cell.Transition portal → L.portals.val[portal.val]? = some pt →
        o = some pt.spec.circle)) := by
  unfold scene.Layout.circle_of
  refine okPost_bind_eq (okPost_trivial _) ?_
  intro c hc _
  have hcs := vec_index_some hc
  cases c with
  | Grid a b d => exact okPost_ok (fun cl hcl => by
      rw [hcs] at hcl; cases hcl
      exact ⟨fun k hk => (by rcases hk with h | ⟨r, s, h⟩ <;> cases h),
        fun _ _ h => (by cases h)⟩)
  | Center x => exact okPost_ok (fun cl hcl => by
      rw [hcs] at hcl; cases hcl
      exact ⟨fun k hk => (by rcases hk with h | ⟨r, s, h⟩ <;> simp_all),
        fun _ _ h => (by cases h)⟩)
  | Sector x r0 s0 => exact okPost_ok (fun cl hcl => by
      rw [hcs] at hcl; cases hcl
      exact ⟨fun k hk => (by rcases hk with h | ⟨r, s, h⟩ <;> simp_all),
        fun _ _ h => (by cases h)⟩)
  | Transition p =>
    refine okPost_bind_eq (okPost_trivial _) (fun pt hpt _ => okPost_ok (fun cl hcl => ?_))
    rw [hcs] at hcl; cases hcl
    refine ⟨fun k hk => (by rcases hk with h | ⟨r, s, h⟩ <;> cases h),
      fun portal pt' h hpt' => ?_⟩
    cases h
    rw [vec_index_some hpt] at hpt'
    cases hpt'
    rfl

/-- `Layout::holds`, when it accepts, keeps the transforms already recorded and records every
transform the cell's doorway computation reads. -/
theorem layout_holds_has (L : scene.Layout) (cell : Std.Usize) (h0 : walker.Holds)
    (hc : h0.count.val ≤ 4) :
    OkPost (scene.Layout.holds L cell h0) (fun r => r.1 = core.result.Result.Ok () →
      r.2.count.val ≤ 4 ∧ (∀ k, HoldHas h0 k → HoldHas r.2 k) ∧
      ∀ k, CellReads L cell.val k → HoldHas r.2 k) := by
  unfold scene.Layout.holds
  refine okPost_bind (circle_of_post L cell) ?_
  intro o ho
  cases o with
  | none =>
    refine okPost_ok (fun _ => ⟨hc, fun k hk => hk, fun k hk => ?_⟩)
    exfalso
    rcases hk with ⟨circle, ring, sector, c, hcl, _⟩ | ⟨circle, c, hcl, _⟩ |
      ⟨portal, pt, c, hcl, hpt, _⟩
    · have := (ho _ hcl).1 circle (Or.inr ⟨ring, sector, rfl⟩); simp at this
    · have := (ho _ hcl).1 circle (Or.inl rfl); simp at this
    · have := (ho _ hcl).2 portal pt rfl hpt; simp at this
  | some circle =>
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro c hcc _
    have hcs := vec_index_some hcc
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro cl hcl _
    have hcls := vec_index_some hcl
    -- the circle of the cell is `circle`
    have hcirc : ∀ k, (cl = scene.Cell.Center k ∨ ∃ r s, cl = scene.Cell.Sector k r s) →
        k = circle := fun k hk => by
      have := (ho cl hcls).1 k hk; simp only [Option.some.injEq] at this; exact this.symm
    cases cl with
    | Grid a b d =>
      refine okPost_ok (fun _ => ⟨hc, fun k hk => hk, fun k hk => ?_⟩)
      exfalso
      rcases hk with ⟨_, _, _, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h, _⟩ <;> rw [hcls] at h <;>
        cases h
    | Center x =>
      have hx := hcirc x (Or.inl rfl); subst hx
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro mm hmm _
      simp only [polar.Circle.mode, ok.injEq] at hmm
      subst hmm
      cases hmode : c.spec.mode with
      | Spinning =>
        refine okPost_ok (fun _ => ⟨hc, fun k hk => hk, fun k hk => ?_⟩)
        exfalso
        rcases hk with ⟨_, _, _, _, h, _⟩ | ⟨circle', c', h, hc', ⟨a, m, htw⟩, _⟩ |
          ⟨_, _, _, h, _⟩
        · rw [hcls] at h; cases h
        · rw [hcls] at h; cases h; rw [hcs] at hc'; cases hc'; rw [hmode] at htw; cases htw
        · rw [hcls] at h; cases h
      | Twisting a m =>
        refine okPost_mono (holds_loop0_has c h0 hc) ?_
        rintro r hr hok
        obtain ⟨h1, h2, h3⟩ := hr hok
        refine ⟨h1, h2, fun k hk => ?_⟩
        rcases hk with ⟨_, _, _, _, h, _⟩ | ⟨circle', c', h, hc', _, rfl⟩ | ⟨_, _, _, h, _⟩
        · rw [hcls] at h; cases h
        · rw [hcls] at h; cases h; rw [hcs] at hc'; cases hc'
          exact h3 0 (le_refl _) (le_refl _)
        · rw [hcls] at h; cases h
    | Sector x ring sector =>
      have hx := hcirc x (Or.inr ⟨ring, sector, rfl⟩); subst hx
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro mm hmm _
      simp only [polar.Circle.mode, ok.injEq] at hmm
      subst hmm
      have hreads : ∀ k, CellReads L cell.val k → ring.val < c.spec.sectors.val.length ∧
          (k = c.transform_start.val + ring.val ∨
          (IsTwisting c ∧ ring.val + 1 < c.spec.sectors.val.length ∧
            k = c.transform_start.val + (ring.val + 1))) := by
        intro k hk
        rcases hk with ⟨circle', ring', sector', c', h, hc', hk⟩ | ⟨_, _, h, _⟩ |
          ⟨_, _, _, h, _⟩
        · rw [hcls] at h; cases h; rw [hcs] at hc'; cases hc'; exact hk
        · rw [hcls] at h; cases h
        · rw [hcls] at h; cases h
      cases hmode : c.spec.mode with
      | Spinning =>
        simp only [Std.bind_ok]
        refine okPost_mono (holds_loop1_has c ring h0 ring hc) ?_
        rintro r hr hok
        obtain ⟨h1, h2, h3⟩ := hr hok
        refine ⟨h1, h2, fun k hk => ?_⟩
        rcases (hreads k hk).2 with rfl | ⟨⟨a, m, htw⟩, _, _⟩
        · exact h3 ring.val (le_refl _) (le_refl _)
        · rw [hmode] at htw; cases htw
      | Twisting a m =>
        have hrlen : ∀ k, CellReads L cell.val k → ring.val < c.spec.sectors.val.length :=
          fun k hk => (hreads k hk).1
        refine okPost_bind (P := fun fl : Std.Usize × Std.Usize => fl.1.val = ring.val - 1 ∧
          (ring.val < c.spec.sectors.val.length →
            fl.2.val = min (ring.val + 1) (c.spec.sectors.val.length - 1))) ?_ ?_
        · simp only [lift, Std.bind_ok]
          refine okPost_bind_eq (okPost_trivial _) ?_
          intro i1 hi1 _
          refine okPost_bind_eq (okPost_trivial _) ?_
          intro i2 hi2 _
          refine okPost_bind_eq (okPost_trivial _) ?_
          intro i3 hi3 _
          have hi1v : i1.val = ring.val + 1 := usize_add_ok _ _ _ hi1
          simp only [polar.Circle.ring_count, ok.injEq] at hi2
          subst hi2
          have hi3v := usize_sub_ok _ _ _ hi3
          simp only [alloc.vec.Vec.len] at hi3v
          refine okPost_ok ⟨usize_saturating_sub_one ring, fun _ => ?_⟩
          have hmin : (core.cmp.impls.OrdUsize.min i1 i3).val = min i1.val i3.val := by simp
          simp only [hmin, hi1v]
          have h3 : i3.val + 1 = c.spec.sectors.val.length := by simpa using hi3v.1
          omega
        rintro ⟨first, last⟩ ⟨hf, hl⟩
        refine okPost_mono (holds_loop1_has c last h0 first hc) ?_
        rintro r hr hok
        obtain ⟨h1, h2, h3⟩ := hr hok
        refine ⟨h1, h2, fun k hk => ?_⟩
        have hrl := hrlen k hk
        have hl' := hl hrl
        simp only at hf hl'
        rcases (hreads k hk).2 with rfl | ⟨_, hlt, rfl⟩
        · exact h3 ring.val (by omega) (by omega)
        · exact h3 (ring.val + 1) (by omega) (by omega)
    | Transition p =>
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro i hi _
      simp only [polar.Circle.ring_count, ok.injEq] at hi
      subst hi
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro first hfirst _
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro last hlast _
      have hf := usize_sub_ok _ _ _ hfirst
      have hl := usize_sub_ok _ _ _ hlast
      simp only [alloc.vec.Vec.len] at hf hl
      refine okPost_mono (holds_loop2_has c _ h0 _ hc) ?_
      rintro r hr hok
      obtain ⟨h1, h2, h3⟩ := hr hok
      refine ⟨h1, h2, fun k hk => ?_⟩
      rcases hk with ⟨_, _, _, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨portal, pt, c', h, hpt, hc', _, rfl⟩
      · rw [hcls] at h; cases h
      · rw [hcls] at h; cases h
      · rw [hcls] at h; cases h
        have := (ho _ hcls).2 _ pt rfl hpt
        simp only [Option.some.injEq] at this
        subst this
        rw [hcs] at hc'; cases hc'
        have e1 : first.val + 1 = c.spec.sectors.val.length := by simpa using hf.1
        have e2 : last.val + 1 = c.spec.sectors.val.length := by simpa using hl.1
        have := h3 (c.spec.sectors.val.length - 1) (by omega) (by omega)
        exact this

end Labyrinth
