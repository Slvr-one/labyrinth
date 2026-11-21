module
public import LabyrinthCore.SceneGeometryBase

/-! Geometry totality (S8), arcs. `angle_delta`, `Arc::contains`, `shifted`, `swept`, `middle` and
the four-arc `overlap` search never fail on validated arcs; the bounds on the angle arguments are
the ones the scene validators enforce (angles and phases stay within `10^9`, which keeps every
intermediate sum inside `i32`). -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Labyrinth

/-- `angle_delta` returns the signed shortest turn from `f` to `t`, in `(-TURN/2, TURN/2]`,
congruent to `t - f` modulo `TURN`. Angles within `10^9` keep `t - f` inside `i32`. -/
@[step]
theorem polar_angle_delta_spec (f t : Std.I32)
    (hf : -1000000000 ≤ f.val ∧ f.val ≤ 1000000000)
    (ht : -1000000000 ≤ t.val ∧ t.val ≤ 1000000000) :
    polar.angle_delta f t ⦃ r => -2048 < r.val ∧ r.val ≤ 2048 ∧ r.val % 4096 = (t.val - f.val) % 4096 ⦄ := by
  unfold polar.angle_delta
  have h2 : (4096 : Int).tdiv 2 = 2048 := by decide
  step*
  all_goals (simp only [turn_val] at *; first | scalar_tac | omega)

/-- `contains` is total for a validated-bounds arc and an angle within `10^9`: it holds when the
arc is a full turn or the angle's offset from the start, modulo `TURN`, is within the length. -/
@[step]
theorem polar_arc_contains_spec (a : polar.Arc) (angle : Std.I32) (ha : ArcBnd a)
    (hang : -1000000000 ≤ angle.val ∧ angle.val ≤ 1000000000) :
    polar.Arc.contains a angle ⦃ b =>
      (b = true ↔ a.length.val = 4096 ∨ (angle.val - a.start.val) % 4096 ≤ a.length.val) ⦄ := by
  unfold polar.Arc.contains
  step*
  all_goals (simp only [turn_val, ArcOk, ArcBnd] at *; first | scalar_tac | omega | skip)

/-- `shifted` is total for a validated arc and a shift within `10^9`, and yields a validated arc
of the same length starting at `(start + amount) mod TURN`. -/
@[step]
theorem polar_arc_shifted_spec (a : polar.Arc) (amount : Std.I32) (ha : ArcOk a)
    (hamt : -1000000000 ≤ amount.val ∧ amount.val ≤ 1000000000) :
    polar.Arc.shifted a amount ⦃ r =>
      ArcOk r ∧ r.length = a.length ∧ r.start.val = (a.start.val + amount.val) % 4096 ⦄ := by
  unfold polar.Arc.shifted
  step*
  all_goals (simp only [turn_val, ArcOk, ArcBnd] at *; first | scalar_tac | omega | skip)

/-- `swept` is total for a validated arc and a sweep of at most one turn either way, and yields
a validated arc. -/
@[step]
theorem polar_arc_swept_spec (a : polar.Arc) (delta : Std.I32) (ha : ArcOk a)
    (hd : -4096 ≤ delta.val ∧ delta.val ≤ 4096) :
    polar.Arc.swept a delta ⦃ r => ArcOk r ⦄ := by
  unfold polar.Arc.swept
  step*
  all_goals (try (have hm : i2.val = min delta.val 0 := by
                    rw [i2_post]; exact core.cmp.impls.OrdI32.min_val _ _))
  all_goals (try (have hlt : i1.val < 4096 := by
                    have h := ‹¬ i1 ≥ polar.TURN›
                    rw [← turn_val]; scalar_tac))
  all_goals (simp only [turn_val, ArcOk, ArcBnd] at *; first | scalar_tac | omega | skip)

/-- `middle` is total for any arc with bounded fields and returns a normalized angle. -/
@[step]
theorem polar_arc_middle_spec (a : polar.Arc) (ha : ArcBnd a) :
    polar.Arc.middle a ⦃ r => 0 ≤ r.val ∧ r.val < 4096 ⦄ := by
  unfold polar.Arc.middle
  step*
  all_goals (simp only [turn_val, ArcOk, ArcBnd] at *; first | scalar_tac | omega | skip)

/-- All four arcs of an `overlap` call are validated. -/
def ArcsOk (arcs : Array polar.Arc 4#usize) : Prop :=
  ∀ i (hi : i < 4), ArcOk (arcs.val[i]'(by rw [arcs.property]; simpa using hi))

theorem arcs_len_val (arcs : Array polar.Arc 4#usize) :
    Slice.len (Array.to_slice arcs) = 4#usize := by
  apply UScalar.eq_of_val_eq
  rw [Slice.len_val]
  simp [Array.to_slice, Slice.length, arcs.property]

/-- The inner scan of `overlap` shortens the candidate `length` by each constraining arc, so it
returns a length in `[0, TURN]` whenever it starts in that range, the candidate start is an angle
in `[0, TURN)`, and every arc is validated. -/
theorem polar_overlap_inner_spec (arcs : Array polar.Arc 4#usize) (start length : Std.I32)
    (j : Std.Usize) (harcs : ArcsOk arcs)
    (hs : 0 ≤ start.val ∧ start.val < 4096) (hl : 0 ≤ length.val ∧ length.val ≤ 4096) :
    polar.overlap_loop0_loop0 arcs start length j ⦃ r => 0 ≤ r.val ∧ r.val ≤ 4096 ⦄ := by
  unfold polar.overlap_loop0_loop0
  apply loop.spec_decr_nat
    (fun state : Std.I32 × Std.Usize => 4 - state.2.val)
    (fun state : Std.I32 × Std.Usize => 0 ≤ state.1.val ∧ state.1.val ≤ 4096)
    (fun r : Std.I32 => 0 ≤ r.val ∧ r.val ≤ 4096)
    _ (length, j) _ ⟨hl.1, hl.2⟩
  rintro ⟨len, k⟩ hinv
  dsimp only at hinv ⊢
  unfold polar.overlap_loop0_loop0.body
  simp only [lift, Std.bind_ok, arcs_len_val]
  by_cases hk : k < 4#usize
  · simp only [hk, ite_true]
    have hk' : k.val < 4 := by scalar_tac
    have hkl : k.val < arcs.length := by simp [Std.Array.length, arcs.property]; omega
    apply spec_bind (Array.index_usize_spec arcs k hkl)
    intro a ha
    have hao : ArcOk a := by rw [ha]; exact harcs k.val hk'
    obtain ⟨h1, h2, h3, h4⟩ := hao
    by_cases hT : (a.length != polar.TURN) = true
    · simp only [hT, ite_true]
      apply spec_bind (Std.I32.sub_spec (x := start) (y := a.start) (by scalar_tac) (by scalar_tac))
      intro i1 hi1
      apply spec_bind (polar_normalize_spec i1)
      intro off ho
      by_cases hg : off > a.length
      · simp only [hg, ite_true, spec_ok]; simp
      · simp only [hg, ite_false]
        have hg' : off.val ≤ a.length.val := by scalar_tac
        apply spec_bind (Std.I32.sub_spec (x := a.length) (y := off) (by scalar_tac) (by scalar_tac))
        intro i2 hi2
        apply spec_bind (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac))
        intro n hn
        simp only [spec_ok, core.cmp.impls.OrdI32.min_val]
        have hnv : n.val = k.val + 1 := by simpa using hn
        refine ⟨?_, by omega⟩
        omega
    · simp only [hT, ite_false]
      apply spec_bind (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac))
      intro n hn
      simp only [spec_ok]
      have hnv : n.val = k.val + 1 := by simpa using hn
      exact ⟨hinv, by omega⟩
  · simp only [hk, ite_false, spec_ok]
    exact hinv

/-- The outer scan of `overlap` keeps the best witness an arc with a start in `[0, TURN)` and a
length in `[0, TURN]`: each candidate start is the start of a validated arc, and each candidate
length comes from the inner scan. -/
theorem polar_overlap_outer_spec (arcs : Array polar.Arc 4#usize) (i i1 : Std.I32)
    (i2 : Std.Usize) (harcs : ArcsOk arcs)
    (hs : 0 ≤ i.val ∧ i.val < 4096) (hl : 0 ≤ i1.val ∧ i1.val ≤ 4096) :
    polar.overlap_loop0 arcs i i1 i2 ⦃ r =>
      (0 ≤ r.1.val ∧ r.1.val < 4096) ∧ 0 ≤ r.2.val ∧ r.2.val ≤ 4096 ⦄ := by
  unfold polar.overlap_loop0
  apply loop.spec_decr_nat
    (fun state : Std.I32 × Std.I32 × Std.Usize => 4 - state.2.2.val)
    (fun state : Std.I32 × Std.I32 × Std.Usize =>
      (0 ≤ state.1.val ∧ state.1.val < 4096) ∧ 0 ≤ state.2.1.val ∧ state.2.1.val ≤ 4096)
    (fun r : Std.I32 × Std.I32 =>
      (0 ≤ r.1.val ∧ r.1.val < 4096) ∧ 0 ≤ r.2.val ∧ r.2.val ≤ 4096)
    _ (i, i1, i2) _ ⟨hs, hl⟩
  rintro ⟨bs, bl, k⟩ hinv
  dsimp only at hinv ⊢
  unfold polar.overlap_loop0.body
  simp only [lift, Std.bind_ok, arcs_len_val]
  by_cases hk : k < 4#usize
  · simp only [hk, ite_true]
    have hk' : k.val < 4 := by scalar_tac
    have hkl : k.val < arcs.length := by simp [Std.Array.length, arcs.property]; omega
    apply spec_bind (Array.index_usize_spec arcs k hkl)
    intro a ha
    have hao : ArcOk a := by rw [ha]; exact harcs k.val hk'
    obtain ⟨h1, h2, h3, h4⟩ := hao
    apply spec_bind (polar_overlap_inner_spec arcs a.start polar.TURN 0#usize harcs
      ⟨h1, h2⟩ (by rw [turn_val]; omega))
    intro len hlen
    by_cases hg : len > bl
    · simp only [hg, ite_true, Std.bind_ok]
      apply spec_bind (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac))
      intro n hn
      have hnv : n.val = k.val + 1 := by simpa using hn
      simp only [spec_ok]
      refine ⟨⟨⟨h1, h2⟩, hlen⟩, by omega⟩
    · simp only [hg, ite_false, Std.bind_ok]
      apply spec_bind (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac))
      intro n hn
      have hnv : n.val = k.val + 1 := by simpa using hn
      simp only [spec_ok]
      exact ⟨hinv, by omega⟩
  · simp only [hk, ite_false, spec_ok]
    exact hinv

/-- `overlap` is total for four validated arcs and any minimum, and the witness it returns is a
well-formed (possibly empty) arc: start in `[0, TURN)` and length in `[0, TURN]`. A failure is
always `InvalidGeometry`, produced when the best common length is below `minimum`. -/
@[step]
theorem polar_overlap_spec (arcs : Array polar.Arc 4#usize) (minimum : Std.I32)
    (h : ArcsOk arcs) :
    polar.overlap arcs minimum ⦃ r =>
      (∀ e, r = .Err e → e = .InvalidGeometry) ∧ (∀ a, r = .Ok a → ArcBnd a) ⦄ := by
  unfold polar.overlap
  apply spec_bind (polar_overlap_outer_spec arcs 0#i32 0#i32 0#usize h (by simp) (by simp))
  rintro ⟨bs, bl⟩ ⟨hs, hl⟩
  dsimp only at hs hl ⊢
  show (if bl < minimum then _ else _) ⦃ _ ⦄
  split_ifs with hm
  · simp only [spec_ok]
    refine ⟨fun e he => ?_, fun a ha => (by cases ha)⟩
    cases he; rfl
  · simp only [spec_ok]
    refine ⟨fun e he => (by cases he), fun a ha => ?_⟩
    cases ha
    exact ⟨hs.1, hs.2, hl.1, hl.2⟩

end Labyrinth
