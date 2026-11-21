module
public import LabyrinthCore.SceneEditPrepare
public import LabyrinthCore.SceneGeometryBase
public import LabyrinthCore.SceneReservationHolds

/-! The scene invariant, part 1: the first loop of `prepare_motion`, and the phase range.

The first loop of `prepare_motion` walks the step table: a negative step or one above `TURN / 8`
is rejected, a nonzero step on a transform whose hold counter is nonzero is rejected (`Occupied`),
and otherwise `normalize(phases[i] + steps[i])` goes into the scratch table. An accepted motion
therefore leaves every held transform's phase as it was, once the published phases lie in
`[0, TURN)`: that range is the invariant `PhaseRange`. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- Every published phase lies in `[0, TURN)`. -/
def PhaseRange (s : scene.Scene) : Prop :=
  ∀ x ∈ s.phases.val, 0 ≤ x.val ∧ x.val < 4096

/-- What the first loop of `prepare_motion` decided at index `j`: an admissible step, zero unless
the hold counter is zero, and the normalized sum in the scratch table. -/
def PrepEntry (phases : List Std.I32) (holds : List Std.Usize) (steps : List Std.I32)
    (acc : List Std.I32) (j : Nat) : Prop :=
  ∃ s ph n : Std.I32, steps[j]? = some s ∧ phases[j]? = some ph ∧ acc[j]? = some n ∧
    0 ≤ s.val ∧ s.val ≤ 512 ∧ (s.val ≠ 0 → holds[j]? = some 0#usize) ∧
    n.val = (ph.val + s.val) % 4096

theorem normalize_ok_val {x n : Std.I32} (h : polar.normalize x = ok n) :
    n.val = x.val % 4096 ∧ 0 ≤ n.val ∧ n.val < 4096 := by
  have hs := polar_normalize_spec x
  rw [h] at hs
  have := (spec_ok _).mp hs
  exact ⟨this.2.2, this.1, this.2.1⟩

theorem i32_add_ok {x y z : Std.I32} (h : x + y = ok z) : z.val = x.val + y.val := by
  have := IScalar.add_equiv x y
  rw [h] at this
  exact this.2.1

theorem vec_index_some {α : Type _} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    v.val[i.val]? = some x := by
  simp only [alloc.vec.Vec.index_slice_index] at h
  exact vec_index_ok v i x h

theorem slice_index_some {α : Type _} {v : Slice α} {i : Std.Usize} {x : α}
    (h : Slice.index_usize v i = ok x) : v.val[i.val]? = some x := by
  unfold Slice.index_usize at h
  cases hv : v[i]? with
  | none => rw [hv] at h; simp at h
  | some y =>
    rw [hv] at h
    simp only [ok.injEq] at h
    subst h
    simp

theorem index_mut_ok_lt {α : Type _} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    {back : α → alloc.vec.Vec α}
    (h : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i = ok (x, back)) :
    i.val < v.val.length := by
  simp only [alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize,
    alloc.vec.Vec.index_usize] at h
  split at h
  · simp only [bind_tc_fail] at h
    exact absurd h fail_not_ok
  · rename_i y hy
    exact (List.getElem?_eq_some_iff.mp (by simpa using hy)).1

theorem prepEntry_set (phases : List Std.I32) (holds : List Std.Usize) (steps acc : List Std.I32)
    (c : Nat) (n : Std.I32) (j : Nat) (hj : j < c) (h : PrepEntry phases holds steps acc j) :
    PrepEntry phases holds steps (acc.set c n) j := by
  obtain ⟨s, ph, m, h1, h2, h3, h4⟩ := h
  exact ⟨s, ph, m, h1, h2, by rw [List.getElem?_set_ne (by omega)]; exact h3, h4⟩

/-- The first loop of `prepare_motion`: the scratch table keeps its length, and when the loop ends
with `Ok` every index of the step table is described by `PrepEntry`. -/
theorem prepare_motion_loop0_spec (phases next : alloc.vec.Vec Std.I32)
    (holds : alloc.vec.Vec Std.Usize) (steps : Slice Std.I32) :
    OkPost (scene.Scene.prepare_motion_loop0 phases next holds steps (core.result.Result.Ok ())
      0#usize) (fun y => y.1.val.length = next.val.length ∧
        (y.2 = core.result.Result.Ok () → ∀ j, j < steps.val.length →
          PrepEntry phases.val holds.val steps.val y.1.val j)) := by
  unfold scene.Scene.prepare_motion_loop0
  refine okPost_loop (fun s : alloc.vec.Vec Std.I32 × (core.result.Result Unit topology.Error) ×
      Std.Usize => s.1.val.length = next.val.length ∧
        (s.2.1 = core.result.Result.Ok () → s.2.2.val ≤ steps.val.length ∧
          ∀ j, j < s.2.2.val → PrepEntry phases.val holds.val steps.val s.1.val j)) _ _ ?_ _
    ⟨rfl, fun _ => ⟨by simp, fun j hj => by simp at hj⟩⟩
  rintro ⟨acc, st, c⟩ ⟨hlen, hinv⟩
  dsimp only at hlen hinv
  unfold scene.Scene.prepare_motion_loop0.body
  by_cases hlt : c < Slice.len steps
  · simp only [hlt, ↓reduceIte]
    have hcl : c.val < steps.val.length := by simpa [Slice.len] using hlt
    cases st with
    | Err x =>
      simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte]
      exact okPost_ok ⟨hlen, fun h => by simp at h⟩
    | Ok u =>
      cases u
      obtain ⟨_, hpre⟩ := hinv rfl
      simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte]
      refine okPost_bind_eq (okPost_trivial _) ?_
      intro i2 hi2 _
      have hs : steps.val[c.val]? = some i2 := slice_index_some hi2
      -- the write at index `c`, for a step `i2` that passed the checks
      have write : ∀ (i5 i6 i7 : Std.I32), phases.val[c.val]? = some i5 → i5 + i2 = ok i6 →
          polar.normalize i6 = ok i7 → 0 ≤ i2.val → i2.val ≤ 512 →
          (i2.val ≠ 0 → holds.val[c.val]? = some 0#usize) →
          OkPost (do
            let (_, index_mut_back) ← alloc.vec.Vec.index_mut
              (core.slice.index.SliceIndexUsizeSlice Std.I32) acc c
            let v4 := index_mut_back i7
            ok (v4, (core.result.Result.Ok () : core.result.Result Unit topology.Error)) :
              Result (alloc.vec.Vec Std.I32 × core.result.Result Unit topology.Error))
            (fun p => p.1.val.length = next.val.length ∧
              (p.2 = core.result.Result.Ok () → c.val + 1 ≤ steps.val.length ∧
                ∀ j, j < c.val + 1 → PrepEntry phases.val holds.val steps.val p.1.val j)) := by
        intro i5 i6 i7 hph hadd hnorm h0 h512 hhold
        refine okPost_bind_eq (okPost_trivial _) ?_
        rintro ⟨x, back⟩ hm _
        have hcl2 : c.val < acc.val.length := index_mut_ok_lt hm
        rw [index_mut_ok_set acc c x back hm]
        refine okPost_ok ⟨by simpa using hlen, fun _ => ⟨by omega, fun j hj => ?_⟩⟩
        simp only [alloc.vec.Vec.set_val_eq]
        by_cases hjc : j = c.val
        · subst hjc
          refine ⟨i2, i5, i7, hs, hph, by rw [List.getElem?_set_self hcl2], h0, h512, hhold, ?_⟩
          rw [(normalize_ok_val hnorm).1, i32_add_ok hadd]
        · exact prepEntry_set _ _ _ _ _ _ j (by omega) (hpre j (by omega))
      refine okPost_bind (P := fun p : alloc.vec.Vec Std.I32 × (core.result.Result Unit
          topology.Error) => p.1.val.length = next.val.length ∧
            (p.2 = core.result.Result.Ok () → c.val + 1 ≤ steps.val.length ∧
              ∀ j, j < c.val + 1 → PrepEntry phases.val holds.val steps.val p.1.val j)) ?_ ?_
      swap
      · rintro ⟨v4, st1⟩ h
        refine okPost_bind_eq (okPost_trivial _) ?_
        intro i3 hi3 _
        have hi3v : i3.val = c.val + 1 := usize_add_ok _ _ _ hi3
        exact okPost_ok ⟨h.1, fun hst => by rw [hi3v]; exact h.2 hst⟩
      by_cases h1 : i2 < 0#i32
      · simp only [h1, ↓reduceIte]
        exact okPost_ok ⟨hlen, fun h => by simp at h⟩
      · simp only [h1, ↓reduceIte]
        have h1' : 0 ≤ i2.val := by
          have : ¬ i2.val < 0 := fun h => h1 (by scalar_tac)
          omega
        refine okPost_bind_eq (okPost_trivial _) ?_
        intro i3 hi3 _
        have hi3v : i3.val = 512 := by
          obtain ⟨z, hz, hzv⟩ := IScalar.div_spec (x := polar.TURN) (y := 8#i32) (by simp)
            (by simp [polar.TURN])
          rw [hz] at hi3
          simp only [ok.injEq] at hi3
          subst hi3
          rw [hzv, turn_val]
          decide
        by_cases h2 : i2 > i3
        · simp only [h2, ↓reduceIte]
          exact okPost_ok ⟨hlen, fun h => by simp at h⟩
        · simp only [h2, ↓reduceIte]
          have h2' : i2.val ≤ 512 := by
            have : ¬ i3.val < i2.val := fun h => h2 (by scalar_tac)
            omega
          by_cases h3 : (i2 != 0#i32) = true
          · simp only [h3, ↓reduceIte]
            refine okPost_bind_eq (okPost_trivial _) ?_
            intro i4 hi4 _
            by_cases h4 : (i4 != 0#usize) = true
            · simp only [h4, ↓reduceIte]
              exact okPost_ok ⟨hlen, fun h => by simp at h⟩
            · simp only [h4, Bool.false_eq_true, ↓reduceIte]
              have hi4z : i4 = 0#usize := UScalar.eq_of_val_eq (by simpa using h4)
              have hh : holds.val[c.val]? = some 0#usize := by
                rw [← hi4z]; exact vec_index_some hi4
              refine okPost_bind_eq (okPost_trivial _) ?_
              intro i5 hi5 _
              refine okPost_bind_eq (okPost_trivial _) ?_
              intro i6 hi6 _
              refine okPost_bind_eq (okPost_trivial _) ?_
              intro i7 hi7 _
              exact write i5 i6 i7 (vec_index_some hi5) hi6 hi7 h1' h2' (fun _ => hh)
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]
            have hz : i2.val = 0 := by simpa using h3
            refine okPost_bind_eq (okPost_trivial _) ?_
            intro i5 hi5 _
            refine okPost_bind_eq (okPost_trivial _) ?_
            intro i6 hi6 _
            refine okPost_bind_eq (okPost_trivial _) ?_
            intro i7 hi7 _
            exact write i5 i6 i7 (vec_index_some hi5) hi6 hi7 h1' h2' (fun h => absurd hz h)
  · simp only [hlt, ↓reduceIte]
    refine okPost_ok ⟨hlen, fun hst j hj => ?_⟩
    obtain ⟨hc, hpre⟩ := hinv hst
    have : ¬ c.val < steps.val.length := by simpa [Slice.len] using hlt
    exact hpre j (by omega)

/-- What an accepted `prepare_motion` wrote into the scratch table. -/
def PrepAccepted (self : scene.Scene) (steps : Slice Std.I32) (np : alloc.vec.Vec Std.I32) : Prop :=
  steps.val.length = self.phases.val.length ∧ np.val.length = self.next_phases.val.length ∧
  ∀ j, j < steps.val.length → PrepEntry self.phases.val self.holds.val steps.val np.val j

/-- `prepare_motion`: only the scratch table changes; an accepted call wrote it as the first loop
describes. -/
theorem prepare_motion_spec (self : scene.Scene) (stamp : walker.Stamp) (steps : Slice Std.I32) :
    OkPost (scene.Scene.prepare_motion self stamp steps) (fun p =>
      ∃ v : alloc.vec.Vec Std.I32, v.val.length = self.next_phases.val.length ∧
        p.2 = { self with next_phases := v } ∧
        ∀ r, p.1 = core.result.Result.Ok r → PrepAccepted self steps v) := by
  unfold scene.Scene.prepare_motion
  refine okPost_bind (okPost_trivial _) ?_
  intro r _
  cases r with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    exact okPost_ok ⟨self.next_phases, rfl, rfl, fun r h => by simp at h⟩
  | Ok val =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    split
    · exact okPost_ok ⟨self.next_phases, rfl, rfl, fun r h => by simp at h⟩
    · split
      · exact okPost_ok ⟨self.next_phases, rfl, rfl, fun r h => by simp at h⟩
      · split
        · exact okPost_ok ⟨self.next_phases, rfl, rfl, fun r h => by simp at h⟩
        · split
          · exact okPost_ok ⟨self.next_phases, rfl, rfl, fun r h => by simp at h⟩
          · rename_i hne
            have hsl : steps.val.length = self.phases.val.length := by
              simpa using hne
            refine okPost_bind (prepare_motion_loop0_spec self.phases self.next_phases self.holds
              steps) ?_
            rintro ⟨v, status⟩ ⟨hv, hacc⟩
            dsimp only at hv hacc
            cases status with
            | Err x =>
              simp
              simp only [Std.bind_ok,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.from, bind_tc_ok]
              exact okPost_ok ⟨v, hv, rfl, fun r h => by simp at h⟩
            | Ok u =>
              cases u
              have hpa : PrepAccepted self steps v := ⟨hsl, hv, hacc rfl⟩
              simp
              refine okPost_bind (P := fun y => ∃ st, y = (self.layout.cell_grid,
                self.layout.cells, self.layout.circles, self.layout.portals, self.layout.bands,
                self.layout.geometry, self.layout.carrier, self.layout.transforms, st))
                (prepare_motion_loop1_frame self.layout steps (core.result.Result.Ok ()) 0#usize)
                ?_
              rintro ⟨g, v1, v2, v3, v4, g1, c, i2, status1⟩ ⟨st, heq⟩
              simp only [Prod.mk.injEq] at heq
              obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := heq
              simp
              cases status1 with
              | Err y =>
                simp only [Std.bind_ok,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  core.convert.FromSame.from, bind_tc_ok]
                exact okPost_ok ⟨v, hv, rfl, fun r h => by simp at h⟩
              | Ok u1 =>
                cases u1
                simp
                refine okPost_bind (okPost_trivial _) ?_
                intro status2 _
                cases status2 with
                | Err z =>
                  simp only [Std.bind_ok,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                    core.convert.FromSame.from, bind_tc_ok]
                  exact okPost_ok ⟨v, hv, rfl, fun r h => by simp at h⟩
                | Ok u2 =>
                  cases u2
                  simp
                  exact okPost_ok ⟨v, hv, rfl, fun _ _ => hpa⟩

/-- An accepted motion's scratch table holds phases in `[0, TURN)` at every step index. -/
theorem prepAccepted_range {self : scene.Scene} {steps : Slice Std.I32} {np : alloc.vec.Vec Std.I32}
    (h : PrepAccepted self steps np) (j : Nat) (hj : j < self.phases.val.length) :
    ∃ n, np.val[j]? = some n ∧ 0 ≤ n.val ∧ n.val < 4096 := by
  obtain ⟨s, ph, n, _, _, hn, _, _, _, hv⟩ := h.2.2 j (by rw [h.1]; exact hj)
  refine ⟨n, hn, ?_, ?_⟩ <;> rw [hv] <;> omega

/-- **The first loop's guarantee.** With the published phases in `[0, TURN)`, an accepted motion
leaves the phase of every held transform (hold counter nonzero) unchanged in the scratch table. -/
theorem prepAccepted_held {self : scene.Scene} {steps : Slice Std.I32} {np : alloc.vec.Vec Std.I32}
    (h : PrepAccepted self steps np) (hr : PhaseRange self) (k : Nat) (a : Std.Usize)
    (hk : self.holds.val[k]? = some a) (ha : a.val ≠ 0) (hkl : k < self.phases.val.length) :
    np.val[k]? = self.phases.val[k]? := by
  obtain ⟨s, ph, n, hs, hph, hn, h0, _, hhold, hv⟩ := h.2.2 k (by rw [h.1]; exact hkl)
  have hs0 : s.val = 0 := by
    by_contra hne
    have := hhold hne
    rw [hk] at this
    simp only [Option.some.injEq] at this
    subst this
    exact ha rfl
  have hrange := hr ph (List.mem_of_getElem? hph)
  rw [hn, hph]
  congr 1
  apply IScalar.eq_of_val_eq
  rw [hv, hs0, Int.add_zero]
  exact Int.emod_eq_of_lt hrange.1 hrange.2

end Labyrinth
