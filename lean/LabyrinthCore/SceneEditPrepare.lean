module
public import LabyrinthCore.SceneEditPublish

/-! Scene edits (S3), part 4: `Scene::prepare_motion` leaves the published scene alone and only
rewrites the scratch phase table `next_phases` (keeping its length). The planner's checks are not
analysed here; this is the frame that `motion` needs. Partial correctness (`OkPost`): the checks
reach the geometry. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

theorem prepare_motion_loop1_frame (l : scene.Layout) (steps : Slice Std.I32)
    (status : core.result.Result Unit topology.Error) (ci : Std.Usize) :
    OkPost (scene.Scene.prepare_motion_loop1 l steps status ci) (fun y =>
      ∃ st, y = (l.cell_grid, l.cells, l.circles, l.portals, l.bands, l.geometry, l.carrier,
        l.transforms, st)) := by
  unfold scene.Scene.prepare_motion_loop1
  refine okPost_loop (fun _ => True) _ _ ?_ (status, ci) trivial
  rintro ⟨st, c⟩ -
  dsimp only
  unfold scene.Scene.prepare_motion_loop1.body
  by_cases hlt : c < alloc.vec.Vec.len l.circles
  · simp only [hlt, ↓reduceIte]
    refine okPost_bind (okPost_trivial _) ?_
    intro b _
    by_cases hb : b = true
    · simp only [hb, ↓reduceIte]
      refine okPost_bind (okPost_trivial _) ?_
      intro circle _
      refine okPost_bind (okPost_trivial _) ?_
      intro mm _
      cases mm with
      | Spinning =>
        refine okPost_bind (okPost_trivial _) ?_
        intro c1 _
        exact okPost_ok trivial
      | Twisting a b =>
        refine okPost_bind (okPost_trivial _) ?_
        intro st1 _
        refine okPost_bind (okPost_trivial _) ?_
        intro c1 _
        exact okPost_ok trivial
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact okPost_ok ⟨st, rfl⟩
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok ⟨st, rfl⟩

/-- A mutable index that succeeded hands back the vector with that entry set. -/
theorem index_mut_ok_set {α : Type _} (v : alloc.vec.Vec α) (i : Std.Usize) (x : α)
    (back : α → alloc.vec.Vec α)
    (h : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i = ok (x, back)) :
    back = alloc.vec.Vec.set v i := by
  simp only [alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize,
    alloc.vec.Vec.index_usize] at h
  split at h
  · simp only [bind_tc_fail] at h
    exact absurd h fail_not_ok
  · simp only [bind_tc_ok, ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm

theorem prepare_motion_loop0_len (v v1 : alloc.vec.Vec Std.I32) (v2 : alloc.vec.Vec Std.Usize)
    (steps : Slice Std.I32) (status : core.result.Result Unit topology.Error) (i : Std.Usize) :
    OkPost (scene.Scene.prepare_motion_loop0 v v1 v2 steps status i)
      (fun y => y.1.val.length = v1.val.length) := by
  unfold scene.Scene.prepare_motion_loop0
  refine okPost_loop (fun s : alloc.vec.Vec Std.I32 × (core.result.Result Unit topology.Error) ×
      Std.Usize => s.1.val.length = v1.val.length) _ _ ?_ (v1, status, i) rfl
  rintro ⟨v3, st, c⟩ hlen
  dsimp only at hlen
  unfold scene.Scene.prepare_motion_loop0.body
  by_cases hlt : c < Slice.len steps
  · simp only [hlt, ↓reduceIte]
    refine okPost_bind (okPost_trivial _) ?_
    intro b _
    by_cases hb : b = true
    · simp only [hb, ↓reduceIte]
      refine okPost_bind (okPost_trivial _) ?_
      intro i2 _
      have step : ∀ (i7 : Std.I32) (st' : core.result.Result Unit topology.Error),
          OkPost (do
            let (_, index_mut_back) ← alloc.vec.Vec.index_mut
              (core.slice.index.SliceIndexUsizeSlice Std.I32) v3 c
            ok (index_mut_back i7, st') : Result (alloc.vec.Vec Std.I32 ×
              (core.result.Result Unit topology.Error)))
            (fun y => y.1.val.length = v1.val.length) := by
        intro i7 st'
        refine okPost_bind_eq (okPost_trivial _) ?_
        rintro ⟨x, back⟩ hm _
        rw [index_mut_ok_set v3 c x back hm]
        exact okPost_ok (by simpa using hlen)
      refine okPost_bind (P := fun p : alloc.vec.Vec Std.I32 × (core.result.Result Unit
          topology.Error) => p.1.val.length = v1.val.length) ?_ ?_
      swap
      · rintro ⟨v4, st1⟩ h
        refine okPost_bind (okPost_trivial _) ?_
        intro i3 _
        exact okPost_ok h
      by_cases h1 : i2 < 0#i32
      · simp only [h1, ↓reduceIte]
        exact okPost_ok hlen
      · simp only [h1, ↓reduceIte]
        refine okPost_bind (okPost_trivial _) ?_
        intro i3 _
        by_cases h2 : i2 > i3
        · simp only [h2, ↓reduceIte]
          exact okPost_ok hlen
        · simp only [h2, ↓reduceIte]
          by_cases h3 : (i2 != 0#i32) = true
          · simp only [h3, ↓reduceIte]
            refine okPost_bind (okPost_trivial _) ?_
            intro i4 _
            by_cases h4 : (i4 != 0#usize) = true
            · simp only [h4, ↓reduceIte]
              exact okPost_ok hlen
            · simp only [h4, Bool.false_eq_true, ↓reduceIte]
              refine okPost_bind (okPost_trivial _) ?_
              intro i5 _
              refine okPost_bind (okPost_trivial _) ?_
              intro i6 _
              refine okPost_bind (okPost_trivial _) ?_
              intro i7 _
              exact step i7 st
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]
            refine okPost_bind (okPost_trivial _) ?_
            intro i5 _
            refine okPost_bind (okPost_trivial _) ?_
            intro i6 _
            refine okPost_bind (okPost_trivial _) ?_
            intro i7 _
            exact step i7 st
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact okPost_ok hlen
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok hlen

/-- `prepare_motion` changes nothing but the scratch phase table, and keeps its length. -/
theorem prepare_motion_frame (self : scene.Scene) (stamp : walker.Stamp) (steps : Slice Std.I32) :
    OkPost (scene.Scene.prepare_motion self stamp steps) (fun p =>
      ∃ v : alloc.vec.Vec Std.I32, v.val.length = self.next_phases.val.length ∧
        p.2 = { self with next_phases := v }) := by
  unfold scene.Scene.prepare_motion
  refine okPost_bind (okPost_trivial _) ?_
  intro r _
  cases r with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok]
    exact okPost_ok ⟨self.next_phases, rfl, rfl⟩
  | Ok val =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    split
    · exact okPost_ok ⟨self.next_phases, rfl, rfl⟩
    · split
      · exact okPost_ok ⟨self.next_phases, rfl, rfl⟩
      · split
        · exact okPost_ok ⟨self.next_phases, rfl, rfl⟩
        · split
          · exact okPost_ok ⟨self.next_phases, rfl, rfl⟩
          · refine okPost_bind (P := fun p : alloc.vec.Vec Std.I32 ×
              (core.result.Result Unit topology.Error) => p.1.val.length =
                self.next_phases.val.length)
              (prepare_motion_loop0_len self.phases self.next_phases self.holds steps
                (core.result.Result.Ok ()) 0#usize) ?_
            rintro ⟨v, status⟩ hv
            dsimp only at hv
            cases status with
            | Err x =>
              simp
              simp only [Std.bind_ok,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.from, bind_tc_ok]
              exact okPost_ok ⟨v, hv, rfl⟩
            | Ok u =>
              cases u
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
                exact okPost_ok ⟨v, hv, rfl⟩
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
                  exact okPost_ok ⟨v, hv, rfl⟩
                | Ok u2 =>
                  cases u2
                  simp
                  exact okPost_ok ⟨v, hv, rfl⟩

end Labyrinth
