module
public import LabyrinthCore.SceneShatterTick

/-! Safety (S5), part 1: `tick` as one theorem. Every path of `tick` keeps the reservation invariant
`ResInv`, and under it the whole function is total: the stamp rejections, the wall regression, the
frozen scene, the reanchoring tick, the clock overflow and the active path all return a value.
What `tick_active_spec` adds for the active path is its exact description. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- The active path of `tick`, as far as the reservation invariant needs it. -/
def TickActiveRes (self : scene.Scene) (wall : Std.U64)
    (res : core.result.Result walker.Stamp topology.Error × scene.Scene) : Prop :=
  ∃ (v z : Std.U64) (hold : alloc.vec.Vec Std.Usize) (cw : alloc.vec.Vec walker.Walker)
    (cp : alloc.vec.Vec shatter.Patch),
    v.val = self.stamp.revision.val + 1 ∧ z.val = self.clock.val + (wall.val - self.wall.val) ∧
    ResInvL cw.val hold.val ∧
    res = (.Ok (bumped self v),
      { self with holds := hold, walkers := cw, patches := cp, stamp := bumped self v,
                  clock := z, wall := wall })

/-- `tick`, path by path. -/
def TickOutcome (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (res : core.result.Result walker.Stamp topology.Error × scene.Scene) : Prop :=
  (¬ StampAccepts self stamp ∧ StampRejects self stamp res) ∨
  (StampAccepts self stamp ∧
    ((wall.val < self.wall.val ∧ res = (.Err topology.Error.InvalidTransition, self)) ∨
     (self.wall.val ≤ wall.val ∧
      ((∃ v : Std.U64, v.val = self.stamp.revision.val + 1 ∧
          (self.suspended = true ∨ self.inactive = true ∨ self.pending ≠ none) ∧
          res = (.Ok (bumped self v), { self with stamp := bumped self v, wall := wall })) ∨
       (∃ v : Std.U64, v.val = self.stamp.revision.val + 1 ∧
          self.suspended = false ∧ self.inactive = false ∧ self.pending = none ∧
          self.reanchor = true ∧
          res = (.Ok (bumped self v),
            { self with stamp := bumped self v, wall := wall, reanchor := false })) ∨
       (self.suspended = false ∧ self.inactive = false ∧ self.pending = none ∧
          self.reanchor = false ∧
          ((U64.max < self.clock.val + (wall.val - self.wall.val) ∧
              res = (.Err topology.Error.Overflow, self)) ∨
           (self.clock.val + (wall.val - self.wall.val) ≤ U64.max ∧
              TickActiveRes self wall res)))))))

theorem tickOutcome_resinv {self : scene.Scene} {stamp : walker.Stamp} {wall : Std.U64}
    {res : core.result.Result walker.Stamp topology.Error × scene.Scene}
    (hinv : ResInv self) (h : TickOutcome self stamp wall res) : ResInv res.2 := by
  rcases h with ⟨hn, hf⟩ | ⟨hacc, h⟩
  · rw [stampFail_scene hn hf]; exact hinv
  · rcases h with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]; exact hinv
    · rcases h with ⟨v, _, _, h⟩ | ⟨v, _, _, _, _, _, h⟩ | ⟨_, _, _, _, h | ⟨_, ⟨v, z, hold, cw, cp, _, _, hr, h⟩⟩⟩
      · rw [h]; exact hinv
      · rw [h]; exact hinv
      · rw [h.2]; exact hinv
      · rw [h]; exact hr

/-- `tick` is total under the reservation invariant, and every path keeps it. -/
theorem tick_spec (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (hinv : ResInv self) :
    scene.Scene.tick self stamp wall ⦃ res => TickOutcome self stamp wall res ⦄ := by
  by_cases hacc : StampAccepts self stamp
  · by_cases hw : wall.val < self.wall.val
    · rw [tick_wall_regressed self stamp wall hacc hw, spec_ok]
      exact Or.inr ⟨hacc, Or.inl ⟨hw, rfl⟩⟩
    · have hw' : self.wall.val ≤ wall.val := by omega
      by_cases hfz : self.suspended = true ∨ self.inactive = true ∨ self.pending.isSome = true
      · obtain ⟨v, hv, he⟩ := tick_frozen self stamp wall hacc hw' hfz
        rw [he, spec_ok]
        refine Or.inr ⟨hacc, Or.inr ⟨hw', Or.inl ⟨v, hv, ?_, rfl⟩⟩⟩
        rcases hfz with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · refine Or.inr (Or.inr ?_)
          intro hn; rw [hn] at h; simp at h
      · have hs : self.suspended = false := by
          cases h : self.suspended <;> simp_all
        have hi : self.inactive = false := by
          cases h : self.inactive <;> simp_all
        have hp : self.pending = none := by
          cases h : self.pending <;> simp_all
        by_cases hr : self.reanchor = true
        · obtain ⟨v, hv, he⟩ := tick_reanchored self stamp wall hacc hw' hs hi hp hr
          rw [he, spec_ok]
          exact Or.inr ⟨hacc, Or.inr ⟨hw', Or.inr (Or.inl ⟨v, hv, hs, hi, hp, hr, rfl⟩)⟩⟩
        · have hr' : self.reanchor = false := by simpa using hr
          by_cases hov : U64.max < self.clock.val + (wall.val - self.wall.val)
          · rw [tick_clock_overflow self stamp wall hacc hw' hs hi hp hr' hov, spec_ok]
            exact Or.inr ⟨hacc, Or.inr ⟨hw', Or.inr (Or.inr ⟨hs, hi, hp, hr', Or.inl ⟨hov, rfl⟩⟩)⟩⟩
          · have hnov : self.clock.val + (wall.val - self.wall.val) ≤ U64.max := by omega
            refine spec_mono (tick_active_spec self stamp wall hacc hw' hs hi hp hr' hnov hinv) ?_
            rintro res ⟨v, z, hold, walk, cw, cp, hv, hz, _, _, _, hcw, _, _, _, _, hres⟩
            exact Or.inr ⟨hacc, Or.inr ⟨hw', Or.inr (Or.inr ⟨hs, hi, hp, hr', Or.inr ⟨hnov,
              v, z, hold, cw, cp, hv, hz, hcw, hres⟩⟩)⟩⟩
  · by_cases h1 : stamp.epoch = self.stamp.epoch
    · by_cases h2 : stamp.revision = self.stamp.revision
      · have h3 : self.stamp.revision.val = U64.max := by
          by_contra h3
          exact hacc ⟨h1, h2, by have := self.stamp.revision.hBounds; scalar_tac⟩
        rw [tick_revision_overflow self stamp wall h1 h2 h3, spec_ok]
        exact Or.inl ⟨hacc, fun h => absurd h1 h, fun _ h => absurd h2 h, fun _ _ _ => rfl⟩
      · rw [tick_stale_revision self stamp wall h1 h2, spec_ok]
        exact Or.inl ⟨hacc, fun h => absurd h1 h, fun _ _ => rfl, fun _ h => absurd h h2⟩
    · rw [tick_stale_epoch self stamp wall h1, spec_ok]
      exact Or.inl ⟨hacc, fun _ => rfl, fun h => absurd h h1, fun h => absurd h h1⟩

/-- Every path of `tick` preserves `ResInv`, and `tick` does not fail. -/
theorem tick_resinv (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (hinv : ResInv self) :
    scene.Scene.tick self stamp wall ⦃ res => ResInv res.2 ⦄ :=
  spec_mono (tick_spec self stamp wall hinv) (fun _ h => tickOutcome_resinv hinv h)

end Labyrinth
