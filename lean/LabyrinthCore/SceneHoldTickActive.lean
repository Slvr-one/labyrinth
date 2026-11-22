module
public import LabyrinthCore.SceneHoldPatches

/-! The hold law, part 4: `tick` keeps the scene invariant and the hold law on every path.

`tick_active_exact` is `tick_active_spec` with what the walker loop also guarantees: every crossing
after it is a crossing from before it, and an exact count stays exact. The two patch sweeps that
follow rewrite only walkers that are not crossing. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

/-- The walker after `tick`'s two patch sweeps. -/
noncomputable def tickSweep (z : Std.U64) (walk : List walker.Walker) (ps : List shatter.Patch)
    (o : walker.Walker) : walker.Walker :=
  reformW z (ps.map (drainP walk)) ps.length (drainW walk ps ps.length o)

/-- What the invariant needs of `tick`'s active path. -/
def TickActiveFacts (self : scene.Scene) (wall : Std.U64)
    (res : core.result.Result walker.Stamp topology.Error × scene.Scene) : Prop :=
  ∃ (v z : Std.U64) (hold : alloc.vec.Vec Std.Usize) (walk cw : alloc.vec.Vec walker.Walker)
    (cp : alloc.vec.Vec shatter.Patch),
    ResInvL walk.val hold.val ∧
    (HoldEqL self.walkers.val self.holds.val → HoldEqL walk.val hold.val) ∧
    CrossSub self.walkers.val walk.val ∧
    cp.val = self.patches.val.map (fun p => reformP z (drainP walk.val p)) ∧
    cw.val = walk.val.map (tickSweep z walk.val self.patches.val) ∧
    res = (.Ok (bumped self v),
      { self with holds := hold, walkers := cw, patches := cp, stamp := bumped self v,
                  clock := z, wall := wall })

/-- **`tick` on its active path**, with the crossings it keeps and the exact count. -/
theorem tick_active_exact (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (hacc : StampAccepts self stamp) (hw : self.wall.val ≤ wall.val)
    (hs : self.suspended = false) (hi : self.inactive = false) (hp : self.pending = none)
    (hr : self.reanchor = false)
    (hnov : self.clock.val + (wall.val - self.wall.val) ≤ U64.max) (hinv : ResInv self) :
    scene.Scene.tick self stamp wall ⦃ res => TickActiveFacts self wall res ⦄ := by
  obtain ⟨h1, h2, h3⟩ := hacc
  unfold scene.Scene.tick
  obtain ⟨v, hv, he⟩ := check_stamp_ok self stamp h1 h2 h3
  rw [he]
  have hnw : ¬ wall < self.wall := by simpa using hw
  have hsub := Std.U64.sub_spec (x := wall) (y := self.wall) (by scalar_tac)
  obtain ⟨d, hd, hdv⟩ := spec_eq_ok hsub
  simp [core.result.Result.Insts.CoreOpsTry.branch, hnw, hs, hi, hp, hr,
    core.option.Option.is_some, hd]
  rcases u64_checked_add self.clock d with ⟨hle, z, hz, hzv⟩ | ⟨hgt, hn⟩
  · simp only [lift, hz, Std.bind_ok, core.option.Option.ok_or]
    apply spec_bind (tick_loop0_exact d self.holds self.walkers 0#usize (by simp) hinv)
    rintro ⟨hold, walk⟩ ⟨hinv1, heq1, hsub1, hl1, hl2⟩
    apply spec_bind (drain_patches_spec _ (fun wk hwk c hc => (hinv1.1 wk hwk c hc).2.2))
    rintro self1 ⟨cwd, cpd, rfl, hlw, hlp, hdp, hdw⟩
    apply spec_bind (tick_loop1_spec z _)
    rintro ⟨l, t, w, v2, v3, v4, v5, v6, v7, v8, s, i, i1, b1, b2, b3, i2, o1, i3⟩
      ⟨cw, cp, hy, hlw2, hlp2, hdp2, hdw2⟩
    simp only [sceneFields, Prod.mk.injEq] at hy
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl⟩ := hy
    refine (spec_ok _).mpr ?_
    dsimp only at hlw hlp hdp hdw hlw2 hlp2 hdp2 hdw2 hinv1 hl1 hl2 heq1 hsub1
    have hcpd : cpd.val = self.patches.val.map (drainP walk.val) :=
      list_eq_map _ _ _ hlp (fun q hq => hdp q hq)
    refine ⟨v, i, v6, walk, v7, v8, hinv1, heq1, hsub1, ?_, ?_, ?_⟩
    · refine list_eq_map _ _ _ (by omega) (fun q hq => ?_)
      obtain ⟨pq, hpq, hc⟩ := hdp q hq
      obtain ⟨pq', hpq', hc'⟩ := hdp2 q (by omega)
      rw [hc] at hpq'; cases hpq'
      exact ⟨pq, hpq, hc'⟩
    · refine list_eq_map _ _ _ (by omega) (fun j hj => ?_)
      obtain ⟨o', ho', hco'⟩ := hdw j hj
      obtain ⟨o'', ho'', hco''⟩ := hdw2 j (by omega)
      rw [hco'] at ho''; cases ho''
      refine ⟨o', ho', ?_⟩
      rw [hco'', hcpd, List.length_map]
      rfl
    · simp only [bumped, hs, hi, hp, hr]
  · omega

/-! ### The sweeps after the walker loop -/

theorem tickSweep_relaxed (z : Std.U64) (walk : List walker.Walker) (ps : List shatter.Patch) :
    RelaxedList walk (walk.map (tickSweep z walk ps)) := by
  refine ⟨by simp, fun i hi => ?_⟩
  refine ⟨walk[i], tickSweep z walk ps walk[i], List.getElem?_eq_getElem hi, by simp [hi], ?_⟩
  unfold tickSweep
  rcases reformW_eq_or z (ps.map (drainP walk)) ps.length (drainW walk ps ps.length walk[i]) with
    e | e
  · rw [e]; exact drainW_eq_or walk ps ps.length walk[i]
  · exact Or.inr e

theorem tickSweep_same (z : Std.U64) (walk : List walker.Walker) (ps : List shatter.Patch)
    (hcs : CrossAtSource walk) (hcl : PatchClearL walk ps) :
    SameCrossings walk (walk.map (tickSweep z walk ps)) := by
  refine sameCrossings_map walk _ (fun o ho => ?_)
  unfold tickSweep
  by_cases hx : ∃ c, o.state = walker.WalkerState.Crossing c
  · obtain ⟨c, hc⟩ := hx
    rw [drainW_crossing walk ps ps.length hcs o ho c hc]
    have hcl' : PatchClearL walk (ps.map (drainP walk)) := drain_clear hcl (crossSub_refl _)
    rcases reformW_same z walk (ps.map (drainP walk)) ps.length hcs hcl' o ho with e | ⟨hn, _⟩
    · exact Or.inl e
    · exact absurd hc (hn c)
  · have hd : ∀ c, (drainW walk ps ps.length o).state ≠ walker.WalkerState.Crossing c := by
      rcases drainW_eq_or walk ps ps.length o with e | e
      · rw [e]; exact fun c hc => hx ⟨c, hc⟩
      · exact e
    refine Or.inr ⟨fun c hc => hx ⟨c, hc⟩, ?_⟩
    rcases reformW_eq_or z (ps.map (drainP walk)) ps.length (drainW walk ps ps.length o) with e | e
    · rw [e]; exact hd
    · exact e

/-- `tick`, path by path, with the active path described by `TickActiveFacts`. -/
theorem tick_cases (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (hinv : ResInv self) :
    OkPost (scene.Scene.tick self stamp wall) (fun res =>
      res.2 = self ∨ (∃ st : walker.Stamp, res.2 = { self with stamp := st, wall := wall }) ∨
      (∃ st : walker.Stamp, res.2 = { self with stamp := st, wall := wall, reanchor := false }) ∨
      TickActiveFacts self wall res) := by
  intro res hres
  have hout := okPost_of_spec (tick_spec self stamp wall hinv) res hres
  rcases hout with ⟨hn, hf⟩ | ⟨hacc, h⟩
  · exact Or.inl (stampFail_scene hn hf)
  · rcases h with ⟨_, h⟩ | ⟨hw, h⟩
    · rw [h]; exact Or.inl rfl
    · rcases h with ⟨v, _, _, h⟩ | ⟨v, _, _, _, _, _, h⟩ | ⟨hs, hi, hp, hr, h | ⟨hnov, _⟩⟩
      · rw [h]; exact Or.inr (Or.inl ⟨_, rfl⟩)
      · rw [h]; exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
      · rw [h.2]; exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr
          (okPost_of_spec (tick_active_exact self stamp wall hacc hw hs hi hp hr hnov hinv) res
            hres)))

/-- **`tick` keeps the scene invariant**, whatever it returns. -/
theorem tick_inv (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64) (h : SceneInv self) :
    OkPost (scene.Scene.tick self stamp wall) (fun res => SceneInv res.2) := by
  obtain ⟨hs, hcap, hL, htr, hpr, hres, hcr, hroom⟩ := h
  intro res hres'
  have hR : ResInv res.2 := okPost_of_spec (tick_resinv self stamp wall hres) res hres'
  rcases tick_cases self stamp wall hres res hres' with e | ⟨st, e⟩ | ⟨st, e⟩ |
      ⟨v, z, hold, walk, cw, cp, _, _, hsub, hcp, hcw, e⟩
  · rw [e]; exact ⟨hs, hcap, hL, htr, hpr, hres, hcr, hroom⟩
  · rw [e]; exact ⟨hs, hcap, hL, htr, hpr, hres, hcr, hroom⟩
  · rw [e]; exact ⟨hs, hcap, hL, htr, hpr, hres, hcr, hroom⟩
  · rw [e] at hR ⊢
    refine ⟨hs, hcap, hL, htr, hpr, hR, ?_, ?_⟩
    · have hsub' : CrossSub self.walkers.val cw.val := by
        rw [hcw]; exact crossSub_trans hsub (relaxed_crossSub (tickSweep_relaxed _ _ _))
      exact crossHeld_transfer self _ hcr hL rfl hsub' (fun _ _ _ _ _ _ hpe => hpe)
        (fun _ _ _ _ _ _ => rfl)
    · intro p hp
      have hp' : p ∈ cp.val := hp
      rw [hcp] at hp'
      obtain ⟨pq, hpq, rfl⟩ := List.mem_map.mp hp'
      rw [reformP_cells, drainP_cells]
      exact hroom pq hpq

/-- **`tick` keeps the hold law**, whatever it returns. -/
theorem tick_holdLaw (self : scene.Scene) (stamp : walker.Stamp) (wall : Std.U64)
    (hres : ResInv self) (h : HoldLaw self) :
    OkPost (scene.Scene.tick self stamp wall) (fun res => HoldLaw res.2) := by
  intro res hres'
  rcases tick_cases self stamp wall hres res hres' with e | ⟨st, e⟩ | ⟨st, e⟩ |
      ⟨v, z, hold, walk, cw, cp, hinv1, heq1, hsub, hcp, hcw, e⟩
  · rw [e]; exact h
  · rw [e]; exact h
  · rw [e]; exact h
  · rw [e]
    have hcs : CrossAtSource walk.val := fun wk hwk c hc => (hinv1.1 wk hwk c hc).2.2
    have hcl : PatchClearL walk.val self.patches.val := patchClear_crossSub h.2 hsub
    have hsame := tickSweep_same z walk.val self.patches.val hcs hcl
    refine ⟨?_, ?_⟩
    · show HoldEqL cw.val hold.val
      rw [hcw]; exact holdEqL_same (heq1 h.1) hsame
    · show PatchClearL cw.val cp.val
      rw [hcp, hcw]
      have := reform_clear z (drain_clear hcl (crossSub_refl _)) (crossSub_of_same hsame)
      rwa [List.map_map] at this

end Labyrinth
