module
public import LabyrinthCore.SceneDoorwayCells

/-! A doorway reads only the phases of the transforms it holds, part 3: the world positions of the
end poses, and the doorway itself. Every successful doorway records, in its hold set, every
transform its computation reads; so a second phase table that agrees with the first on the hold set
gives the same doorway. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core

namespace Labyrinth

theorem world_polar_congr (L : scene.Layout) (circle : Std.Usize) (radius angle : Std.I32)
    (p p' : Slice Std.I32)
    (H : ∀ c band, L.circles.val[circle.val]? = some c → IsTwisting c →
      L.bands.val[circle.val]? = some band →
      polar.Circle.offset_at_valid c radius band p = polar.Circle.offset_at_valid c radius band p') :
    scene.Layout.world L (walker.LocalPose.Polar circle radius angle) p =
      scene.Layout.world L (walker.LocalPose.Polar circle radius angle) p' := by
  unfold scene.Layout.world
  apply bind_congr_ok; intro c hc
  apply bind_congr_ok; intro mm hmm
  simp only [polar.Circle.mode, ok.injEq] at hmm
  subst hmm
  cases hmode : c.spec.mode with
  | Spinning => rfl
  | Twisting a m =>
    have : (do
        let i ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.I32) L.bands circle
        polar.Circle.offset_at_valid c radius i p : Result Std.I32) =
      (do
        let i ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.I32) L.bands circle
        polar.Circle.offset_at_valid c radius i p' : Result Std.I32) :=
      bind_congr_ok (fun band hb => H c band (vec_index_some hc) ⟨a, m, hmode⟩ (vec_index_some hb))
    simp only [this]

/-- Where a polar local pose comes from: a sector's centre line, a centre, or a transition cell's
band edge. -/
def PolarSource (L : scene.Layout) (cell : Nat) (circle : Std.Usize) (radius : Std.I32) : Prop :=
  (∃ ring sector c, L.cells.val[cell]? = some (scene.Cell.Sector circle ring sector) ∧
    L.circles.val[circle.val]? = some c ∧ ring.val < c.spec.sectors.val.length ∧
    radius.val = ringRadius c ring.val) ∨
  (L.cells.val[cell]? = some (scene.Cell.Center circle) ∧ radius.val = 0) ∨
  (∃ portal pt c band, L.cells.val[cell]? = some (scene.Cell.Transition portal) ∧
    L.portals.val[portal.val]? = some pt ∧ pt.spec.circle = circle ∧
    L.circles.val[circle.val]? = some c ∧ L.bands.val[circle.val]? = some band ∧
    radius.val = c.outer.val + band.val)

theorem local_pose_post (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize) :
    OkPost (scene.Layout.local_pose L cell) (fun loc => ∀ circle radius angle,
      loc = walker.LocalPose.Polar circle radius angle → PolarSource L cell.val circle radius) := by
  unfold scene.Layout.local_pose
  refine okPost_bind_eq (okPost_trivial _) ?_
  intro cl hcl _
  have hcls := vec_index_some hcl
  cases cl with
  | Grid a b d =>
    refine okPost_bind (okPost_trivial _) (fun _ _ => okPost_ok ?_)
    intro circle radius angle h; cases h
  | Center x =>
    refine okPost_ok ?_
    intro circle radius angle h
    cases h
    exact Or.inr (Or.inl ⟨hcls, rfl⟩)
  | Sector x r s =>
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro c1 hc1 _
    have hc1s := vec_index_some hc1
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro i hi _
    refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
    refine okPost_bind (okPost_trivial _) (fun _ _ => okPost_ok ?_)
    intro circle radius angle h
    cases h
    have hr := sector_ring_lt hL hcls hc1s
    exact Or.inl ⟨r, s, c1, hcls, hc1s, hr, (radius_ok_val (circle_ok_of hL hc1s) hr hi).1⟩
  | Transition pr =>
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro pt hpt _
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro c1 hc1 _
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro band hband _
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro i1 hi1 _
    refine okPost_bind (okPost_trivial _) (fun _ _ => okPost_ok ?_)
    intro circle radius angle h
    cases h
    exact Or.inr (Or.inr ⟨pr, pt, c1, band, hcls, vec_index_some hpt, rfl, vec_index_some hc1,
      vec_index_some hband, i32_add_ok hi1⟩)

theorem band_nonneg {L : scene.Layout} (hL : LayoutGeom L) {i : Nat} {band : Std.I32}
    (hb : L.bands.val[i]? = some band) : 0 ≤ band.val := by
  obtain ⟨hi, hx⟩ := getElem_of_some hb
  have hi2 : i < L.circles.val.length := by rw [← hL.bands_len]; exact hi
  have := (hL.bands i hi hi2).1
  rw [hx] at this
  exact this

/-- The world position of a cell's frame pose agrees on two tables that agree on the cell's reads,
whatever table the pose was framed with. -/
theorem world_frame_congr (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize)
    (p p' q : Slice Std.I32) (h : CellAgree L cell.val p p') :
    OkPost (scene.Layout.frame_pose L cell q) (fun pose =>
      scene.Layout.world L pose p = scene.Layout.world L pose p') := by
  -- the world position of a polar pose with a known source
  have hpolar : ∀ circle radius angle, PolarSource L cell.val circle radius →
      scene.Layout.world L (walker.LocalPose.Polar circle radius angle) p =
        scene.Layout.world L (walker.LocalPose.Polar circle radius angle) p' := by
    intro circle radius angle hsrc
    apply world_polar_congr
    intro c band hc htw hb
    have hok := circle_ok_of hL hc
    rcases hsrc with ⟨ring, sector, c', hcl, hc', hr, hrad⟩ | ⟨hcl, hrad⟩ |
      ⟨portal, pt, c', band', hcl, hpt, hcirc, hc', hb', hrad⟩
    · rw [hc] at hc'; cases hc'
      exact offset_at_valid_sector c hok ring.val hr radius band hrad p p'
        (h _ (Or.inl ⟨circle, ring, sector, c, hcl, hc, hr, Or.inl rfl⟩))
        (fun h1 => h _ (Or.inl ⟨circle, ring, sector, c, hcl, hc, hr, Or.inr ⟨htw, h1, rfl⟩⟩))
    · exact offset_at_valid_center c hok radius band hrad p p'
        (h _ (Or.inr (Or.inl ⟨circle, c, hcl, hc, htw, rfl⟩)))
    · rw [hc] at hc'; cases hc'
      rw [hb] at hb'; cases hb'
      subst hcirc
      exact offset_at_valid_transition c hok radius band (band_nonneg hL hb) hrad p p'
        (h _ (Or.inr (Or.inr ⟨portal, pt, c, hcl, hpt, hc, htw, rfl⟩)))
  have hcart : ∀ pt, scene.Layout.world L (walker.LocalPose.Cartesian pt) p =
      scene.Layout.world L (walker.LocalPose.Cartesian pt) p' := fun _ => rfl
  unfold scene.Layout.frame_pose
  refine okPost_bind (local_pose_post L hL cell) ?_
  intro loc hloc
  have hlocw : scene.Layout.world L loc p = scene.Layout.world L loc p' := by
    cases loc with
    | Cartesian pt => exact hcart pt
    | Polar circle radius angle => exact hpolar circle radius angle (hloc _ _ _ rfl)
  refine okPost_bind_eq (okPost_trivial _) ?_
  intro cl hcl _
  have hcls := vec_index_some hcl
  cases cl with
  | Sector circle ring sector =>
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro c1 hc1 _
    have hc1s := vec_index_some hc1
    refine okPost_bind_eq (okPost_trivial _) ?_
    intro mm hmm _
    simp only [polar.Circle.mode, ok.injEq] at hmm
    subst hmm
    cases hmode : c1.spec.mode with
    | Spinning =>
      cases loc with
      | Cartesian pt => exact okPost_ok (hcart pt)
      | Polar k r a =>
        refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
        refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
        refine okPost_bind (okPost_trivial _) (fun _ _ => okPost_ok ?_)
        apply world_polar_congr
        intro c band hc ⟨a', m', htw⟩ _
        rw [hc1s] at hc; cases hc
        rw [hmode] at htw; cases htw
    | Twisting a m => exact okPost_ok hlocw
  | _ => exact okPost_ok hlocw

/-! ### The doorway -/

theorem world_frame_eq (L : scene.Layout) (hL : LayoutGeom L) (cell : Std.Usize)
    (p p' : Slice Std.I32) (h : CellAgree L cell.val p p') (pose : walker.LocalPose)
    (hf : scene.Layout.frame_pose L cell p' = ok pose) :
    scene.Layout.world L pose p = scene.Layout.world L pose p' :=
  world_frame_congr L hL cell p p' p' h pose hf

/-- Two phase tables that agree on both end cells' reads give the same doorway. -/
theorem doorway_congr (L : scene.Layout) (hL : LayoutGeom L) (e : topology.Edge)
    (p p' : Slice Std.I32) (hu : CellAgree L e.u.val p p') (hv : CellAgree L e.v.val p p') :
    scene.Layout.doorway L e p p = scene.Layout.doorway L e p' p' := by
  unfold scene.Layout.doorway
  simp only [cell_arc_congr L hL e.u p p' hu, cell_arc_congr L hL e.v p p' hv,
    cell_sweep_congr L hL e.u p p' hu, cell_sweep_congr L hL e.v p p' hv,
    frame_pose_congr L hL e.u p p' hu, frame_pose_congr L hL e.v p p' hv]
  repeat (first | (apply bind_congr_ok; intro _ _) | split | with_reducible rfl)
  all_goals simp (disch := assumption) only [world_frame_eq L hL e.u p p' hu,
    world_frame_eq L hL e.v p p' hv]

theorem from_residual_not_ok {T E : Type _} (x : core.result.Result Never E) :
    OkPost (core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
      (core.convert.FromSame E) x) (fun r => ∀ d, r ≠ core.result.Result.Ok d) := by
  cases x with
  | Ok n => cases n
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    exact okPost_bind (okPost_trivial _) (fun v _ => okPost_ok (fun d h => by cases h))

/-- A successful doorway records every transform its computation reads, in at most four slots. -/
theorem doorway_holds_reads (L : scene.Layout) (e : topology.Edge) (p q : Slice Std.I32) :
    OkPost (scene.Layout.doorway L e p q) (fun r => ∀ d, r = core.result.Result.Ok d →
      d.holds.count.val ≤ 4 ∧
      ∀ k, (CellReads L e.u.val k ∨ CellReads L e.v.val k) → HoldHas d.holds k) := by
  unfold scene.Layout.doorway
  dsimp only
  split
  · exact okPost_ok (fun d h => by cases h)
  split
  · exact okPost_ok (fun d h => by cases h)
  refine okPost_bind (okPost_trivial _) (fun b _ => ?_)
  split
  swap
  · exact okPost_ok (fun d h => by cases h)
  refine okPost_bind (okPost_trivial _) (fun r _ => ?_)
  refine okPost_bind (okPost_trivial _) (fun cf _ => ?_)
  split
  swap
  · exact okPost_mono (from_residual_not_ok _) (fun r hr d hd => absurd hd (hr d))
  refine okPost_bind_eq (okPost_trivial _) (fun h0 hh0 _ => ?_)
  simp only [walker.Holds.new, ok.injEq] at hh0
  subst hh0
  refine okPost_bind (layout_holds_has L e.u _ (by simp)) ?_
  rintro ⟨r1, holds1⟩ hr1
  refine okPost_bind_eq (okPost_trivial _) (fun cf1 hcf1 _ => ?_)
  cases r1 with
  | Err x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf1
    subst hcf1
    exact okPost_mono (from_residual_not_ok _) (fun r hr d hd => absurd hd (hr d))
  | Ok u1 =>
    cases u1
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf1
    subst hcf1
    obtain ⟨hc1, -, hk1⟩ := hr1 rfl
    refine okPost_bind (layout_holds_has L e.v holds1 hc1) ?_
    rintro ⟨r2, holds2⟩ hr2
    refine okPost_bind_eq (okPost_trivial _) (fun cf2 hcf2 _ => ?_)
    cases r2 with
    | Err x =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf2
      subst hcf2
      exact okPost_mono (from_residual_not_ok _) (fun r hr d hd => absurd hd (hr d))
    | Ok u2 =>
      cases u2
      simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf2
      subst hcf2
      obtain ⟨hc2, hkeep2, hk2⟩ := hr2 rfl
      have hfinal : holds2.count.val ≤ 4 ∧
          ∀ k, (CellReads L e.u.val k ∨ CellReads L e.v.val k) → HoldHas holds2 k :=
        ⟨hc2, fun k hk => hk.elim (fun h => hkeep2 k (hk1 k h)) (hk2 k)⟩
      repeat (first
        | exact okPost_ok (fun d hd => by cases hd; exact hfinal)
        | exact okPost_ok (fun d hd => by cases hd)
        | exact okPost_mono (from_residual_not_ok _) (fun r hr d hd => absurd hd (hr d))
        | refine okPost_bind (okPost_trivial _) (fun _ _ => ?_)
        | split)

/-- **A doorway reads only the phases at its holds.** If the doorway of `e` at the phase table `p`
exists, then at any table `p'` that agrees with `p` on every transform the doorway holds, the
doorway is the same. -/
theorem doorway_phase_local (L : scene.Layout) (hL : LayoutGeom L) (e : topology.Edge)
    (p p' : Slice Std.I32) (d : scene.Doorway)
    (hd : scene.Layout.doorway L e p p = ok (core.result.Result.Ok d))
    (hag : ∀ x ∈ d.holds.ids.val.take d.holds.count.val, p.val[x.val]? = p'.val[x.val]?) :
    scene.Layout.doorway L e p' p' = ok (core.result.Result.Ok d) := by
  obtain ⟨_, hreads⟩ := doorway_holds_reads L e p p _ hd d rfl
  have hall : ∀ k, (CellReads L e.u.val k ∨ CellReads L e.v.val k) → PhAgree p p' k := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := (holdHas_iff_mem d.holds k).mp (hreads k hk)
    exact hag x hx
  rw [← doorway_congr L hL e p p' (fun k hk => hall k (Or.inl hk)) (fun k hk => hall k (Or.inr hk))]
  exact hd

end Labyrinth
