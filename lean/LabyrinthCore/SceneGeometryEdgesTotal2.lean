module
public import LabyrinthCore.SceneGeometryEdgesTotal

/-! Geometry totality, portal cells: `resolve_portal` and the portal loop of `Layout::new`
return when the grid lookups do, and the circles built by the first loop of `Layout::new` carry one
`ring_starts` entry per ring. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

/-! ### `resolve_portal` -/

theorem arcsOk_of_two (a b : polar.Arc) (ha : ArcOk a) (hb : ArcOk b) :
    ArcsOk (Array.make 4#usize [a, b, a, b]) := by
  intro i hi
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> simpa [Array.make]

theorem resolve_portal_loop_total (i : Std.Usize) (a : polar.Arc) (portals : Slice scene.Portal)
    (grid_cell : Std.Usize) (conflict : Bool) (j : Std.Usize) (ha : ArcOk a)
    (hp : ∀ p ∈ portals.val, ArcOk p.spec.mouth) :
    scene.resolve_portal_loop i a portals grid_cell conflict j ⦃ _ => True ⦄ := by
  unfold scene.resolve_portal_loop
  apply loop.spec_decr_nat
    (fun st : Bool × Std.Usize => portals.val.length - st.2.val)
    (fun _ => True) (fun _ => True) _ (conflict, j) _ trivial
  rintro ⟨cf, jj⟩ _
  unfold scene.resolve_portal_loop.body
  by_cases hlt : jj < Slice.len portals
  · simp only [hlt, ↓reduceIte]
    cases cf with
    | true => simp only [↓reduceIte, spec_ok]
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hjj : jj.val < portals.val.length := by scalar_tac
    step as ⟨previous, hprev⟩
    have hpm : ArcOk previous.spec.mouth := hp previous (by rw [hprev]; exact List.getElem_mem hjj)
    have harcs := arcsOk_of_two previous.spec.mouth a hpm ha
    by_cases h1 : previous.spec.circle = i
    · simp only [h1, ↓reduceIte]
      by_cases h2 : previous.grid_cell = grid_cell
      · simp only [h2, ↓reduceIte, Std.bind_ok]
        step as ⟨j1, hj1⟩
        scalar_tac
      · simp only [h2, ↓reduceIte]
        step as ⟨r, hr⟩
        step as ⟨b, hb⟩
        step as ⟨j1, hj1⟩
        scalar_tac
    · simp only [h1, ↓reduceIte, Std.bind_ok]
      step as ⟨j1, hj1⟩
      scalar_tac
  · simp only [hlt, ↓reduceIte, spec_ok]

/-- `resolve_portal` returns whenever the portal's grid cell lookup does and the arcs involved are
validated; an error is `InvalidGeometry`. -/
theorem resolve_portal_total (spec : polar.PortalSpec) (cell_grid : grid.Grid)
    (portals : Slice scene.Portal) (tc : Std.Usize) (hmouth : ArcOk spec.mouth)
    (hp : ∀ p ∈ portals.val, ArcOk p.spec.mouth)
    (hcell : ∃ o, grid.Grid.cell cell_grid spec.column spec.row = ok o) :
    scene.resolve_portal spec cell_grid portals tc ⦃ r =>
      (∀ p, r = .Ok p → p.spec = spec) ∧ (∀ e, r = .Err e → e = topology.Error.InvalidGeometry) ⦄ := by
  unfold scene.resolve_portal
  obtain ⟨o, ho⟩ := hcell
  rw [ho, Std.bind_ok]
  cases o with
  | none =>
    simp only [core.option.Option.ok_or, Std.bind_ok, branch_err_eq]
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.from, Std.bind_ok, bind_tc_ok, spec_ok]
    simp
  | some v =>
    simp only [core.option.Option.ok_or, Std.bind_ok, branch_ok_eq]
    refine spec_bind (resolve_portal_loop_total spec.circle spec.mouth portals v false 0#usize
      hmouth hp) ?_
    intro conflict _
    by_cases hc : conflict = true
    · simp only [hc, ↓reduceIte, spec_ok]
      simp
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, spec_ok]
      simp

/-! ### The portal loop -/

/-- `Layout::new`'s portal loop returns when the grid lookups do and the cell vector has room for one
cell per remaining portal. It keeps one portal per spec, adds one non-grid cell per portal, and every
portal built carries one of the portal specs. -/
theorem layout_new_loop5_total (ps : Slice polar.PortalSpec) (cell_grid : grid.Grid)
    (status : core.result.Result Unit topology.Error) (cells : alloc.vec.Vec scene.Cell)
    (portals : alloc.vec.Vec scene.Portal) (i : Std.Usize) (specs : List polar.PolarSpec)
    (hps : ∀ j (h : j < ps.val.length), PortalSpecOk specs.length (ps.val[j]'h))
    (hinv : PortalLoopInv specs ps status cells portals i.val)
    (hcell : ∀ c r, ∃ o, grid.Grid.cell cell_grid c r = ok o)
    (hcap : cells.val.length + (ps.val.length - i.val) ≤ Std.Usize.max) :
    scene.Layout.new_loop5 ps cell_grid status cells portals i ⦃ r =>
      r.2.2.val.length + cells.val.length ≤ r.2.1.val.length + portals.val.length ∧
      (∀ p ∈ r.2.2.val, ∃ j, ∃ h : j < ps.val.length, p.spec = ps.val[j]'h) ∧
      (∃ k, r.2.1.val = cells.val ++ k ∧ GridFree k) ⦄ := by
  unfold scene.Layout.new_loop5
  obtain ⟨hst0, hspec0, _⟩ := hinv
  apply loop.spec_decr_nat
    (fun st : core.result.Result Unit topology.Error × alloc.vec.Vec scene.Cell ×
      alloc.vec.Vec scene.Portal × Std.Usize => ps.val.length - st.2.2.2.val)
    (fun st : core.result.Result Unit topology.Error × alloc.vec.Vec scene.Cell ×
      alloc.vec.Vec scene.Portal × Std.Usize =>
      (st.1 = .Ok () → st.2.2.1.val.length = st.2.2.2.val) ∧
      (∀ j (h : j < st.2.2.1.val.length), ∃ hj : j < ps.val.length,
        (st.2.2.1.val[j]'h).spec = ps.val[j]'hj) ∧
      st.2.2.1.val.length + cells.val.length ≤ st.2.1.val.length + portals.val.length ∧
      st.2.1.val.length + (ps.val.length - st.2.2.2.val) ≤ Std.Usize.max ∧
      ∃ k, st.2.1.val = cells.val ++ k ∧ GridFree k)
    _
  · rintro ⟨st, cs, pt, kk⟩ ⟨hst, hspec, hcnt, hcp, k, hk, hfree⟩
    simp only at hst hspec hcnt hcp hk
    unfold scene.Layout.new_loop5.body
    by_cases hlt : kk < Slice.len ps
    · simp only [hlt, ↓reduceIte]
      cases st with
      | Err e =>
        simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte, spec_ok]
        refine ⟨hcnt, fun p hp => ?_, k, hk, hfree⟩
        obtain ⟨j, hj⟩ := List.getElem_of_mem hp
        obtain ⟨hj1, hj2⟩ := hj
        obtain ⟨hjs, he⟩ := hspec j hj1
        exact ⟨j, hjs, by rw [← hj2]; exact he⟩
      | Ok u =>
      simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte]
      have hlen := hst (by cases u; rfl)
      have hkk : kk.val < ps.val.length := by scalar_tac
      step as ⟨p, hp⟩
      have hpp : p = ps.val[kk.val]'hkk := hp
      have hmouth : ArcOk p.mouth := by rw [hpp]; exact (hps kk.val hkk).2.1
      have hprev : ∀ q ∈ (alloc.vec.Vec.deref pt).val, ArcOk q.spec.mouth := by
        intro q hq
        rw [vec_deref_val] at hq
        obtain ⟨j, hj1, hj2⟩ := List.getElem_of_mem hq
        obtain ⟨hjs, he⟩ := hspec j hj1
        rw [← hj2, he]; exact (hps j hjs).2.1
      refine spec_bind (resolve_portal_total p cell_grid (alloc.vec.Vec.deref pt)
        (alloc.vec.Vec.len cs) hmouth hprev
        (hcell _ _)) ?_
      intro r hr
      cases r with
      | Err e =>
        simp only [Std.bind_ok]
        step as ⟨k1, hk1⟩
        have hk1v : k1.val = kk.val + 1 := hk1
        refine ⟨?_, hspec, hcnt, ?_, ⟨k, hk, hfree⟩, ?_⟩
        · intro h; cases h
        · omega
        · omega
      | Ok portal =>
        simp only [Std.bind_ok]
        have hptl : pt.val.length < Std.Usize.max := by
          have := pt.property; scalar_tac
        have hcsl : cs.val.length < Std.Usize.max := by omega
        step as ⟨cs2, hcs2⟩
        step as ⟨pt2, hpt2⟩
        step as ⟨k1, hk1⟩
        have hk1v : k1.val = kk.val + 1 := hk1
        refine ⟨?_, ?_, ?_, ?_, ⟨k ++ [scene.Cell.Transition kk], ?_, ?_⟩, ?_⟩
        · intro _; rw [hpt2]; simp [hlen, hk1v]
        · intro j hj
          rw [hpt2] at hj
          by_cases hjl : j < pt.val.length
          · obtain ⟨hj', he⟩ := hspec j hjl
            refine ⟨hj', ?_⟩
            simp only [hpt2, List.getElem_append_left hjl]; exact he
          · have hj2 : j = pt.val.length := by simp at hj; omega
            subst hj2
            refine ⟨by omega, ?_⟩
            simp only [hpt2, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
              List.getElem_cons_zero]
            rw [(hr.1 portal rfl), hpp]; simp [hlen]
        · rw [hpt2, hcs2]; simp; omega
        · rw [hcs2]; simp; omega
        · rw [hcs2, hk]; simp
        · exact hfree.append (GridFree.singleton _ (by intro a b d h; cases h))
        · omega
    · simp only [hlt, ↓reduceIte, spec_ok]
      refine ⟨hcnt, fun p hp => ?_, k, hk, hfree⟩
      obtain ⟨j, hj⟩ := List.getElem_of_mem hp
      obtain ⟨hj1, hj2⟩ := hj
      obtain ⟨hjs, he⟩ := hspec j hj1
      exact ⟨j, hjs, by rw [← hj2]; exact he⟩
  · refine ⟨hst0, hspec0, by dsimp only; omega, hcap, [], by simp, by intro c hc; simp at hc⟩

/-- The ring loop of `Circle::new` pushes one start per ring while the status stays `Ok`. -/
theorem circle_new_loop0_rs (cr rw : Std.I32) (v : alloc.vec.Vec Std.Usize) (margin : Std.I32)
    (rs : alloc.vec.Vec Std.Usize) (next : Std.Usize) (status : core.result.Result Unit topology.Error)
    (ring : Std.Usize)
    (hinv : status = .Ok () → rs.val.length = ring.val ∧ ring.val ≤ v.val.length) :
    OkPost (polar.Circle.new_loop0 cr rw v margin rs next status ring)
      (fun r => r.2 = .Ok () → r.1.val.length = v.val.length) := by
  unfold polar.Circle.new_loop0
  refine okPost_loop
    (fun st : alloc.vec.Vec Std.Usize × Std.Usize × core.result.Result Unit topology.Error ×
      Std.Usize => st.2.2.1 = .Ok () → st.1.val.length = st.2.2.2.val ∧ st.2.2.2.val ≤ v.val.length)
    _ _ ?_ (rs, next, status, ring) hinv
  rintro ⟨rs, nx, st, rg⟩ hst
  unfold polar.Circle.new_loop0.body
  by_cases hlt : rg < alloc.vec.Vec.len v
  swap
  · simp only [hlt, ↓reduceIte]
    refine okPost_ok (fun hs => ?_)
    have := hst hs
    have : ¬ rg.val < v.val.length := by simpa [alloc.vec.Vec.len] using hlt
    scalar_tac
  simp only [hlt, ↓reduceIte]
  cases st with
  | Err e =>
    simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact okPost_ok (fun h => by cases h)
  | Ok u =>
    simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte, alloc.vec.Vec.index_slice_index]
    have hst' := hst (by cases u; rfl)
    dsimp only at hst'
    have hlt' : rg.val < v.val.length := by simpa [alloc.vec.Vec.len] using hlt
    refine okPost_spec (alloc.vec.Vec.index_usize_spec v rg hlt') ?_
    intro count hcount
    refine okPost_any (fun i3 => okPost_any (fun i4 => okPost_any (fun inner => ?_)))
    refine okPost_bind (P := fun t : alloc.vec.Vec Std.Usize × Std.Usize ×
        core.result.Result Unit topology.Error =>
        t.2.2 = .Ok () → t.1.val.length = rg.val + 1) ?_ ?_
    · by_cases hc2 : count < 2#usize
      · simp only [hc2, ↓reduceIte]; exact okPost_ok (fun h => by cases h)
      simp only [hc2, ↓reduceIte]
      refine okPost_any (fun i5 => ?_)
      refine okPost_any (fun i6 => ?_)
      by_cases hc3 : count > i6
      · simp only [hc3, ↓reduceIte]; exact okPost_ok (fun h => by cases h)
      simp only [hc3, ↓reduceIte]
      refine okPost_any (fun i7 => okPost_any (fun i8 => okPost_any (fun i9 => okPost_any
        (fun i10 => okPost_any (fun i11 => okPost_any (fun i12 => okPost_any (fun i13 =>
        okPost_any (fun i14 => okPost_any (fun i15 => ?_)))))))))
      by_cases hc4 : i11 < i15
      · simp only [hc4, ↓reduceIte]; exact okPost_ok (fun h => by cases h)
      simp only [hc4, ↓reduceIte]
      refine okPost_bind (vec_push_okPost rs nx) ?_
      intro rs2 hrs2
      refine okPost_any (fun o => ?_)
      cases o with
      | none => simp only [Std.bind_ok]; exact okPost_ok (fun h => by cases h)
      | some value =>
        simp only [Std.bind_ok]
        refine okPost_ok (fun _ => ?_)
        simp only [hrs2, List.length_append, List.length_singleton]
        have := (hst' ).1
        omega
    · rintro ⟨rs1, nx1, st1⟩ hP
      refine okPost_spec (Usize.add_spec (x := rg) (y := 1#usize) (by scalar_tac)) ?_
      intro rg1 hrg1
      refine okPost_ok (fun hs1 => ?_)
      have := hP hs1
      refine ⟨by simp only []; scalar_tac, by scalar_tac⟩

/-- A circle accepted by `Circle::new` has one ring start per ring. -/
theorem circle_new_ring_starts (spec : polar.PolarSpec) (cc ts : Std.Usize) (margin : Std.I32)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000) :
    OkPost (polar.Circle.new spec cc ts margin) (fun r => ∀ c, r = .Ok c →
      c.ring_starts.val.length = c.spec.sectors.val.length ∧ c.spec = spec) := by
  unfold polar.Circle.new
  refine okPost_spec (grid_point_validate_spec spec.center) ?_
  rintro r ⟨hr1, hr2⟩
  cases r with
  | Err e => simp only [branch_err_eq, Std.bind_ok]; exact okPost_residual e (fun c hc => by cases hc)
  | Ok u =>
  have hpt := hr1.mp (by cases u; rfl)
  simp only [branch_ok_eq, Std.bind_ok, alloc.vec.Vec.is_empty]
  by_cases he : alloc.vec.Vec.length spec.sectors = 0
  · simp only [he, decide_true, ↓reduceIte]; exact okPost_ok (fun c hc => by cases hc)
  simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte]
  by_cases hd : (alloc.vec.Vec.len spec.sectors != alloc.vec.Vec.len spec.directions) = true
  · simp only [hd, ↓reduceIte]; exact okPost_ok (fun c hc => by cases hc)
  have hd' : (alloc.vec.Vec.len spec.sectors != alloc.vec.Vec.len spec.directions) = false :=
    Bool.eq_false_iff.mpr hd
  simp only [hd', Bool.false_eq_true, ↓reduceIte]
  have hdl : spec.sectors.val.length = spec.directions.val.length := by
    simp at hd'; scalar_tac
  refine okPost_spec (I32.mul_spec (x := margin) (y := 4#i32) (by scalar_tac) (by scalar_tac)) ?_
  intro i2 hi2
  by_cases hc1 : spec.center_radius < i2
  · simp only [hc1, ↓reduceIte]; exact okPost_ok (fun c hc => by cases hc)
  simp only [hc1, ↓reduceIte]
  by_cases hc2 : spec.ring_width < i2
  · simp only [hc2, ↓reduceIte]; exact okPost_ok (fun c hc => by cases hc)
  simp only [hc2, ↓reduceIte]
  have hmax : core.num.I32.MAX.val = 2147483647 := rfl
  refine okPost_spec (IScalar.hcast_inBounds_spec .Usize core.num.I32.MAX
    (by rw [hmax]; constructor; omega; scalar_tac)) ?_
  intro i4 hi4
  by_cases hc3 : alloc.vec.Vec.len spec.sectors > i4
  · simp only [hc3, ↓reduceIte]; exact okPost_ok (fun c hc => by cases hc)
  simp only [hc3, ↓reduceIte]
  have hlen : spec.sectors.val.length ≤ 2147483647 := by scalar_tac
  refine okPost_spec (usize_hcast_i32_spec (alloc.vec.Vec.len spec.sectors) (by scalar_tac)) ?_
  intro rc hrc
  simp only [lift, Std.bind_ok]
  rcases i32_checked_mul_cases rc spec.ring_width with hn | ⟨val, hv, hvv⟩
  · simp only [hn, core.option.Option.ok_or, Std.bind_ok, branch_err_eq]
    exact okPost_residual _ (fun c hc => by cases hc)
  simp only [hv, core.option.Option.ok_or, Std.bind_ok, branch_ok_eq]
  rcases i32_checked_add_cases val spec.center_radius with ⟨hn, _⟩ | ⟨val1, hv1, hvv1⟩
  · simp only [hn, core.option.Option.ok_or, Std.bind_ok, branch_err_eq]
    exact okPost_residual _ (fun c hc => by cases hc)
  simp only [hv1, core.option.Option.ok_or, Std.bind_ok, branch_ok_eq]
  have hcl := coord_limit_val
  by_cases hc4 : val1 > grid.COORD_LIMIT
  · simp only [hc4, ↓reduceIte]; exact okPost_ok (fun c hc => by cases hc)
  simp only [hc4, ↓reduceIte]
  refine okPost_any (fun r3 => ?_)
  cases r3 with
  | Err e => simp only [branch_err_eq, Std.bind_ok]; exact okPost_residual e (fun c hc => by cases hc)
  | Ok u3 =>
  simp only [branch_ok_eq, Std.bind_ok]
  rcases hopt : Usize.checked_add cc 1#usize with _ | val2
  · simp only [hopt, core.option.Option.ok_or, Std.bind_ok, branch_err_eq]
    exact okPost_residual _ (fun c hc => by cases hc)
  simp only [hopt, core.option.Option.ok_or, Std.bind_ok, branch_ok_eq]
  refine okPost_bind (circle_new_loop0_rs _ _ _ _ _ _ _ _ (fun _ => ⟨by simp [alloc.vec.Vec.with_capacity], by simp⟩)) ?_
  rintro ⟨rs1, st⟩ hsec
  cases st with
  | Err e =>
    refine okPost_spec (core.result.Result.Insts.CoreOpsTry.branch_Err.spec (T := Unit) e) ?_
    intro cf hcf; subst hcf
    exact okPost_residual_gen _ (fun e c hc => by cases hc)
  | Ok u5 =>
  have hsec' := hsec (by cases u5; rfl)
  refine okPost_spec (core.result.Result.Insts.CoreOpsTry.branch_Ok.spec (E := topology.Error) u5) ?_
  intro cf hcf; subst hcf
  cases hmode : spec.mode with
  | Spinning =>
    repeat' (first
      | contradiction
      | (refine okPost_residual_gen _ ?_; intro e c hc; cases hc; done)
      | (refine okPost_ok ?_; intro c hc; cases hc; done)
      | (refine okPost_any (fun _ => ?_))
      | split)
    all_goals exact okPost_ok (fun c hc => by cases hc; exact ⟨hsec', rfl⟩)
  | Twisting amp mr =>
    repeat' (first
      | contradiction
      | (refine okPost_residual_gen _ ?_; intro e c hc; cases hc; done)
      | (refine okPost_ok ?_; intro c hc; cases hc; done)
      | (refine okPost_spec (range_inclusive_contains_i32_spec _ _) (fun b2 hb2 => ?_))
      | (refine okPost_spec i32_div_turn_eight (fun i17 hi17 => ?_))
      | (rw [range_inclusive_new_eq, Std.bind_ok])
      | (refine okPost_any (fun _ => ?_))
      | split)
    all_goals exact okPost_ok (fun c hc => by cases hc; exact ⟨hsec', rfl⟩)



/-- The first loop of `Layout::new` builds circles with one ring start per ring. -/
theorem layout_new_loop0_ring_starts (iter : alloc.vec.into_iter.IntoIter polar.PolarSpec)
    (margin : Std.I32) (circles : alloc.vec.Vec polar.Circle) (transforms : Std.Usize)
    (status : core.result.Result Unit topology.Error)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000) (hinv : RingStartsLen circles.val) :
    OkPost (scene.Layout.new_loop0 iter margin circles transforms status)
      (fun r => RingStartsLen r.1.val) := by
  unfold scene.Layout.new_loop0
  refine okPost_loop
    (fun st : alloc.vec.into_iter.IntoIter polar.PolarSpec × alloc.vec.Vec polar.Circle ×
      Std.Usize × core.result.Result Unit topology.Error => RingStartsLen st.2.1.val)
    _ _ ?_ (iter, circles, transforms, status) hinv
  rintro ⟨it, cs, tr, st⟩ hcs
  unfold scene.Layout.new_loop0.body
  refine okPost_any (fun p => ?_)
  obtain ⟨o, it1⟩ := p
  cases o with
  | none => exact okPost_ok hcs
  | some spec =>
  refine okPost_spec (core.result.Result.is_ok.step_spec st) ?_
  intro b hb
  cases b with
  | false => exact okPost_ok hcs
  | true =>
  refine okPost_bind (circle_new_ring_starts spec 0#usize tr margin hm) ?_
  intro r hr
  cases r with
  | Err e => exact okPost_ok hcs
  | Ok circle =>
  obtain ⟨hrs, _⟩ := hr circle rfl
  refine okPost_spec (circle_ring_count_spec circle) ?_
  intro i hi
  simp only [lift, Std.bind_ok]
  rcases hadd : Usize.checked_add tr i with _ | count
  · exact okPost_ok hcs
  refine okPost_bind (vec_push_okPost cs circle) ?_
  intro cs1 hcs1
  refine okPost_ok ?_
  intro c hc
  simp only [hcs1, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | hc
  · exact hcs c hc
  · subst hc; exact hrs

end Labyrinth
