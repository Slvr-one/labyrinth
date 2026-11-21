module
public import LabyrinthCore.SceneGeometryCircleTotal

/-! Geometry totality (S8), the constructor loops: the circle loop of `Layout::new` returns, the
portal check returns with only `InvalidGeometry`, and the portal loop and the extent checks return
whenever the circles, bands and counts carry the facts the earlier loops establish. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

/-! ### The vector iterator -/

/-- `IntoIter::next` returns; an exhausted iterator stays put and a live one yields its head. -/
theorem into_iter_next_spec {T : Type _} (it : alloc.vec.into_iter.IntoIter T) :
    alloc.vec.into_iter.IteratorIntoIter.next it ⦃ p =>
      (it.val = [] → p.1 = none) ∧
      (∀ hd tl, it.val = hd :: tl → p.1 = some hd ∧ p.2.val = tl) ⦄ := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  · rename_i h
    simp only [spec_ok]
    constructor <;> intros <;> simp_all
  · rename_i hd tl h
    simp only [spec_ok]
    constructor <;> intros <;> simp_all

/-! ### Loop 0: circles -/

theorem layout_new_loop0_spec (iter : alloc.vec.into_iter.IntoIter polar.PolarSpec)
    (margin : Std.I32) (circles : alloc.vec.Vec polar.Circle) (transforms : Std.Usize)
    (status : core.result.Result Unit topology.Error)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000)
    (hlen : circles.val.length + iter.val.length ≤ Std.Usize.max) :
    scene.Layout.new_loop0 iter margin circles transforms status ⦃ r =>
      (CircleStatus status → CircleStatus r.2.2) ⦄ := by
  unfold scene.Layout.new_loop0
  apply loop.spec_decr_nat
    (fun st : alloc.vec.into_iter.IntoIter polar.PolarSpec × alloc.vec.Vec polar.Circle ×
      Std.Usize × core.result.Result Unit topology.Error => st.1.val.length)
    (fun st : alloc.vec.into_iter.IntoIter polar.PolarSpec × alloc.vec.Vec polar.Circle ×
      Std.Usize × core.result.Result Unit topology.Error =>
      st.2.1.val.length + st.1.val.length ≤ Std.Usize.max ∧
        (CircleStatus status → CircleStatus st.2.2.2))
    _
  · rintro ⟨it, cs, tr, st⟩ ⟨hl, hs⟩
    dsimp only at hl hs ⊢
    unfold scene.Layout.new_loop0.body
    refine spec_bind (into_iter_next_spec it) ?_
    rintro ⟨o, it1⟩ ⟨hn1, hn2⟩
    cases o with
    | none => exact (spec_ok _).mpr hs
    | some spec =>
    obtain ⟨hd, tl, hit⟩ : ∃ hd tl, it.val = hd :: tl := by
      match h : it.val with
      | [] => have := (hn1 h); cases this
      | hd :: tl => exact ⟨hd, tl, rfl⟩
    obtain ⟨_, hit1⟩ := hn2 hd tl hit
    have hlt : it1.val.length < it.val.length := by rw [hit1, hit]; simp
    have hl1 : it1.val.length + 1 = it.val.length := by rw [hit1, hit]; simp
    cases st with
    | Err e =>
      simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte]
      refine (spec_ok _).mpr ?_
      dsimp only
      exact ⟨⟨by omega, hs⟩, hlt⟩
    | Ok u =>
    simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte]
    refine spec_bind (circle_new_spec spec 0#usize tr margin hm) ?_
    intro r hr
    cases r with
    | Err e =>
      refine (spec_ok _).mpr ?_
      dsimp only
      exact ⟨⟨by omega, fun h => circle_status_err e (hr e rfl)⟩, hlt⟩
    | Ok circle =>
    step as ⟨i, hi⟩
    simp only [lift, Std.bind_ok]
    rcases hadd : Usize.checked_add tr i with _ | count
    · refine (spec_ok _).mpr ?_
      dsimp only
      and_intros
      all_goals first | omega | exact hlt | exact fun h => circle_status_err _ (by simp [CircleErr])
    · have hpl : cs.val.length < Std.Usize.max := by omega
      step as ⟨cs1, hcs1⟩
      have : cs1.val.length = cs.val.length + 1 := by rw [hcs1]; simp
      exact ⟨by omega, hs, hlt⟩
  · exact ⟨hlen, fun h => h⟩

/-- The circle loop of `Layout::new` returns, and its status stays among the circle errors. -/
theorem layout_new_loop0_total (iter : alloc.vec.into_iter.IntoIter polar.PolarSpec)
    (margin : Std.I32) (circles : alloc.vec.Vec polar.Circle) (transforms : Std.Usize)
    (status : core.result.Result Unit topology.Error)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000)
    (hlen : circles.val.length + iter.val.length ≤ Std.Usize.max) :
    ∃ r, scene.Layout.new_loop0 iter margin circles transforms status = ok r ∧
      (CircleStatus status → CircleStatus r.2.2) :=
  spec_exists_ok (layout_new_loop0_spec iter margin circles transforms status hm hlen)

/-! ### `check_portal_spec` -/

theorem polar_arc_validate_err (a : polar.Arc) :
    polar.Arc.validate a ⦃ r => (r = .Ok () → ArcOk a) ∧
      (∀ e, r = .Err e → e = .InvalidGeometry) ⦄ := by
  unfold polar.Arc.validate
  have ht := turn_val
  split_ifs <;> simp only [spec_ok, ArcOk] <;> refine ⟨?_, ?_⟩ <;> intros <;>
    first | scalar_tac | (simp_all; done) | skip

theorem i32_prod_bound (a b : Std.I32) :
    -4611686018427387904 ≤ a.val * b.val ∧ a.val * b.val ≤ 4611686018427387904 := by
  have ha := i32_val_bounds a
  have hb := i32_val_bounds b
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

/-- `check_portal_spec` returns; every error is `InvalidGeometry`, and acceptance gives
`PortalSpecOk`. -/
theorem check_portal_spec_spec (p : polar.PortalSpec) (circles : Slice polar.Circle)
    (margin : Std.I32) (hm : 0 < margin.val ∧ margin.val ≤ 1000000) :
    scene.check_portal_spec p circles margin ⦃ r =>
      (r = .Ok () → PortalSpecOk circles.val.length p) ∧
      (∀ e, r = .Err e → e = .InvalidGeometry) ⦄ := by
  unfold scene.check_portal_spec
  by_cases h1 : p.circle ≥ Slice.len circles
  · simp only [h1, ↓reduceIte, spec_ok]
    exact ⟨(fun h => by cases h), fun e h => by cases h; rfl⟩
  simp only [h1, ↓reduceIte]
  step as ⟨i1, hi1⟩
  by_cases h2 : p.band < i1
  · simp only [h2, ↓reduceIte, spec_ok]
    exact ⟨(fun h => by cases h), fun e h => by cases h; rfl⟩
  simp only [h2, ↓reduceIte]
  refine spec_bind (polar_arc_validate_err p.mouth) ?_
  rintro r ⟨hr1, hr2⟩
  cases r with
  | Err e =>
    refine spec_bind (core.result.Result.Insts.CoreOpsTry.branch_Err.spec (T := Unit) e) ?_
    intro cf hcf; subst hcf
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.from, Std.bind_ok, bind_tc_ok, spec_ok]
    exact ⟨(fun h => by cases h), fun e' h => by cases h; exact hr2 e rfl⟩
  | Ok u =>
  refine spec_bind (core.result.Result.Insts.CoreOpsTry.branch_Ok.spec (E := topology.Error) u) ?_
  intro cf hcf; subst hcf
  have ht := turn_val
  have hmouth := hr1 (by cases u; rfl)
  have hc1 : p.circle.val < circles.val.length := by scalar_tac
  step as ⟨i2, hi2⟩
  by_cases h3 : p.mouth.length > i2
  · simp only [h3, ↓reduceIte, spec_ok]
    exact ⟨(fun h => by cases h), fun e h => by cases h; rfl⟩
  simp only [h3, ↓reduceIte, Std.bind_assoc]
  step as ⟨c, hc⟩
  step as ⟨i3, hi3⟩
  step as ⟨i4, hi4⟩
  have hb := i32_prod_bound c.outer p.mouth.length
  step as ⟨i5, hi5⟩
  step as ⟨i6, hi6⟩
  step as ⟨i7, hi7⟩
  step as ⟨i8, hi8⟩
  step as ⟨i9, hi9⟩
  by_cases h4 : i5 < i9
  · simp only [h4, ↓reduceIte, spec_ok]
    exact ⟨(fun h => by cases h), fun e h => by cases h; rfl⟩
  · simp only [h4, ↓reduceIte, spec_ok]
    exact ⟨fun _ => ⟨hc1, hmouth, by scalar_tac⟩, fun e h => by cases h⟩

/-! ### Loop 1: portal specs -/

theorem layout_new_loop1_spec (ps : Slice polar.PortalSpec) (margin : Std.I32)
    (circles : alloc.vec.Vec polar.Circle) (status : core.result.Result Unit topology.Error)
    (bands : alloc.vec.Vec Std.I32) (counts : alloc.vec.Vec Std.Usize) (i : Std.Usize)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000)
    (hbl : bands.val.length = circles.val.length)
    (hcl : counts.val.length = circles.val.length)
    (hcnt : ∀ k (h : k < counts.val.length), (counts.val[k]'h).val ≤ i.val) :
    scene.Layout.new_loop1 ps margin circles status bands counts i ⦃ r =>
      r.2.1.val.length = circles.val.length ∧ r.2.2.val.length = circles.val.length ⦄ := by
  unfold scene.Layout.new_loop1
  apply loop.spec_decr_nat
    (fun st : core.result.Result Unit topology.Error × alloc.vec.Vec Std.I32 ×
      alloc.vec.Vec Std.Usize × Std.Usize => ps.val.length - st.2.2.2.val)
    (fun st : core.result.Result Unit topology.Error × alloc.vec.Vec Std.I32 ×
      alloc.vec.Vec Std.Usize × Std.Usize => st.2.1.val.length = circles.val.length ∧
        st.2.2.1.val.length = circles.val.length ∧
        ∀ k (h : k < st.2.2.1.val.length), (st.2.2.1.val[k]'h).val ≤ st.2.2.2.val)
    _
  · rintro ⟨st, bs, cs, k⟩ ⟨hbs, hcs, hck⟩
    dsimp only at hbs hcs hck ⊢
    unfold scene.Layout.new_loop1.body
    simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
    by_cases hlt : k < Slice.len ps
    swap
    · simp only [hlt, ↓reduceIte, spec_ok]
      exact ⟨hbs, hcs⟩
    simp only [hlt, ↓reduceIte]
    cases st with
    | Err e =>
      simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte, spec_ok]
      exact ⟨hbs, hcs⟩
    | Ok u =>
    simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte]
    have hkl : k.val < ps.val.length := by scalar_tac
    step as ⟨portal, hportal⟩
    refine spec_bind (check_portal_spec_spec portal (alloc.vec.Vec.deref circles) margin hm) ?_
    rintro st1 ⟨hp1, hp2⟩
    have hlen : (alloc.vec.Vec.deref circles).val.length = circles.val.length := by
      simp [alloc.vec.Vec.deref]
    rw [hlen] at hp1
    cases st1 with
    | Err e =>
      simp only [Std.bind_ok, Bool.false_eq_true, ↓reduceIte]
      step as ⟨k1, hk1⟩
      and_intros
      · exact hbs
      · exact hcs
      · intro kk hh; have := hck kk hh; omega
      · omega
    | Ok v =>
    simp only [Std.bind_ok, ↓reduceIte]
    obtain ⟨hpc, _, _⟩ := hp1 (by cases v; rfl)
    have hcb : portal.circle.val < bs.val.length := by omega
    have hcc : portal.circle.val < cs.val.length := by omega
    step as ⟨i2, hi2⟩
    simp only [lift, Std.bind_ok]
    step as ⟨x, hx1, hx2⟩
    obtain ⟨xv, xb⟩ := x
    dsimp only at hx2 ⊢
    step as ⟨y, hy1, hy2⟩
    obtain ⟨yv, yb⟩ := y
    dsimp only at hy1 hy2 ⊢
    have hx4' : yv.val ≤ k.val := by rw [hy1]; exact hck _ hcc
    have hkm : k.val < Std.Usize.max := by scalar_tac
    step as ⟨i5, hi5⟩
    step as ⟨k1, hk1⟩
    rw [hy2, hx2]
    simp only [alloc.vec.Vec.set_val_eq, List.getElem_set, List.length_set]
    and_intros
    · exact hbs
    · exact hcs
    · intro kk hh
      by_cases hkc : portal.circle.val = kk
      · simp only [hkc, ite_true]; omega
      · simp only [hkc, ite_false]; have := hck kk (by simpa using hh); omega
    · omega
  · exact ⟨hbl, hcl, hcnt⟩

/-- The portal loop of `Layout::new` returns, and keeps one band and one count per circle. -/
theorem layout_new_loop1_total (ps : Slice polar.PortalSpec) (margin : Std.I32)
    (circles : alloc.vec.Vec polar.Circle) (status : core.result.Result Unit topology.Error)
    (bands : alloc.vec.Vec Std.I32) (counts : alloc.vec.Vec Std.Usize) (i : Std.Usize)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000) (hb : BandsOk bands.val circles.val.length)
    (hcl : counts.val.length = circles.val.length)
    (hcnt : ∀ k (h : k < counts.val.length), (counts.val[k]'h).val ≤ i.val) :
    ∃ r, scene.Layout.new_loop1 ps margin circles status bands counts i = ok r ∧
      r.2.1.val.length = circles.val.length ∧ r.2.2.val.length = circles.val.length := by
  obtain ⟨r, hr, h1, h2⟩ := spec_exists_ok
    (layout_new_loop1_spec ps margin circles status bands counts i hm hb.1 hcl hcnt)
  exact ⟨r, hr, h1, h2⟩

/-! ### `check_circle_extent` -/

theorem i32_sq_bound (a : Int) (h : -4000000 ≤ a ∧ a ≤ 4000000) :
    0 ≤ a * a ∧ a * a ≤ 16000000000000 := by
  constructor <;> nlinarith [h.1, h.2]

theorem check_circle_extent_loop0_spec (index : Std.Usize) (circles : Slice polar.Circle)
    (bands : Slice Std.I32) (margin : Std.I32) (ps : polar.PolarSpec) (i : Std.Usize)
    (v : alloc.vec.Vec Std.Usize) (i1 : Std.Usize) (i2 radius : Std.I32) (overlap : Bool)
    (j : Std.Usize) (n : Nat) (hcirc : CirclesOk circles.val n)
    (hbl : bands.val.length = circles.val.length)
    (hbnd : ∀ k (h : k < bands.val.length), 0 ≤ (bands.val[k]'h).val)
    (hext : ExtentOk circles.val bands.val index.val)
    (hidx : index.val ≤ circles.val.length) (hp : PointOk ps.center)
    (hrad : 0 ≤ radius.val ∧ radius.val ≤ 1000000) (hm : 0 < margin.val ∧ margin.val ≤ 1000000) :
    scene.check_circle_extent_loop0 index circles bands margin ps i v i1 i2 radius overlap j
      ⦃ r => True ⦄ := by
  unfold scene.check_circle_extent_loop0
  apply loop.spec_decr_nat
    (fun st : Bool × Std.Usize => index.val - st.2.val)
    (fun st : Bool × Std.Usize => True)
    _
  · rintro ⟨ov, jj⟩ _
    dsimp only
    unfold scene.check_circle_extent_loop0.body
    by_cases hlt : jj < index
    swap
    · simp only [hlt, ↓reduceIte, spec_ok]
    simp only [hlt, ↓reduceIte]
    by_cases hov : ov = true
    · simp only [hov, ↓reduceIte, spec_ok]
    have hov' : ov = false := by simpa using hov
    simp only [hov', Bool.false_eq_true, ↓reduceIte]
    have hjc : jj.val < circles.val.length := by scalar_tac
    have hjb : jj.val < bands.val.length := by omega
    step as ⟨c, hc⟩
    step as ⟨i3, hi3⟩
    have hcj := hcirc jj.val hjc
    have hbj := hbnd jj.val hjb
    have hej := hext jj.val hjc hjb (by scalar_tac)
    have hc' : c = circles.val[jj.val] := hc
    have hi3' : i3 = bands.val[jj.val] := hi3
    subst hc' hi3'
    have ho1 := hcj.outer_pos
    have ho2 := hcj.outer_le
    have hpc := hcj.center
    step as ⟨other, hother⟩
    step as ⟨i4, hi4⟩
    step as ⟨i5, hi5⟩
    step as ⟨i6, hi6⟩
    step as ⟨i7, hi7⟩
    step as ⟨i8, hi8⟩
    step as ⟨distance, hdist⟩
    step as ⟨pc, hpc'⟩
    have e1 : pc = ps.center := hpc'
    subst e1
    step as ⟨i9, hi9⟩
    step as ⟨p1, hp1⟩
    have e2 : p1 = (circles.val[jj.val]).spec.center := hp1
    subst e2
    step as ⟨i10, hi10⟩
    step as ⟨dx, hdx⟩
    step as ⟨i11, hi11⟩
    step as ⟨p2, hp2⟩
    have e3 : p2 = (circles.val[jj.val]).spec.center := hp2
    subst e3
    step as ⟨i12, hi12⟩
    step as ⟨dy, hdy⟩
    obtain ⟨hdx1, hdx2⟩ := i32_sq_bound dx.val (by simp only [PointOk] at hp hpc; omega)
    obtain ⟨hdy1, hdy2⟩ := i32_sq_bound dy.val (by simp only [PointOk] at hp hpc; omega)
    obtain ⟨hd1, hd2⟩ := i32_sq_bound distance.val (by omega)
    step as ⟨i13, hi13⟩
    step as ⟨i14, hi14⟩
    step as ⟨i15, hi15⟩
    step as ⟨i16, hi16⟩
    have hlt' : jj.val < index.val := by scalar_tac
    step as ⟨j1, hj1⟩
    omega
  · trivial

theorem check_circle_extent_loop1_spec (index : Std.Usize) (circles : Slice polar.Circle)
    (bands : Slice Std.I32) (margin : Std.I32) (p : grid.Point) (i i1 : Std.I32)
    (v : alloc.vec.Vec Std.Usize) (v1 : alloc.vec.Vec polar.Direction) (mm : polar.MotionMode)
    (i2 : Std.Usize) (v2 : alloc.vec.Vec Std.Usize) (i3 : Std.Usize) (i4 radius : Std.I32)
    (overlap : Bool) (j : Std.Usize) (n : Nat) (hcirc : CirclesOk circles.val n)
    (hbl : bands.val.length = circles.val.length)
    (hbnd : ∀ k (h : k < bands.val.length), 0 ≤ (bands.val[k]'h).val)
    (hext : ExtentOk circles.val bands.val index.val)
    (hidx : index.val ≤ circles.val.length) (hp : PointOk p)
    (hrad : 0 ≤ radius.val ∧ radius.val ≤ 1000000) (hm : 0 < margin.val ∧ margin.val ≤ 1000000) :
    scene.check_circle_extent_loop1 index circles bands margin p i i1 v v1 mm i2 v2 i3 i4 radius overlap j
      ⦃ r => True ⦄ := by
  unfold scene.check_circle_extent_loop1
  apply loop.spec_decr_nat
    (fun st : Bool × Std.Usize => index.val - st.2.val)
    (fun st : Bool × Std.Usize => True)
    _
  · rintro ⟨ov, jj⟩ _
    dsimp only
    unfold scene.check_circle_extent_loop1.body
    by_cases hlt : jj < index
    swap
    · simp only [hlt, ↓reduceIte, spec_ok]
    simp only [hlt, ↓reduceIte]
    by_cases hov : ov = true
    · simp only [hov, ↓reduceIte, spec_ok]
    have hov' : ov = false := by simpa using hov
    simp only [hov', Bool.false_eq_true, ↓reduceIte]
    have hjc : jj.val < circles.val.length := by scalar_tac
    have hjb : jj.val < bands.val.length := by omega
    step as ⟨c, hc⟩
    step as ⟨ib, hib⟩
    have hcj := hcirc jj.val hjc
    have hbj := hbnd jj.val hjb
    have hej := hext jj.val hjc hjb (by scalar_tac)
    have hc' : c = circles.val[jj.val] := hc
    have hi3' : ib = bands.val[jj.val] := hib
    subst hc' hi3'
    have ho1 := hcj.outer_pos
    have ho2 := hcj.outer_le
    have hpc := hcj.center
    step as ⟨other, hother⟩
    step as ⟨i4, hi4⟩
    step as ⟨i5, hi5⟩
    step as ⟨i6, hi6⟩
    step as ⟨i7, hi7⟩
    step as ⟨i8, hi8⟩
    step as ⟨distance, hdist⟩
    step as ⟨pc, hpc'⟩
    have e1 : pc = p := hpc'
    subst e1
    step as ⟨i9, hi9⟩
    step as ⟨p1, hp1⟩
    have e2 : p1 = (circles.val[jj.val]).spec.center := hp1
    subst e2
    step as ⟨i10, hi10⟩
    step as ⟨dx, hdx⟩
    step as ⟨i11, hi11⟩
    step as ⟨p2, hp2⟩
    have e3 : p2 = (circles.val[jj.val]).spec.center := hp2
    subst e3
    step as ⟨i12, hi12⟩
    step as ⟨dy, hdy⟩
    obtain ⟨hdx1, hdx2⟩ := i32_sq_bound dx.val (by simp only [PointOk] at hp hpc; omega)
    obtain ⟨hdy1, hdy2⟩ := i32_sq_bound dy.val (by simp only [PointOk] at hp hpc; omega)
    obtain ⟨hd1, hd2⟩ := i32_sq_bound distance.val (by omega)
    step as ⟨i13, hi13⟩
    step as ⟨i14, hi14⟩
    step as ⟨i15, hi15⟩
    step as ⟨i16, hi16⟩
    have hlt' : jj.val < index.val := by scalar_tac
    step as ⟨j1, hj1⟩
    omega
  · trivial

/-- The errors `check_circle_extent` raises. -/
def ExtentErr (e : topology.Error) : Prop := e = .InvalidGeometry ∨ e = .Overflow

theorem unit_residual_spec (e : topology.Error) (h : ExtentErr e) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
      (core.convert.FromSame topology.Error) (.Err e) ⦃ r => ∀ e', r = .Err e' → ExtentErr e' ⦄ := by
  simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, core.convert.FromSame.from, Std.bind_ok, bind_tc_ok, spec_ok]
  intro e' h'; cases h'; exact h

theorem check_circle_extent_spec (index : Std.Usize) (circles : Slice polar.Circle)
    (bands : Slice Std.I32) (counts : Slice Std.Usize) (margin : Std.I32) (n : Nat)
    (hcirc : CirclesOk circles.val n) (hbl : bands.val.length = circles.val.length)
    (hbnd : ∀ k (h : k < bands.val.length), 0 ≤ (bands.val[k]'h).val)
    (hext : ExtentOk circles.val bands.val index.val)
    (hc : index.val < circles.val.length) (hcnt : index.val < counts.val.length)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000) :
    scene.check_circle_extent index circles bands counts margin ⦃ r =>
      ∀ e, r = .Err e → ExtentErr e ⦄ := by
  unfold scene.check_circle_extent
  step as ⟨i, hi⟩
  by_cases h1 : i < 2#usize
  · simp only [h1, ↓reduceIte, spec_ok]; intro e h; cases h; simp [ExtentErr]
  simp only [h1, ↓reduceIte, Std.bind_assoc]
  have hb : index.val < bands.val.length := by omega
  step as ⟨circle, hcircle⟩
  step as ⟨i1, hi1⟩
  have hcj := hcirc index.val hc
  have hbj := hbnd index.val hb
  have hc' : circle = circles.val[index.val] := hcircle
  have hi1' : i1 = bands.val[index.val] := hi1
  subst hc' hi1'
  have ho1 := hcj.outer_pos
  have ho2 := hcj.outer_le
  have hcl := coord_limit_val
  simp only [lift, Std.bind_ok]
  rcases i32_checked_add_cases circles.val[index.val].outer bands.val[index.val] with
    ⟨hn, _⟩ | ⟨val, hz, hzv⟩
  · simp only [hn, core.option.Option.ok_or, Std.bind_ok, branch_err_eq]
    exact unit_residual_spec _ (by simp [ExtentErr])
  simp only [hz, core.option.Option.ok_or, Std.bind_ok, branch_ok_eq]
  by_cases h2 : val > grid.COORD_LIMIT
  · simp only [h2, ↓reduceIte, spec_ok]; intro e h; cases h; simp [ExtentErr]
  simp only [h2, ↓reduceIte]
  have hval : 0 ≤ val.val ∧ val.val ≤ 1000000 := by scalar_tac
  step as ⟨p, hp⟩
  have hpt : PointOk p := by rw [hp]; exact hcj.center
  have ht := turn_val
  refine spec_bind (polar_bounds_spec p 0#i32 val { start := 0#i32, length := polar.TURN } margin
    hpt (by simp) hval (by unfold ArcBnd; dsimp only; scalar_tac)) ?_
  rintro r1 ⟨_, h3, _⟩
  cases r1 with
  | Err e =>
    simp only [branch_err_eq, Std.bind_ok]
    exact unit_residual_spec e (h3 e rfl)
  | Ok u3 =>
  simp only [branch_ok_eq, Std.bind_ok]
  step as ⟨mm, hmm⟩
  cases mm with
  | Spinning =>
    refine spec_bind (check_circle_extent_loop0_spec index circles bands margin _ _ _ _ _ val false
      0#usize n hcirc hbl hbnd hext (by omega) hcj.center hval hm) ?_
    intro ov _
    by_cases hov : ov = true
    · simp only [hov, ↓reduceIte, spec_ok]; intro e h; cases h; simp [ExtentErr]
    · have : ov = false := by simpa using hov
      simp only [this, Bool.false_eq_true, ↓reduceIte, spec_ok]; intro e h; cases h
  | Twisting amp a =>
    have hamp := hcj.twist amp a hmm.symm
    have hrw := hcj.ring_width
    have hrwle : circles.val[index.val].spec.ring_width.val ≤ 1000000 := by
      have h1 := hcj.outer; have h2 := hcj.rings; have h3 := hcj.center_radius
      have : circles.val[index.val].spec.ring_width.val ≤
          circles.val[index.val].spec.sectors.val.length * circles.val[index.val].spec.ring_width.val := by
        nlinarith
      omega
    have hfT : (core.convert.num.FromI64I32.from polar.TURN).val = 4096 := by
      rw [core.convert.num.FromI64I32.from_val_eq]; exact ht
    have hfv : (core.convert.num.FromI64I32.from val).val = val.val :=
      core.convert.num.FromI64I32.from_val_eq _
    have hfa : (core.convert.num.FromI64I32.from amp).val = amp.val :=
      core.convert.num.FromI64I32.from_val_eq _
    have hpr : (core.convert.num.FromI64I32.from val).val * (core.convert.num.FromI64I32.from amp).val
        ≤ 1000000 * 512 ∧
        0 ≤ (core.convert.num.FromI64I32.from val).val * (core.convert.num.FromI64I32.from amp).val := by
      rw [hfv, hfa]; constructor <;> nlinarith [hval.1, hval.2, hamp.1, hamp.2]
    step as ⟨i2, hi2⟩
    step as ⟨width, hw⟩
    step as ⟨i5, hi5⟩
    step as ⟨i6, hi6⟩
    step as ⟨i7, hi7⟩
    step as ⟨i8, hi8⟩
    step as ⟨i11, hi11⟩
    by_cases hgt : i6 > i11
    · simp only [hgt, ↓reduceIte, spec_ok]; intro e h; cases h; simp [ExtentErr]
    simp only [hgt, ↓reduceIte, Std.bind_assoc]
    refine spec_bind (check_circle_extent_loop1_spec index circles bands margin _ _ _ _ _ _ _ _ _ _
      val false 0#usize n hcirc hbl hbnd hext (by omega) hcj.center hval hm) ?_
    intro ov _
    by_cases hov : ov = true
    · simp only [hov, ↓reduceIte, spec_ok]; intro e h; cases h; simp [ExtentErr]
    · have : ov = false := by simpa using hov
      simp only [this, Bool.false_eq_true, ↓reduceIte, spec_ok]; intro e h; cases h

/-- `check_circle_extent` returns, and every error is `InvalidGeometry` or `Overflow`. -/
theorem check_circle_extent_total (index : Std.Usize) (circles : Slice polar.Circle)
    (bands : Slice Std.I32) (counts : Slice Std.Usize) (margin : Std.I32) (n : Nat)
    (hcirc : CirclesOk circles.val n) (hbl : bands.val.length = circles.val.length)
    (hbnd : ∀ k (h : k < bands.val.length), 0 ≤ (bands.val[k]'h).val)
    (hext : ExtentOk circles.val bands.val index.val)
    (hc : index.val < circles.val.length) (hcnt : index.val < counts.val.length)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000) :
    ∃ r, scene.check_circle_extent index circles bands counts margin = ok r ∧
      (∀ e, r = .Err e → e = .InvalidGeometry ∨ e = .Overflow) := by
  obtain ⟨r, hr, h⟩ := spec_exists_ok
    (check_circle_extent_spec index circles bands counts margin n hcirc hbl hbnd hext hc hcnt hm)
  exact ⟨r, hr, h⟩

/-! ### Loop 2: circle extents -/

theorem layout_new_loop2_spec (margin : Std.I32) (circles : alloc.vec.Vec polar.Circle)
    (status : core.result.Result Unit topology.Error) (bands : alloc.vec.Vec Std.I32)
    (counts : alloc.vec.Vec Std.Usize) (i : Std.Usize) (n : Nat)
    (hcirc : CirclesOk circles.val n) (hbl : bands.val.length = circles.val.length)
    (hbnd : ∀ k (h : k < bands.val.length), 0 ≤ (bands.val[k]'h).val)
    (hcl : counts.val.length = circles.val.length)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000)
    (hst : status = .Ok () → ExtentOk circles.val bands.val i.val) :
    scene.Layout.new_loop2 margin circles status bands counts i ⦃ r => True ⦄ := by
  unfold scene.Layout.new_loop2
  apply loop.spec_decr_nat
    (fun st : core.result.Result Unit topology.Error × Std.Usize =>
      circles.val.length - st.2.val)
    (fun st : core.result.Result Unit topology.Error × Std.Usize =>
      st.1 = .Ok () → ExtentOk circles.val bands.val st.2.val)
    _
  · rintro ⟨st, k⟩ hsts
    dsimp only at hsts ⊢
    unfold scene.Layout.new_loop2.body
    by_cases hlt : k < alloc.vec.Vec.len circles
    swap
    · simp only [hlt, ↓reduceIte, spec_ok]
    simp only [hlt, ↓reduceIte]
    cases st with
    | Err e =>
      simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte, spec_ok]
    | Ok u =>
    simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte]
    have hsts' := hsts (by cases u; rfl)
    have hkc : k.val < circles.val.length := by scalar_tac
    have hc1 : k.val < (alloc.vec.Vec.deref circles).val.length := by
      rw [vec_deref_val]; exact hkc
    obtain ⟨r, hr, herr⟩ := check_circle_extent_total k (alloc.vec.Vec.deref circles)
      (alloc.vec.Vec.deref bands) (alloc.vec.Vec.deref counts) margin n
      (by rw [vec_deref_val]; exact hcirc) (by rw [vec_deref_val, vec_deref_val]; exact hbl)
      (by rw [vec_deref_val]; exact hbnd) (by rw [vec_deref_val, vec_deref_val]; exact hsts')
      hc1 (by rw [vec_deref_val]; omega) hm
    have hok := check_circle_extent_ok k (alloc.vec.Vec.deref circles) (alloc.vec.Vec.deref bands)
      (alloc.vec.Vec.deref counts) margin hc1 (by rw [vec_deref_val]; omega) r hr
    rw [hr]
    simp only [Std.bind_ok]
    step as ⟨k1, hk1⟩
    refine ⟨fun h1 j hj1 hj2 hjk => ?_, by omega⟩
    by_cases hjk' : j < k.val
    · exact hsts' j hj1 hj2 hjk'
    · have : j = k.val := by scalar_tac
      subst this
      have := hok h1
      simpa [vec_deref_val] using this
  · exact hst

/-- The extent loop of `Layout::new` returns. -/
theorem layout_new_loop2_total (margin : Std.I32) (circles : alloc.vec.Vec polar.Circle)
    (status : core.result.Result Unit topology.Error) (bands : alloc.vec.Vec Std.I32)
    (counts : alloc.vec.Vec Std.Usize) (i : Std.Usize) (n : Nat)
    (hcirc : CirclesOk circles.val n) (hb : BandsOk bands.val circles.val.length)
    (hcl : counts.val.length = circles.val.length)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000)
    (hst : status = .Ok () → ExtentOk circles.val bands.val i.val) :
    ∃ r, scene.Layout.new_loop2 margin circles status bands counts i = ok r :=
  let ⟨r, hr, _⟩ := spec_exists_ok
    (layout_new_loop2_spec margin circles status bands counts i n hcirc hb.1 hb.2 hcl hm hst)
  ⟨r, hr⟩

/-- `check_portal_spec` returns; every error is `InvalidGeometry`. -/
theorem check_portal_spec_total (p : polar.PortalSpec) (circles : Slice polar.Circle)
    (margin : Std.I32) (hm : 0 < margin.val ∧ margin.val ≤ 1000000) :
    ∃ r, scene.check_portal_spec p circles margin = ok r ∧
      (∀ e, r = .Err e → e = .InvalidGeometry) ∧
      (r = .Ok () → PortalSpecOk circles.val.length p) := by
  obtain ⟨r, hr, h1, h2⟩ := spec_exists_ok (check_portal_spec_spec p circles margin hm)
  exact ⟨r, hr, h2, h1⟩

end Labyrinth
