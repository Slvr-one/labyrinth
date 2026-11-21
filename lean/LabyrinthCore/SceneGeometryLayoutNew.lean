module
public import LabyrinthCore.SceneGeometryValidate
import all Aeneas.Std.Scalar.CheckedOps.Add

/-! Geometry totality (S8), the validator link continued: the loops of `Layout::new` build circles,
bands and cells that satisfy `LayoutGeom`, so every layout `Layout::new` accepts satisfies it. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

/-! ### Small facts -/

theorem CircleOk.congr {c c' : polar.Circle} {n : Nat} (h : CircleOk c n) (hs : c'.spec = c.spec)
    (ho : c'.outer = c.outer) (ht : c'.transform_start = c.transform_start) : CircleOk c' n := by
  obtain ⟨s1, cc1, rs1, ts1, o1⟩ := c
  obtain ⟨s2, cc2, rs2, ts2, o2⟩ := c'
  simp only at hs ho ht
  subst hs ho ht
  exact ⟨h.center, h.center_radius, h.ring_width, h.rings, h.directions, h.sectors, h.outer,
    h.outer_le, h.transform, h.twist⟩

theorem CircleOk.mono {c : polar.Circle} {n n' : Nat} (h : CircleOk c n) (hn : n ≤ n') :
    CircleOk c n' :=
  ⟨h.center, h.center_radius, h.ring_width, h.rings, h.directions, h.sectors, h.outer,
    h.outer_le, by have := h.transform; omega, h.twist⟩

theorem usize_checked_add_some (x y z : Std.Usize) (h : Usize.checked_add x y = some z) :
    z.val = x.val + y.val := by
  have hb := Usize.checked_add_bv_spec x y
  rw [h] at hb
  exact hb.2.1

theorem vec_push_okPost {α : Type _} (v : alloc.vec.Vec α) (x : α) :
    OkPost (alloc.vec.Vec.push v x) (fun v1 => v1.val = v.val ++ [x]) := by
  intro v1 hv1
  simp only [alloc.vec.Vec.push] at hv1
  split_ifs at hv1 with hc
  · simp at hv1; rw [← hv1]; simp
  · simp at hv1

/-! ### Loop 0: circles -/

/-- Every circle built so far satisfies `CircleOk` for the current transform count. -/
def CirclesOk (cs : List polar.Circle) (n : Nat) : Prop :=
  ∀ i (h : i < cs.length), CircleOk (cs[i]'h) n

theorem layout_new_loop0_ok (iter : alloc.vec.into_iter.IntoIter polar.PolarSpec) (margin : Std.I32)
    (circles : alloc.vec.Vec polar.Circle) (transforms : Std.Usize)
    (status : core.result.Result Unit topology.Error)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000) (hinv : CirclesOk circles.val transforms.val) :
    OkPost (scene.Layout.new_loop0 iter margin circles transforms status)
      (fun r => CirclesOk r.1.val r.2.1.val) := by
  unfold scene.Layout.new_loop0
  refine okPost_loop
    (fun st : alloc.vec.into_iter.IntoIter polar.PolarSpec × alloc.vec.Vec polar.Circle ×
      Std.Usize × core.result.Result Unit topology.Error => CirclesOk st.2.1.val st.2.2.1.val)
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
  refine okPost_bind (circle_new_ok spec 0#usize tr margin hm) ?_
  intro r hr
  cases r with
  | Err e => exact okPost_ok hcs
  | Ok circle =>
  obtain ⟨hco, hts, hsp⟩ := hr circle rfl
  refine okPost_spec (circle_ring_count_spec circle) ?_
  intro i hi
  simp only [lift, Std.bind_ok]
  rcases hadd : Usize.checked_add tr i with _ | count
  · exact okPost_ok hcs
  have hcount := usize_checked_add_some _ _ _ hadd
  refine okPost_bind (vec_push_okPost cs circle) ?_
  intro cs1 hcs1
  refine okPost_ok ?_
  intro j hj
  simp only [hcs1] at hj ⊢
  have hle : tr.val ≤ count.val := by omega
  by_cases hjl : j < cs.val.length
  · rw [List.getElem_append_left hjl]
    exact (hcs j hjl).mono hle
  · have : j = cs.val.length := by simp at hj; omega
    subst this
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
    rw [hsp] at hi
    have : count.val = tr.val + spec.sectors.val.length := by rw [hcount, hi]
    rw [this]; exact hco

/-! ### Loop 1: portal specs and bands -/

/-- One band per circle, none negative. -/
def BandsOk (bands : List Std.I32) (n : Nat) : Prop :=
  bands.length = n ∧ ∀ k (h : k < bands.length), 0 ≤ (bands[k]'h).val

theorem layout_new_loop1_ok (ps : Slice polar.PortalSpec) (margin : Std.I32)
    (circles : alloc.vec.Vec polar.Circle) (status : core.result.Result Unit topology.Error)
    (bands : alloc.vec.Vec Std.I32) (counts : alloc.vec.Vec Std.Usize) (i : Std.Usize)
    (hm : 0 < margin.val ∧ margin.val ≤ 1000000) (hb : BandsOk bands.val circles.val.length)
    (hst : status = .Ok () → ∀ j (h : j < ps.val.length), j < i.val →
      PortalSpecOk circles.val.length (ps.val[j]'h)) :
    OkPost (scene.Layout.new_loop1 ps margin circles status bands counts i)
      (fun r => BandsOk r.2.1.val circles.val.length ∧
        (r.1 = .Ok () → ∀ j (h : j < ps.val.length), PortalSpecOk circles.val.length (ps.val[j]'h))) := by
  unfold scene.Layout.new_loop1
  refine okPost_loop
    (fun st : core.result.Result Unit topology.Error × alloc.vec.Vec Std.I32 ×
      alloc.vec.Vec Std.Usize × Std.Usize => BandsOk st.2.1.val circles.val.length ∧
      (st.1 = .Ok () → ∀ j (h : j < ps.val.length), j < st.2.2.2.val →
        PortalSpecOk circles.val.length (ps.val[j]'h)))
    _ _ ?_ (status, bands, counts, i) ⟨hb, hst⟩
  rintro ⟨st, bs, cs, k⟩ ⟨hbs, hsts⟩
  simp only at hbs hsts
  unfold scene.Layout.new_loop1.body
  simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
  by_cases hlt : k < Slice.len ps
  swap
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok ⟨hbs, fun h j hj => hsts h j hj (by scalar_tac)⟩
  simp only [hlt, ↓reduceIte]
  cases st with
  | Err e =>
    simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact okPost_ok ⟨hbs, fun h => by cases h⟩
  | Ok u =>
  simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte]
  have hsts' := hsts (by cases u; rfl)
  refine okPost_spec (Slice.index_usize_spec ps k (by scalar_tac)) ?_
  intro portal hportal
  refine okPost_bind (check_portal_spec_ok portal _ margin hm) ?_
  intro st1 hst1
  have hlen : (alloc.vec.Vec.deref circles).val.length = circles.val.length := by
    simp [alloc.vec.Vec.deref]
  rw [hlen] at hst1
  refine okPost_spec (core.result.Result.is_ok.step_spec st1) ?_
  intro b1 hb1
  refine okPost_bind (P := fun t : alloc.vec.Vec Std.I32 × alloc.vec.Vec Std.Usize =>
    BandsOk t.1.val circles.val.length) ?_ ?_
  · cases b1 with
    | false => exact okPost_ok hbs
    | true =>
    have hpo : PortalSpecOk circles.val.length portal := by
      apply hst1; cases st1 with
      | Ok v => cases v; rfl
      | Err e => simp [core.result.Result.ok?] at hb1
    obtain ⟨hpc, _, hpb⟩ := hpo
    have hbl := hbs.1
    have hcb : portal.circle.val < bs.length := by scalar_tac
    refine okPost_spec (alloc.vec.Vec.index_usize_spec bs portal.circle hcb) ?_
    intro i2 hi2
    simp only [lift, Std.bind_ok]
    refine okPost_spec (alloc.vec.Vec.index_mut_usize_spec bs portal.circle hcb) ?_
    rintro ⟨x, back⟩ ⟨hx, hback⟩
    refine okPost_any (fun p2 => ?_)
    obtain ⟨i4, back1⟩ := p2
    refine okPost_any (fun i5 => ?_)
    refine okPost_ok ?_
    subst hback
    refine ⟨by simp [hbl], fun j hj => ?_⟩
    simp only [alloc.vec.Vec.set_val_eq, List.getElem_set] at hj ⊢
    split
    · have h0 := hbs.2 _ (by simpa using hj)
      have : 0 ≤ (core.cmp.impls.OrdI32.max i2 portal.band).val := by simp; omega
      exact this
    · exact hbs.2 j (by simpa using hj)
  · rintro ⟨bs1, cs1⟩ hbs1
    refine okPost_spec (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac)) ?_
    intro k1 hk1
    refine okPost_ok ⟨hbs1, fun h1 j hj hjk => ?_⟩
    by_cases hjk' : j < k.val
    · exact hsts' j hj hjk'
    · have : j = k.val := by scalar_tac
      subst this
      have := hst1 h1
      rw [hportal] at this
      exact this

/-! ### Loop 2: circle extents -/

theorem vec_deref_val {T : Type _} (v : alloc.vec.Vec T) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

/-- The first `n` circles stay within the coordinate limit together with their adapter band. -/
def ExtentOk (cs : List polar.Circle) (bs : List Std.I32) (n : Nat) : Prop :=
  ∀ j (h1 : j < cs.length) (h2 : j < bs.length), j < n → (cs[j]'h1).outer.val + (bs[j]'h2).val ≤ 1000000

theorem layout_new_loop2_ok (margin : Std.I32) (circles : alloc.vec.Vec polar.Circle)
    (status : core.result.Result Unit topology.Error) (bands : alloc.vec.Vec Std.I32)
    (counts : alloc.vec.Vec Std.Usize) (i : Std.Usize)
    (hbl : bands.val.length = circles.val.length)
    (hst : status = .Ok () → ExtentOk circles.val bands.val i.val) :
    OkPost (scene.Layout.new_loop2 margin circles status bands counts i)
      (fun r => r = .Ok () → ExtentOk circles.val bands.val circles.val.length) := by
  unfold scene.Layout.new_loop2
  refine okPost_loop
    (fun st : core.result.Result Unit topology.Error × Std.Usize =>
      st.1 = .Ok () → ExtentOk circles.val bands.val st.2.val) _ _ ?_ (status, i) hst
  rintro ⟨st, k⟩ hsts
  simp only at hsts
  unfold scene.Layout.new_loop2.body
  by_cases hlt : k < alloc.vec.Vec.len circles
  swap
  · simp only [hlt, ↓reduceIte]
    exact okPost_ok (fun h j h1 h2 _ => hsts h j h1 h2 (by scalar_tac))
  simp only [hlt, ↓reduceIte]
  cases st with
  | Err e =>
    simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact okPost_ok (fun h => by cases h)
  | Ok u =>
  simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte]
  have hsts' := hsts (by cases u; rfl)
  have hkc : k.val < circles.val.length := by scalar_tac
  refine okPost_bind (check_circle_extent_ok k _ _ _ margin
    (by rw [vec_deref_val]; exact hkc) (by rw [vec_deref_val]; omega)) ?_
  intro st1 hst1
  refine okPost_spec (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac)) ?_
  intro k1 hk1
  refine okPost_ok (fun h1 j hj1 hj2 hjk => ?_)
  by_cases hjk' : j < k.val
  · exact hsts' j hj1 hj2 hjk'
  · have : j = k.val := by scalar_tac
    subst this
    have := hst1 h1
    simpa [vec_deref_val] using this

end Labyrinth
