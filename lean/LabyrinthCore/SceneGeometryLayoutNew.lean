module
public import LabyrinthCore.SceneGeometryValidate
public import LabyrinthCore.ConstructorCarrierEdges
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

/-! ### Cells -/

/-- `CellOk` stated over the circle specs and the portal list of a layout. -/
def CellOkS (specs : List polar.PolarSpec) (ps : List scene.Portal) : scene.Cell → Prop
  | .Grid _ _ b => RectOk b
  | .Center c => c.val < specs.length
  | .Sector c r s => ∃ h : c.val < specs.length, ∃ hr : r.val < (specs[c.val]'h).sectors.val.length,
      s.val < ((specs[c.val]'h).sectors.val[r.val]'hr).val
  | .Transition p => ∃ h : p.val < ps.length,
      (ps[p.val]'h).spec.circle.val < specs.length ∧ ArcOk (ps[p.val]'h).spec.mouth

theorem CellOkS.extend {specs : List polar.PolarSpec} {ps : List scene.Portal} {c : scene.Cell}
    (h : CellOkS specs ps c) (ps' : List scene.Portal) : CellOkS specs (ps ++ ps') c := by
  cases c with
  | Transition p =>
    obtain ⟨hp, h1, h2⟩ := h
    refine ⟨by simp; omega, ?_⟩
    rw [List.getElem_append_left hp]
    exact ⟨h1, h2⟩
  | _ => exact h

/-- A grid cell whose bounds are a valid rectangle. -/
def GridCellOk (c : scene.Cell) : Prop := ∃ a b r, c = .Grid a b r ∧ RectOk r

theorem layout_new_loop3_inner_ok (circles : alloc.vec.Vec polar.Circle) (bands : alloc.vec.Vec Std.I32)
    (bounds : grid.Rect) (removed : Bool) (i : Std.Usize) :
    OkPost (scene.Layout.new_loop3_loop0_loop0 circles bands bounds removed i)
      (fun r => removed = true → r = true) := by
  unfold scene.Layout.new_loop3_loop0_loop0
  refine okPost_loop (fun st : Bool × Std.Usize => removed = true → st.1 = true) _ _ ?_
    (removed, i) id
  rintro ⟨rm, k⟩ hrm
  simp only at hrm
  unfold scene.Layout.new_loop3_loop0_loop0.body
  by_cases hlt : k < alloc.vec.Vec.len circles <;> simp only [hlt, ↓reduceIte]
  · refine okPost_any (fun _ => okPost_any (fun _ => okPost_any (fun _ => okPost_any (fun _ =>
      okPost_any (fun b => ?_)))))
    simp only [bind_ite_ok]
    refine okPost_any (fun _ => okPost_ok ?_)
    intro h; simp only; split <;> simp_all
  · exact okPost_ok hrm

theorem layout_new_loop3_loop0_ok (n : Std.Usize) (geometry : grid.Geometry) (cell_grid : grid.Grid)
    (circles : alloc.vec.Vec polar.Circle) (bands : alloc.vec.Vec Std.I32)
    (cells : alloc.vec.Vec scene.Cell) (row column : Std.Usize)
    (hc : ∀ c ∈ cells.val, GridCellOk c) :
    OkPost (scene.Layout.new_loop3_loop0 n geometry cell_grid circles bands cells row column)
      (fun r => ∀ c ∈ r.2.val, GridCellOk c) := by
  unfold scene.Layout.new_loop3_loop0
  refine okPost_loop (fun st : grid.Grid × alloc.vec.Vec scene.Cell × Std.Usize =>
    ∀ c ∈ st.2.1.val, GridCellOk c) _ _ ?_ (cell_grid, cells, column) hc
  rintro ⟨g, cs, col⟩ hcs
  simp only at hcs
  unfold scene.Layout.new_loop3_loop0.body
  by_cases hlt : col < n <;> simp only [hlt, ↓reduceIte]
  · refine okPost_any (fun bounds => ?_)
    refine okPost_spec (grid_geometry_check_spec geometry bounds) ?_
    rintro r ⟨hr1, hr2⟩
    refine okPost_spec (result_is_err_spec r) ?_
    intro removed hremoved
    refine okPost_bind (layout_new_loop3_inner_ok circles bands bounds removed 0#usize) ?_
    intro removed1 hremoved1
    refine okPost_bind (P := fun t : grid.Grid × alloc.vec.Vec scene.Cell =>
      ∀ c ∈ t.2.val, GridCellOk c) ?_ ?_
    · cases removed1 with
      | true => exact okPost_ok hcs
      | false =>
      have hrf : removed = false := by
        cases removed with
        | true => exact absurd (hremoved1 rfl) (by simp)
        | false => rfl
      have hok : r = .Ok () := by
        cases r with
        | Ok u => cases u; rfl
        | Err e => simp [hrf, core.result.Result.ok?] at hremoved
      have hrect := ((hr1.mp hok).1)
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine okPost_any (fun g2 => ?_)
      refine okPost_bind (vec_push_okPost cs _) ?_
      intro cs2 hcs2
      refine okPost_ok ?_
      intro c hcm
      simp only [hcs2, List.mem_append, List.mem_singleton] at hcm
      rcases hcm with hcm | hcm
      · exact hcs c hcm
      · exact ⟨_, _, _, hcm, hrect⟩
    · rintro ⟨g1, cs1⟩ hcs1
      exact okPost_any (fun _ => okPost_ok hcs1)
  · exact okPost_ok hcs

theorem layout_new_loop3_ok (n n1 : Std.Usize) (geometry : grid.Geometry) (cell_grid : grid.Grid)
    (circles : alloc.vec.Vec polar.Circle) (bands : alloc.vec.Vec Std.I32)
    (cells : alloc.vec.Vec scene.Cell) (row : Std.Usize) (hc : ∀ c ∈ cells.val, GridCellOk c) :
    OkPost (scene.Layout.new_loop3 n n1 geometry cell_grid circles bands cells row)
      (fun r => ∀ c ∈ r.2.val, GridCellOk c) := by
  unfold scene.Layout.new_loop3
  refine okPost_loop (fun st : grid.Grid × alloc.vec.Vec scene.Cell × Std.Usize =>
    ∀ c ∈ st.2.1.val, GridCellOk c) _ _ ?_ (cell_grid, cells, row) hc
  rintro ⟨g, cs, rw⟩ hcs
  simp only at hcs
  unfold scene.Layout.new_loop3.body
  by_cases hlt : rw < n1 <;> simp only [hlt, ↓reduceIte]
  · refine okPost_bind (layout_new_loop3_loop0_ok n geometry g circles bands cs rw 0#usize hcs) ?_
    rintro ⟨g1, cs1⟩ hcs1
    exact okPost_any (fun _ => okPost_ok hcs1)
  · exact okPost_ok hcs

/-- What a circle contributes to `LayoutGeom`: its spec, outer radius and transform start. -/
def circleKey (c : polar.Circle) : polar.PolarSpec × Std.I32 × Std.Usize :=
  (c.spec, c.outer, c.transform_start)

theorem keys_set {l : List polar.Circle} {i : Nat} {x : polar.Circle} (hi : i < l.length)
    (hx : circleKey x = circleKey (l[i]'hi)) : (l.set i x).map circleKey = l.map circleKey := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_set]
  split
  · subst_vars; exact hx
  · rfl

theorem specs_of_keys {l : List polar.Circle} {K : List (polar.PolarSpec × Std.I32 × Std.Usize)}
    (h : l.map circleKey = K) : l.map (·.spec) = K.map (·.1) := by
  rw [← h, List.map_map]; rfl

theorem layout_new_loop4_sectors_ok (circles : alloc.vec.Vec polar.Circle)
    (cells : alloc.vec.Vec scene.Cell) (ci ring sector : Std.Usize)
    (hci : ci.val < circles.val.length)
    (hring : ring.val < (circles.val[ci.val]'hci).spec.sectors.val.length)
    (hc : ∀ c ∈ cells.val, CellOkS (circles.val.map (·.spec)) [] c) :
    OkPost (scene.Layout.new_loop4_loop0_loop0 circles cells ci ring sector)
      (fun r => ∀ c ∈ r.val, CellOkS (circles.val.map (·.spec)) [] c) := by
  unfold scene.Layout.new_loop4_loop0_loop0
  refine okPost_loop (fun st : alloc.vec.Vec scene.Cell × Std.Usize =>
    ∀ c ∈ st.1.val, CellOkS (circles.val.map (·.spec)) [] c) _ _ ?_ (cells, sector) hc
  rintro ⟨cs, sec⟩ hcs
  simp only at hcs
  unfold scene.Layout.new_loop4_loop0_loop0.body
  simp only [alloc.vec.Vec.index_slice_index]
  refine okPost_spec (alloc.vec.Vec.index_usize_spec circles ci hci) ?_
  intro c hc'
  refine okPost_spec (alloc.vec.Vec.index_usize_spec c.spec.sectors ring (by rw [hc']; exact hring)) ?_
  intro cnt hcnt
  by_cases hlt : sec < cnt <;> simp only [hlt, ↓reduceIte]
  · skip
    refine okPost_bind (vec_push_okPost cs _) ?_
    intro cs2 hcs2
    refine okPost_any (fun _ => okPost_ok ?_)
    intro x hx
    simp only [hcs2, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact hcs x hx
    · subst hx
      refine ⟨by simpa using hci, by simpa using hring, ?_⟩
      subst hc'
      simp only [List.getElem_map]
      rw [← hcnt]; scalar_tac
  · exact okPost_ok hcs

theorem layout_new_loop4_rings_ok (circles : alloc.vec.Vec polar.Circle)
    (cells : alloc.vec.Vec scene.Cell) (ci ring : Std.Usize)
    (K : List (polar.PolarSpec × Std.I32 × Std.Usize)) (hK : circles.val.map circleKey = K)
    (hci : ci.val < K.length) (hc : ∀ c ∈ cells.val, CellOkS (K.map (·.1)) [] c) :
    OkPost (scene.Layout.new_loop4_loop0 circles cells ci ring)
      (fun r => r.1.val.map circleKey = K ∧ ∀ c ∈ r.2.val, CellOkS (K.map (·.1)) [] c) := by
  unfold scene.Layout.new_loop4_loop0
  refine okPost_loop (fun st : alloc.vec.Vec polar.Circle × alloc.vec.Vec scene.Cell × Std.Usize =>
    st.1.val.map circleKey = K ∧ ∀ c ∈ st.2.1.val, CellOkS (K.map (·.1)) [] c) _ _ ?_
    (circles, cells, ring) ⟨hK, hc⟩
  rintro ⟨cl, cs, rg⟩ ⟨hcl, hcs⟩
  simp only at hcl hcs
  have hlen : cl.val.length = K.length := by rw [← hcl, List.length_map]
  have hci' : ci.val < cl.val.length := by omega
  unfold scene.Layout.new_loop4_loop0.body
  simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
  refine okPost_spec (alloc.vec.Vec.index_usize_spec cl ci hci') ?_
  intro c hc'
  refine okPost_spec (circle_ring_count_spec c) ?_
  intro n hn
  by_cases hlt : rg < n <;> simp only [hlt, ↓reduceIte]
  · skip
    refine okPost_spec (alloc.vec.Vec.index_mut_usize_spec cl ci hci') ?_
    rintro ⟨c1, back⟩ ⟨hc1, hback⟩
    refine okPost_any (fun p => ?_)
    obtain ⟨_, back1⟩ := p
    subst hback
    have hkeys : (cl.set ci { c1 with ring_starts := back1 cs.len }).val.map circleKey = K := by
      rw [alloc.vec.Vec.set_val_eq, keys_set hci' (by subst hc1; rfl), hcl]
    have hspecs := specs_of_keys hkeys
    have hci2 : ci.val < (cl.set ci { c1 with ring_starts := back1 cs.len }).val.length := by
      simp; omega
    have hring2 : rg.val < ((cl.set ci { c1 with ring_starts := back1 cs.len }).val[ci.val]'hci2).spec.sectors.val.length := by
      simp only [alloc.vec.Vec.set_val_eq, List.getElem_set_self]
      have hn' := hn; rw [hc'] at hn'; subst hc1; scalar_tac
    refine okPost_bind (layout_new_loop4_sectors_ok _ cs ci rg 0#usize hci2 hring2
      (by rw [hspecs]; exact hcs)) ?_
    intro cs1 hcs1
    rw [hspecs] at hcs1
    exact okPost_any (fun _ => okPost_ok ⟨hkeys, hcs1⟩)
  · exact okPost_ok ⟨hcl, hcs⟩

theorem layout_new_loop4_ok (circles : alloc.vec.Vec polar.Circle) (cells : alloc.vec.Vec scene.Cell)
    (ci : Std.Usize) (K : List (polar.PolarSpec × Std.I32 × Std.Usize))
    (hK : circles.val.map circleKey = K) (hc : ∀ c ∈ cells.val, CellOkS (K.map (·.1)) [] c) :
    OkPost (scene.Layout.new_loop4 circles cells ci)
      (fun r => r.1.val.map circleKey = K ∧ ∀ c ∈ r.2.val, CellOkS (K.map (·.1)) [] c) := by
  unfold scene.Layout.new_loop4
  refine okPost_loop (fun st : alloc.vec.Vec polar.Circle × alloc.vec.Vec scene.Cell × Std.Usize =>
    st.1.val.map circleKey = K ∧ ∀ c ∈ st.2.1.val, CellOkS (K.map (·.1)) [] c) _ _ ?_
    (circles, cells, ci) ⟨hK, hc⟩
  rintro ⟨cl, cs, k⟩ ⟨hcl, hcs⟩
  simp only at hcl hcs
  have hlen : cl.val.length = K.length := by rw [← hcl, List.length_map]
  unfold scene.Layout.new_loop4.body
  simp only [alloc.vec.Vec.index_mut_slice_index]
  by_cases hlt : k < alloc.vec.Vec.len cl <;> simp only [hlt, ↓reduceIte]
  · skip
    have hk : k.val < cl.val.length := by scalar_tac
    refine okPost_spec (alloc.vec.Vec.index_mut_usize_spec cl k hk) ?_
    rintro ⟨c, back⟩ ⟨hc', hback⟩
    refine okPost_bind (vec_push_okPost cs _) ?_
    intro cs1 hcs1
    subst hback
    have hkeys : (cl.set k { c with center_cell := cs.len }).val.map circleKey = K := by
      rw [alloc.vec.Vec.set_val_eq, keys_set hk (by subst hc'; rfl), hcl]
    refine okPost_bind (layout_new_loop4_rings_ok _ cs1 k 0#usize K hkeys (by omega) ?_) ?_
    · intro x hx
      simp only [hcs1, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact hcs x hx
      · subst hx; show k.val < (K.map (·.1)).length; simp; omega
    · rintro ⟨cl2, cs2⟩ ⟨hcl2, hcs2⟩
      exact okPost_any (fun _ => okPost_ok ⟨hcl2, hcs2⟩)
  · exact okPost_ok ⟨hcl, hcs⟩

theorem resolve_portal_ok (spec : polar.PortalSpec) (cell_grid : grid.Grid)
    (portals : Slice scene.Portal) (tc : Std.Usize) :
    OkPost (scene.resolve_portal spec cell_grid portals tc)
      (fun r => ∀ p, r = .Ok p → p.spec = spec) := by
  unfold scene.resolve_portal
  refine okPost_any (fun o => ?_)
  cases o with
  | none =>
    simp only [core.option.Option.ok_or, Std.bind_ok, branch_err_eq]
    exact okPost_residual_gen _ (fun e p hp => by cases hp)
  | some v =>
    simp only [core.option.Option.ok_or, Std.bind_ok, branch_ok_eq]
    refine okPost_any (fun conflict => ?_)
    split
    · exact okPost_ok (fun p hp => by cases hp)
    · exact okPost_ok (fun p hp => by cases hp; rfl)

/-- The portal loop's invariant: on success one portal per spec so far, each carrying its spec,
and every cell valid against the portals built so far. -/
def PortalLoopInv (specs : List polar.PolarSpec) (ps : Slice polar.PortalSpec)
    (st : core.result.Result Unit topology.Error) (cells : alloc.vec.Vec scene.Cell)
    (portals : alloc.vec.Vec scene.Portal) (i : Nat) : Prop :=
  (st = .Ok () → portals.val.length = i) ∧
  (∀ j (h : j < portals.val.length), ∃ hj : j < ps.val.length, (portals.val[j]'h).spec = ps.val[j]'hj) ∧
  ∀ c ∈ cells.val, CellOkS specs portals.val c

theorem layout_new_loop5_ok (ps : Slice polar.PortalSpec) (cell_grid : grid.Grid)
    (status : core.result.Result Unit topology.Error) (cells : alloc.vec.Vec scene.Cell)
    (portals : alloc.vec.Vec scene.Portal) (i : Std.Usize) (specs : List polar.PolarSpec)
    (hps : ∀ j (h : j < ps.val.length), PortalSpecOk specs.length (ps.val[j]'h))
    (hinv : PortalLoopInv specs ps status cells portals i.val) :
    OkPost (scene.Layout.new_loop5 ps cell_grid status cells portals i)
      (fun r => ∀ c ∈ r.2.1.val, CellOkS specs r.2.2.val c) := by
  unfold scene.Layout.new_loop5
  refine okPost_loop (fun st : core.result.Result Unit topology.Error × alloc.vec.Vec scene.Cell ×
    alloc.vec.Vec scene.Portal × Std.Usize => PortalLoopInv specs ps st.1 st.2.1 st.2.2.1 st.2.2.2.val)
    _ _ ?_ (status, cells, portals, i) hinv
  rintro ⟨st, cs, pt, k⟩ ⟨hst, hspec, hcs⟩
  simp only at hst hspec hcs
  unfold scene.Layout.new_loop5.body
  by_cases hlt : k < Slice.len ps <;> simp only [hlt, ↓reduceIte]
  · skip
    cases st with
    | Err e =>
      simp only [core.result.Result.is_ok, Std.bind_ok, Bool.false_eq_true, ↓reduceIte]
      exact okPost_ok hcs
    | Ok u =>
    simp only [core.result.Result.is_ok, Std.bind_ok, ↓reduceIte]
    have hlen := hst (by cases u; rfl)
    refine okPost_spec (Slice.index_usize_spec ps k (by scalar_tac)) ?_
    intro p hp
    refine okPost_bind (resolve_portal_ok p cell_grid _ _) ?_
    intro r hr
    refine okPost_bind (P := fun t : core.result.Result Unit topology.Error × alloc.vec.Vec scene.Cell ×
      alloc.vec.Vec scene.Portal => PortalLoopInv specs ps t.1 t.2.1 t.2.2 (k.val + 1)) ?_ ?_
    · cases r with
      | Err e => exact okPost_ok ⟨(fun h => by cases h), hspec, hcs⟩
      | Ok portal =>
      have hps' := hr portal rfl
      refine okPost_bind (vec_push_okPost cs _) ?_
      intro cs2 hcs2
      refine okPost_bind (vec_push_okPost pt portal) ?_
      intro pt2 hpt2
      refine okPost_ok ⟨fun _ => by simp [hpt2]; omega, ?_, ?_⟩
      · intro j hj
        by_cases hjl : j < pt.val.length
        · obtain ⟨hj', he⟩ := hspec j hjl
          refine ⟨hj', ?_⟩
          simp only [hpt2, List.getElem_append_left hjl]; exact he
        · have hj2 : j = pt.val.length := by simp [hpt2] at hj; omega
          subst hj2
          refine ⟨by scalar_tac, ?_⟩
          simp only [hpt2, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
            List.getElem_cons_zero]
          rw [hps', hp]; simp [hlen]
      · intro c hc
        simp only [hcs2, List.mem_append, List.mem_singleton] at hc
        rw [hpt2]
        rcases hc with hc | hc
        · exact (hcs c hc).extend [portal]
        · subst hc
          have hkp : k.val < (pt.val ++ [portal]).length := by simp; omega
          refine ⟨hkp, ?_⟩
          have he : (pt.val ++ [portal])[k.val]'hkp = portal := by
            simp only [← hlen, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
              List.getElem_cons_zero]
          rw [he, hps', hp]
          exact ⟨(hps _ _).1, (hps _ _).2.1⟩
    · rintro ⟨st1, cs1, pt1⟩ hinv1
      refine okPost_spec (Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac)) ?_
      intro k1 hk1
      refine okPost_ok ?_
      have : k1.val = k.val + 1 := by scalar_tac
      show PortalLoopInv specs ps st1 cs1 pt1 k1.val
      rw [this]; exact hinv1
  · exact okPost_ok hcs

/-! ### `Layout::new` -/

theorem cellOkS_cellOk (L : scene.Layout) (c : scene.Cell)
    (h : CellOkS (L.circles.val.map (·.spec)) L.portals.val c) : CellOk L c := by
  cases c with
  | Grid a b r => exact h
  | Center k => simpa [CellOkS, CellOk] using h
  | Sector k r s =>
    obtain ⟨h1, h2, h3⟩ := h
    have h1' : k.val < L.circles.val.length := by simpa using h1
    refine ⟨h1', by simpa using h2, by simpa using h3⟩
  | Transition p =>
    obtain ⟨hp, h1, h2⟩ := h
    exact ⟨hp, by simpa using h1, h2⟩

theorem keys_get {l l' : List polar.Circle} (h : l.map circleKey = l'.map circleKey) (i : Nat)
    (hi : i < l.length) (hi' : i < l'.length) : circleKey (l[i]'hi) = circleKey (l'[i]'hi') := by
  have := congrArg (fun l => l[i]?) h
  simpa [hi, hi'] using this

theorem okPost_branch_err {T β : Type _} {Q : β → Prop} (e : topology.Error)
    (k : core.ops.control_flow.ControlFlow (core.result.Result Never topology.Error) T → Result β)
    (hk : OkPost (k (.Break (.Err e))) Q) :
    OkPost (Std.bind (core.result.Result.Insts.CoreOpsTry.branch (.Err e : core.result.Result T topology.Error)) k) Q := by
  have h : core.result.Result.Insts.CoreOpsTry.branch (.Err e : core.result.Result T topology.Error) =
      ok (.Break (.Err e)) := rfl
  rw [h, Std.bind_ok]; exact hk

theorem okPost_branch_ok {T β : Type _} {Q : β → Prop} (v : T)
    (k : core.ops.control_flow.ControlFlow (core.result.Result Never topology.Error) T → Result β)
    (hk : OkPost (k (.Continue v)) Q) :
    OkPost (Std.bind (core.result.Result.Insts.CoreOpsTry.branch (.Ok v : core.result.Result T topology.Error)) k) Q := by
  have h : core.result.Result.Insts.CoreOpsTry.branch (.Ok v : core.result.Result T topology.Error) =
      ok (.Continue v) := rfl
  rw [h, Std.bind_ok]; exact hk

/-- Every layout `Layout::new` accepts satisfies `LayoutGeom`: the invariant the doorway and sweep
totality theorems assume is established by the validators. -/
theorem layout_new_geom (grid_spec : grid.GridSpec) (specs : alloc.vec.Vec polar.PolarSpec)
    (ps : Slice polar.PortalSpec) (geometry : grid.Geometry) :
    OkPost (scene.Layout.new grid_spec specs ps geometry)
      (fun r => ∀ L, r = .Ok L → LayoutGeom L ∧ CarrierValid L.carrier) := by
  unfold scene.Layout.new
  have hres : ∀ (residual : core.result.Result Never topology.Error),
      OkPost (core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual scene.Layout
        (core.convert.FromSame topology.Error) residual)
        (fun r => ∀ L, r = .Ok L → LayoutGeom L ∧ CarrierValid L.carrier) :=
    fun residual => okPost_residual_gen residual (fun e L h => by cases h)
  refine okPost_any (fun r => ?_)
  cases r with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u =>
  refine okPost_branch_ok u _ ?_
  refine okPost_spec (grid_geometry_margin_spec geometry) ?_
  rintro r1 ⟨hm1, hm2, hm3⟩
  cases r1 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok m =>
  refine okPost_branch_ok m _ ?_
  obtain ⟨hmg, hmv⟩ := hm1 m rfl
  have hmg' := hmg; unfold MarginOk at hmg'
  have hm : 0 < m.val ∧ m.val ≤ 1000000 := by omega
  refine okPost_any (fun i => ?_)
  by_cases hcs : grid_spec.cell_size < i <;> simp only [hcs, ↓reduceIte]
  · exact okPost_ok (fun L h => by cases h)
  refine okPost_any (fun r2 => ?_)
  cases r2 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok val1 =>
  refine okPost_branch_ok val1 _ ?_
  refine okPost_any (fun r3 => ?_)
  cases r3 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u3 =>
  refine okPost_branch_ok u3 _ ?_
  refine okPost_any (fun r4 => ?_)
  cases r4 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u4 =>
  refine okPost_branch_ok u4 _ ?_
  refine okPost_any (fun iter => ?_)
  refine okPost_bind (layout_new_loop0_ok iter m _ 0#usize (.Ok ()) hm
    (fun i h => by simp [alloc.vec.Vec.with_capacity] at h)) ?_
  rintro ⟨circles1, transforms, status⟩ hc1
  simp only at hc1
  cases status with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u5 =>
  refine okPost_branch_ok u5 _ ?_
  refine okPost_spec (alloc.vec.from_elem_spec core.clone.CloneI32 0#i32 _ rfl) ?_
  rintro bands ⟨hbv, hbl⟩
  refine okPost_any (fun counts => ?_)
  have hb0 : BandsOk bands.val circles1.val.length := by
    refine ⟨by simp [hbv], fun k hk => ?_⟩
    simp [hbv]
  refine okPost_bind (layout_new_loop1_ok ps m circles1 _ bands counts 0#usize hm hb0
    (fun _ j _ hj => by simp at hj)) ?_
  rintro ⟨status1, bands1, counts1⟩ ⟨hb1, hp1⟩
  simp only at hb1 hp1
  cases status1 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u6 =>
  have hp1' := hp1 (by cases u6; rfl)
  refine okPost_branch_ok u6 _ ?_
  refine okPost_bind (layout_new_loop2_ok m circles1 _ bands1 counts1 0#usize hb1.1
    (fun _ j _ _ hj => by simp at hj)) ?_
  intro status2 hs2
  cases status2 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u7 =>
  have hext := hs2 (by cases u7; rfl)
  refine okPost_branch_ok u7 _ ?_
  refine okPost_bind (layout_new_loop3_ok _ _ geometry val1 circles1 bands1 _ 0#usize
    (fun c hc => by simp [alloc.vec.Vec.new] at hc)) ?_
  rintro ⟨cell_grid, cells⟩ hcells
  simp only at hcells
  refine okPost_bind (layout_new_loop4_ok circles1 cells 0#usize (circles1.val.map circleKey) rfl
    (fun c hc => by
      obtain ⟨a, b, r, rfl, hr⟩ := hcells c hc
      exact hr)) ?_
  rintro ⟨circles2, cells1⟩ ⟨hk2, hc2⟩
  simp only at hk2 hc2
  have hlen2 : circles2.val.length = circles1.val.length := by
    have := congrArg List.length hk2; simpa using this
  refine okPost_bind (layout_new_loop5_ok ps cell_grid _ cells1 _ 0#usize
    ((circles1.val.map circleKey).map (·.1))
    (fun j h => by simpa using hp1' j h)
    ⟨fun _ => by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new],
     fun j h => by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] at h,
     fun c hc => by simpa [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new] using hc2 c hc⟩) ?_
  rintro ⟨status3, cells2, portals1⟩ hc3
  simp only at hc3
  cases status3 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u8 =>
  refine okPost_branch_ok u8 _ ?_
  refine okPost_any (fun b => ?_)
  cases b
  case true => simp only [↓reduceIte]; exact okPost_ok (fun L h => by cases h)
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine okPost_any (fun o => okPost_any (fun r5 => ?_))
  cases r5 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u9 =>
  refine okPost_branch_ok u9 _ ?_
  refine okPost_any (fun _ => okPost_any (fun _ => okPost_any (fun _ => ?_)))
  refine okPost_spec (constructor_carrier_from_edges_total_spec _ _) (fun r6 hr6 => ?_)
  cases r6 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok carrier =>
  refine okPost_branch_ok carrier _ ?_
  refine okPost_any (fun _ => okPost_any (fun r7 => ?_))
  cases r7 with
  | Err e => exact okPost_branch_err e _ (hres _)
  | Ok u10 =>
  refine okPost_branch_ok u10 _ ?_
  refine okPost_ok (fun L hL => ?_)
  cases hL
  have hspecs := specs_of_keys hk2
  refine ⟨⟨hmg, fun i h => ?_, by simp [hb1.1, hlen2], fun i h h2 => ?_, fun i h => ?_⟩, hr6⟩
  · simp only at h
    have hi1 : i < circles1.val.length := by omega
    have hkey := keys_get hk2 i h hi1
    simp only [circleKey, Prod.mk.injEq] at hkey
    exact (hc1 i hi1).congr hkey.1 hkey.2.1 hkey.2.2
  · simp only at h h2
    have hi1 : i < circles1.val.length := by omega
    have hkey := keys_get hk2 i h2 hi1
    simp only [circleKey, Prod.mk.injEq] at hkey
    refine ⟨hb1.2 i h, ?_⟩
    rw [hkey.2.1]
    exact hext i hi1 h hi1
  · apply cellOkS_cellOk
    simp only
    rw [hspecs]
    exact hc3 _ (List.getElem_mem h)

/-- For a layout accepted by `Layout::new`, `doorway` returns for every edge and phase vectors
covering the layout's transforms; no geometry assumption remains. -/
theorem layout_new_doorway_total (grid_spec : grid.GridSpec) (specs : alloc.vec.Vec polar.PolarSpec)
    (ps : Slice polar.PortalSpec) (geometry : grid.Geometry) (L : scene.Layout)
    (hnew : scene.Layout.new grid_spec specs ps geometry = ok (.Ok L))
    (edge : topology.Edge) (phases next : Slice Std.I32)
    (hph : L.transforms.val ≤ phases.val.length) (hnext : L.transforms.val ≤ next.val.length) :
    ∃ r, scene.Layout.doorway L edge phases next = ok r ∧ DoorwayOk L edge r := by
  obtain ⟨hg, hc⟩ := layout_new_geom grid_spec specs ps geometry _ hnew L rfl
  obtain ⟨r, hr, hok, _⟩ := layout_doorway_total L hg hc edge phases next hph hnext
  exact ⟨r, hr, hok⟩

end Labyrinth
