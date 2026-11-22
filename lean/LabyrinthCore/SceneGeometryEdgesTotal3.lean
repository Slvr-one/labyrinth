module
public import LabyrinthCore.SceneGeometryEdgesTotal

/-! Geometry totality, the edge loops of `Layout::new`: `new_loop6` (grid adjacency),
`new_loop7` (ring and sector adjacency) and `new_loop8` (portal doorways) return when the edge
vector has room for the edges they push. Each sector contributes at most `2049` edges and each portal
at most `2049`, so the vector stays within `Usize.max` once the cell count satisfies the product check
that precedes them. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

/-- `push_edge` appends one edge when the vector is not full. -/
theorem push_edge_spec (edges : alloc.vec.Vec topology.Edge) (u v : Std.Usize)
    (h : edges.val.length < Std.Usize.max) :
    scene.push_edge edges u v ⦃ r => r.val.length = edges.val.length + 1 ⦄ := by
  unfold scene.push_edge topology.Edge.new
  split_ifs
  · simp only [Std.bind_ok]
    step as ⟨v1, hv1⟩
    simp [hv1]
  · simp only [Std.bind_ok]
    step as ⟨v1, hv1⟩
    simp [hv1]

/-! ### Loop 7: ring and sector adjacency -/

theorem sectorsFrom_past_end (cs : List polar.Circle) (ci : Nat) (h : cs.length ≤ ci) :
    sectorsFrom cs ci = 0 := by
  unfold sectorsFrom
  rw [List.drop_of_length_le h]
  simp

theorem layout_new_loop7_inner_total (edges : alloc.vec.Vec topology.Edge) (here inner_sectors inner_start inner : Std.Usize)
    (hpos : inner_start.val + inner_sectors.val ≤ Std.Usize.max)
    (hcap : edges.val.length + (inner_sectors.val - inner.val) ≤ Std.Usize.max) :
    scene.Layout.new_loop7_loop0_loop0_loop0 edges here inner_sectors inner_start inner ⦃ r =>
      r.val.length = edges.val.length + (inner_sectors.val - inner.val) ⦄ := by
  unfold scene.Layout.new_loop7_loop0_loop0_loop0
  apply loop.spec_decr_nat
    (fun st : alloc.vec.Vec topology.Edge × Std.Usize => inner_sectors.val - st.2.val)
    (fun st : alloc.vec.Vec topology.Edge × Std.Usize =>
      st.1.val.length + (inner_sectors.val - st.2.val) = edges.val.length + (inner_sectors.val - inner.val))
    _
  · rintro ⟨es, k⟩ hlen
    simp only at hlen
    unfold scene.Layout.new_loop7_loop0_loop0_loop0.body
    by_cases hlt : k < inner_sectors
    · simp only [hlt, ↓reduceIte]
      have hlt' : k.val < inner_sectors.val := hlt
      step as ⟨i, hi⟩
      have hes : es.val.length < Std.Usize.max := by omega
      step with push_edge_spec es here i hes as ⟨es1, hes1⟩
      step as ⟨k1, hk1⟩
      refine ⟨?_, ?_⟩
      · omega
      · omega
    · simp only [hlt, ↓reduceIte, spec_ok]
      have : ¬ k.val < inner_sectors.val := hlt
      omega
  · rfl

theorem edges_cond_push (es : alloc.vec.Vec topology.Edge) (here next sectors sec : Std.Usize)
    (h : es.val.length < Std.Usize.max) :
    ∃ es1, (if sectors > 2#usize then scene.push_edge es here next
      else if sec = 0#usize then scene.push_edge es here next else ok es) = ok es1 ∧
      es1.val.length ≤ es.val.length + 1 := by
  by_cases h2 : sectors > 2#usize
  · simp only [h2, ↓reduceIte]
    obtain ⟨es1, he, hl⟩ := spec_exists_ok (push_edge_spec es here next h)
    exact ⟨es1, he, by omega⟩
  · by_cases h3 : sec = 0#usize
    · simp only [h2, h3, ↓reduceIte]
      obtain ⟨es1, he, hl⟩ := spec_exists_ok (push_edge_spec es here next h)
      exact ⟨es1, he, by omega⟩
    · simp only [h2, h3, ↓reduceIte]
      exact ⟨es, rfl, by omega⟩

theorem layout_new_loop7_sectors_total (circles : alloc.vec.Vec polar.Circle)
    (edges : alloc.vec.Vec topology.Edge) (ci center_cell ring sectors ring_start sector : Std.Usize)
    (c : polar.Circle) (hc : circles.val[ci.val]? = some c) (N : Nat) (hN : N ≤ Std.Usize.max)
    (hco : ∀ j (h : j < c.spec.sectors.val.length), (c.spec.sectors.val[j]'h).val ≤ 2048)
    (hpl : Placed N c) (hring : ring.val < c.spec.sectors.val.length)
    (hrs : ring_start.val + sectors.val ≤ Std.Usize.max)
    (hcap : edges.val.length + 2049 * (sectors.val - sector.val) ≤ Std.Usize.max) :
    scene.Layout.new_loop7_loop0_loop0 circles edges ci center_cell ring sectors ring_start sector ⦃ r =>
      r.val.length ≤ edges.val.length + 2049 * (sectors.val - sector.val) ⦄ := by
  unfold scene.Layout.new_loop7_loop0_loop0
  have hci : ci.val < circles.val.length := (List.getElem?_eq_some_iff.mp hc).1
  have hcc : circles.val[ci.val]'hci = c := (List.getElem?_eq_some_iff.mp hc).2
  apply loop.spec_decr_nat
    (fun st : alloc.vec.Vec topology.Edge × Std.Usize => sectors.val - st.2.val)
    (fun st : alloc.vec.Vec topology.Edge × Std.Usize =>
      st.1.val.length + 2049 * (sectors.val - st.2.val) ≤
        edges.val.length + 2049 * (sectors.val - sector.val))
    _
  · rintro ⟨es, sec⟩ hlen
    simp only at hlen
    unfold scene.Layout.new_loop7_loop0_loop0.body
    by_cases hlt : sec < sectors
    · simp only [hlt, ↓reduceIte]
      have hlt' : sec.val < sectors.val := hlt
      step as ⟨here, hhere⟩
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < sectors.val := by rw [hi1]; exact Nat.mod_lt _ (by omega)
      step as ⟨next, hnext⟩
      have hes : es.val.length < Std.Usize.max := by omega
      obtain ⟨es1, hes1, hes1l⟩ := edges_cond_push es here next sectors sec hes
      rw [hes1, Std.bind_ok]
      by_cases hr0 : ring = 0#usize
      · simp only [hr0, ↓reduceIte]
        have hes1' : es1.val.length < Std.Usize.max := by omega
        step with push_edge_spec es1 here center_cell hes1' as ⟨es2, hes2⟩
        refine ⟨?_, ?_⟩
        · have hiv : i.val = sec.val + 1 := hi
          omega
        · have hiv : i.val = sec.val + 1 := hi
          omega
      · simp only [hr0, ↓reduceIte]
        have hring0 : ring.val ≠ 0 := fun h => hr0 (UScalar.eq_of_val_eq (by simpa using h))
        step as ⟨c1, hc1⟩
        have hc1' : c1 = c := hc1.trans hcc
        subst hc1'
        step as ⟨i2, hi2⟩
        have hi2v : i2.val = ring.val - 1 := hi2
        have hi2l : i2.val < c1.spec.sectors.val.length := by omega
        step as ⟨inner_sectors, hins⟩
        have hi2r : i2.val < c1.ring_starts.val.length := by rw [hpl.2.1]; exact hi2l
        step as ⟨inner_start, hinst⟩
        have hpos : inner_start.val + inner_sectors.val ≤ Std.Usize.max := by
          have := hpl.2.2 i2.val hi2r hi2l (by omega)
          rw [hins, hinst]
          omega
        have hco2 : inner_sectors.val ≤ 2048 := by rw [hins]; exact hco _ hi2l
        have hcap2 : es1.val.length + (inner_sectors.val - (0#usize).val) ≤ Std.Usize.max := by
          have h0 : (0#usize).val = 0 := by simp
          rw [h0]; omega
        step with layout_new_loop7_inner_total es1 here inner_sectors inner_start 0#usize hpos hcap2
          as ⟨es2, hes2⟩
        step as ⟨sector1, hs1⟩
        have hiv : sector1.val = sec.val + 1 := hs1
        have h0 : (0#usize).val = 0 := by simp
        refine ⟨?_, ?_⟩
        · omega
        · omega
    · simp only [hlt, ↓reduceIte, spec_ok]
      have : ¬ sec.val < sectors.val := hlt
      omega
  · exact le_refl _

theorem layout_new_loop7_rings_total (circles : alloc.vec.Vec polar.Circle)
    (edges : alloc.vec.Vec topology.Edge) (ci ring_count center_cell ring : Std.Usize)
    (c : polar.Circle) (hc : circles.val[ci.val]? = some c) (N : Nat) (hN : N ≤ Std.Usize.max)
    (hco : ∀ j (h : j < c.spec.sectors.val.length), (c.spec.sectors.val[j]'h).val ≤ 2048)
    (hpl : Placed N c) (hrc : ring_count.val = c.spec.sectors.val.length)
    (hcap : edges.val.length + 2049 * ringSum c ring.val ≤ Std.Usize.max) :
    scene.Layout.new_loop7_loop0 circles edges ci ring_count center_cell ring ⦃ r =>
      r.val.length ≤ edges.val.length + 2049 * ringSum c ring.val ⦄ := by
  unfold scene.Layout.new_loop7_loop0
  have hci : ci.val < circles.val.length := (List.getElem?_eq_some_iff.mp hc).1
  have hcc : circles.val[ci.val]'hci = c := (List.getElem?_eq_some_iff.mp hc).2
  apply loop.spec_decr_nat
    (fun st : alloc.vec.Vec topology.Edge × Std.Usize => c.spec.sectors.val.length - st.2.val)
    (fun st : alloc.vec.Vec topology.Edge × Std.Usize =>
      st.1.val.length + 2049 * ringSum c st.2.val ≤ edges.val.length + 2049 * ringSum c ring.val)
    _
  · rintro ⟨es, rg⟩ hlen
    simp only at hlen
    unfold scene.Layout.new_loop7_loop0.body
    by_cases hlt : rg < ring_count
    · simp only [hlt, ↓reduceIte]
      have hlt' : rg.val < c.spec.sectors.val.length := by
        have : rg.val < ring_count.val := hlt
        omega
      step as ⟨c1, hc1⟩
      have hc1' : c1 = c := hc1.trans hcc
      subst hc1'
      step as ⟨sectors, hsec⟩
      have hrr : rg.val < c1.ring_starts.val.length := by rw [hpl.2.1]; exact hlt'
      step as ⟨ring_start, hrst⟩
      have hrs : ring_start.val + sectors.val ≤ Std.Usize.max := by
        have := hpl.2.2 rg.val hrr hlt' hlt'
        rw [hsec, hrst]; omega
      have hsum := ringSum_succ c1 rg.val hlt'
      have hsv : sectors.val = (c1.spec.sectors.val[rg.val]'hlt').val := by rw [hsec]
      have h0 : (0#usize).val = 0 := by simp
      have hcap2 : es.val.length + 2049 * (sectors.val - (0#usize).val) ≤ Std.Usize.max := by
        rw [h0]; omega
      step with layout_new_loop7_sectors_total circles es ci center_cell rg sectors ring_start
        0#usize c1 hc N hN hco hpl hlt' hrs hcap2 as ⟨es2, hes2⟩
      step as ⟨rg1, hrg1⟩
      have hrg1v : rg1.val = rg.val + 1 := hrg1
      refine ⟨?_, ?_⟩
      · rw [hrg1v]; omega
      · omega
    · simp only [hlt, ↓reduceIte, spec_ok]
      have : ¬ rg.val < ring_count.val := hlt
      have hrg : c.spec.sectors.val.length ≤ rg.val := by omega
      rw [ringSum_of_ge c rg.val hrg] at hlen
      have := ringSum_ge c
      omega
  · exact le_refl _

theorem layout_new_loop7_total (circles : alloc.vec.Vec polar.Circle)
    (edges : alloc.vec.Vec topology.Edge) (ci : Std.Usize) (T N : Nat) (hN : N ≤ Std.Usize.max)
    (hcs : CirclesOk circles.val T) (hpl : ∀ c ∈ circles.val, Placed N c)
    (hcap : edges.val.length + 2049 * sectorsFrom circles.val ci.val ≤ Std.Usize.max) :
    scene.Layout.new_loop7 circles edges ci ⦃ r =>
      r.val.length ≤ edges.val.length + 2049 * sectorsFrom circles.val ci.val ⦄ := by
  unfold scene.Layout.new_loop7
  apply loop.spec_decr_nat
    (fun st : alloc.vec.Vec topology.Edge × Std.Usize => circles.val.length - st.2.val)
    (fun st : alloc.vec.Vec topology.Edge × Std.Usize =>
      st.1.val.length + 2049 * sectorsFrom circles.val st.2.val ≤
        edges.val.length + 2049 * sectorsFrom circles.val ci.val)
    _
  · rintro ⟨es, k⟩ hlen
    simp only at hlen
    unfold scene.Layout.new_loop7.body
    simp only [alloc.vec.Vec.index_slice_index]
    by_cases hlt : k < alloc.vec.Vec.len circles
    · simp only [hlt, ↓reduceIte]
      have hk : k.val < circles.val.length := by scalar_tac
      step as ⟨c, hc⟩
      have hcget : circles.val[k.val]? = some c := by rw [hc]; simp [hk]
      step as ⟨rc, hrc⟩
      have hsum := sectorsFrom_succ circles.val k.val hk
      rw [← hc] at hsum
      have h0 : (0#usize).val = 0 := by simp
      have hcap2 : es.val.length + 2049 * ringSum c (0#usize).val ≤ Std.Usize.max := by
        rw [h0]; simp only [sectorSum] at hsum; omega
      have hco : ∀ j (h : j < c.spec.sectors.val.length), (c.spec.sectors.val[j]'h).val ≤ 2048 := by
        intro j h
        have := (hcs k.val hk).sectors j (by rw [← hc]; exact h)
        simpa [hc] using this.2
      step with layout_new_loop7_rings_total circles es k rc c.center_cell 0#usize c hcget N hN hco
        (hpl c (by rw [hc]; exact List.getElem_mem hk)) hrc hcap2 as ⟨es2, hes2⟩
      step as ⟨k1, hk1⟩
      have hk1v : k1.val = k.val + 1 := hk1
      refine ⟨?_, ?_⟩
      · rw [hk1v]; simp only [sectorSum] at hsum; omega
      · omega
    · simp only [hlt, ↓reduceIte, spec_ok]
      have hge : circles.val.length ≤ k.val := by
        by_contra hcon; exact hlt (by simp only [alloc.vec.Vec.len]; scalar_tac)
      rw [sectorsFrom_past_end circles.val k.val hge] at hlen
      omega
  · exact le_refl _

/-! ### Loop 8: portal doorways -/

theorem layout_new_loop8_inner_total (edges : alloc.vec.Vec topology.Edge) (i : Std.Usize)
    (circle : polar.Circle) (ring sector : Std.Usize) (N : Nat) (hN : N ≤ Std.Usize.max)
    (hpl : Placed N circle) (hring : ring.val < circle.spec.sectors.val.length)
    (hcap : edges.val.length + ((circle.spec.sectors.val[ring.val]'hring).val - sector.val)
      ≤ Std.Usize.max) :
    scene.Layout.new_loop8_loop0 edges i circle ring sector ⦃ r =>
      r.val.length = edges.val.length +
        ((circle.spec.sectors.val[ring.val]'hring).val - sector.val) ⦄ := by
  unfold scene.Layout.new_loop8_loop0
  obtain ⟨cnt, hcnt⟩ : ∃ cnt, circle.spec.sectors.val[ring.val]'hring = cnt := ⟨_, rfl⟩
  rw [hcnt] at hcap ⊢
  have hrr : ring.val < circle.ring_starts.val.length := by rw [hpl.2.1]; exact hring
  apply loop.spec_decr_nat
    (fun st : alloc.vec.Vec topology.Edge × Std.Usize => cnt.val - st.2.val)
    (fun st : alloc.vec.Vec topology.Edge × Std.Usize =>
      st.1.val.length + (cnt.val - st.2.val) = edges.val.length + (cnt.val - sector.val))
    _
  · rintro ⟨es, k⟩ hlen
    simp only at hlen
    unfold scene.Layout.new_loop8_loop0.body
    simp only [alloc.vec.Vec.index_slice_index]
    step as ⟨i1, hi1⟩
    have hi1' : i1 = cnt := by rw [hi1]; exact hcnt
    subst hi1'
    by_cases hlt : k < i1
    · simp only [hlt, ↓reduceIte]
      have hlt' : k.val < i1.val := hlt
      step as ⟨i2, hi2⟩
      have hi2' := hpl.2.2 ring.val hrr hring hring
      have hi2v : i2.val + i1.val ≤ N := by
        rw [hi2]; rw [← hcnt]; exact hi2'
      step as ⟨i3, hi3⟩
      have hes : es.val.length < Std.Usize.max := by omega
      step with push_edge_spec es i i3 hes as ⟨es1, hes1⟩
      step as ⟨k1, hk1⟩
      refine ⟨?_, ?_⟩
      · omega
      · omega
    · simp only [hlt, ↓reduceIte, spec_ok]
      have : ¬ k.val < i1.val := hlt
      omega
  · rfl

theorem layout_new_loop8_total (circles : alloc.vec.Vec polar.Circle)
    (portals : alloc.vec.Vec scene.Portal) (edges : alloc.vec.Vec topology.Edge) (i : Std.Usize)
    (T N : Nat) (hN : N ≤ Std.Usize.max) (hcs : CirclesOk circles.val T)
    (hpl : ∀ c ∈ circles.val, Placed N c)
    (hpc : ∀ p ∈ portals.val, p.spec.circle.val < circles.val.length)
    (hcap : edges.val.length + 2049 * (portals.val.length - i.val) ≤ Std.Usize.max) :
    scene.Layout.new_loop8 circles portals edges i ⦃ r =>
      r.val.length ≤ edges.val.length + 2049 * (portals.val.length - i.val) ⦄ := by
  unfold scene.Layout.new_loop8
  apply loop.spec_decr_nat
    (fun st : alloc.vec.Vec topology.Edge × Std.Usize => portals.val.length - st.2.val)
    (fun st : alloc.vec.Vec topology.Edge × Std.Usize =>
      st.1.val.length + 2049 * (portals.val.length - st.2.val) ≤
        edges.val.length + 2049 * (portals.val.length - i.val))
    _
  · rintro ⟨es, k⟩ hlen
    simp only at hlen
    unfold scene.Layout.new_loop8.body
    simp only [alloc.vec.Vec.index_slice_index]
    by_cases hlt : k < alloc.vec.Vec.len portals
    · simp only [hlt, ↓reduceIte]
      have hk : k.val < portals.val.length := by scalar_tac
      step as ⟨portal, hportal⟩
      have hpcirc : portal.spec.circle.val < circles.val.length := by
        apply hpc; rw [hportal]; exact List.getElem_mem hk
      step as ⟨circle, hcirc⟩
      have hcm : circle ∈ circles.val := by rw [hcirc]; exact List.getElem_mem hpcirc
      have hco := hcs
      have hcok : CircleOk circle T := by
        have := hcs portal.spec.circle.val hpcirc
        rw [← hcirc] at this; exact this
      have hes : es.val.length < Std.Usize.max := by omega
      step with push_edge_spec es portal.grid_cell portal.transition_cell hes as ⟨es1, hes1⟩
      step as ⟨i2, hi2⟩
      have hrings := hcok.rings
      step as ⟨ring, hring⟩
      have hringv : ring.val = circle.spec.sectors.val.length - 1 := by omega
      have hring2 : ring.val < circle.spec.sectors.val.length := by omega
      have hsec2048 := (hcok.sectors ring.val hring2).2
      have h0 : (0#usize).val = 0 := by simp
      have hcap2 : es1.val.length + ((circle.spec.sectors.val[ring.val]'hring2).val -
          (0#usize).val) ≤ Std.Usize.max := by rw [h0]; omega
      step with layout_new_loop8_inner_total es1 portal.transition_cell circle ring 0#usize N hN
        (hpl circle hcm) hring2 hcap2 as ⟨es2, hes2⟩
      step as ⟨k1, hk1⟩
      refine ⟨?_, ?_⟩
      · omega
      · omega
    · simp only [hlt, ↓reduceIte, spec_ok]
      have hge : portals.val.length ≤ k.val := by
        by_contra hcon; exact hlt (by simp only [alloc.vec.Vec.len]; scalar_tac)
      omega
  · exact le_refl _

/-! ### Loop 6: grid adjacency -/

theorem layout_new_loop6_down (cell_grid : grid.Grid) (cell column row : Std.Usize)
    (es : alloc.vec.Vec topology.Edge) (hrow : row.val < Std.Usize.max)
    (hcell : ∀ c r, ∃ o, grid.Grid.cell cell_grid c r = ok o)
    (hes : es.val.length < Std.Usize.max) :
    (do
      let i2 ← row + 1#usize
      let o1 ← grid.Grid.cell cell_grid column i2
      match o1 with
      | none => ok es
      | some down => scene.push_edge es cell down) ⦃ r => r.val.length ≤ es.val.length + 1 ⦄ := by
  step as ⟨i2, hi2⟩
  obtain ⟨o1, ho1⟩ := hcell column i2
  rw [ho1, Std.bind_ok]
  cases o1 with
  | none => simp only [spec_ok]; omega
  | some down =>
    simp only []
    step with push_edge_spec es cell down hes as ⟨es1, hes1⟩
    omega

theorem layout_new_loop6_block (cell_grid : grid.Grid) (cell column row : Std.Usize)
    (es : alloc.vec.Vec topology.Edge) (hcol : column.val < Std.Usize.max)
    (hrow : row.val < Std.Usize.max) (hcell : ∀ c r, ∃ o, grid.Grid.cell cell_grid c r = ok o)
    (hes : es.val.length + 2 ≤ Std.Usize.max) :
    (do
      let i1 ← column + 1#usize
      let o ← grid.Grid.cell cell_grid i1 row
      let edges2 ←
        match o with
        | none => ok es
        | some right => scene.push_edge es cell right
      let i2 ← row + 1#usize
      let o1 ← grid.Grid.cell cell_grid column i2
      match o1 with
      | none => ok edges2
      | some down => scene.push_edge edges2 cell down) ⦃ r => r.val.length ≤ es.val.length + 2 ⦄ := by
  step as ⟨i1, hi1⟩
  obtain ⟨o, ho⟩ := hcell i1 row
  rw [ho, Std.bind_ok]
  cases o with
  | none =>
    simp only [Std.bind_ok]
    apply spec_mono (layout_new_loop6_down cell_grid cell column row es hrow hcell (by omega))
    intro r hr; omega
  | some right =>
    simp only []
    step with push_edge_spec es cell right (by omega) as ⟨es1, hes1⟩
    apply spec_mono (layout_new_loop6_down cell_grid cell column row es1 hrow hcell (by omega))
    intro r hr; omega

theorem layout_new_loop6_total (cell_grid : grid.Grid) (cells : alloc.vec.Vec scene.Cell)
    (edges : alloc.vec.Vec topology.Edge) (cell : Std.Usize)
    (hcell : ∀ c r, ∃ o, grid.Grid.cell cell_grid c r = ok o)
    (hg : GridIdx cells.val Std.Usize.max Std.Usize.max)
    (hcap : edges.val.length + 2 * (cells.val.length - cell.val) ≤ Std.Usize.max) :
    scene.Layout.new_loop6 cell_grid cells edges cell ⦃ r =>
      r.val.length ≤ edges.val.length + 2 * (cells.val.length - cell.val) ⦄ := by
  unfold scene.Layout.new_loop6
  apply loop.spec_decr_nat
    (fun st : alloc.vec.Vec topology.Edge × Std.Usize => cells.val.length - st.2.val)
    (fun st : alloc.vec.Vec topology.Edge × Std.Usize =>
      st.1.val.length + 2 * (cells.val.length - st.2.val) ≤
        edges.val.length + 2 * (cells.val.length - cell.val))
    _
  · rintro ⟨es, k⟩ hlen
    simp only at hlen
    unfold scene.Layout.new_loop6.body
    simp only [alloc.vec.Vec.index_slice_index]
    by_cases hlt : k < alloc.vec.Vec.len cells
    · simp only [hlt, ↓reduceIte]
      have hk : k.val < cells.val.length := by scalar_tac
      step as ⟨c, hc⟩
      have hcm : c ∈ cells.val := by rw [hc]; exact List.getElem_mem hk
      have hesc : es.val.length + 2 ≤ Std.Usize.max := by omega
      cases c with
      | Grid column row b =>
        obtain ⟨hcol, hrow⟩ := hg _ hcm column row b rfl
        simp only []
        refine spec_bind (layout_new_loop6_block cell_grid k column row es hcol hrow hcell hesc) ?_
        intro es1 hl
        step as ⟨k1, hk1⟩
        refine ⟨?_, ?_⟩ <;> omega
      | Center a =>
        simp only [Std.bind_ok]
        step as ⟨k1, hk1⟩
        refine ⟨?_, ?_⟩ <;> omega
      | Sector a b d =>
        simp only [Std.bind_ok]
        step as ⟨k1, hk1⟩
        refine ⟨?_, ?_⟩ <;> omega
      | Transition a =>
        simp only [Std.bind_ok]
        step as ⟨k1, hk1⟩
        refine ⟨?_, ?_⟩ <;> omega
    · simp only [hlt, ↓reduceIte, spec_ok]
      have hge : cells.val.length ≤ k.val := by
        by_contra hcon; exact hlt (by simp only [alloc.vec.Vec.len]; scalar_tac)
      omega
  · exact le_refl _

/-! ### The three edge loops together -/

theorem circlesOk_of_keys {cs cs' : List polar.Circle} {T : Nat}
    (h : cs.map circleKey = cs'.map circleKey) (hc : CirclesOk cs T) : CirclesOk cs' T := by
  have hl : cs.length = cs'.length := by simpa using congrArg List.length h
  intro i hi
  have hi' : i < cs.length := by omega
  have hkey := keys_get h i hi' hi
  simp only [circleKey, Prod.mk.injEq] at hkey
  exact (hc i hi').congr hkey.1.symm hkey.2.1.symm hkey.2.2.symm

/-- Cell counts after the circle loop and the portal loop bound the sector and portal counts. -/
theorem edges_sum_bound (circles circles2 : List polar.Circle) (n0 n1 n2 P : Nat)
    (hk : circles2.map circleKey = circles.map circleKey) (h1 : n1 = n0 + cellsFrom circles 0)
    (h2 : P + n1 ≤ n2) : sectorsFrom circles2 0 + P ≤ n2 := by
  rw [sectorsFrom_congr hk 0]
  have := sectorsFrom_le_cellsFrom circles 0
  omega

/-- `Layout::new_loop4` leaves every circle placed below the final cell count (partial form of
`layout_new_loop4_total`, for the capacity hypothesis it needs). -/
theorem layout_new_loop4_positions (circles : alloc.vec.Vec polar.Circle)
    (cells : alloc.vec.Vec scene.Cell) (hrs : RingStartsLen circles.val)
    (hcap : cells.val.length + cellsFrom circles.val 0 ≤ Std.Usize.max) :
    OkPost (scene.Layout.new_loop4 circles cells 0#usize) (fun r =>
      r.1.val.map circleKey = circles.val.map circleKey ∧
      (∀ c ∈ r.1.val, Placed r.2.val.length c) ∧
      r.2.val.length = cells.val.length + cellsFrom circles.val 0 ∧
      ∃ k, r.2.val = cells.val ++ k ∧ GridFree k) := by
  have h0 : (0#usize).val = 0 := by simp
  apply okPost_of_spec
  apply spec_mono (layout_new_loop4_total circles cells 0#usize hrs (by rw [h0]; exact hcap))
  rintro ⟨cl, cs⟩ ⟨hk, hpl, hlen, hex⟩
  rw [h0] at hlen
  refine ⟨hk, fun c hc => ?_, hlen, hex⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  exact hpl j hj (by omega)

/-- The edge loops of `Layout::new` all return, under the product bound that `Layout::new` checks
just before them: the grid adjacency loop, the ring/sector adjacency loop and the portal loop. The
cell vector carries `columns`/`rows` below `Usize.max` for its grid cells, every circle is placed below
the cell count, there are enough cells for every sector and portal, and every portal's circle exists. -/
theorem layout_new_edges_total (cell_grid : grid.Grid) (cells : alloc.vec.Vec scene.Cell)
    (circles : alloc.vec.Vec polar.Circle) (portals : alloc.vec.Vec scene.Portal) (T : Nat)
    (hc : cells.val.length * cells.val.length ≤ Std.Usize.max)
    (hcell : ∀ c r, ∃ o, grid.Grid.cell cell_grid c r = ok o)
    (hg : GridIdx cells.val Std.Usize.max Std.Usize.max)
    (hcs : CirclesOk circles.val T) (hpl : ∀ c ∈ circles.val, Placed cells.val.length c)
    (hpc : ∀ p ∈ portals.val, p.spec.circle.val < circles.val.length)
    (hsum : sectorsFrom circles.val 0 + portals.val.length ≤ cells.val.length) :
    ∃ e1 e2 e3, scene.Layout.new_loop6 cell_grid cells (alloc.vec.Vec.new topology.Edge) 0#usize = ok e1 ∧
      scene.Layout.new_loop7 circles e1 0#usize = ok e2 ∧
      scene.Layout.new_loop8 circles portals e2 0#usize = ok e3 ∧
      e3.val.length ≤ 2051 * cells.val.length := by
  have hN : cells.val.length ≤ Std.Usize.max := cells.property
  have hbig : 2051 * cells.val.length ≤ Std.Usize.max := by
    have hm := usize_max_ge
    by_cases hs : cells.val.length ≤ 2050
    · omega
    · have : 2051 * cells.val.length ≤ cells.val.length * cells.val.length :=
        Nat.mul_le_mul_right _ (by omega)
      omega
  have h0 : (0#usize).val = 0 := by simp
  have hnew : (alloc.vec.Vec.new topology.Edge).val.length = 0 := by simp [alloc.vec.Vec.new]
  obtain ⟨e1, he1, hl1⟩ := spec_exists_ok (layout_new_loop6_total cell_grid cells
    (alloc.vec.Vec.new topology.Edge) 0#usize hcell hg (by rw [h0, hnew]; omega))
  rw [h0, hnew] at hl1
  obtain ⟨e2, he2, hl2⟩ := spec_exists_ok (layout_new_loop7_total circles e1 0#usize T
    cells.val.length hN hcs hpl (by rw [h0]; omega))
  rw [h0] at hl2
  obtain ⟨e3, he3, hl3⟩ := spec_exists_ok (layout_new_loop8_total circles portals e2 0#usize T
    cells.val.length hN hcs hpl hpc (by rw [h0]; omega))
  rw [h0] at hl3
  exact ⟨e1, e2, e3, he1, he2, he3, by omega⟩

end Labyrinth
