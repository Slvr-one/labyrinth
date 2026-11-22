module
public import LabyrinthCore.SceneGeometryLayoutNew

/-! Geometry totality, cells of circles and portals: the center/ring/sector loops of
`Layout::new` (`new_loop4` and its inner loops) return when the cell vector has room for every cell
they add, and they leave each circle's `center_cell` and `ring_starts` pointing at the cells they
created: `center_cell < cells.len()` and `ring_starts[r] + sectors[r] <= cells.len()` for every ring. -/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result labyrinth_core
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Labyrinth

/-! ### Counting cells -/

/-- Sector cells of the rings `r..` of a circle. -/
def ringSum (c : polar.Circle) (r : Nat) : Nat :=
  ((c.spec.sectors.val.drop r).map (fun s => s.val)).sum

/-- All sector cells of a circle. -/
def sectorSum (c : polar.Circle) : Nat := ringSum c 0

/-- The center cell and all sector cells of a circle. -/
def circleCells (c : polar.Circle) : Nat := 1 + sectorSum c

/-- Cells of the circles `ci..`. -/
def cellsFrom (cs : List polar.Circle) (ci : Nat) : Nat := ((cs.drop ci).map circleCells).sum

/-- Sector cells of the circles `ci..`. -/
def sectorsFrom (cs : List polar.Circle) (ci : Nat) : Nat := ((cs.drop ci).map sectorSum).sum

theorem ringSum_succ (c : polar.Circle) (r : Nat) (h : r < c.spec.sectors.val.length) :
    ringSum c r = (c.spec.sectors.val[r]'h).val + ringSum c (r + 1) := by
  unfold ringSum
  rw [List.drop_eq_getElem_cons h]
  simp only [List.map_cons, List.sum_cons]

theorem ringSum_ge (c : polar.Circle) (r : Nat) (h : r < c.spec.sectors.val.length) :
    (c.spec.sectors.val[r]'h).val ≤ ringSum c r := by
  rw [ringSum_succ c r h]; omega

theorem ringSum_of_ge (c : polar.Circle) (r : Nat) (h : c.spec.sectors.val.length ≤ r) :
    ringSum c r = 0 := by
  unfold ringSum
  rw [List.drop_of_length_le h]
  simp

theorem cellsFrom_succ (cs : List polar.Circle) (ci : Nat) (h : ci < cs.length) :
    cellsFrom cs ci = circleCells (cs[ci]'h) + cellsFrom cs (ci + 1) := by
  unfold cellsFrom
  rw [List.drop_eq_getElem_cons h]
  simp only [List.map_cons, List.sum_cons]

theorem sectorsFrom_succ (cs : List polar.Circle) (ci : Nat) (h : ci < cs.length) :
    sectorsFrom cs ci = sectorSum (cs[ci]'h) + sectorsFrom cs (ci + 1) := by
  unfold sectorsFrom
  rw [List.drop_eq_getElem_cons h]
  simp only [List.map_cons, List.sum_cons]

theorem cellsFrom_of_ge (cs : List polar.Circle) (ci : Nat) (h : cs.length ≤ ci) :
    cellsFrom cs ci = 0 := by
  unfold cellsFrom
  rw [List.drop_of_length_le h]
  simp

theorem sectorsFrom_le_cellsFrom (cs : List polar.Circle) (ci : Nat) :
    sectorsFrom cs ci ≤ cellsFrom cs ci := by
  unfold sectorsFrom cellsFrom
  generalize cs.drop ci = l
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, circleCells]; omega

theorem circleKey_spec {c c' : polar.Circle} (h : circleKey c = circleKey c') : c.spec = c'.spec := by
  simp only [circleKey, Prod.mk.injEq] at h; exact h.1

theorem ringSum_congr {c c' : polar.Circle} (h : circleKey c = circleKey c') (r : Nat) :
    ringSum c r = ringSum c' r := by
  unfold ringSum; rw [circleKey_spec h]

theorem circleCells_congr {c c' : polar.Circle} (h : circleKey c = circleKey c') :
    circleCells c = circleCells c' := by
  unfold circleCells sectorSum; rw [ringSum_congr h]

theorem cellsFrom_congr {cs cs' : List polar.Circle} (h : cs.map circleKey = cs'.map circleKey)
    (ci : Nat) : cellsFrom cs ci = cellsFrom cs' ci := by
  have hl : cs.length = cs'.length := by simpa using congrArg List.length h
  unfold cellsFrom
  congr 1
  apply List.ext_getElem
  · simp [hl]
  · intro j h1 h2
    simp only [List.length_map, List.length_drop] at h1 h2
    simp only [List.getElem_map, List.getElem_drop]
    exact circleCells_congr (keys_get h (ci + j) (by omega) (by omega))

theorem sectorSum_congr {c c' : polar.Circle} (h : circleKey c = circleKey c') :
    sectorSum c = sectorSum c' := by
  unfold sectorSum; exact ringSum_congr h 0

theorem sectorsFrom_congr {cs cs' : List polar.Circle} (h : cs.map circleKey = cs'.map circleKey)
    (ci : Nat) : sectorsFrom cs ci = sectorsFrom cs' ci := by
  have hl : cs.length = cs'.length := by simpa using congrArg List.length h
  unfold sectorsFrom
  congr 1
  apply List.ext_getElem
  · simp [hl]
  · intro j h1 h2
    simp only [List.length_map, List.length_drop] at h1 h2
    simp only [List.getElem_map, List.getElem_drop]
    exact sectorSum_congr (keys_get h (ci + j) (by omega) (by omega))

/-! ### Positions of a circle's cells -/

/-- Every circle has one `ring_starts` entry per ring. -/
def RingStartsLen (cs : List polar.Circle) : Prop :=
  ∀ c ∈ cs, c.ring_starts.val.length = c.spec.sectors.val.length

/-- The center cell is below `n`, there is one start per ring, and the sector cells of each of the
first `r` rings end at or below `n`. -/
def PlacedTo (n r : Nat) (c : polar.Circle) : Prop :=
  c.center_cell.val < n ∧ c.ring_starts.val.length = c.spec.sectors.val.length ∧
  ∀ j (h1 : j < c.ring_starts.val.length) (h2 : j < c.spec.sectors.val.length), j < r →
    (c.ring_starts.val[j]'h1).val + (c.spec.sectors.val[j]'h2).val ≤ n

/-- Every ring of the circle is placed below `n`. -/
def Placed (n : Nat) (c : polar.Circle) : Prop := PlacedTo n c.spec.sectors.val.length c

theorem PlacedTo.mono {n n' r : Nat} {c : polar.Circle} (h : PlacedTo n r c) (hn : n ≤ n') :
    PlacedTo n' r c :=
  ⟨by have := h.1; omega, h.2.1, fun j h1 h2 hj => by have := h.2.2 j h1 h2 hj; omega⟩

theorem Placed.mono {n n' : Nat} {c : polar.Circle} (h : Placed n c) (hn : n ≤ n') :
    Placed n' c := PlacedTo.mono h hn

theorem PlacedTo.placed {n r : Nat} {c : polar.Circle} (h : PlacedTo n r c)
    (hr : c.spec.sectors.val.length ≤ r) : Placed n c :=
  ⟨h.1, h.2.1, fun j h1 h2 hj => h.2.2 j h1 h2 (by omega)⟩

theorem Placed.congr {n : Nat} {c c' : polar.Circle} (h : Placed n c)
    (hs : c'.spec = c.spec) (hr : c'.ring_starts = c.ring_starts) (hcc : c'.center_cell = c.center_cell) :
    Placed n c' := by
  obtain ⟨s1, cc1, rs1, ts1, o1⟩ := c
  obtain ⟨s2, cc2, rs2, ts2, o2⟩ := c'
  simp only at hs hr hcc
  subst hs hr hcc
  exact h

/-- The cells added beyond `old` are not grid cells. -/
def GridFree (l : List scene.Cell) : Prop := ∀ c ∈ l, ∀ a b d, c ≠ scene.Cell.Grid a b d

/-- Grid cells carry a column below `n` and a row below `m`. -/
def GridIdx (cs : List scene.Cell) (n m : Nat) : Prop :=
  ∀ c ∈ cs, ∀ col row b, c = scene.Cell.Grid col row b → col.val < n ∧ row.val < m

theorem GridIdx.append {cs k : List scene.Cell} {n m : Nat} (h : GridIdx cs n m) (hk : GridFree k) :
    GridIdx (cs ++ k) n m := by
  intro c hc col row b hcb
  rcases List.mem_append.mp hc with hc | hc
  · exact h c hc col row b hcb
  · exact absurd hcb (hk c hc col row b)

theorem GridFree.append {k k' : List scene.Cell} (h : GridFree k) (h' : GridFree k') :
    GridFree (k ++ k') := by
  intro c hc a b d
  rcases List.mem_append.mp hc with hc | hc
  · exact h c hc a b d
  · exact h' c hc a b d

theorem GridFree.singleton (c : scene.Cell) (h : ∀ a b d, c ≠ scene.Cell.Grid a b d) :
    GridFree [c] := by
  intro x hx a b d
  rw [List.mem_singleton] at hx
  subst hx; exact h a b d

theorem usize_max_ge : 4294967295 ≤ Std.Usize.max := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max, U64.max, U32.numBits, U64.numBits]

/-! ### The sector loop -/

theorem layout_new_loop4_sectors_total (circles : alloc.vec.Vec polar.Circle)
    (cells : alloc.vec.Vec scene.Cell) (ci ring sector : Std.Usize) (c : polar.Circle)
    (hc : circles.val[ci.val]? = some c) (hring : ring.val < c.spec.sectors.val.length)
    (hcap : cells.val.length + ((c.spec.sectors.val[ring.val]'hring).val - sector.val)
        ≤ Std.Usize.max) :
    scene.Layout.new_loop4_loop0_loop0 circles cells ci ring sector ⦃ r =>
      r.val.length = cells.val.length + ((c.spec.sectors.val[ring.val]'hring).val - sector.val) ∧
      ∃ k, r.val = cells.val ++ k ∧ GridFree k ⦄ := by
  unfold scene.Layout.new_loop4_loop0_loop0
  have hci : ci.val < circles.val.length := (List.getElem?_eq_some_iff.mp hc).1
  have hcc : circles.val[ci.val]'hci = c := (List.getElem?_eq_some_iff.mp hc).2
  obtain ⟨cnt, hcnt⟩ : ∃ cnt, c.spec.sectors.val[ring.val]'hring = cnt := ⟨_, rfl⟩
  rw [hcnt] at hcap ⊢
  apply loop.spec_decr_nat
    (fun st : alloc.vec.Vec scene.Cell × Std.Usize => cnt.val - st.2.val)
    (fun st : alloc.vec.Vec scene.Cell × Std.Usize =>
      st.1.val.length + (cnt.val - st.2.val) = cells.val.length + (cnt.val - sector.val) ∧
      ∃ k, st.1.val = cells.val ++ k ∧ GridFree k)
    _
  · rintro ⟨cs, sec⟩ ⟨hlen, k, hk, hfree⟩
    simp only at hlen hk
    unfold scene.Layout.new_loop4_loop0_loop0.body
    simp only [alloc.vec.Vec.index_slice_index]
    step as ⟨c1, hc1⟩
    have hc1' : c1 = c := by rw [hc1]; exact hcc
    subst hc1'
    step as ⟨i, hi⟩
    have hi' : i = cnt := by rw [hi]; exact hcnt
    subst hi'
    by_cases hlt : sec < i
    · simp only [hlt, ↓reduceIte]
      have hlt' : sec.val < i.val := hlt
      step as ⟨cs1, hcs1⟩
      step as ⟨sec1, hsec1⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [hcs1]; simp; omega
      · refine ⟨k ++ [scene.Cell.Sector ci ring sec], ?_, ?_⟩
        · rw [hcs1, hk]; simp
        · exact hfree.append (GridFree.singleton _ (by intro a b d h; cases h))
      · omega
    · simp only [hlt, ↓reduceIte, spec_ok]
      have : ¬ sec.val < i.val := hlt
      refine ⟨?_, k, hk, hfree⟩
      omega
  · exact ⟨rfl, [], by simp, by intro c hc; simp at hc⟩

/-! ### The ring loop -/

theorem layout_new_loop4_rings_total (circles : alloc.vec.Vec polar.Circle)
    (cells : alloc.vec.Vec scene.Cell) (ci ring : Std.Usize) (c0 : polar.Circle)
    (hc0 : circles.val[ci.val]? = some c0)
    (hplaced : PlacedTo cells.val.length ring.val c0)
    (hcap : cells.val.length + ringSum c0 ring.val ≤ Std.Usize.max) :
    scene.Layout.new_loop4_loop0 circles cells ci ring ⦃ r =>
      (∃ c', r.1.val = circles.val.set ci.val c' ∧
        circleKey c' = circleKey c0 ∧ Placed r.2.val.length c') ∧
      r.2.val.length = cells.val.length + ringSum c0 ring.val ∧
      ∃ k, r.2.val = cells.val ++ k ∧ GridFree k ⦄ := by
  unfold scene.Layout.new_loop4_loop0
  have hci : ci.val < circles.val.length := (List.getElem?_eq_some_iff.mp hc0).1
  have hc0' : circles.val[ci.val]'hci = c0 := (List.getElem?_eq_some_iff.mp hc0).2
  apply loop.spec_decr_nat
    (fun st : alloc.vec.Vec polar.Circle × alloc.vec.Vec scene.Cell × Std.Usize =>
      c0.spec.sectors.val.length - st.2.2.val)
    (fun st : alloc.vec.Vec polar.Circle × alloc.vec.Vec scene.Cell × Std.Usize =>
      (∃ c', st.1.val = circles.val.set ci.val c' ∧ circleKey c' = circleKey c0 ∧
        PlacedTo st.2.1.val.length st.2.2.val c') ∧
      st.2.1.val.length + ringSum c0 st.2.2.val = cells.val.length + ringSum c0 ring.val ∧
      ∃ k, st.2.1.val = cells.val ++ k ∧ GridFree k)
    _
  · rintro ⟨cl, cs, rg⟩ ⟨⟨c', hcl, hkey, hpl⟩, hlen, k, hk, hfree⟩
    simp only at hcl hlen hk hpl
    have hspec : c'.spec = c0.spec := circleKey_spec hkey
    have hci' : ci.val < cl.val.length := by rw [hcl]; simpa using hci
    have hcl_ci : cl.val[ci.val]'hci' = c' := by simp [hcl]
    unfold scene.Layout.new_loop4_loop0.body
    simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
    step as ⟨c, hc⟩
    have hcc : c = c' := hc.trans hcl_ci
    subst hcc
    step as ⟨n, hn⟩
    have hlt1 : rg < n ↔ rg.val < c.spec.sectors.val.length := by
      rw [← hn]; exact Iff.rfl
    by_cases hlt : rg < n
    · simp only [hlt, ↓reduceIte]
      have hlt' : rg.val < c.spec.sectors.val.length := hlt1.mp hlt
      have hlt0 : rg.val < c0.spec.sectors.val.length := by rw [← hspec]; exact hlt'
      have hrg : rg.val < c.ring_starts.val.length := by rw [hpl.2.1]; exact hlt'
      have hnmax : rg.val < n.val := hlt
      step as ⟨c1, back, hc1, hback⟩
      have hc1' : c1 = c := hc1.trans hcl_ci
      subst hc1'
      step as ⟨x, back1, hx, hback1⟩
      subst hback hback1
      obtain ⟨c'', hc''⟩ : ∃ c'', c'' =
          { c1 with ring_starts := c1.ring_starts.set rg (alloc.vec.Vec.len cs) } := ⟨_, rfl⟩
      rw [← hc'']
      have hsv : c''.spec.sectors = c0.spec.sectors := by
        rw [hc'']; exact congrArg (·.sectors) hspec
      have hcircles2 : (cl.set ci c'').val = circles.val.set ci.val c'' := by
        rw [alloc.vec.Vec.set_val_eq, hcl, List.set_set]
      have hget : (cl.set ci c'').val[ci.val]? = some c'' := by
        rw [hcircles2]; simp [hci]
      obtain ⟨s0, hs0⟩ : ∃ s0, c0.spec.sectors.val[rg.val]'hlt0 = s0 := ⟨_, rfl⟩
      have hring'' : rg.val < c''.spec.sectors.val.length := by rw [hsv]; exact hlt0
      have hsec : (c''.spec.sectors.val[rg.val]'hring'') = s0 := by
        rw [← hs0]; simp [hsv]
      have hrsum := ringSum_succ c0 rg.val hlt0
      rw [hs0] at hrsum
      have hlen_cs : (alloc.vec.Vec.len cs).val = cs.val.length := by simp
      have h0 : (0#usize).val = 0 := by simp
      have hcapr : cs.val.length + ((c''.spec.sectors.val[rg.val]'hring'').val - (0#usize).val)
          ≤ Std.Usize.max := by
        rw [hsec, h0, Nat.sub_zero]; omega
      refine spec_bind (layout_new_loop4_sectors_total (cl.set ci c'') cs ci rg 0#usize c'' hget
        hring'' hcapr) ?_
      rintro cs1 ⟨hcs1len, k2, hk2, hfree2⟩
      rw [hsec] at hcs1len
      rw [h0, Nat.sub_zero] at hcs1len
      step as ⟨ring1, hring1⟩
      have hring1v : ring1.val = rg.val + 1 := hring1
      refine ⟨⟨c'', hcircles2, ?_, ?_⟩, ?_, ⟨k ++ k2, ?_, hfree.append hfree2⟩, ?_⟩
      · rw [← hkey]; rw [hc'']; rfl
      · rw [hring1v]
        have hcs1 : cs.val.length ≤ cs1.val.length := by omega
        refine ⟨?_, ?_, ?_⟩
        · have := hpl.1; simp only [hc'']; omega
        · simp only [hc'', alloc.vec.Vec.set_length]; exact hpl.2.1
        · intro j h1 h2 hj
          by_cases hjr : j = rg.val
          · subst hjr
            simp only [hc'', alloc.vec.Vec.set_val_eq, List.getElem_set_self, hlen_cs]
            have hs1 : (c1.spec.sectors.val[rg.val]'hlt').val = s0.val := by rw [← hs0]; simp [hspec]
            omega
          · have h1' : j < c1.ring_starts.val.length := by
              simpa [hc'', alloc.vec.Vec.set_length] using h1
            have h2' : j < c1.spec.sectors.val.length := by
              have : j < c0.spec.sectors.val.length := by rw [← hsv]; exact h2
              rw [hspec]; exact this
            have hj' : j < rg.val := by omega
            have := hpl.2.2 j h1' h2' hj'
            have hsame : (c''.spec.sectors.val[j]'h2) = c1.spec.sectors.val[j]'h2' := by
              simp [hc'']
            simp only [hc'', alloc.vec.Vec.set_val_eq, List.getElem_set, hjr, ↓reduceIte,
              Ne.symm hjr] at *
            omega
      · rw [hcs1len, hring1v]; simp only [hlen_cs] at *; omega
      · rw [hk2.trans (by rw [hk])] ; simp
      · rw [hring1v]; omega
    · simp only [hlt, ↓reduceIte, spec_ok]
      have hlt' : c.spec.sectors.val.length ≤ rg.val := by
        by_contra hcon; exact hlt (hlt1.mpr (by omega))
      have hlt0 : c0.spec.sectors.val.length ≤ rg.val := by rw [← hspec]; exact hlt'
      refine ⟨⟨c, hcl, hkey, hpl.placed hlt'⟩, ?_, k, hk, hfree⟩
      rw [ringSum_of_ge c0 rg.val hlt0] at hlen; omega
  · exact ⟨⟨c0, by rw [← hc0']; simp, rfl, hplaced⟩, rfl, [], by simp, by intro c hc; simp at hc⟩

/-! ### The circle loop -/

/-- `Layout::new`'s center/ring/sector loop returns when the cell vector has room for the cells of
circles `ci..`; it keeps every circle's key, adds exactly `cellsFrom` cells (none a grid cell), and
leaves every circle `ci..` placed below the final cell count. -/
theorem layout_new_loop4_total (circles : alloc.vec.Vec polar.Circle)
    (cells : alloc.vec.Vec scene.Cell) (ci : Std.Usize) (hrs : RingStartsLen circles.val)
    (hcap : cells.val.length + cellsFrom circles.val ci.val ≤ Std.Usize.max) :
    scene.Layout.new_loop4 circles cells ci ⦃ r =>
      r.1.val.map circleKey = circles.val.map circleKey ∧
      (∀ j (h : j < r.1.val.length), ci.val ≤ j → Placed r.2.val.length (r.1.val[j]'h)) ∧
      r.2.val.length = cells.val.length + cellsFrom circles.val ci.val ∧
      ∃ k, r.2.val = cells.val ++ k ∧ GridFree k ⦄ := by
  unfold scene.Layout.new_loop4
  apply loop.spec_decr_nat
    (fun st : alloc.vec.Vec polar.Circle × alloc.vec.Vec scene.Cell × Std.Usize =>
      circles.val.length - st.2.2.val)
    (fun st : alloc.vec.Vec polar.Circle × alloc.vec.Vec scene.Cell × Std.Usize =>
      st.1.val.map circleKey = circles.val.map circleKey ∧
      (∀ j (h : j < st.1.val.length), ci.val ≤ j → j < st.2.2.val →
        Placed st.2.1.val.length (st.1.val[j]'h)) ∧
      (∀ j, st.2.2.val ≤ j → st.1.val[j]? = circles.val[j]?) ∧
      st.2.1.val.length + cellsFrom circles.val st.2.2.val =
        cells.val.length + cellsFrom circles.val ci.val ∧
      ∃ k, st.2.1.val = cells.val ++ k ∧ GridFree k)
    _
  · rintro ⟨cl, cs, kk⟩ ⟨hkeys, hplaced, hsame, hlen, k, hk, hfree⟩
    simp only at hkeys hplaced hsame hlen hk
    have hcl_len : cl.val.length = circles.val.length := by simpa using congrArg List.length hkeys
    unfold scene.Layout.new_loop4.body
    simp only [alloc.vec.Vec.index_mut_slice_index]
    by_cases hlt : kk < alloc.vec.Vec.len cl
    · simp only [hlt, ↓reduceIte]
      have hk1 : kk.val < cl.val.length := by scalar_tac
      have hk2 : kk.val < circles.val.length := by omega
      have hcl_kk : cl.val[kk.val]? = circles.val[kk.val]? := hsame kk.val (le_refl _)
      have hcl_kk' : cl.val[kk.val]'hk1 = circles.val[kk.val]'hk2 := by
        have := hcl_kk
        simp only [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hk2, Option.some.injEq] at this
        exact this
      step as ⟨c, back, hc, hback⟩
      have hcc : c = circles.val[kk.val]'hk2 := hc.trans hcl_kk'
      have hrs_c : c.ring_starts.val.length = c.spec.sectors.val.length := by
        rw [hcc]; exact hrs _ (List.getElem_mem hk2)
      subst hback
      have hcs1cap : cs.val.length + 1 + ringSum c 0 ≤ Std.Usize.max := by
        have := cellsFrom_succ circles.val kk.val hk2
        rw [← hcc] at this
        simp only [circleCells, sectorSum] at this
        omega
      have hcs_lt : cs.val.length < Std.Usize.max := by omega
      obtain ⟨c', hc'⟩ : ∃ c', c' = { c with center_cell := alloc.vec.Vec.len cs } := ⟨_, rfl⟩
      have hlen_cs : (alloc.vec.Vec.len cs).val = cs.val.length := by simp
      step as ⟨cs1, hcs1⟩
      rw [← hc']
      have hget : (cl.set kk c').val[kk.val]? = some c' := by simp [hk1]
      have hplc : PlacedTo cs1.val.length 0 c' := by
        refine ⟨?_, ?_, fun j h1 h2 hj => by omega⟩
        · rw [hcs1, hc']; simp [hlen_cs]
        · rw [hc']; exact hrs_c
      have hcap' : cs1.val.length + ringSum c' 0 ≤ Std.Usize.max := by
        have : ringSum c' 0 = ringSum c 0 := by rw [hc']; rfl
        rw [hcs1, this]; simp; omega
      refine spec_bind (layout_new_loop4_rings_total (cl.set kk c') cs1 kk 0#usize c' hget hplc hcap') ?_
      rintro ⟨cl2, cs2⟩ ⟨⟨c'', hcl2, hkey'', hpl''⟩, hlen2, k2, hk2', hfree2⟩
      simp only at hcl2 hlen2 hk2' hpl''
      have h0 : (0#usize).val = 0 := by simp
      rw [h0] at hlen2
      step as ⟨ci1, hci1⟩
      have hci1v : ci1.val = kk.val + 1 := hci1
      have hcl2' : cl2.val = cl.val.set kk.val c'' := by
        rw [hcl2, alloc.vec.Vec.set_val_eq, List.set_set]
      have hkc'' : circleKey c'' = circleKey (cl.val[kk.val]'hk1) := by
        rw [hkey'', hc', ← hc]; rfl
      have hring_eq : ringSum c' 0 = ringSum c 0 := by rw [hc']; rfl
      have hcs1len : cs1.val.length = cs.val.length + 1 := by rw [hcs1]; simp
      have hcf := cellsFrom_succ circles.val kk.val hk2
      rw [← hcc] at hcf
      simp only [circleCells, sectorSum] at hcf
      refine ⟨?_, ?_, ?_, ?_, ⟨k ++ [scene.Cell.Center kk] ++ k2, ?_, ?_⟩, ?_⟩
      · rw [hcl2', keys_set hk1 hkc'']; exact hkeys
      · intro j h hj1 hj2
        rw [hci1v] at hj2
        have hcs12 : cs.val.length ≤ cs2.val.length := by omega
        by_cases hjk : j = kk.val
        · subst hjk
          have : cl2.val[kk.val]'h = c'' := by simp [hcl2']
          rw [this]; exact hpl''
        · have hjk' : j < kk.val := by omega
          have hjl : j < cl.val.length := by
            rw [hcl2'] at h; simpa using h
          have : cl2.val[j]'h = cl.val[j]'hjl := by simp [hcl2', List.getElem_set, Ne.symm hjk]
          rw [this]
          exact (hplaced j hjl hj1 hjk').mono hcs12
      · intro j hj
        rw [hci1v] at hj
        rw [hcl2', List.getElem?_set_ne (by omega)]
        exact hsame j (by omega)
      · rw [hci1v, hlen2, hcs1]
        simp only [List.length_append, List.length_singleton, hring_eq] at *
        omega
      · rw [hk2', hcs1, hk]; simp
      · exact (hfree.append (GridFree.singleton _ (by intro a b d h; cases h))).append hfree2
      · rw [hci1v]; omega
    · simp only [hlt, ↓reduceIte, spec_ok]
      have hge : cl.val.length ≤ kk.val := by
        by_contra hcon; exact hlt (by simp only [alloc.vec.Vec.len]; scalar_tac)
      have hge2 : circles.val.length ≤ kk.val := by omega
      refine ⟨hkeys, fun j h hj => hplaced j h hj (by omega), ?_, k, hk, hfree⟩
      rw [cellsFrom_of_ge circles.val kk.val hge2] at hlen
      omega
  · exact ⟨rfl, fun j h hj hj' => by dsimp only at hj'; omega, fun j _ => rfl, by simp,
      [], by simp, by intro c hc; simp at hc⟩

/-! ### Grid cells carry in-range columns and rows -/

theorem layout_new_loop3_loop0_idx (n : Std.Usize) (R : Nat) (geometry : grid.Geometry)
    (cell_grid : grid.Grid) (circles : alloc.vec.Vec polar.Circle) (bands : alloc.vec.Vec Std.I32)
    (cells : alloc.vec.Vec scene.Cell) (row column : Std.Usize) (hrow : row.val < R)
    (hc : GridIdx cells.val n.val R) :
    OkPost (scene.Layout.new_loop3_loop0 n geometry cell_grid circles bands cells row column)
      (fun r => GridIdx r.2.val n.val R) := by
  unfold scene.Layout.new_loop3_loop0
  refine okPost_loop (fun st : grid.Grid × alloc.vec.Vec scene.Cell × Std.Usize =>
    GridIdx st.2.1.val n.val R) _ _ ?_ (cell_grid, cells, column) hc
  rintro ⟨g, cs, col⟩ hcs
  simp only at hcs
  unfold scene.Layout.new_loop3_loop0.body
  by_cases hlt : col < n <;> simp only [hlt, ↓reduceIte]
  · have hlt' : col.val < n.val := hlt
    refine okPost_any (fun bounds => ?_)
    refine okPost_spec (grid_geometry_check_spec geometry bounds) ?_
    rintro r ⟨hr1, hr2⟩
    refine okPost_spec (result_is_err_spec r) ?_
    intro removed hremoved
    refine okPost_bind (layout_new_loop3_inner_ok circles bands bounds removed 0#usize) ?_
    intro removed1 hremoved1
    refine okPost_bind (P := fun t : grid.Grid × alloc.vec.Vec scene.Cell =>
      GridIdx t.2.val n.val R) ?_ ?_
    · cases removed1 with
      | true => exact okPost_ok hcs
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine okPost_any (fun g2 => ?_)
        refine okPost_bind (vec_push_okPost cs _) ?_
        intro cs2 hcs2
        refine okPost_ok ?_
        intro c hcm col' row' b hceq
        simp only [hcs2, List.mem_append, List.mem_singleton] at hcm
        rcases hcm with hcm | hcm
        · exact hcs c hcm col' row' b hceq
        · rw [hcm] at hceq
          injection hceq with h1 h2 h3
          subst h1 h2
          exact ⟨hlt', hrow⟩
    · rintro ⟨g1, cs1⟩ hcs1
      exact okPost_any (fun _ => okPost_ok hcs1)
  · exact okPost_ok hcs

/-- Every grid cell `new_loop3` pushes has a column below `n` and a row below `n1`. -/
theorem layout_new_loop3_idx (n n1 : Std.Usize) (geometry : grid.Geometry) (cell_grid : grid.Grid)
    (circles : alloc.vec.Vec polar.Circle) (bands : alloc.vec.Vec Std.I32)
    (cells : alloc.vec.Vec scene.Cell) (row : Std.Usize) (hc : GridIdx cells.val n.val n1.val) :
    OkPost (scene.Layout.new_loop3 n n1 geometry cell_grid circles bands cells row)
      (fun r => GridIdx r.2.val n.val n1.val) := by
  unfold scene.Layout.new_loop3
  refine okPost_loop (fun st : grid.Grid × alloc.vec.Vec scene.Cell × Std.Usize =>
    GridIdx st.2.1.val n.val n1.val) _ _ ?_ (cell_grid, cells, row) hc
  rintro ⟨g, cs, rw⟩ hcs
  simp only at hcs
  unfold scene.Layout.new_loop3.body
  by_cases hlt : rw < n1 <;> simp only [hlt, ↓reduceIte]
  · refine okPost_bind (layout_new_loop3_loop0_idx n n1.val geometry g circles bands cs rw 0#usize
      hlt hcs) ?_
    rintro ⟨g1, cs1⟩ hcs1
    exact okPost_any (fun _ => okPost_ok hcs1)
  · exact okPost_ok hcs

end Labyrinth
