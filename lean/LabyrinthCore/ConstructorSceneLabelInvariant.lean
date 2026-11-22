module
public import LabyrinthCore.ConstructorSceneLabels
@[expose] public section

open Aeneas Aeneas.Std labyrinth_core

namespace Labyrinth

/-- Dense labels record both their original class representative and a processed vertex witness. -/
structure ConstructorSceneLabelsExact (n : Usize) (component : Usize → Usize) (processed : Nat)
    (components labels : alloc.vec.Vec Usize) (count : Usize) : Prop where
  prefix_le : processed ≤ n.val
  count_le : count.val ≤ processed
  range : ∀ root : Usize, root.val < n.val → ∃ value : Usize,
    labels.val[root.val]? = some value ∧ (value = n ∨ value.val < count.val)
  unique : ∀ root other : Usize, root.val < n.val → other.val < n.val →
    ∀ value : Usize, value.val < count.val →
      labels.val[root.val]? = some value → labels.val[other.val]? = some value → root = other
  assigned : ∀ node : Usize, node.val < processed → ∃ value : Usize,
    components.val[node.val]? = some value ∧
      labels.val[(component node).val]? = some value ∧ value.val < count.val
  dense : ∀ value : Usize, value.val < count.val → ∃ node : Usize,
    node.val < processed ∧ components.val[node.val]? = some value

theorem constructor_scene_labels_exact_initial (n : Usize) (component : Usize → Usize)
    (components labels : alloc.vec.Vec Usize)
    (hempty : ∀ root : Usize, root.val < n.val → labels.val[root.val]? = some n) :
    ConstructorSceneLabelsExact n component 0 components labels 0#usize := by
  refine ⟨by omega, by simp, ?_, ?_, ?_, ?_⟩
  · intro root hr
    exact ⟨n, hempty root hr, Or.inl rfl⟩
  · intro root other hr ho value hv
    simp at hv
  · intro node hn
    omega
  · intro value hv
    simp at hv

/-- Revisiting an assigned representative changes only the current vertex's component entry. -/
theorem constructor_scene_labels_exact_existing (n index count value : Usize)
    (component : Usize → Usize) (components labels : alloc.vec.Vec Usize)
    (h : ConstructorSceneLabelsExact n component index.val components labels count)
    (hi : index.val < n.val) (hic : index.val < components.val.length)
    (hvalue : labels.val[(component index).val]? = some value) (hv : value.val < count.val) :
    ConstructorSceneLabelsExact n component (index.val + 1) (components.set index value) labels count := by
  refine ⟨by omega, by have := h.count_le; omega, h.range, h.unique, ?_, ?_⟩
  · intro node hn
    by_cases he : node = index
    · subst node
      exact ⟨value, by simp [alloc.vec.Vec.set, hic], hvalue, hv⟩
    · have hnv : node.val ≠ index.val := fun hv => he ((UScalar.eq_equiv _ _).mpr hv)
      obtain ⟨old, hc, hl, hb⟩ := h.assigned node (by omega)
      exact ⟨old, by simpa [alloc.vec.Vec.set, hnv, Ne.symm hnv] using hc, hl, hb⟩
  · intro old ho
    obtain ⟨node, hn, hc⟩ := h.dense old ho
    have hnv : node.val ≠ index.val := by omega
    exact ⟨node, by omega, by simpa [alloc.vec.Vec.set, hnv, Ne.symm hnv] using hc⟩

/-- The next fresh ID is distinct from every earlier live label and has this vertex as witness. -/
theorem constructor_scene_labels_exact_fresh (n index count nextCount : Usize)
    (component : Usize → Usize) (components labels : alloc.vec.Vec Usize)
    (h : ConstructorSceneLabelsExact n component index.val components labels count)
    (hi : index.val < n.val) (hic : index.val < components.val.length)
    (hrl : (component index).val < labels.val.length)
    (hempty : labels.val[(component index).val]? = some n)
    (hnext : nextCount.val = count.val + 1) :
    ConstructorSceneLabelsExact n component (index.val + 1) (components.set index count)
      (labels.set (component index) count) nextCount := by
  have hcount := h.count_le
  have hcn : count.val < n.val := by omega
  have hcnne : count ≠ n := by intro he; have := congrArg UScalar.val he; omega
  have holdLookup : ∀ root : Usize, root ≠ component index →
      (labels.set (component index) count).val[root.val]? = labels.val[root.val]? := by
    intro root he
    have hev : root.val ≠ (component index).val := fun hv => he ((UScalar.eq_equiv _ _).mpr hv)
    simp [alloc.vec.Vec.set, Ne.symm hev]
  have hnewLookup : (labels.set (component index) count).val[(component index).val]? = some count := by
    simp [alloc.vec.Vec.set, hrl]
  have hnoOldCount : ∀ root : Usize, root.val < n.val → labels.val[root.val]? ≠ some count := by
    intro root hb he
    obtain ⟨old, ho, hc⟩ := h.range root hb
    have heq : old = count := Option.some.inj (ho.symm.trans he)
    rcases hc with hc | hc
    · exact hcnne (heq.symm.trans hc)
    · have := congrArg UScalar.val heq
      omega
  refine ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩
  · intro root hb
    by_cases he : root = component index
    · subst root
      exact ⟨count, hnewLookup, Or.inr (by omega)⟩
    · obtain ⟨old, ho, hc⟩ := h.range root hb
      refine ⟨old, by simpa only [holdLookup root he] using ho, ?_⟩
      rcases hc with heq | hlt
      · exact Or.inl heq
      · exact Or.inr (by omega)
  · intro root other hb hob value hv hl ho
    by_cases he : root = component index
    · subst root
      have heq : value = count := Option.some.inj (hl.symm.trans hnewLookup)
      by_cases hoe : other = component index
      · exact hoe.symm
      · rw [holdLookup other hoe] at ho
        rw [heq] at ho
        exact False.elim (hnoOldCount other hob ho)
    · rw [holdLookup root he] at hl
      by_cases hoe : other = component index
      · subst other
        have heq : value = count := Option.some.inj (ho.symm.trans hnewLookup)
        rw [heq] at hl
        exact False.elim (hnoOldCount root hb hl)
      · rw [holdLookup other hoe] at ho
        have hvc : value.val < count.val := by
          have hne : value ≠ count := by intro heq; rw [heq] at hl; exact hnoOldCount root hb hl
          have hnev : value.val ≠ count.val := fun heq => hne ((UScalar.eq_equiv _ _).mpr heq)
          omega
        exact h.unique root other hb hob value hvc hl ho
  · intro node hn
    by_cases he : node = index
    · subst node
      exact ⟨count, by simp [alloc.vec.Vec.set, hic], hnewLookup, by omega⟩
    · have hnv : node.val ≠ index.val := fun hv => he ((UScalar.eq_equiv _ _).mpr hv)
      obtain ⟨old, hc, hl, hb⟩ := h.assigned node (by omega)
      have hrootne : component node ≠ component index := by
        intro heq
        rw [heq] at hl
        have hon : old = n := Option.some.inj (hl.symm.trans hempty)
        have := congrArg UScalar.val hon
        omega
      exact ⟨old, by simpa [alloc.vec.Vec.set, hnv, Ne.symm hnv] using hc,
        by simpa only [holdLookup (component node) hrootne] using hl, by omega⟩
  · intro value hv
    by_cases he : value = count
    · subst value
      exact ⟨index, by omega, by simp [alloc.vec.Vec.set, hic]⟩
    · have hev : value.val ≠ count.val := fun hv => he ((UScalar.eq_equiv _ _).mpr hv)
      obtain ⟨node, hn, hc⟩ := h.dense value (by omega)
      have hnv : node.val ≠ index.val := by omega
      exact ⟨node, by omega, by simpa [alloc.vec.Vec.set, hnv, Ne.symm hnv] using hc⟩

/-- Final equal component IDs are equivalent to equal original representatives, not merely bounded. -/
theorem constructor_scene_labels_exact_partition (n count : Usize)
    (component : Usize → Usize) (components labels : alloc.vec.Vec Usize)
    (h : ConstructorSceneLabelsExact n component n.val components labels count)
    (hroot : ∀ node : Usize, node.val < n.val → (component node).val < n.val)
    (u v : Usize) (hu : u.val < n.val) (hv : v.val < n.val) :
    components.val[u.val]? = components.val[v.val]? ↔ component u = component v := by
  obtain ⟨ul, hul, hur, hub⟩ := h.assigned u hu
  obtain ⟨vl, hvl, hvr, hvb⟩ := h.assigned v hv
  constructor
  · intro he
    have heq : ul = vl := Option.some.inj (hul.symm.trans (he.trans hvl))
    exact h.unique (component u) (component v) (hroot u hu) (hroot v hv) ul hub hur
      (by simpa only [heq] using hvr)
  · intro he
    have heq : ul = vl := Option.some.inj (hur.symm.trans (by simpa only [he] using hvr))
    exact hul.trans ((congrArg some heq).trans hvl.symm)

end Labyrinth
