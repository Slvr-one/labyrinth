module
public import LabyrinthCore.ConstructorSceneLabelLoop
public import LabyrinthCore.ConstructorSceneForestPrefix
public import LabyrinthCore.ConstructorSceneForestLoop
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- Read a component ID from the actual produced vector, not an auxiliary relabeling. -/
def constructorSceneComponentAt (components : alloc.vec.Vec Usize) (node : Usize) : Usize :=
  (components.val[node.val]?).getD 0#usize

/-- A true concrete root test recovers the fixed union-find entry at that index. -/
theorem constructor_scene_root_test_true (links : alloc.vec.Vec Usize) (index : Nat)
    (hroot : constructorSceneRootTest links index = true) :
    ∃ root : Usize, root.val = index ∧ links.val[index]? = some root := by
  unfold constructorSceneRootTest at hroot
  split at hroot
  next root hlookup =>
    refine ⟨root, ?_, hlookup⟩
    simpa only [beq_iff_eq] using hroot
  next =>
    simp at hroot

/-- The dense IDs emitted by the actual label loop are in bijection with concrete fixed roots. -/
theorem constructor_scene_component_count_eq_root_count (n : Usize)
    (links components : alloc.vec.Vec Usize) (rank : Usize → Nat)
    (component : Usize → Usize) (count : Usize)
    (hrank : constructorRankedLinks links.slice rank)
    (hlabel : constructorComponentLabels links.slice component)
    (hlinks : links.val.length = n.val)
    (hbounded : ∀ node : Usize, node.val < n.val →
      (constructorSceneComponentAt components node).val < count.val)
    (hdense : ∀ id : Usize, id.val < count.val → ∃ node : Usize,
      node.val < n.val ∧ constructorSceneComponentAt components node = id)
    (hequiv : ∀ u v : Usize, u.val < n.val → v.val < n.val →
      (constructorSceneComponentAt components u = constructorSceneComponentAt components v ↔
        component u = component v)) :
    count.val = constructorSceneRootCount links := by
  let roots := (List.range links.val.length).filter (constructorSceneRootTest links)
  let componentAtNat : Nat → Nat :=
    fun index => ((components.val[index]?).getD 0#usize).val
  have rootFacts {index : Nat} (hi : index ∈ roots) :
      ∃ root : Usize, root.val = index ∧ links.val[index]? = some root := by
    have ht := (List.mem_filter.mp hi).2
    exact constructor_scene_root_test_true links index ht
  have mappedNodup : (roots.map componentAtNat).Nodup := by
    apply (List.nodup_range.filter _).map_on
    intro left hleft right hright heq
    obtain ⟨leftRoot, hlv, hlfixed⟩ := rootFacts hleft
    obtain ⟨rightRoot, hrv, hrfixed⟩ := rootFacts hright
    have hlb : leftRoot.val < n.val := by
      have := (List.mem_filter.mp hleft).1
      simpa only [List.mem_range, hlinks, hlv] using this
    have hrb : rightRoot.val < n.val := by
      have := (List.mem_filter.mp hright).1
      simpa only [List.mem_range, hlinks, hrv] using this
    have hcomponent :
        constructorSceneComponentAt components leftRoot =
          constructorSceneComponentAt components rightRoot := by
      apply (UScalar.eq_equiv _ _).mpr
      simpa only [componentAtNat, constructorSceneComponentAt, hlv, hrv] using heq
    have hroots := (hequiv leftRoot rightRoot hlb hrb).mp hcomponent
    have hleftLabel := hlabel.2 leftRoot (by
      change leftRoot.val < links.val.length
      omega) (by
        change links.val[leftRoot.val]? = some leftRoot
        simpa only [hlv] using hlfixed)
    have hrightLabel := hlabel.2 rightRoot (by
      change rightRoot.val < links.val.length
      omega) (by
        change links.val[rightRoot.val]? = some rightRoot
        simpa only [hrv] using hrfixed)
    exact hlv.symm.trans ((congrArg UScalar.val
      (hleftLabel.symm.trans (hroots.trans hrightLabel))).trans hrv)
  have mappedMem : ∀ id, id ∈ roots.map componentAtNat ↔ id ∈ List.range count.val := by
    intro id
    constructor
    · intro hid
      obtain ⟨index, hroot, rfl⟩ := List.mem_map.mp hid
      obtain ⟨root, hrv, _⟩ := rootFacts hroot
      have hrb : root.val < n.val := by
        have := (List.mem_filter.mp hroot).1
        simpa only [List.mem_range, hlinks, hrv] using this
      apply List.mem_range.mpr
      simpa only [componentAtNat, constructorSceneComponentAt, hrv] using hbounded root hrb
    · intro hid
      have hib : id < count.val := List.mem_range.mp hid
      have hiwidth : id < 2 ^ UScalarTy.Usize.numBits := lt_trans hib count.hBounds
      let actualId : Usize := UScalar.ofNatCore id hiwidth
      have haiv : actualId.val = id := by
        simp only [actualId, UScalar.ofNatCore_val_eq]
      obtain ⟨node, hnode, hnodeId⟩ := hdense actualId (by simpa only [haiv] using hib)
      obtain ⟨hrootBound, hrootFixed⟩ :=
        constructor_component_root_properties links.slice rank component hrank hlabel node
          (by
            change node.val < links.val.length
            omega)
      have hrootBound' : (component node).val < n.val := by
        change (component node).val < links.val.length at hrootBound
        omega
      have hrootFixed' : links.val[(component node).val]? = some (component node) := by
        change links.val[(component node).val]? = some (component node) at hrootFixed
        exact hrootFixed
      have hrootMem : (component node).val ∈ roots := by
        apply List.mem_filter.mpr
        refine ⟨List.mem_range.mpr (by simpa only [hlinks] using hrootBound'), ?_⟩
        simp [constructorSceneRootTest, hrootFixed']
      apply List.mem_map.mpr
      refine ⟨(component node).val, hrootMem, ?_⟩
      have hsameComponent : component (component node) = component node :=
        hlabel.2 (component node) hrootBound hrootFixed
      have hsameOutput :=
        (hequiv (component node) node hrootBound' hnode).mpr hsameComponent
      have hnodeIdVal := congrArg UScalar.val hnodeId
      simpa only [componentAtNat, constructorSceneComponentAt] using
        ((congrArg UScalar.val hsameOutput).trans hnodeIdVal).trans haiv
  have hperm : List.Perm (roots.map componentAtNat) (List.range count.val) :=
    (List.perm_ext_iff_of_nodup mappedNodup List.nodup_range).mpr mappedMem
  have hlength := hperm.length_eq
  simpa only [List.length_map, List.length_range, roots, constructorSceneRootCount] using hlength.symm
/-- Actual contraction produces a nonempty dense quotient and exactly the required-edge classes. -/
theorem constructor_scene_components_spec (n : Usize) (required : Slice topology.Edge)
    (links components labels : alloc.vec.Vec Usize) (rank : Usize → Nat)
    (component : Usize → Usize)
    (hn : 0 < n.val) (hrank : constructorRankedLinks links.slice rank)
    (hlabel : constructorComponentLabels links.slice component)
    (hlinks : links.val.length = n.val)
    (hc : n.val ≤ components.val.length) (hl : n.val ≤ labels.val.length)
    (hempty : ∀ r : Usize, r.val < n.val → labels.val[r.val]? = some n)
    (hforest : ∀ u v, Relation.ReflTransGen
      (constructorRequiredPrefixArc required required.val.length) u v ↔ component u = component v) :
    WP.spec (spanning_tree.Tree.scene_dfs_loop2 n links 0#usize components labels 0#usize)
      (fun output => output.1.val.length = components.val.length ∧
        0 < output.2.val ∧ output.2.val ≤ n.val ∧
        (∀ node : Usize, node.val < n.val →
          (constructorSceneComponentAt output.1 node).val < output.2.val) ∧
        (∀ id : Usize, id.val < output.2.val → ∃ node : Usize,
          node.val < n.val ∧ constructorSceneComponentAt output.1 node = id) ∧
        ∀ u v : Usize, u.val < n.val → v.val < n.val →
          (constructorSceneComponentAt output.1 u = constructorSceneComponentAt output.1 v ↔
            Relation.ReflTransGen (constructorRequiredPrefixArc required required.val.length) u v)) := by
  apply WP.spec_mono (constructor_scene_labels_exact_spec n links components labels rank component
    hrank hlabel hlinks hc hl hempty)
  intro output hout
  obtain ⟨hlen, hcount, hbounded, hdense, hequiv⟩ := hout
  have hzero : (0#usize).val < n.val := by simpa using hn
  obtain ⟨zeroId, _, hzeroId⟩ := hbounded 0#usize hzero
  refine ⟨hlen, by omega, hcount, ?_, ?_, ?_⟩
  · intro node hnode
    obtain ⟨id, hid, hib⟩ := hbounded node hnode
    simpa only [constructorSceneComponentAt, hid, Option.getD_some] using hib
  · intro id hid
    obtain ⟨node, hnode, hlookup⟩ := hdense id hid
    exact ⟨node, hnode, by simp only [constructorSceneComponentAt, hlookup, Option.getD_some]⟩
  · intro u v hu hv
    obtain ⟨uid, hulookup, _⟩ := hbounded u hu
    obtain ⟨vid, hvlookup, _⟩ := hbounded v hv
    have he := hequiv u v hu hv
    rw [hulookup, hvlookup] at he
    simpa only [constructorSceneComponentAt, hulookup, hvlookup, Option.getD_some,
      Option.some.injEq, ← hforest u v] using he

end Labyrinth
