module
public import LabyrinthCore.ConstructorSceneLabelLoop
public import LabyrinthCore.ConstructorSceneForestPrefix
@[expose] public section

open Aeneas Aeneas.Std Result labyrinth_core

namespace Labyrinth

/-- Read a component ID from the actual produced vector, not an auxiliary relabeling. -/
def constructorSceneComponentAt (components : alloc.vec.Vec Usize) (node : Usize) : Usize :=
  (components.val[node.val]?).getD 0#usize

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
