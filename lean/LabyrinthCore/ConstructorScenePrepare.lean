module
public import LabyrinthCore.ConstructorSceneComponents
public import LabyrinthCore.ConstructorSceneInitialize
public import Mathlib.Data.List.FinRange
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow labyrinth_core

namespace Labyrinth

/-- The genuine finite vertex universe used to justify union-by-size arithmetic. -/
def constructorSceneVertices (n : Usize) : List Usize :=
  List.ofFn fun index : Fin n.val =>
    UScalar.ofNatCore index.val (lt_trans index.isLt n.hBounds)

theorem constructor_scene_vertices_length (n : Usize) :
    (constructorSceneVertices n).length = n.val := by
  simp [constructorSceneVertices]

theorem constructor_scene_vertices_population (n root : Usize)
    (hroot : root.val < n.val) :
    constructorComponentPopulation (constructorSceneVertices n) (fun node => node) root = 1 := by
  let vertex : Fin n.val → Usize := fun index =>
    UScalar.ofNatCore index.val (lt_trans index.isLt n.hBounds)
  have hinjective : Function.Injective vertex := by
    intro left right heq
    apply Fin.ext
    exact congrArg UScalar.val heq
  have hvertices : constructorSceneVertices n = List.ofFn vertex := rfl
  have hnodup : (constructorSceneVertices n).Nodup := by
    rw [hvertices]
    exact List.nodup_ofFn_ofInjective hinjective
  have hrootMem : root ∈ constructorSceneVertices n := by
    rw [hvertices, List.mem_ofFn]
    refine ⟨⟨root.val, hroot⟩, ?_⟩
    apply UScalar.eq_of_val_eq
    simp [vertex]
  let filtered := (constructorSceneVertices n).filter (fun node => node == root)
  have hfilteredNodup : filtered.Nodup := hnodup.filter _
  have hmembership : ∀ value, value ∈ filtered ↔ value ∈ [root] := by
    intro value
    constructor
    · intro hvalue
      have heq : value = root := by
        exact (beq_iff_eq.mp (List.mem_filter.mp hvalue).2)
      simpa only [List.mem_singleton] using heq
    · intro hvalue
      have heq : value = root := by simpa only [List.mem_singleton] using hvalue
      subst value
      exact List.mem_filter.mpr ⟨hrootMem, by simp⟩
  have hperm : filtered.Perm [root] :=
    (List.perm_ext_iff_of_nodup hfilteredNodup (by simp)).mpr hmembership
  unfold constructorComponentPopulation
  change filtered.length = 1
  simpa using hperm.length_eq

/-- The actual initialized vectors form singleton union-find classes with exact live sizes. -/
theorem constructor_scene_singleton_state (n : Usize) (required : Slice topology.Edge)
    (links sizes : alloc.vec.Vec Usize)
    (hlinksLength : links.val.length = n.val)
    (hidentity : ∀ node : Usize, node.val < n.val → links.val[node.val]? = some node)
    (hsizes : sizes.val = List.replicate n.val 1#usize) :
    ConstructorSceneForestState (constructorSceneVertices n) required 0 links sizes := by
  let rank : Usize → Nat := fun _ => 0
  let component : Usize → Usize := fun node => node
  refine ⟨rank, component, ?_, ?_, ?_, ?_, ?_⟩
  · intro node parent hnode hparent
    have hnode' : node.val < n.val := by
      rw [← hlinksLength]
      exact hnode
    have heq : parent = node := Option.some.inj (hparent.symm.trans (hidentity node hnode'))
    subst parent
    exact ⟨by omega, by simp⟩
  · constructor
    · intro node parent hnode hparent
      have hnode' : node.val < n.val := by
        rw [← hlinksLength]
        exact hnode
      have heq : parent = node := Option.some.inj (hparent.symm.trans (hidentity node hnode'))
      simp only [component, heq]
    · intro node _ _
      rfl
  · intro root hroot _
    have hroot' : root.val < n.val := by
      rw [← hlinksLength]
      exact hroot
    refine ⟨1#usize, ?_, ?_⟩
    · change sizes.val[root.val]? = some 1#usize
      simp [hsizes, hroot']
    · simpa only [UScalar.ofNatCore_val_eq] using
        (constructor_scene_vertices_population n root hroot').symm
  · intro u v
    simpa only [component] using constructor_required_prefix_zero_iff required u v
  · have hroots := constructor_scene_root_count_identity links (fun node hnode =>
      hidentity node (by simpa only [hlinksLength] using hnode))
    simpa only [Nat.zero_add] using hroots

/-- The first actual constructor phases derive singleton initialization, valid required-forest
union, dense component IDs, and the exact edge/component cardinality used by selection. -/
theorem constructor_scene_prepare_accepts (carrier : topology.Carrier)
    (n : Usize) (required : Slice topology.Edge)
    (hc : CarrierValid carrier) (hn : n.val = cellCount carrier)
    (hforest : ConstructorRequiredForest carrier required) :
    WP.spec (do
      let links ← alloc.vec.from_elem core.clone.CloneUsize 0#usize n
      let sizes ← alloc.vec.from_elem core.clone.CloneUsize 1#usize n
      let links1 ← spanning_tree.Tree.scene_dfs_loop0 n links 0#usize
      let (links2, status) ←
        spanning_tree.Tree.scene_dfs_loop1 carrier required links1 sizes 0#usize (.Ok ())
      let cf ← core.result.Result.Insts.CoreOpsTry.branch status
      match cf with
      | .Continue _ =>
        let components ← alloc.vec.from_elem core.clone.CloneUsize 0#usize n
        let labels ← alloc.vec.from_elem core.clone.CloneUsize n n
        let (components1, componentCount) ←
          spanning_tree.Tree.scene_dfs_loop2 n links2 0#usize components labels 0#usize
        ok (core.result.Result.Ok (links2, components1, componentCount))
      | .Break residual => ok (core.result.Result.Err residual)) (fun result =>
      ∃ (links components : alloc.vec.Vec Usize) (componentCount : Usize)
          (rank : Usize → Nat) (component : Usize → Usize),
        result = core.result.Result.Ok (links, components, componentCount) ∧
        links.val.length = n.val ∧
        components.val.length = n.val ∧
        required.val.length + constructorSceneRootCount links = n.val ∧
        constructorRankedLinks links.slice rank ∧
        constructorComponentLabels links.slice component ∧
        0 < componentCount.val ∧ componentCount.val ≤ n.val ∧
        (∀ node : Usize, node.val < n.val →
          (constructorSceneComponentAt components node).val < componentCount.val) ∧
        (∀ id : Usize, id.val < componentCount.val → ∃ node : Usize,
          node.val < n.val ∧ constructorSceneComponentAt components node = id) ∧
        (∀ u v : Usize, u.val < n.val → v.val < n.val →
          (constructorSceneComponentAt components u = constructorSceneComponentAt components v ↔
            Relation.ReflTransGen
              (constructorRequiredPrefixArc required required.val.length) u v)) ∧
        componentCount.val = constructorSceneRootCount links) := by
  apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize n rfl)
  intro links hlinks
  apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize 1#usize n rfl)
  intro sizes hsizes
  have hlinksLength : links.val.length = n.val := by simp [hlinks.1]
  have hsizesLength : sizes.val.length = links.val.length := by simp [hsizes.1, hlinks.1]
  apply WP.spec_bind (constructor_scene_links_spec n links (by omega))
  intro links1 hlinks1
  have hstate : ConstructorSceneForestState (constructorSceneVertices n) required 0 links1 sizes :=
    constructor_scene_singleton_state n required links1 sizes
      (by omega) hlinks1.2.1 hsizes.1
  apply WP.spec_bind (constructor_scene_forest_loop_accepts carrier required
    (constructorSceneVertices n) links1 sizes 0#usize hc hforest (by
      rw [constructor_scene_vertices_length]
      scalar_tac) (by omega) (by omega) (by simp) hstate)
  rintro ⟨links2, status⟩ hjoined
  obtain ⟨hstatus, hlinks2, hcardinality, rank, component, hrank, hlabels,
    hclasses⟩ := hjoined
  change status = core.result.Result.Ok () at hstatus
  change links2.val.length = links1.val.length at hlinks2
  change required.val.length + constructorSceneRootCount links2 = links1.val.length at hcardinality
  change constructorRankedLinks links2.slice rank at hrank
  change constructorComponentLabels links2.slice component at hlabels
  change (∀ u v, Relation.ReflTransGen
    (constructorRequiredPrefixArc required required.val.length) u v ↔
      component u = component v) at hclasses
  rw [hstatus]
  have hbranch : WP.spec
      (core.result.Result.Insts.CoreOpsTry.branch
        (core.result.Result.Ok () : core.result.Result Unit topology.Error))
      (fun cf => cf = .Continue ()) := (WP.spec_ok _).mpr rfl
  apply WP.spec_bind hbranch
  intro cf hcf
  subst cf
  apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize 0#usize n rfl)
  intro components hcomponents
  apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneUsize n n rfl)
  intro labels hlabelsInit
  apply WP.spec_bind (constructor_scene_components_spec n required links2 components labels rank
    component (by rw [hn]; exact hc.1) hrank hlabels (by omega) (by simp [hcomponents.1])
    (by simp [hlabelsInit.1]) (by
      intro root hroot
      simp [hlabelsInit.1, hroot]) hclasses)
  rintro ⟨components1, componentCount⟩ houtput
  obtain ⟨hcomponentsLength, hpositive, hcount, hbounded, hdense, hequiv⟩ := houtput
  change components1.val.length = components.val.length at hcomponentsLength
  change 0 < componentCount.val at hpositive
  change componentCount.val ≤ n.val at hcount
  change (∀ node : Usize, node.val < n.val →
    (constructorSceneComponentAt components1 node).val < componentCount.val) at hbounded
  change (∀ id : Usize, id.val < componentCount.val → ∃ node : Usize,
    node.val < n.val ∧ constructorSceneComponentAt components1 node = id) at hdense
  change (∀ u v : Usize, u.val < n.val → v.val < n.val →
    (constructorSceneComponentAt components1 u = constructorSceneComponentAt components1 v ↔
      Relation.ReflTransGen
        (constructorRequiredPrefixArc required required.val.length) u v)) at hequiv
  have hlinks2Length : links2.val.length = n.val :=
    hlinks2.trans (hlinks1.1.trans hlinksLength)
  have hcomponents1Length : components1.val.length = n.val := by
    rw [hcomponentsLength, hcomponents.1, List.length_replicate]
  have hcardinality' :
      required.val.length + constructorSceneRootCount links2 = n.val :=
    hcardinality.trans (hlinks1.1.trans hlinksLength)
  apply (WP.spec_ok _).mpr
  refine ⟨links2, components1, componentCount, rank, component, rfl, hlinks2Length,
    hcomponents1Length, hcardinality', hrank, hlabels, hpositive, hcount, hbounded, hdense,
    hequiv, ?_⟩
  apply constructor_scene_component_count_eq_root_count n links2 components1 rank component
    componentCount hrank hlabels hlinks2Length hbounded hdense
  intro u v hu hv
  exact (hequiv u v hu hv).trans (hclasses u v)

end Labyrinth
