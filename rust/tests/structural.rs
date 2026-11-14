use std::collections::BTreeSet;

use labyrinth_core::spanning_tree::{Tree, Workspace};
use labyrinth_core::topology::{Carrier, Edge, Error};
use labyrinth_core::tree::Rng;

struct Choices {
    values: Vec<usize>,
    bounds: Vec<usize>,
}

impl Choices {
    fn new(values: &[usize]) -> Self {
        Self {
            values: values.to_vec(),
            bounds: Vec::new(),
        }
    }
}

impl Rng for Choices {
    fn next_below(&mut self, bound: usize) -> usize {
        assert!(bound > 0);
        let index = self.bounds.len();
        self.bounds.push(bound);
        self.values.get(index).copied().unwrap_or(0)
    }
}

struct NoChoice;

impl Rng for NoChoice {
    fn next_below(&mut self, _: usize) -> usize {
        panic!("a singleton must not request a random choice")
    }
}

fn edges(pairs: &[(usize, usize)]) -> Vec<Edge> {
    pairs.iter().map(|&(u, v)| Edge::new(u, v)).collect()
}

fn edge_set(tree: &Tree) -> BTreeSet<(usize, usize)> {
    let mut result = BTreeSet::new();
    for (cell, &parent) in tree.parents().iter().enumerate() {
        if cell != parent {
            let edge = Edge::new(cell, parent);
            result.insert((edge.u, edge.v));
        }
    }
    result
}

fn complete(n: usize) -> Carrier {
    let mut input = Vec::new();
    for u in 0..n {
        for v in u + 1..n {
            input.push(Edge::new(u, v));
        }
    }
    Carrier::from_edges(n, &input).unwrap()
}

fn make_tree(carrier: &Carrier, root: usize) -> (Tree, Workspace) {
    let mut work = Workspace::new(carrier.len(), carrier.edges().len()).unwrap();
    let tree = Tree::dfs(carrier, root, &mut Choices::new(&[]), &mut work).unwrap();
    (tree, work)
}

#[test]
fn reciprocal_construction_preserves_rows_and_canonical_edges() {
    let input = [Edge { u: 2, v: 0 }, Edge::new(1, 2), Edge::new(0, 1)];
    let carrier = Carrier::from_edges(3, &input).unwrap();
    assert_eq!(carrier.len(), 3);
    assert!(!carrier.is_empty());
    assert_eq!(carrier.neighbors(0), &[2, 1]);
    assert_eq!(carrier.neighbors(1), &[2, 0]);
    assert_eq!(carrier.neighbors(2), &[0, 1]);
    assert_eq!(carrier.edges(), &edges(&[(0, 2), (0, 1), (1, 2)]));
    assert!(carrier.contains_edge(Edge { u: 2, v: 0 }));
    assert!(!carrier.contains_edge(Edge::new(1, 1)));
    assert!(!carrier.contains_edge(Edge::new(0, usize::MAX)));
    assert_eq!(carrier.neighbors(usize::MAX), &[]);
    assert_eq!(
        carrier,
        Carrier::from_csr(vec![0, 2, 4, 6], vec![2, 1, 2, 0, 0, 1]).unwrap()
    );
}

#[test]
fn edge_constructor_rejects_empty_invalid_duplicate_and_disconnected_input() {
    assert_eq!(Carrier::from_edges(0, &[]), Err(Error::InvalidSize));
    assert_eq!(Carrier::from_edges(usize::MAX, &[]), Err(Error::Overflow));
    assert_eq!(
        Carrier::from_edges(2, &[Edge::new(0, 2)]),
        Err(Error::InvalidIndex)
    );
    assert_eq!(
        Carrier::from_edges(1, &[Edge::new(0, 0)]),
        Err(Error::InvalidCarrier)
    );
    assert_eq!(
        Carrier::from_edges(2, &[Edge::new(0, 1), Edge { u: 1, v: 0 }]),
        Err(Error::InvalidCarrier)
    );
    assert_eq!(Carrier::from_edges(2, &[]), Err(Error::Disconnected));
    assert_eq!(
        Carrier::from_edges(3, &[Edge::new(0, 1)]),
        Err(Error::Disconnected)
    );
}

#[test]
fn csr_constructor_guards_all_storage_boundaries() {
    assert_eq!(Carrier::from_csr(vec![], vec![]), Err(Error::InvalidSize));
    assert_eq!(Carrier::from_csr(vec![0], vec![]), Err(Error::InvalidSize));
    let malformed = [
        (vec![1, 1], vec![0]),
        (vec![0, 1], vec![]),
        (vec![0, 0], vec![0]),
        (vec![0, 2, 1], vec![1]),
        (vec![0, usize::MAX, 2], vec![1, 0]),
        (vec![0, 1, 0, 2], vec![1, 0]),
    ];
    for (offsets, neighbors) in malformed {
        assert_eq!(
            Carrier::from_csr(offsets, neighbors),
            Err(Error::InvalidCarrier)
        );
    }
    assert_eq!(
        Carrier::from_csr(vec![0, 1, 2], vec![usize::MAX, 0]),
        Err(Error::InvalidIndex)
    );
}

#[test]
fn csr_constructor_rejects_loops_duplicates_asymmetry_and_disconnection() {
    assert_eq!(
        Carrier::from_csr(vec![0, 1], vec![0]),
        Err(Error::InvalidCarrier)
    );
    assert_eq!(
        Carrier::from_csr(vec![0, 1, 1], vec![1]),
        Err(Error::InvalidCarrier)
    );
    assert_eq!(
        Carrier::from_csr(vec![0, 2, 4], vec![1, 1, 0, 0]),
        Err(Error::InvalidCarrier)
    );
    assert_eq!(
        Carrier::from_csr(vec![0, 1, 2, 3, 4], vec![1, 0, 3, 2]),
        Err(Error::Disconnected)
    );
    assert_eq!(
        Carrier::from_csr(vec![0, 0, 0], vec![]),
        Err(Error::Disconnected)
    );
}

#[test]
fn dfs_descends_immediately_and_samples_each_entered_row_once() {
    let carrier = complete(3);
    let mut work = Workspace::new(3, 3).unwrap();
    let mut choices = Choices::new(&[]);
    let tree = Tree::dfs(&carrier, 0, &mut choices, &mut work).unwrap();
    assert_eq!(tree.parents(), &[0, 0, 1]);
    assert_eq!(choices.bounds, vec![2, 2, 2]);
    tree.validate(&carrier).unwrap();

    let mut choices = Choices::new(&[1, 1, 0]);
    let tree = Tree::dfs(&carrier, 0, &mut choices, &mut work).unwrap();
    assert_eq!(tree.parents(), &[0, 2, 0]);
    assert_eq!(choices.bounds, vec![2, 2, 2]);
}

#[test]
fn singleton_constructors_and_reroot_are_stationary_without_rng() {
    let carrier = Carrier::from_csr(vec![0, 0], vec![]).unwrap();
    let mut work = Workspace::new(1, 0).unwrap();
    let mut tree = Tree::dfs(&carrier, 0, &mut NoChoice, &mut work).unwrap();
    assert_eq!(tree.parents(), &[0]);
    assert_eq!(
        Tree::scene_dfs(&carrier, &[], 0, &mut NoChoice, &mut work).unwrap(),
        tree
    );
    tree.reroot(0, &mut work).unwrap();
    tree.edit_edges(&carrier, &[], &[], &mut work).unwrap();
    assert_eq!(
        tree.exchange(&carrier, 0, Edge::new(0, 0), &mut work),
        Err(Error::InvalidTransition)
    );
    assert_eq!(tree.parents(), &[0]);
    assert_eq!(tree.root(), 0);
    tree.validate(&carrier).unwrap();
}

#[test]
fn construction_checks_choices_and_recovers_scratch_after_failure() {
    let carrier = complete(3);
    let mut work = Workspace::new(3, 3).unwrap();
    assert_eq!(
        Tree::dfs(&carrier, 0, &mut Choices::new(&[2]), &mut work),
        Err(Error::InvalidChoice)
    );
    assert_eq!(
        Tree::dfs(
            &carrier,
            0,
            &mut Choices::new(&[0, 0, usize::MAX]),
            &mut work
        ),
        Err(Error::InvalidChoice)
    );
    assert_eq!(
        Tree::dfs(&carrier, 3, &mut NoChoice, &mut work),
        Err(Error::InvalidIndex)
    );
    let tree = Tree::dfs(&carrier, 0, &mut Choices::new(&[]), &mut work).unwrap();
    assert_eq!(tree.parents(), &[0, 0, 1]);
    tree.validate(&carrier).unwrap();
}

#[test]
fn workspace_bounds_are_checked_before_choices_or_mutation() {
    assert!(matches!(Workspace::new(0, 0), Err(Error::InvalidSize)));
    assert!(matches!(
        Workspace::new(usize::MAX, 0),
        Err(Error::Overflow)
    ));
    assert!(matches!(
        Workspace::new(1, usize::MAX),
        Err(Error::Overflow)
    ));
    let carrier = complete(3);
    let (mut tree, _) = make_tree(&carrier, 0);
    let original = tree.parents().to_vec();
    let mut small_cells = Workspace::new(2, 3).unwrap();
    let mut small_edges = Workspace::new(3, 2).unwrap();
    assert_eq!(
        Tree::dfs(&carrier, 0, &mut NoChoice, &mut small_cells),
        Err(Error::InsufficientWorkspace)
    );
    assert_eq!(
        Tree::scene_dfs(&carrier, &[], 0, &mut NoChoice, &mut small_edges),
        Err(Error::InsufficientWorkspace)
    );
    assert_eq!(
        tree.reroot(2, &mut small_cells),
        Err(Error::InsufficientWorkspace)
    );
    assert_eq!(
        tree.exchange(&carrier, 1, Edge::new(0, 2), &mut small_edges),
        Err(Error::InsufficientWorkspace)
    );
    assert_eq!(tree.parents(), original);
    assert_eq!(tree.root(), 0);
}

#[test]
fn scene_constructor_contracts_forest_and_retains_original_witnesses() {
    let carrier = Carrier::from_edges(
        6,
        &edges(&[(0, 1), (2, 3), (4, 5), (0, 2), (1, 4), (3, 4), (1, 3)]),
    )
    .unwrap();
    let required = edges(&[(0, 1), (2, 3), (4, 5)]);
    let mut work = Workspace::new(6, carrier.edges().len()).unwrap();
    let mut choices = Choices::new(&[]);
    let tree = Tree::scene_dfs(&carrier, &required, 0, &mut choices, &mut work).unwrap();
    assert_eq!(choices.bounds, vec![3, 3, 2]);
    assert_eq!(tree.parents(), &[0, 0, 0, 2, 3, 4]);
    for edge in &required {
        assert!(tree.has_edge(*edge));
    }
    assert!(!tree.has_edge(Edge::new(1, 4)));
    assert!(!tree.has_edge(Edge::new(1, 3)));
    tree.validate(&carrier).unwrap();

    let tree = Tree::scene_dfs(&carrier, &required, 5, &mut Choices::new(&[]), &mut work).unwrap();
    assert_eq!(tree.root(), 5);
    assert_eq!(tree.parents(), &[1, 4, 0, 2, 5, 5]);
    tree.validate(&carrier).unwrap();
}

#[test]
fn quotient_parallel_edges_have_distinct_checked_choices() {
    let carrier = Carrier::from_edges(4, &edges(&[(0, 1), (0, 2), (1, 3), (2, 3)])).unwrap();
    let required = edges(&[(0, 1), (2, 3)]);
    let mut work = Workspace::new(4, 4).unwrap();
    let mut choices = Choices::new(&[1, 0]);
    let tree = Tree::scene_dfs(&carrier, &required, 0, &mut choices, &mut work).unwrap();
    assert_eq!(choices.bounds, vec![2, 2]);
    assert_eq!(tree.parents(), &[0, 0, 3, 1]);
    assert!(!tree.has_edge(Edge::new(0, 2)));
    assert_eq!(
        Tree::scene_dfs(
            &carrier,
            &required,
            0,
            &mut Choices::new(&[0, 2]),
            &mut work
        ),
        Err(Error::InvalidChoice)
    );
    Tree::scene_dfs(&carrier, &required, 0, &mut Choices::new(&[]), &mut work)
        .unwrap()
        .validate(&carrier)
        .unwrap();
}

#[test]
fn complete_required_tree_needs_no_quotient_choice() {
    let carrier = complete(4);
    let required = edges(&[(0, 2), (2, 1), (1, 3)]);
    let mut work = Workspace::new(4, 6).unwrap();
    let tree = Tree::scene_dfs(&carrier, &required, 3, &mut NoChoice, &mut work).unwrap();
    assert_eq!(tree.parents(), &[2, 3, 1, 3]);
    assert_eq!(edge_set(&tree), BTreeSet::from([(0, 2), (1, 2), (1, 3)]));
}

#[test]
fn scene_constructor_rejects_invalid_forest_before_rng() {
    let carrier = complete(5);
    let mut work = Workspace::new(5, 10).unwrap();
    for required in [
        edges(&[(0, 1), (1, 2), (2, 0)]),
        edges(&[(0, 1), (1, 0)]),
        edges(&[(0, 0)]),
        edges(&[(0, 5)]),
    ] {
        assert_eq!(
            Tree::scene_dfs(&carrier, &required, 0, &mut NoChoice, &mut work),
            Err(Error::InvalidForest)
        );
    }
    let path = Carrier::from_edges(3, &edges(&[(0, 1), (1, 2)])).unwrap();
    assert_eq!(
        Tree::scene_dfs(&path, &[Edge::new(0, 2)], 0, &mut NoChoice, &mut work),
        Err(Error::InvalidForest)
    );
    assert_eq!(
        Tree::scene_dfs(&carrier, &[], 5, &mut NoChoice, &mut work),
        Err(Error::InvalidIndex)
    );
}

#[test]
fn reroot_preserves_exact_edges_and_changes_only_ancestor_path() {
    let carrier = Carrier::from_edges(5, &edges(&[(0, 1), (1, 2), (1, 3), (3, 4)])).unwrap();
    let (mut tree, mut work) = make_tree(&carrier, 0);
    let before = edge_set(&tree);
    tree.reroot(4, &mut work).unwrap();
    assert_eq!(tree.parents(), &[1, 3, 1, 4, 4]);
    assert_eq!(tree.root(), 4);
    assert_eq!(edge_set(&tree), before);
    tree.validate(&carrier).unwrap();
    let parents = tree.parents().to_vec();
    assert_eq!(tree.reroot(usize::MAX, &mut work), Err(Error::InvalidIndex));
    assert_eq!(tree.parents(), parents);
    assert_eq!(tree.root(), 4);
    tree.reroot(0, &mut work).unwrap();
    assert_eq!(tree.parents(), &[0, 0, 1, 1, 3]);
}

#[test]
fn exchange_reverses_only_inside_path_and_keeps_global_root() {
    let carrier = complete(4);
    let (mut tree, mut work) = make_tree(&carrier, 0);
    assert_eq!(tree.parents(), &[0, 0, 1, 2]);
    tree.exchange(&carrier, 1, Edge { u: 3, v: 0 }, &mut work)
        .unwrap();
    assert_eq!(tree.parents(), &[0, 2, 3, 0]);
    assert_eq!(tree.root(), 0);
    assert_eq!(edge_set(&tree), BTreeSet::from([(0, 3), (1, 2), (2, 3)]));
    tree.validate(&carrier).unwrap();
    tree.reroot(3, &mut work).unwrap();
    tree.exchange(&carrier, 2, Edge::new(0, 1), &mut work)
        .unwrap();
    assert_eq!(tree.parents(), &[3, 0, 1, 3]);
    assert_eq!(tree.root(), 3);
    tree.validate(&carrier).unwrap();
}

#[test]
fn exchange_rejection_and_same_edge_replacement_preserve_parents() {
    let carrier = complete(4);
    let (mut tree, mut work) = make_tree(&carrier, 0);
    let before = tree.parents().to_vec();
    for (child, edge, error) in [
        (0, Edge::new(0, 3), Error::InvalidTransition),
        (4, Edge::new(0, 3), Error::InvalidIndex),
        (2, Edge::new(0, 1), Error::InvalidTransition),
        (1, Edge::new(1, 3), Error::InvalidTransition),
        (1, Edge::new(0, 4), Error::InvalidIndex),
        (1, Edge::new(0, 0), Error::InvalidTransition),
    ] {
        assert_eq!(tree.exchange(&carrier, child, edge, &mut work), Err(error));
        assert_eq!(tree.parents(), before);
        assert_eq!(tree.root(), 0);
    }
    tree.exchange(&carrier, 2, Edge::new(1, 2), &mut work)
        .unwrap();
    assert_eq!(tree.parents(), before);
    tree.exchange(&carrier, 1, Edge::new(0, 3), &mut work)
        .unwrap();
    tree.validate(&carrier).unwrap();
}

#[test]
fn batch_edits_join_detached_components_before_root_component_atomically() {
    let carrier = complete(5);
    let (mut tree, mut work) = make_tree(&carrier, 0);
    let remove = edges(&[(0, 1), (2, 3)]);
    let add = edges(&[(2, 4), (0, 3)]);
    tree.edit_edges(&carrier, &remove, &add, &mut work).unwrap();
    assert_eq!(tree.parents(), &[0, 2, 4, 0, 3]);
    assert_eq!(tree.root(), 0);
    assert_eq!(
        edge_set(&tree),
        BTreeSet::from([(0, 3), (1, 2), (2, 4), (3, 4)])
    );
    tree.validate(&carrier).unwrap();
    tree.edit_edges(&carrier, &add, &remove, &mut work).unwrap();
    assert_eq!(tree.parents(), &[0, 0, 1, 2, 3]);
}

#[test]
fn late_batch_cycle_rejection_keeps_every_published_parent() {
    let carrier = complete(5);
    let (mut tree, mut work) = make_tree(&carrier, 0);
    let before = tree.parents().to_vec();
    let remove = edges(&[(0, 1), (2, 3)]);
    let cyclic = edges(&[(0, 2), (0, 1)]);
    assert_eq!(
        tree.edit_edges(&carrier, &remove, &cyclic, &mut work),
        Err(Error::InvalidTransition)
    );
    assert_eq!(tree.parents(), before);
    assert_eq!(tree.root(), 0);
    let add = edges(&[(0, 3), (1, 4)]);
    tree.edit_edges(&carrier, &remove, &add, &mut work).unwrap();
    assert_eq!(tree.parents(), &[0, 4, 1, 0, 3]);
    tree.validate(&carrier).unwrap();
}

#[test]
fn batch_preflight_rejects_duplicate_absent_existing_and_noncarrier_edges() {
    let carrier = complete(4);
    let (mut tree, mut work) = make_tree(&carrier, 0);
    let before = tree.parents().to_vec();
    for (remove, add) in [
        (edges(&[(0, 1)]), edges(&[])),
        (edges(&[(0, 1), (1, 0)]), edges(&[(0, 2), (0, 3)])),
        (edges(&[(0, 1), (2, 3)]), edges(&[(0, 2), (2, 0)])),
        (edges(&[(0, 2)]), edges(&[(0, 3)])),
        (edges(&[(0, 1)]), edges(&[(1, 2)])),
    ] {
        assert_eq!(
            tree.edit_edges(&carrier, &remove, &add, &mut work),
            Err(Error::InvalidTransition)
        );
        assert_eq!(tree.parents(), before);
    }
    let path = Carrier::from_edges(4, &edges(&[(0, 1), (1, 2), (2, 3)])).unwrap();
    assert_eq!(
        tree.edit_edges(&path, &[Edge::new(0, 1)], &[Edge::new(0, 3)], &mut work),
        Err(Error::InvalidTransition)
    );
    assert_eq!(tree.parents(), before);
    let remove = edges(&[(0, 1), (2, 3)]);
    let add = edges(&[(2, 3), (0, 1)]);
    tree.edit_edges(&carrier, &remove, &add, &mut work).unwrap();
    assert_eq!(tree.parents(), before);
}

#[test]
fn validation_rejects_incompatible_carriers_and_mutation_preserves_state() {
    let complete = complete(4);
    let (mut tree, mut work) = make_tree(&complete, 0);
    let other = Carrier::from_edges(4, &edges(&[(0, 1), (0, 2), (0, 3)])).unwrap();
    assert_eq!(tree.validate(&other), Err(Error::InvalidTree));
    assert_eq!(
        tree.validate(&Carrier::from_edges(1, &[]).unwrap()),
        Err(Error::InvalidTree)
    );
    let before = tree.parents().to_vec();
    assert_eq!(
        tree.exchange(&other, 1, Edge::new(0, 3), &mut work),
        Err(Error::InvalidTree)
    );
    assert_eq!(tree.parents(), before);
    tree.validate(&complete).unwrap();
}

#[test]
fn every_single_exchange_matches_independent_cut_connectivity() {
    let carrier = complete(5);
    for root in 0..5 {
        for child in 0..5 {
            if child == root {
                continue;
            }
            for &attach in carrier.edges() {
                let (mut tree, mut work) = make_tree(&carrier, root);
                let before_parents = tree.parents().to_vec();
                let mut expected = edge_set(&tree);
                let cut = Edge::new(child, tree.parents()[child]);
                expected.remove(&(cut.u, cut.v));
                let mut reached = BTreeSet::from([attach.u]);
                loop {
                    let old_len = reached.len();
                    for &(u, v) in &expected {
                        if reached.contains(&u) || reached.contains(&v) {
                            reached.insert(u);
                            reached.insert(v);
                        }
                    }
                    if reached.len() == old_len {
                        break;
                    }
                }
                let result = tree.exchange(&carrier, child, attach, &mut work);
                if reached.contains(&attach.v) {
                    assert_eq!(result, Err(Error::InvalidTransition));
                    assert_eq!(tree.parents(), before_parents);
                } else {
                    result.unwrap();
                    expected.insert((attach.u, attach.v));
                    assert_eq!(edge_set(&tree), expected);
                    tree.validate(&carrier).unwrap();
                }
                assert_eq!(tree.root(), root);
            }
        }
    }
}
