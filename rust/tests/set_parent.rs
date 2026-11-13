use labyrinth_core::tree::{random_reparent, set_parent, Error, Rng};

struct Fixed(usize);
impl Rng for Fixed {
    fn next_below(&mut self, bound: usize) -> usize {
        self.0 % bound
    }
}

#[test]
fn valid_update_changes_only_child() {
    let mut p = vec![0, 0, 1, 2];
    assert_eq!(set_parent(&mut p, 3, 0), Ok(()));
    assert_eq!(p, vec![0, 0, 1, 0]);
}

#[test]
fn singleton_rejects_self_parent() {
    let mut p = vec![0];
    assert_eq!(set_parent(&mut p, 0, 0), Err(Error::SelfParent));
    assert_eq!(p, vec![0]);
}

#[test]
fn invalid_index_leaves_storage_unchanged() {
    let mut p = vec![0, 0];
    assert_eq!(set_parent(&mut p, 2, 0), Err(Error::InvalidIndex));
    assert_eq!(set_parent(&mut p, 0, 5), Err(Error::InvalidIndex));
    assert_eq!(p, vec![0, 0]);
}

#[test]
fn cycle_is_rejected() {
    let mut p = vec![0, 0, 1];
    assert_eq!(set_parent(&mut p, 0, 2), Err(Error::Cycle));
    assert_eq!(p, vec![0, 0, 1]);
}

#[test]
fn random_adapter_uses_set_parent() {
    let mut p = vec![0, 0, 1];
    assert_eq!(random_reparent(&mut p, 2, &mut Fixed(0)), Ok(()));
    assert_eq!(p, vec![0, 0, 0]);
    let mut empty: Vec<usize> = vec![];
    assert_eq!(
        random_reparent(&mut empty, 0, &mut Fixed(0)),
        Err(Error::InvalidIndex)
    );
}
