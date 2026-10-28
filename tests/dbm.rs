//! Public DBM API: constructors, accessors,
//! dimension limits, storage-level equality and the workspace.
//!
//! Closure itself is not public until #10; it is tested differentially
//! against the oracle in `src/dbm/tests.rs`.

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use clock_dbm::{Dbm, Error, MAX_VARIABLES, Workspace};

fn hash(z: &Dbm) -> u64 {
    let mut h = DefaultHasher::new();
    z.hash(&mut h);
    h.finish()
}

#[test]
fn constructors_for_small_dimensions() {
    for n in [0, 1, 2, 4] {
        for (z, empty) in [
            (Dbm::zero(n).unwrap(), false),
            (Dbm::universe(n).unwrap(), false),
            (Dbm::empty(n).unwrap(), true),
        ] {
            assert_eq!(z.variables(), n);
            assert_eq!(z.dimension(), n + 1);
            assert_eq!(z.is_empty(), empty);
        }
    }
}

#[test]
fn dimension_limits() {
    for n in [MAX_VARIABLES + 1, MAX_VARIABLES + 2, usize::MAX] {
        let e = Error::TooManyVariables { requested: n };
        assert_eq!(Dbm::zero(n), Err(e));
        assert_eq!(Dbm::universe(n), Err(e));
        assert_eq!(Dbm::empty(n), Err(e));
    }
    // The empty zone allocates nothing, so the largest dimension is cheap.
    let e = Dbm::empty(MAX_VARIABLES).unwrap();
    assert_eq!(e.variables(), MAX_VARIABLES);
    assert_eq!(e.dimension(), MAX_VARIABLES + 1);
    assert!(e.is_empty());
}

#[test]
fn equality_is_semantic() {
    // n = 0: zero and universe are the same one-point zone.
    assert_eq!(Dbm::zero(0).unwrap(), Dbm::universe(0).unwrap());
    assert_eq!(
        hash(&Dbm::zero(0).unwrap()),
        hash(&Dbm::universe(0).unwrap())
    );
    for n in [1, 2, 4] {
        assert_ne!(Dbm::zero(n).unwrap(), Dbm::universe(n).unwrap());
        assert_ne!(Dbm::zero(n).unwrap(), Dbm::empty(n).unwrap());
    }
    // The empty zone remembers its dimension.
    assert_ne!(Dbm::empty(2).unwrap(), Dbm::empty(3).unwrap());
    assert_ne!(Dbm::zero(2).unwrap(), Dbm::zero(3).unwrap());
    for z in [
        Dbm::zero(3).unwrap(),
        Dbm::universe(3).unwrap(),
        Dbm::empty(3).unwrap(),
    ] {
        let c = z.clone();
        assert_eq!(c, z);
        assert_eq!(hash(&c), hash(&z));
    }
}

#[test]
fn workspace() {
    fn send<T: Send>() {}
    send::<Workspace>();
    send::<Dbm>();
    let _ = Workspace::new();
    let _ = Workspace::default();
    let _ = Workspace::with_capacity(4);
    let _ = Workspace::with_capacity(usize::MAX);
}
