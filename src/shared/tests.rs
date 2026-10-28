//! Tests of `SharedDbm`: snapshot isolation, exact agreement
//! with `Dbm` (results and errors), the no-copy shortcuts, pointer-independent
//! `Eq`/`Hash`, and workspace reuse.

use super::*;
use crate::bounds::MAX_CONSTANT;
use crate::ops::test_support::{apply, cons, initial, start_zone, var};
use crate::oracle;
use std::collections::HashSet;
use std::hash::{BuildHasher, RandomState};
// `super::*` brings creusot-std's `vec!` too (as in `dbm/tests.rs`).
use std::vec;

use oracle::random::{self, SplitMix64};
use oracle::scenario::{Op, le, lt};
use oracle::{OracleConstraint, fixtures};

fn c(g: OracleConstraint) -> Constraint {
    cons(&[g])[0]
}

/// `x₁ ∈ [1, 4]`, `x₂ ∈ [0, 3]`, `x₁ − x₂ ≤ 2` over two clocks.
fn sample() -> Dbm {
    start_zone(2, &[le(1, 0, 4), le(0, 1, -1), le(2, 0, 3), le(1, 2, 2)])
}

/// `SharedDbm` counterpart of `test_support::apply`.
fn apply_shared(z: SharedDbm, op: &Op, ws: &mut Workspace) -> Result<SharedDbm, Error> {
    match op {
        Op::Constrain(g) => z.try_constrain(c(g.clone())),
        Op::ConstrainAll(gs) => z.try_constrain_all(&cons(gs), ws),
        Op::Future => Ok(z.future()),
        Op::Past => Ok(z.past()),
        Op::Reset { x, value } => z.try_reset(var(*x), i32::try_from(*value).unwrap()),
        Op::ResetZero(x) => z.try_reset_zero(var(*x)),
        Op::Free(x) => z.try_free(var(*x)),
        Op::Intersect(gs) => {
            let e = SharedDbm::try_from_constraints(z.variables(), &cons(gs), ws)?;
            z.try_intersect(&e, ws)
        }
        Op::ExtrapolateMax(m) => {
            let m: Vec<i32> = m.iter().map(|&c| i32::try_from(c).unwrap()).collect();
            z.try_extrapolate_max(&MaxBounds::new(m)?, ws)
        }
    }
}

/// Applies `op` to a unique handle and to a shared one, checks both against
/// the owned result, and checks that the other handle kept its snapshot.
#[track_caller]
fn check_op(label: &str, z: &Dbm, op: &Op, ws: &mut Workspace) -> Result<Dbm, Error> {
    let expected = apply(z.clone(), op);
    let unique = apply_shared(SharedDbm::from(z.clone()), op, ws).map(SharedDbm::into_dbm);
    assert_eq!(unique, expected, "{label}: unique handle, {op:?}");
    let keep = SharedDbm::from(z.clone());
    let shared = apply_shared(keep.clone(), op, ws).map(SharedDbm::into_dbm);
    assert_eq!(shared, expected, "{label}: shared handle, {op:?}");
    assert_eq!(keep.as_dbm(), z, "{label}: snapshot changed by {op:?}");
    expected
}

#[test]
fn snapshot_isolation_for_every_update() {
    let z = sample();
    let ws = &mut Workspace::new();
    let ops = [
        Op::Constrain(le(1, 0, 2)), // tightens
        Op::Constrain(le(1, 0, 9)), // implied
        Op::Constrain(lt(1, 0, 1)), // contradicts x₁ ≥ 1
        Op::ConstrainAll(vec![le(2, 0, 1), le(0, 2, -1)]),
        Op::ConstrainAll(vec![le(1, 0, 9), le(2, 0, 9)]),
        Op::ConstrainAll(vec![le(2, 0, 1), lt(0, 1, -4)]),
        Op::Intersect(vec![le(1, 0, 3)]),
        Op::Intersect(vec![le(1, 0, 9)]),
        Op::Intersect(vec![lt(1, 0, 1)]),
        Op::Future,
        Op::Past,
        Op::ResetZero(1),
        Op::Reset { x: 2, value: 7 },
        Op::Free(1),
        Op::ExtrapolateMax(vec![2, 1]),
    ];
    for op in &ops {
        check_op("sample", &z, op, ws).unwrap();
    }
}

#[test]
fn range_error_leaves_other_snapshots_unchanged() {
    let z = SharedDbm::from(sample());
    let keep = z.clone();
    let x = var(1);
    let big = i32::try_from(i64::from(MAX_CONSTANT) + 1).unwrap();
    assert_eq!(z.clone().try_reset(x, big), Err(Error::Range));
    assert_eq!(keep.as_dbm(), &sample());
    // Range is not emptiness: on ∅_d the same reset succeeds.
    let e = SharedDbm::empty(2).unwrap();
    assert_eq!(e.clone().try_reset(x, big), Ok(e));

    // Range failures inside the closure kernels, on shared handles.
    let ws = &mut Workspace::new();
    let m = i64::from(MAX_CONSTANT);
    let ks = [-m, -m / 2 - 1, 0, m / 2 + 1, m];
    let mut ranges = 0;
    for &a in &ks {
        for &b in &ks {
            let Ok(z) = Dbm::try_from_constraints(2, &cons(&[le(1, 0, a), le(0, 2, b)]), ws) else {
                continue;
            };
            for &k in &ks {
                for g in [le(2, 1, k), le(1, 2, k), lt(0, 1, k)] {
                    for op in [Op::Constrain(g.clone()), Op::ConstrainAll(vec![g.clone()])] {
                        if check_op("large constants", &z, &op, ws) == Err(Error::Range) {
                            ranges += 1;
                        }
                    }
                }
            }
        }
    }
    assert!(ranges > 0, "no Range failure exercised");
}

#[test]
fn argument_errors_match_dbm_also_on_empty() {
    let ws = &mut Workspace::new();
    for z in [sample(), Dbm::empty(2).unwrap()] {
        let s = SharedDbm::from(z.clone());
        let far = Constraint::le(Clock::new(3).unwrap(), Clock::ZERO, 0).unwrap();
        assert_eq!(
            s.clone().try_constrain(far).map(SharedDbm::into_dbm),
            z.clone().try_constrain(far)
        );
        let ok = c(le(1, 0, 0));
        assert_eq!(
            s.clone()
                .try_constrain_all(&[ok, far], ws)
                .map(SharedDbm::into_dbm),
            z.clone().try_constrain_all(&[ok, far], ws)
        );
        assert_eq!(
            s.clone().try_reset(var(1), -1).map(SharedDbm::into_dbm),
            z.clone().try_reset(var(1), -1)
        );
        assert_eq!(
            s.clone().try_free(var(3)).map(SharedDbm::into_dbm),
            z.clone().try_free(var(3))
        );
        let other = SharedDbm::universe(3).unwrap();
        assert_eq!(
            s.clone().try_intersect(&other, ws).map(SharedDbm::into_dbm),
            z.clone().try_intersect(other.as_dbm(), ws)
        );
        let m = MaxBounds::new(vec![1]).unwrap();
        assert_eq!(
            s.clone()
                .try_extrapolate_max(&m, ws)
                .map(SharedDbm::into_dbm),
            z.clone().try_extrapolate_max(&m, ws)
        );
    }
}

#[test]
fn fixtures_and_random_scenarios_agree_with_dbm() {
    let ws = &mut Workspace::new();
    let mut steps = 0;
    let mut run = |label: &str, s: &oracle::scenario::Scenario| {
        let mut z = initial(s);
        for op in &s.ops {
            match check_op(label, &z, op, ws) {
                Ok(r) => z = r,
                Err(_) => break,
            }
            steps += 1;
        }
    };
    for f in fixtures::all() {
        run(&f.name, &f.scenario);
    }
    for seed in random::seeds(300) {
        let mut rng: SplitMix64 = random::case_rng("shared", seed);
        let s = random::scenario(&mut rng, 6, 12);
        run(&format!("seed {seed}"), &s);
    }
    assert!(steps > 1000, "too few steps compared: {steps}");
}

#[test]
fn shortcuts_do_not_copy() {
    let ws = &mut Workspace::new();
    let z = SharedDbm::from(sample());
    let keep = z.clone();

    // Implied constraint: the same handle.
    let r = z.clone().try_constrain(c(le(1, 0, 9))).unwrap();
    assert!(r.ptr_eq(&keep));
    let r = z
        .clone()
        .try_constrain_all(&cons(&[le(1, 0, 9), le(2, 0, 3)]), ws)
        .unwrap();
    assert!(r.ptr_eq(&keep));

    // Contradiction: a fresh ∅_d, the snapshot untouched.
    let r = z.clone().try_constrain(c(lt(1, 0, 1))).unwrap();
    assert!(r.is_empty() && !r.ptr_eq(&keep));
    let r = z
        .clone()
        .try_constrain_all(&cons(&[le(2, 0, 1), lt(1, 0, 1)]), ws)
        .unwrap();
    assert!(r.is_empty());
    assert_eq!(keep.as_dbm(), &sample());

    // Intersection with a superset, or with itself.
    let sup = SharedDbm::universe(2).unwrap();
    assert!(z.clone().try_intersect(&sup, ws).unwrap().ptr_eq(&keep));
    assert!(z.clone().try_intersect(&keep, ws).unwrap().ptr_eq(&keep));

    // Empty input.
    let e = SharedDbm::empty(2).unwrap();
    let r = e.clone().try_constrain(c(le(1, 0, 0))).unwrap();
    assert!(r.ptr_eq(&e));
    assert!(e.clone().try_intersect(&keep, ws).unwrap().ptr_eq(&e));

    // A tightening update detaches.
    let r = z.try_constrain(c(le(1, 0, 2))).unwrap();
    assert!(!r.ptr_eq(&keep));
    assert_eq!(keep.as_dbm(), &sample());
}

#[test]
fn unique_updates_keep_the_allocation() {
    let z = SharedDbm::from(sample());
    let before = Rc::as_ptr(&z.0);
    let z = z.try_constrain(c(le(1, 0, 2))).unwrap().future();
    assert_eq!(Rc::as_ptr(&z.0), before);
}

#[test]
fn equality_and_hash_ignore_pointers() {
    let a = SharedDbm::from(sample());
    let b = SharedDbm::from(sample());
    assert!(!a.ptr_eq(&b));
    assert_eq!(a, b);
    let h = RandomState::new();
    assert_eq!(h.hash_one(&a), h.hash_one(&b));
    assert_eq!(h.hash_one(&a), h.hash_one(sample()));

    // Built along different paths.
    let ws = &mut Workspace::new();
    let gs = cons(&[le(1, 0, 4), le(0, 1, -1), le(2, 0, 3), le(1, 2, 2)]);
    let mut rev = gs.clone();
    rev.reverse();
    let d = SharedDbm::try_from_constraints(2, &rev, ws).unwrap();
    assert_eq!(a, d);
    assert_eq!(h.hash_one(&a), h.hash_one(&d));

    let set: HashSet<SharedDbm> = [a.clone(), b, d, a.clone().future()].into_iter().collect();
    assert_eq!(set.len(), 2);

    // Different dimensions are never equal, also when empty.
    assert_ne!(SharedDbm::empty(2).unwrap(), SharedDbm::empty(3).unwrap());
    assert_ne!(SharedDbm::zero(2).unwrap(), SharedDbm::zero(3).unwrap());
    assert_ne!(a, SharedDbm::empty(2).unwrap());
}

#[test]
fn workspace_reuse_has_no_effect() {
    let mut shared_ws = Workspace::new();
    let mut rng = random::case_rng("shared-workspace", 0);
    // Large dimensions first, then small ones, then large again.
    for &n in &[8usize, 2, 6, 1, 0, 8, 3] {
        for _ in 0..20 {
            let z = Dbm::try_from_constraints(
                n,
                &cons(&random::consistent_constraints(&mut rng, n, 2 * n + 1, 6).0),
                &mut Workspace::new(),
            )
            .unwrap();
            let ops = [
                Op::ConstrainAll((0..3).map(|_| random::constraint(&mut rng, n, 6)).collect()),
                Op::Intersect((0..3).map(|_| random::constraint(&mut rng, n, 6)).collect()),
                Op::ExtrapolateMax((0..n).map(|_| rng.range(0, 6)).collect()),
            ];
            for op in &ops {
                let fresh = apply(z.clone(), op);
                let reused = apply_shared(SharedDbm::from(z.clone()), op, &mut shared_ws)
                    .map(SharedDbm::into_dbm);
                assert_eq!(reused, fresh, "n = {n}, {op:?}");
            }
        }
    }
}

#[test]
fn conversions() {
    let z = sample();
    let s = SharedDbm::from(z.clone());
    assert_eq!(s.as_dbm(), &z);
    assert_eq!(<SharedDbm as AsRef<Dbm>>::as_ref(&s), &z);
    assert_eq!((s.variables(), s.dimension(), s.is_empty()), (2, 3, false));

    assert_eq!(s.into_dbm(), z);

    // Shared: the other handle is untouched.
    let s = SharedDbm::from(z.clone());
    let keep = s.clone();
    let owned = s.into_dbm().try_reset_zero(var(1)).unwrap();
    assert_ne!(owned, z);
    assert_eq!(keep.as_dbm(), &z);

    // Queries forward to `Dbm`.
    let g = c(le(1, 0, 4));
    assert_eq!(keep.entails(&g), z.entails(&g));
    assert_eq!(keep.intersects_constraint(&g), z.intersects_constraint(&g));
    let (i, j) = (Clock::new(1).unwrap(), Clock::ZERO);
    assert_eq!(keep.difference_bound(i, j), z.difference_bound(i, j));
    let u = SharedDbm::universe(2).unwrap();
    assert_eq!(keep.is_subset_of(&u), z.is_subset_of(u.as_dbm()));
}
