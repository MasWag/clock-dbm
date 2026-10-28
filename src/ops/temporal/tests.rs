//! Differential tests of the temporal operations against the independent
//! exact oracle (`tests/support/oracle/`).
//!
//! Every successful result also passes the debug-build canonicity check of
//! `Matrix::publish_canonical` and the public-invariant check of the
//! oracle's `check_outcome`. Passing tests provide regression evidence;
//! the temporal operation contracts are proved separately with Creusot.

use super::*;
use crate::bounds::{MAX_CONSTANT, MIN_CONSTANT};
use crate::dbm::{MAX_VARIABLES, Workspace};
use crate::ops::test_support::{
    as_oracle, assert_outcome, cons, exact, oracle_zone, replay, start_zone, time_op, var,
};
use num_bigint::BigInt;
use std::vec;

use crate::oracle;

use oracle::compare::{PRODUCTION_MAX_CONSTANT, RangeExpectation, classify_range};
use oracle::random::{self, SplitMix64};
use oracle::scenario::{Op, Scenario, Start, le, lt};
use oracle::valuation::{Valuation, in_past_image};
use oracle::{OracleConstraint, OracleDbm, OracleError, fixtures};

/// Every temporal operation on `universe(n) ∧ start`, checked exactly
/// against the oracle (none of them may fail with `Range` for small values),
/// plus the laws of `past`.
fn check_all_ops(label: &str, n: usize, start: &[OracleConstraint], values: &[i32]) {
    let z = start_zone(n, start);
    let o = oracle_zone(n, start);
    let must = RangeExpectation::MustSucceed;
    assert_outcome(
        &format!("{label} future"),
        &Ok(z.clone().future()),
        &Ok(o.future()),
        must,
    );
    check_past_laws(label, &z);
    assert_outcome(
        &format!("{label} past"),
        &Ok(z.clone().past()),
        &Ok(o.past()),
        must,
    );
    for x in 1..=n {
        let l = format!("{label} x{x}");
        assert_outcome(
            &format!("{l} reset_zero"),
            &z.clone().try_reset_zero(var(x)),
            &o.reset_zero(x),
            must,
        );
        assert_outcome(
            &format!("{l} free"),
            &z.clone().try_free(var(x)),
            &o.free(x),
            must,
        );
        for &c in values {
            assert_outcome(
                &format!("{l} reset {c}"),
                &z.clone().try_reset(var(x), c),
                &o.reset(x, c),
                must,
            );
        }
    }
}

fn row(z: &Dbm, i: usize) -> Vec<String> {
    (0..z.dimension())
        .map(|j| exact(z.entry(i, j)).to_string())
        .collect()
}

// ----- worked examples of reset, free and future -----

/// `D = zero(2)↑ ∧ x ≤ 1 ∧ x ≥ 1`, the single point `{x = y = 1}`.
fn point_one_one() -> Dbm {
    Dbm::zero(2)
        .unwrap()
        .future()
        .try_constrain(cons(&[le(1, 0, 1)])[0])
        .unwrap()
        .try_constrain(cons(&[le(0, 1, -1)])[0])
        .unwrap()
}

#[track_caller]
fn assert_rows(z: &Dbm, rows: &[&[&str]]) {
    for (i, r) in rows.iter().enumerate() {
        assert_eq!(row(z, i), *r, "row {i} of {z:?}");
    }
}

#[test]
fn worked_8_4_reset_versus_free() {
    let d = point_one_one();
    assert_rows(
        &d,
        &[
            &["<=0", "<=-1", "<=-1"],
            &["<=1", "<=0", "<=0"],
            &["<=1", "<=0", "<=0"],
        ],
    );
    let reset0 = d.clone().try_reset_zero(var(1)).unwrap();
    assert_rows(
        &reset0,
        &[
            &["<=0", "<=0", "<=-1"],
            &["<=0", "<=0", "<=-1"],
            &["<=1", "<=1", "<=0"],
        ],
    );
    let freed = d.clone().try_free(var(1)).unwrap();
    assert_rows(
        &freed,
        &[
            &["<=0", "<=0", "<=-1"],
            &["inf", "<=0", "inf"],
            &["<=1", "<=1", "<=0"],
        ],
    );
    let reset2 = d.clone().try_reset(var(1), 2).unwrap();
    assert_rows(
        &reset2,
        &[
            &["<=0", "<=-2", "<=-1"],
            &["<=2", "<=0", "<=1"],
            &["<=1", "<=-1", "<=0"],
        ],
    );
    let up = reset0.clone().future();
    assert_rows(
        &up,
        &[
            &["<=0", "<=0", "<=-1"],
            &["inf", "<=0", "<=-1"],
            &["inf", "<=1", "<=0"],
        ],
    );
    assert_ne!(up, freed);
    let o = oracle_zone(2, &[le(1, 0, 1), le(0, 1, -1), le(2, 0, 1), le(0, 2, -1)]);
    let must = RangeExpectation::MustSucceed;
    assert_outcome("reset0", &Ok(reset0), &o.reset_zero(1), must);
    assert_outcome("free", &Ok(freed), &o.free(1), must);
    assert_outcome("reset2", &Ok(reset2), &o.reset(1, 2), must);
    assert_outcome("up", &Ok(up), &Ok(o.reset_zero(1).unwrap().future()), must);
}

// ----- regressions -----

#[test]
fn future_advances_all_clocks_together() {
    // {x = 1, y = 0}: future is the ray {(1 + t, t) | t ≥ 0}.
    let start = [le(1, 0, 1), le(0, 1, -1), le(2, 0, 0)];
    let z = start_zone(2, &start).future();
    assert_eq!(exact(z.entry(1, 2)).to_string(), "<=1");
    assert_eq!(exact(z.entry(2, 1)).to_string(), "<=-1");
    assert!(z.entry(1, 0).is_infinite() && z.entry(2, 0).is_infinite());
    let r = as_oracle(&z);
    assert!(r.contains(&Valuation::from_integers(&[3, 2])));
    assert!(r.contains(&Valuation::from_ratios(&[(5, 2), (3, 2)])));
    // Independent delays would reach these.
    assert!(!r.contains(&Valuation::from_integers(&[2, 0])));
    assert!(!r.contains(&Valuation::from_integers(&[1, 1])));
    assert_outcome(
        "future",
        &Ok(z),
        &Ok(oracle_zone(2, &start).future()),
        RangeExpectation::MustSucceed,
    );
    // Lower bounds and strict differences survive.
    let start = [lt(0, 1, -2), lt(1, 2, 3), le(2, 1, -1), le(1, 0, 7)];
    check_all_ops("strict ray", 2, &start, &[0, 4]);
    let z = start_zone(2, &start).future();
    assert_eq!(exact(z.entry(0, 1)).to_string(), "<-2");
    assert_eq!(exact(z.entry(1, 2)).to_string(), "<3");
}

#[test]
fn free_is_not_reset() {
    let d = point_one_one();
    let freed = d.clone().try_free(var(1)).unwrap();
    let reset = d.clone().try_reset_zero(var(1)).unwrap();
    assert_ne!(freed, reset);
    assert_eq!(freed.variables(), 2, "free keeps the clock");
    let (f, r) = (as_oracle(&freed), as_oracle(&reset));
    let far = Valuation::from_integers(&[5, 1]);
    assert!(f.contains(&far) && !r.contains(&far));
    // Free contains every reset of x, and nothing moves y.
    for x in [0, 1, 2, 7] {
        assert!(f.contains(&Valuation::from_integers(&[x, 1])));
        assert!(!f.contains(&Valuation::from_integers(&[x, 2])));
        let rx = d.clone().try_reset(var(1), x as i32).unwrap();
        assert!(as_oracle(&rx).is_subset_of(&f).unwrap());
    }
    // Neither is future after reset (y would advance too).
    let up = reset.future();
    assert!(as_oracle(&up).contains(&Valuation::from_integers(&[3, 4])));
    assert!(!f.contains(&Valuation::from_integers(&[3, 4])));
}

#[test]
fn reset_and_free_preserve_the_other_clocks() {
    let mut rng = random::case_rng("temporal_preserve", 0);
    for n in 1..=6 {
        for _ in 0..20 {
            let (cs, _) = random::consistent_constraints(&mut rng, n, 3 * n, 20);
            let z = start_zone(n, &cs);
            let k = rng.index(n) + 1;
            let c = rng.range(0, 30) as i32;
            for (name, r) in [
                ("reset", z.clone().try_reset(var(k), c).unwrap()),
                ("reset_zero", z.clone().try_reset_zero(var(k)).unwrap()),
                ("free", z.clone().try_free(var(k)).unwrap()),
            ] {
                for i in 0..=n {
                    for j in 0..=n {
                        if i != k && j != k {
                            assert_eq!(r.entry(i, j), z.entry(i, j), "{name} ({i},{j})");
                        }
                    }
                }
                if name != "free" {
                    let c = if name == "reset" { c } else { 0 };
                    assert_eq!(r.entry(k, 0), Bound::le(c).unwrap(), "{name}: x{k} = {c}");
                    assert_eq!(r.entry(0, k), Bound::le(-c).unwrap(), "{name}: x{k} = {c}");
                }
            }
        }
    }
}

#[test]
fn empty_zones_keep_their_dimension() {
    for n in [0usize, 1, 2, 5] {
        let e = Dbm::empty(n).unwrap();
        let f = e.clone().future();
        assert!(f.is_empty() && f.variables() == n);
        assert_eq!(e.clone().past(), e);
        for x in 1..=n {
            for r in [
                e.clone().try_reset_zero(var(x)),
                e.clone().try_reset(var(x), 3),
                e.clone().try_reset(var(x), MAX_CONSTANT),
                // Range is checked after emptiness.
                e.clone().try_reset(var(x), MAX_CONSTANT + 1),
                e.clone().try_reset(var(x), i32::MAX),
                e.clone().try_free(var(x)),
            ] {
                assert_eq!(r, Ok(Dbm::empty(n).unwrap()));
            }
        }
    }
}

// ----- past -----

/// The laws `Z ⊆ past(Z)` and `past(past(Z)) = past(Z)`, with the clock
/// count and emptiness kept.
fn check_past_laws(label: &str, z: &Dbm) {
    let p = z.clone().past();
    assert_eq!(p.variables(), z.variables(), "{label}: past clock count");
    assert_eq!(p.is_empty(), z.is_empty(), "{label}: past emptiness");
    assert_eq!(z.is_subset_of(&p), Ok(true), "{label}: Z ⊆ past(Z)");
    assert_eq!(p.clone().past(), p, "{label}: past is idempotent");
}

#[test]
fn past_of_zero_and_universe() {
    for n in [0usize, 1, 2, 5] {
        // Only the origin reaches the origin: v + t = 0 forces v = 0.
        let zero = Dbm::zero(n).unwrap();
        assert_eq!(zero.clone().past(), zero);
        let u = Dbm::universe(n).unwrap();
        assert_eq!(u.clone().past(), u);
        // The past of the future of the origin is the whole diagonal.
        let diagonal = zero.clone().future();
        assert_eq!(diagonal.clone().past(), diagonal);
        check_past_laws(&format!("zero({n})"), &zero);
        check_past_laws(&format!("universe({n})"), &u);
    }
}

/// Exact expected results; `start` and `expected` describe
/// `universe(n) ∧ constraints`.
#[test]
fn past_examples() {
    #[allow(clippy::type_complexity)]
    let cases: Vec<(&str, usize, Vec<OracleConstraint>, Vec<OracleConstraint>)> = vec![
        // Lower bounds go, upper bounds stay.
        (
            "x in [2, 5]",
            1,
            vec![le(0, 1, -2), le(1, 0, 5)],
            vec![le(1, 0, 5)],
        ),
        (
            "2 < x < 5",
            1,
            vec![lt(0, 1, -2), lt(1, 0, 5)],
            vec![lt(1, 0, 5)],
        ),
        // A point becomes a diagonal segment through the origin.
        (
            "x = 3, y = 1",
            2,
            vec![le(1, 0, 3), le(0, 1, -3), le(2, 0, 1), le(0, 2, -1)],
            vec![le(1, 0, 3), le(2, 0, 1), le(1, 2, 2), le(2, 1, -2)],
        ),
        // An implied lower bound survives: x − y ≥ 5 ∧ y ≥ 0 ⇒ x ≥ 5.
        (
            "x - y >= 5, y >= 3",
            2,
            vec![le(2, 1, -5), le(0, 2, -3)],
            vec![le(2, 1, -5)],
        ),
        // The same with a strict difference: x − y > 5 ⇒ x > 5.
        (
            "x - y > 5, y > 3",
            2,
            vec![lt(2, 1, -5), lt(0, 2, -3)],
            vec![lt(2, 1, -5)],
        ),
        // Chains of differences: z − y ≥ 1, y − x ≥ 2 ⇒ z ≥ 3, y ≥ 2. The
        // differences implied by x ≥ 4 and z ≤ 20 (y − x ≤ 15, z − x ≤ 16,
        // z − y ≤ 14) are differences, so they stay in the past.
        (
            "chain",
            3,
            vec![le(2, 3, -1), le(1, 2, -2), le(0, 1, -4), le(3, 0, 20)],
            vec![
                le(2, 3, -1),
                le(1, 2, -2),
                le(3, 0, 20),
                le(2, 1, 15),
                le(3, 1, 16),
                le(3, 2, 14),
            ],
        ),
    ];
    for (label, n, start, expected) in cases {
        let z = start_zone(n, &start);
        let p = z.clone().past();
        assert_eq!(p, start_zone(n, &expected), "{label}");
        assert_outcome(
            label,
            &Ok(p.clone()),
            &Ok(oracle_zone(n, &start).past()),
            RangeExpectation::MustSucceed,
        );
        check_past_laws(label, &z);
        // Every example's past is strictly larger than the zone.
        assert_eq!(p.is_subset_of(&z), Ok(false), "{label}: past(Z) ⊋ Z");
    }
    // The canonical lower bounds implied by differences are explicit
    // entries of the result, not merely implied.
    let p = start_zone(2, &[lt(2, 1, -5), lt(0, 2, -3)]).past();
    assert_eq!(p.entry(0, 1), Bound::lt(-5).unwrap());
    assert_eq!(p.entry(0, 2), Bound::LE_ZERO);
}

/// `v ∈ past(Z)` iff `∃t ≥ 0. v + t ∈ Z`, decided by the oracle's exact
/// interval solver (no closure) on a grid of half-integer points.
#[test]
fn past_matches_its_set_equation() {
    let zones: Vec<(usize, Vec<OracleConstraint>)> = vec![
        (1, vec![le(0, 1, -2), lt(1, 0, 4)]),
        (2, vec![lt(2, 1, -2), le(0, 2, -1), le(1, 0, 5)]),
        (
            2,
            vec![le(1, 0, 3), le(0, 1, -3), le(2, 0, 1), le(0, 2, -1)],
        ),
        (2, vec![lt(1, 2, 1), lt(2, 1, 1), lt(0, 1, -2), le(2, 0, 4)]),
        (
            3,
            vec![le(1, 2, -1), lt(2, 3, 0), le(0, 3, -1), le(1, 0, 4)],
        ),
    ];
    for (n, start) in zones {
        let o = oracle_zone(n, &start);
        let p = as_oracle(&start_zone(n, &start).past());
        let steps = 13usize; // 0, 1/2, …, 6
        let mut point = vec![0usize; n];
        loop {
            let clocks: Vec<(i64, i64)> = point.iter().map(|&k| (k as i64, 2)).collect();
            let v = Valuation::from_ratios(&clocks);
            assert_eq!(p.contains(&v), in_past_image(&o, &v), "{start:?} at {v}");
            // Next grid point.
            let mut k = 0;
            while k < n && point[k] + 1 == steps {
                point[k] = 0;
                k += 1;
            }
            if k == n {
                break;
            }
            point[k] += 1;
        }
    }
}

// ----- argument errors -----

#[test]
fn argument_errors_precede_emptiness() {
    for n in [0usize, 1, 3] {
        for z in [
            Dbm::zero(n).unwrap(),
            Dbm::universe(n).unwrap(),
            Dbm::empty(n).unwrap(),
        ] {
            for x in [n + 1, n + 7, MAX_VARIABLES] {
                let err = Err(Error::ClockOutOfRange {
                    clock: x,
                    variables: n,
                });
                assert_eq!(z.clone().try_reset_zero(var(x)), err);
                assert_eq!(z.clone().try_reset(var(x), 1), err);
                // The clock is checked before the value.
                assert_eq!(z.clone().try_reset(var(x), -1), err);
                assert_eq!(z.clone().try_free(var(x)), err);
            }
            for x in 1..=n {
                for v in [-1, -5, MIN_CONSTANT, i32::MIN] {
                    assert_eq!(
                        z.clone().try_reset(var(x), v),
                        Err(Error::NegativeConstant { value: v })
                    );
                }
            }
            // Future and past have no arguments and never fail.
            for f in [z.clone().future(), z.clone().past()] {
                assert_eq!(f.variables(), n);
                assert_eq!(f.is_empty(), z.is_empty());
            }
        }
    }
    // Zero clocks: future and past are the identity.
    for z in [Dbm::zero(0).unwrap(), Dbm::universe(0).unwrap()] {
        assert_eq!(z.clone().future(), z);
        assert_eq!(z.clone().past(), z);
    }
    // The oracle agrees on the error values.
    let o = OracleDbm::empty(2);
    assert_eq!(
        o.reset(1, -1),
        Err(OracleError::NegativeConstant { value: (-1).into() })
    );
    assert_eq!(
        o.free(3),
        Err(OracleError::ClockOutOfRange {
            clock: 3,
            variables: 2
        })
    );
}

// ----- strict and weak boundaries, repetition -----

#[test]
fn strict_and_weak_boundaries() {
    let cases: Vec<(usize, Vec<OracleConstraint>)> = vec![
        (1, vec![lt(1, 0, 3)]),
        (1, vec![le(1, 0, 3), lt(0, 1, -1)]),
        (1, vec![lt(1, 0, 1), lt(0, 1, 0)]),
        (2, vec![lt(1, 2, 0), le(2, 0, 4)]),
        (2, vec![le(1, 2, 0), le(2, 1, 0), lt(1, 0, 2)]),
        (2, vec![lt(0, 1, -1), lt(2, 1, -1), lt(1, 0, 5)]),
        (3, vec![lt(1, 2, 2), lt(2, 3, 2), le(3, 0, 1), lt(0, 1, -2)]),
        (3, vec![le(1, 0, 0), lt(2, 0, 1), le(0, 3, -3)]),
    ];
    for (k, (n, start)) in cases.iter().enumerate() {
        check_all_ops(&format!("boundary case {k}"), *n, start, &[0, 1, 2, 9]);
    }
}

#[test]
fn repeated_and_redundant_operations() {
    let start = [le(1, 0, 3), lt(0, 2, -1), le(2, 1, 4), lt(3, 0, 6)];
    let z = start_zone(3, &start);
    let o = oracle_zone(3, &start);
    let must = RangeExpectation::MustSucceed;

    let f = z.clone().future();
    assert_eq!(f.clone().future(), f, "future is idempotent");
    let r = z.clone().try_reset(var(2), 5).unwrap();
    assert_eq!(
        r.clone().try_reset(var(2), 5).unwrap(),
        r,
        "redundant reset"
    );
    let r0 = Dbm::zero(3).unwrap();
    assert_eq!(r0.clone().try_reset_zero(var(1)).unwrap(), r0);
    let fr = z.clone().try_free(var(1)).unwrap();
    assert_eq!(
        fr.clone().try_free(var(1)).unwrap(),
        fr,
        "free is idempotent"
    );
    assert_eq!(Dbm::universe(3).unwrap().try_free(var(2)), Dbm::universe(3));

    let sequences: Vec<Vec<Op>> = vec![
        vec![Op::Reset { x: 1, value: 2 }, Op::Reset { x: 1, value: 7 }],
        vec![Op::Free(2), Op::Reset { x: 2, value: 1 }],
        vec![Op::Reset { x: 3, value: 4 }, Op::Free(3)],
        vec![
            Op::Future,
            Op::ResetZero(1),
            Op::Future,
            Op::ResetZero(2),
            Op::Future,
        ],
        vec![Op::Free(1), Op::Free(2), Op::Free(3)],
        vec![
            Op::ResetZero(1),
            Op::ResetZero(2),
            Op::ResetZero(3),
            Op::Future,
        ],
        vec![
            Op::Future,
            Op::Constrain(le(1, 0, 4)),
            Op::Free(1),
            Op::Constrain(lt(1, 2, -1)),
            Op::Future,
        ],
        vec![Op::Past, Op::Past, Op::Future, Op::Past],
        vec![
            Op::ResetZero(2),
            Op::Past,
            Op::Constrain(le(0, 1, -2)),
            Op::Past,
        ],
    ];
    for (k, ops) in sequences.into_iter().enumerate() {
        let s = Scenario {
            variables: 3,
            start: Start::Constraints(start.to_vec()),
            ops,
        };
        assert_eq!(replay(&format!("sequence {k}"), &s), s.ops.len());
    }
    // Commuting resets of distinct clocks give equal values.
    let a = z.clone().try_reset(var(1), 3).unwrap().try_reset(var(2), 4);
    let b = z.clone().try_reset(var(2), 4).unwrap().try_reset(var(1), 3);
    assert_eq!(a, b);
    assert_outcome("future", &Ok(f), &Ok(o.future()), must);
}

// ----- arithmetic limits -----

#[test]
fn range_limits() {
    let max = i64::from(MAX_CONSTANT);
    let min = i64::from(MIN_CONSTANT);
    let check = |label: &str, n: usize, start: &[OracleConstraint], x: usize, c: i32| {
        let z = start_zone(n, start);
        let o = oracle_zone(n, start);
        let expected = o.reset(x, c);
        // Exact rule: Range iff the input is nonempty and c > MAX_CONSTANT.
        let range = if !o.is_empty() && c > MAX_CONSTANT {
            RangeExpectation::MustFailRange
        } else {
            RangeExpectation::MustSucceed
        };
        assert_outcome(label, &z.clone().try_reset(var(x), c), &expected, range);
        assert_outcome(
            &format!("{label} free"),
            &z.clone().try_free(var(x)),
            &o.free(x),
            RangeExpectation::MustSucceed,
        );
        assert_outcome(
            &format!("{label} future"),
            &Ok(z.future()),
            &Ok(o.future()),
            RangeExpectation::MustSucceed,
        );
    };
    // Extreme upper and lower bounds on the other clocks.
    let wide = [
        le(1, 0, max),
        le(0, 2, min),
        lt(3, 0, max),
        lt(0, 3, min + 1),
    ];
    for c in [
        0,
        1,
        MAX_CONSTANT - 1,
        MAX_CONSTANT,
        MAX_CONSTANT + 1,
        i32::MAX,
    ] {
        for x in 1..=3 {
            check(&format!("wide x{x} := {c}"), 3, &wide, x, c);
        }
    }
    // Extreme differences.
    let diff = [le(1, 2, max - 10), le(2, 1, min + 5), le(2, 0, 3)];
    for c in [0, 2, MAX_CONSTANT] {
        check(&format!("diff := {c}"), 2, &diff, 1, c);
        check(&format!("diff y := {c}"), 2, &diff, 2, c);
    }
    let z = start_zone(1, &[le(1, 0, max)]);
    assert_eq!(
        z.clone().try_reset(var(1), MAX_CONSTANT + 1),
        Err(Error::Range)
    );
    let r = z.try_reset(var(1), MAX_CONSTANT).unwrap();
    assert_eq!(r.entry(1, 0), Bound::le(MAX_CONSTANT).unwrap());
    assert_eq!(r.entry(0, 1), Bound::le(MIN_CONSTANT).unwrap());
    // x = MAX, y ≥ MAX, then reset y to MAX: every result constant is in range.
    check(
        "x=y=MAX",
        2,
        &[le(1, 0, max), le(0, 1, min), le(0, 2, min)],
        2,
        MAX_CONSTANT,
    );
}

#[test]
fn random_near_limit_zones() {
    let max = PRODUCTION_MAX_CONSTANT;
    for seed in random::seeds(300) {
        let mut rng = random::case_rng("temporal_near_limit", seed);
        let n = rng.index(4) + 1;
        let mut start = Vec::new();
        for _ in 0..rng.index(2 * n + 1) {
            let (i, j) = (rng.index(n + 1), rng.index(n + 1));
            let mag = max - rng.range(0, 3) - if rng.chance(1, 2) { max / 2 } else { 0 };
            let c = if rng.chance(1, 2) { mag } else { -mag };
            let g = if rng.chance(1, 2) {
                lt(i, j, c)
            } else {
                le(i, j, c)
            };
            let mut next = start.clone();
            next.push(g);
            let e = oracle_zone(n, &next);
            if e.max_abs_constant() <= BigInt::from(max) && !e.is_empty() {
                start = next;
            }
        }
        let big = MAX_CONSTANT - rng.range(0, 2) as i32;
        check_all_ops(
            &format!("seed {seed} (ORACLE_SEED={seed})"),
            n,
            &start,
            &[0, 1, big],
        );
    }
}

// ----- exhaustive and random differential tests -----

#[test]
fn exhaustive_one_clock() {
    let mut uppers: Vec<Option<OracleConstraint>> = vec![None];
    let mut lowers: Vec<Option<OracleConstraint>> = vec![None];
    for c in 0..4 {
        uppers.push(Some(le(1, 0, c)));
        uppers.push(Some(lt(1, 0, c)));
        lowers.push(Some(le(0, 1, -c)));
        lowers.push(Some(lt(0, 1, -c)));
    }
    let mut count = 0;
    for u in &uppers {
        for l in &lowers {
            let start: Vec<_> = u.iter().chain(l).cloned().collect();
            if oracle_zone(1, &start).is_empty() {
                continue;
            }
            check_all_ops(&format!("{start:?}"), 1, &start, &[0, 1, 2, 3, 5]);
            count += 1;
        }
    }
    assert!(count >= 30, "{count} one-clock zones");
}

#[test]
fn fixtures_match_oracle() {
    let mut temporal_steps = 0;
    for f in fixtures::all() {
        let steps = replay(&f.name, &f.scenario);
        temporal_steps += f.scenario.ops[..steps]
            .iter()
            .filter(|op| {
                matches!(
                    op,
                    Op::Future | Op::Past | Op::Reset { .. } | Op::ResetZero(_) | Op::Free(_)
                )
            })
            .count();
    }
    assert!(
        temporal_steps >= 10,
        "{temporal_steps} temporal fixture steps"
    );
}

/// A random scenario in which temporal operations dominate.
fn temporal_scenario(rng: &mut SplitMix64) -> Scenario {
    let mut s = random::scenario(rng, 6, 10);
    // Extra temporal operations, so that they dominate.
    let n = s.variables;
    for _ in 0..rng.index(6) {
        let op = match (n, rng.below(5)) {
            (_, 0) => Op::Future,
            (_, 4) | (0, _) => Op::Past,
            (_, 1) => Op::ResetZero(rng.index(n) + 1),
            (_, 2) => Op::Free(rng.index(n) + 1),
            _ => Op::Reset {
                x: rng.index(n) + 1,
                value: rng.range(0, 20),
            },
        };
        let at = rng.index(s.ops.len() + 1);
        s.ops.insert(at, op);
    }
    s
}

#[test]
fn random_scenarios_match_oracle() {
    let (mut temporal, mut total) = (0, 0);
    for seed in random::seeds(1500) {
        let mut rng = random::case_rng("temporal_random_scenarios", seed);
        let s = temporal_scenario(&mut rng);
        let steps = replay(&format!("seed {seed} (ORACLE_SEED={seed})\n{s}"), &s);
        assert_eq!(steps, s.ops.len());
        total += steps;
        temporal += s
            .ops
            .iter()
            .filter(|op| {
                matches!(
                    op,
                    Op::Future | Op::Past | Op::Reset { .. } | Op::ResetZero(_) | Op::Free(_)
                )
            })
            .count();
    }
    if random::seeds(1500).count() >= 100 {
        assert!(
            temporal * 3 >= total,
            "{temporal} temporal of {total} steps"
        );
    }
}

#[test]
fn random_zones_every_operation() {
    for seed in random::seeds(400) {
        let mut rng = random::case_rng("temporal_random_zones", seed);
        let n = rng.index(8) + 1;
        let count = rng.index(4 * n + 1);
        let (cs, _) = random::consistent_constraints(&mut rng, n, count, 50);
        let values = [0, rng.range(1, 60) as i32];
        check_all_ops(
            &format!("seed {seed} (ORACLE_SEED={seed})"),
            n,
            &cs,
            &values,
        );
    }
}

// ----- timing: intrinsic cost vs the consuming API -----

/// Separates each operation's intrinsic cost from the fixed cost of the
/// `self`-consuming API (moving the zone through the harness, **consume**).
/// Run with
/// `cargo test --release --lib bench_temporal_paths -- --ignored --nocapture`.
#[test]
#[ignore = "timing benchmark; run explicitly with --release"]
fn bench_temporal_paths() {
    if cfg!(debug_assertions) {
        eprintln!("warning: debug build; publish_canonical runs an O(d³) check");
    }
    let samples = 15;
    println!(
        "| n | consume (ns) | future (ns) | past (ns) | reset 0 (ns) | reset c (ns) | free (ns) |"
    );
    println!("|---:|---:|---:|---:|---:|---:|---:|");
    // The first configuration is timed twice; the first pass only warms up
    // the allocator and caches.
    for (pass, n) in [
        (0, 1usize),
        (1, 1),
        (1, 2),
        (1, 4),
        (1, 8),
        (1, 16),
        (1, 32),
        (1, 64),
    ] {
        let mut rng = random::case_rng("bench_temporal_paths", n as u64);
        let (cs, _) = random::consistent_constraints(&mut rng, n, 3 * n, 1000);
        let z = start_zone(n, &cs);
        let x = var(rng.index(n) + 1);
        let stage = (4_000_000 / ((n + 1) * (n + 1) * 4)).clamp(8, 4096);
        let consume = time_op(&z, stage, samples, |d| d);
        let future = time_op(&z, stage, samples, |d| d.future());
        let past = time_op(&z, stage, samples, |d| d.past());
        let zero = time_op(&z, stage, samples, |d| d.try_reset_zero(x).unwrap());
        let value = time_op(&z, stage, samples, |d| d.try_reset(x, 57).unwrap());
        let free = time_op(&z, stage, samples, |d| d.try_free(x).unwrap());
        if pass == 1 {
            println!(
                "| {n} | {consume:.1} | {future:.1} | {past:.1} | {zero:.1} | {value:.1} | {free:.1} |"
            );
        }
    }
}

/// Hot-cache loop: `R` operations on one zone in place (each result feeds
/// the next), best of 7. The zone is `xᵢ ≤ 100 + 7i ∧ xᵢ − xᵢ₋₁ < 3`.
/// Temporal-operation benchmark case (same zones,
/// operations and output format). Unlike the kernel benchmark, whose staged
/// inputs (~1 MiB) make it memory-bound, this measures the compute cost.
fn hot_time(n: usize, z0: &Dbm, name: &str, f: impl Fn(Dbm, usize) -> Dbm) {
    let r = 2_000_000 / (n + 1);
    let mut best = f64::MAX;
    for _ in 0..7 {
        let mut w = z0.clone();
        let t0 = std::time::Instant::now();
        for k in 0..r {
            w = f(w, k);
        }
        let ns = t0.elapsed().as_nanos() as f64 / r as f64;
        std::hint::black_box(&w);
        best = best.min(ns);
    }
    println!("impl=clock-dbm n={n} op={name} ns={best:.2}");
}

/// Run with
/// `cargo test --release --lib bench_temporal_hot -- --ignored --nocapture`.
#[test]
#[ignore = "timing benchmark; run explicitly with --release"]
fn bench_temporal_hot() {
    for n in [1usize, 2, 4, 8, 16, 32, 64] {
        let mut cs = Vec::new();
        for i in 1..=n {
            cs.push(le(i, 0, 100 + 7 * i as i64));
        }
        for i in 2..=n {
            cs.push(lt(i, i - 1, 3));
        }
        let z0 = start_zone(n, &cs);
        hot_time(n, &z0, "future", |w, _| w.future());
        hot_time(n, &z0, "past", |w, _| w.past());
        hot_time(n, &z0, "reset", |w, k| {
            w.try_reset(var(1 + k % n), (k & 7) as i32).unwrap()
        });
        hot_time(n, &z0, "free", |w, k| w.try_free(var(1 + k % n)).unwrap());
    }
}
