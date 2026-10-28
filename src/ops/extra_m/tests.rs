//! Differential tests of ExtraM against the independent exact oracle
//! (`tests/support/oracle/`), whose `extrapolate_max` is a literal BigInt
//! definition of `norm` followed by the exact closure of
//! the full-closure algorithm.
//!
//! Every successful result is compared entry by entry with the oracle and
//! checked for the public invariant (canonical or empty) and for
//! extensiveness, `γ(D) ⊆ γ(ExtraM(D, M))`, both in production and in the
//! oracle. The executable implementation is also machine-checked with
//! Creusot (`verification/PROOF_STATUS.md`); these tests provide additional
//! regression coverage.
//! Idempotence is only observed, never asserted as a requirement.

use super::*;
use crate::bounds::MIN_CONSTANT;
use crate::ops::test_support::{
    as_oracle, assert_outcome, exact, observe, oracle_zone, replay, start_zone, time_op, var,
};
use num_bigint::BigInt;
use std::vec;

use crate::oracle;

use oracle::compare::{PRODUCTION_MAX_CONSTANT, RangeExpectation, classify_range};
use oracle::random::{self, SplitMix64};
use oracle::scenario::{Op, le, lt};
use oracle::{ExactBound, OracleConstraint, OracleDbm, OracleError, fixtures};

fn mb(ceilings: &[i32]) -> MaxBounds {
    MaxBounds::new(ceilings.to_vec()).unwrap()
}

fn big(ceilings: &[i32]) -> Vec<BigInt> {
    ceilings.iter().map(|&c| BigInt::from(c)).collect()
}

/// `B` of S§7.1 for ExtraM: the input's constants and the ceilings.
fn input_bound(o: &OracleDbm, ceilings: &[i32]) -> BigInt {
    let top = ceilings.iter().map(|&c| BigInt::from(c)).max();
    o.max_abs_constant().max(top.unwrap_or_default())
}

/// `try_extrapolate_max(z, M)` checked against the oracle (exact entries,
/// `Inv`, range rules) and for extensiveness. Returns the production result.
#[track_caller]
fn check_with(label: &str, z: &Dbm, ceilings: &[i32], ws: &mut Workspace) -> Result<Dbm, Error> {
    let o = as_oracle(z);
    let expected = o.extrapolate_max(&big(ceilings));
    let range = match &expected {
        Ok(e) => classify_range(
            z.variables(),
            &input_bound(&o, ceilings),
            e,
            PRODUCTION_MAX_CONSTANT,
        ),
        Err(_) => RangeExpectation::MustSucceed,
    };
    let observed = z.clone().try_extrapolate_max(&mb(ceilings), ws);
    assert_outcome(label, &observed, &expected, range);
    if let (Ok(r), Ok(e)) = (&observed, &expected) {
        assert!(z.is_subset_of(r).unwrap(), "{label}: not extensive");
        assert!(o.is_subset_of(e).unwrap(), "{label}: oracle not extensive");
        assert_eq!(r.variables(), z.variables(), "{label}: dimension");
    }
    observed
}

#[track_caller]
fn check(label: &str, z: &Dbm, ceilings: &[i32]) -> Result<Dbm, Error> {
    check_with(label, z, ceilings, &mut Workspace::new())
}

fn row(z: &Dbm, i: usize) -> Vec<String> {
    (0..z.dimension())
        .map(|j| exact(z.entry(i, j)).to_string())
        .collect()
}

#[track_caller]
fn assert_rows(z: &Dbm, rows: &[&[&str]]) {
    for (i, r) in rows.iter().enumerate() {
        assert_eq!(row(z, i), *r, "row {i} of {z:?}");
    }
}

// ----- the entrywise rules -----

#[test]
fn norm_rules_on_bounds() {
    let (le, lt) = (|c| Bound::le(c).unwrap(), |c| Bound::lt(c).unwrap());
    let inf = Bound::INFINITY;
    // norm_upper with t = 3: only bounds looser than Le 3 become ∞.
    for (e, r) in [
        (lt(2), lt(2)),
        (le(2), le(2)),
        (lt(3), lt(3)),
        (le(3), le(3)),
        (lt(4), inf),
        (le(4), inf),
        (inf, inf),
        (le(-7), le(-7)),
    ] {
        assert_eq!(norm_upper(e, le(3)), r, "norm_upper {e:?}");
    }
    // norm_lower with t = −3: only bounds tighter than Lt −3 become Lt −3.
    for (e, r) in [
        (le(-4), lt(-3)),
        (lt(-4), lt(-3)),
        (lt(-3), lt(-3)),
        (le(-3), le(-3)),
        (lt(-2), lt(-2)),
        (le(-2), le(-2)),
        (inf, inf),
        (le(5), le(5)),
    ] {
        assert_eq!(norm_lower(e, lt(-3)), r, "norm_lower {e:?}");
    }
    // norm_diag.
    for (e, r) in [
        (lt(0), lt(0)),
        (le(-1), lt(0)),
        (le(0), le(0)),
        (lt(1), inf),
        (inf, inf),
    ] {
        assert_eq!(norm_diag(e), r, "norm_diag {e:?}");
    }
    // Ceiling 0 (reference clock) and the extreme ceilings are representable.
    assert_eq!(thresholds(0), (le(0), lt(0)));
    assert_eq!(
        thresholds(MAX_CONSTANT),
        (le(MAX_CONSTANT), lt(MIN_CONSTANT))
    );
}

/// The order matters: `norm_upper` first, then `norm_lower`. With a lower
/// threshold above the upper one this would differ, but `−k(j) ≤ 0 ≤ k(i)`,
/// so a dropped entry (`∞`) is never raised and a raised one is never dropped.
#[test]
fn norm_upper_then_lower_on_one_entry() {
    let (le, lt) = (|c| Bound::le(c).unwrap(), |c| Bound::lt(c).unwrap());
    for k_i in 0..4 {
        for k_j in 0..4 {
            let (up, _) = thresholds(k_i);
            let (_, low) = thresholds(k_j);
            for c in -6..=6 {
                for e in [le(c), lt(c), Bound::INFINITY] {
                    let r = norm_lower(norm_upper(e, up), low);
                    let o = oracle_norm(&exact(e), k_i, k_j);
                    assert_eq!(exact(r), o, "e = {e:?}, k(i) = {k_i}, k(j) = {k_j}");
                }
            }
        }
    }
}

/// Entrywise normalization of one off-diagonal bound on the oracle's
/// exact bounds (independent of the production comparisons).
fn oracle_norm(e: &ExactBound, k_i: i32, k_j: i32) -> ExactBound {
    let e = if ExactBound::le(k_i) < *e {
        ExactBound::Infinity
    } else {
        e.clone()
    };
    let low = ExactBound::lt(-k_j);
    if e < low { low } else { e }
}

// ----- worked examples and thresholds -----

/// Concrete ExtraM example, also replayed from the shared fixtures below.
#[test]
fn worked_examples() {
    // zero(2)↑ ∧ x₁ ≥ 5 with M = (3, 3): x₁ > 3 (lower bound relaxed),
    // and the difference x₂ − x₁ ≤ −5 is relaxed to < −3.
    let z = start_zone(2, &[le(0, 1, -5), le(1, 2, 5), le(2, 1, -5)]);
    let r = check("8.5 lower", &z, &[3, 3]).unwrap();
    assert_rows(
        &r,
        &[
            &["<=0", "<-3", "<=0"],
            &["inf", "<=0", "inf"],
            &["inf", "<-3", "<=0"],
        ],
    );
    // x₁ − x₂ ≤ 4, x₂ ≤ 1 with M = (3, 3): the difference bound 4 > 3 is
    // dropped and so is x₁ ≤ 5; closure re-derives nothing (x₂ ≤ 1 only).
    let z = start_zone(2, &[le(1, 2, 4), le(2, 0, 1)]);
    let r = check("8.5 diagonal", &z, &[3, 3]).unwrap();
    assert_rows(
        &r,
        &[
            &["<=0", "<=0", "<=0"],
            &["inf", "<=0", "inf"],
            &["<=1", "<=1", "<=0"],
        ],
    );
}

/// One clock: every upper bound `x ⋈ c` and lower bound `x ⋈ c` around the
/// ceiling `k`, strict and weak, at `c ∈ {k − 1, k, k + 1}`.
#[test]
fn thresholds_one_clock() {
    for k in [0, 1, 3, 1000] {
        for c in [k - 1, k, k + 1] {
            for strict in [false, true] {
                let mk = |i, j, c| if strict { lt(i, j, c) } else { le(i, j, c) };
                // Upper bound x ⋈ c (D[1][0]).
                if c > 0 || (c == 0 && !strict) {
                    let z = start_zone(1, &[mk(1, 0, c)]);
                    let r = check(&format!("x ⋈ {c}, k = {k}"), &z, &[k as i32]).unwrap();
                    let kept = c <= k;
                    let want = if kept {
                        row(&z, 1)[0].clone()
                    } else {
                        "inf".to_string()
                    };
                    assert_eq!(row(&r, 1)[0], want, "x ⋈ {c}, k = {k}");
                }
                // Lower bound x ⋈' c, i.e. −x ⋈ −c (D[0][1]).
                if c >= 0 {
                    let z = start_zone(1, &[mk(0, 1, -c)]);
                    let r = check(&format!("x ⋈' {c}, k = {k}"), &z, &[k as i32]).unwrap();
                    let raised = c > k;
                    let want = if raised {
                        format!("<{}", -k)
                    } else {
                        row(&z, 0)[1].clone()
                    };
                    assert_eq!(row(&r, 0)[1], want, "x ⋈' {c}, k = {k}");
                }
            }
        }
    }
}

/// Difference entries between two actual clocks use `k(i)` above and
/// `−k(j)` below, including strictness exactly at the thresholds.
#[test]
fn thresholds_two_clocks() {
    let (k1, k2) = (4, 2);
    // Free clocks (x₁, x₂ unbounded) so that only the difference matters.
    for c in [-4, -3, -2, -1, 0, 3, 4, 5] {
        for strict in [false, true] {
            let g = if strict { lt(1, 2, c) } else { le(1, 2, c) };
            let z = start_zone(2, std::slice::from_ref(&g));
            let r = check(&format!("{g}"), &z, &[k1, k2]).unwrap();
            let e = &row(&r, 1)[2];
            let want = if c > k1.into() {
                "inf".to_string()
            } else if c < (-k2).into() {
                format!("<{}", -k2)
            } else {
                row(&z, 1)[2].clone()
            };
            assert_eq!(*e, want, "{g}");
        }
    }
}

/// Zero ceilings: every positive upper bound is dropped, every positive
/// lower bound becomes `> 0`, and `x = 0` is kept.
#[test]
fn zero_ceilings() {
    let z = Dbm::zero(3).unwrap();
    let r = check("zero", &z, &[0, 0, 0]).unwrap();
    assert_eq!(r, z);
    let z = start_zone(2, &[le(0, 1, -2), le(1, 0, 7), le(2, 0, 0)]);
    let r = check("2 ≤ x₁ ≤ 7, x₂ = 0", &z, &[0, 0]).unwrap();
    assert_rows(
        &r,
        &[
            &["<=0", "<0", "<=0"],
            &["inf", "<=0", "inf"],
            &["<=0", "<0", "<=0"],
        ],
    );
}

/// Unbounded clocks, `∞` entries and the universe are fixed points of the
/// upper rule; the reference row (`Le 0` threshold) never becomes `∞`.
#[test]
fn infinity_and_reference_row() {
    for n in 0..5 {
        let m = vec![2; n];
        let u = Dbm::universe(n).unwrap();
        assert_eq!(check("universe", &u, &m).unwrap(), u);
        let up = Dbm::zero(n).unwrap().future();
        assert_eq!(check("zero↑", &up, &m).unwrap(), up);
    }
    // x₁ ≥ 10, x₂ unbounded, k = (3, 3): D[0][1] = Le −10 → Lt −3, and the
    // reference row keeps finite entries.
    let z = start_zone(2, &[le(0, 1, -10)]);
    let r = check("x₁ ≥ 10", &z, &[3, 3]).unwrap();
    assert_eq!(row(&r, 0), ["<=0", "<-3", "<=0"]);
}

// ----- dimensions, empty zones and argument errors -----

#[test]
fn zero_clocks() {
    let b = MaxBounds::new(vec![]).unwrap();
    assert_eq!(b.variables(), 0);
    let mut ws = Workspace::new();
    let z = Dbm::zero(0).unwrap();
    assert_eq!(z.clone().try_extrapolate_max(&b, &mut ws), Ok(z));
    let e = Dbm::empty(0).unwrap();
    assert_eq!(e.clone().try_extrapolate_max(&b, &mut ws), Ok(e));
    assert_eq!(
        Dbm::zero(0)
            .unwrap()
            .try_extrapolate_max(&mb(&[1]), &mut ws),
        Err(Error::DimensionMismatch {
            expected: 0,
            found: 1
        })
    );
}

#[test]
fn empty_zones_keep_their_dimension() {
    let mut ws = Workspace::new();
    for n in 0..6 {
        let e = Dbm::empty(n).unwrap();
        let r = e.clone().try_extrapolate_max(&mb(&vec![3; n]), &mut ws);
        assert_eq!(r, Ok(e.clone()));
        let r = r.unwrap();
        assert!(r.is_empty() && r.variables() == n);
        assert_eq!(
            as_oracle(&e).extrapolate_max(&big(&vec![3; n])),
            Ok(OracleDbm::empty(n))
        );
    }
}

#[test]
fn dimension_mismatch_also_for_empty_zones() {
    let mut ws = Workspace::new();
    for (z, n) in [
        (Dbm::zero(2).unwrap(), 2),
        (Dbm::universe(2).unwrap(), 2),
        (Dbm::empty(2).unwrap(), 2),
    ] {
        for found in [0, 1, 3, 7] {
            let want = Err(Error::DimensionMismatch { expected: n, found });
            assert_eq!(
                z.clone().try_extrapolate_max(&mb(&vec![1; found]), &mut ws),
                want
            );
            assert_eq!(
                as_oracle(&z).extrapolate_max(&big(&vec![1; found])),
                Err(OracleError::DimensionMismatch { expected: n, found })
            );
        }
    }
}

#[test]
fn max_bounds_validation() {
    let invalid = |variable, value| Err(Error::InvalidMaxBounds { variable, value });
    assert_eq!(MaxBounds::new(vec![0, -1]), invalid(2, -1));
    assert_eq!(MaxBounds::new(vec![i32::MIN]), invalid(1, i32::MIN));
    assert_eq!(
        MaxBounds::new(vec![MAX_CONSTANT + 1]),
        invalid(1, MAX_CONSTANT + 1)
    );
    assert_eq!(MaxBounds::new(vec![i32::MAX]), invalid(1, i32::MAX));
    // The first invalid ceiling is reported.
    assert_eq!(MaxBounds::new(vec![1, 2, -5, i32::MAX]), invalid(3, -5));
    assert_eq!(
        MaxBounds::new(vec![0; MAX_VARIABLES + 1]),
        Err(Error::TooManyVariables {
            requested: MAX_VARIABLES + 1
        })
    );
    // Length is checked before the values.
    assert_eq!(
        MaxBounds::new(vec![-1; MAX_VARIABLES + 1]),
        Err(Error::TooManyVariables {
            requested: MAX_VARIABLES + 1
        })
    );
    let b = MaxBounds::new(vec![0, MAX_CONSTANT, 7]).unwrap();
    assert_eq!(b.variables(), 3);
    assert_eq!(b.get(var(1)), Some(0));
    assert_eq!(b.get(var(2)), Some(MAX_CONSTANT));
    assert_eq!(b.get(var(3)), Some(7));
    assert_eq!(b.get(var(4)), None);
    assert_eq!(
        MaxBounds::new(vec![0; MAX_VARIABLES]).unwrap().variables(),
        MAX_VARIABLES
    );
    // The oracle agrees on the argument error for negative ceilings.
    assert_eq!(
        OracleDbm::zero(2).extrapolate_max(&big(&[0, -1])),
        Err(OracleError::InvalidMaxBounds {
            variable: 2,
            value: BigInt::from(-1)
        })
    );
}

// ----- representable limits and range failures -----

#[test]
fn constants_at_the_limits() {
    let m = MAX_CONSTANT;
    // x = MAX_CONSTANT is unchanged with the largest ceiling.
    let z = start_zone(1, &[le(1, 0, m.into()), le(0, 1, (-m).into())]);
    assert_eq!(check("x = MAX", &z, &[m]).unwrap(), z);
    // ... and becomes x > MAX − 1 with ceiling MAX − 1.
    let r = check("x = MAX, k = MAX − 1", &z, &[m - 1]).unwrap();
    assert_rows(&r, &[&["<=0", &format!("<{}", -(m - 1))], &["inf", "<=0"]]);
    // Lt MIN_CONSTANT is a threshold, never exceeded.
    let z = start_zone(1, &[lt(0, 1, MIN_CONSTANT.into())]);
    assert_eq!(check("x > MAX", &z, &[m]).unwrap(), z);
    // Large differences with large ceilings.
    let z = start_zone(
        2,
        &[
            le(1, 0, m.into()),
            le(2, 0, m.into()),
            le(1, 2, (m - 1).into()),
        ],
    );
    for ceil in [[0, m], [m, 0], [1, 1]] {
        check(&format!("large {ceil:?}"), &z, &ceil).unwrap();
    }
    // `norm` changes nothing with ceilings (MAX, MAX): the zone is returned
    // as is.
    assert_eq!(check("large [MAX, MAX]", &z, &[m, m]).unwrap(), z);
    // With M(x₁) = MAX − 1, `D[1][0] = Le MAX` becomes ∞, and the exact
    // closure re-derives `x₁ ≤ D[1][2] + D[2][0] = 2·MAX − 1`, which is
    // unrepresentable (`check` asserts that the oracle requires the error).
    assert_eq!(
        check("large [MAX − 1, MAX]", &z, &[m - 1, m]),
        Err(Error::Range)
    );
}

/// `Err(Range)` is reported, not saturated or mistaken for emptiness, when
/// the exact closure of the normalized matrix needs a constant beyond
/// `MAX_CONSTANT` (module documentation).
#[test]
fn unrepresentable_result_is_a_range_error() {
    let m = i64::from(MAX_CONSTANT);
    let z = start_zone(2, &[le(1, 0, 100), le(2, 0, m - 1), le(1, 2, 3)]);
    let r = check("re-derived x₁ ≤ MAX + 2", &z, &[5, MAX_CONSTANT]);
    assert_eq!(r, Err(Error::Range));
    let exact = as_oracle(&z)
        .extrapolate_max(&big(&[5, MAX_CONSTANT]))
        .unwrap();
    assert_eq!(
        exact.entry(1, 0),
        Some(&ExactBound::le(m + 2)),
        "the exact result is nonempty and unrepresentable"
    );
    // With a smaller ceiling for x₂ the result is representable again.
    check("smaller k(2)", &z, &[5, MAX_CONSTANT - 3]).unwrap();
}

// ----- exhaustive small cases -----

/// Every one-clock zone with bounds in `0..=4` and every ceiling in `0..=4`.
#[test]
fn exhaustive_one_clock() {
    let mut uppers = vec![None];
    let mut lowers = vec![None];
    for c in 0..=4 {
        uppers.push(Some(le(1, 0, c)));
        uppers.push(Some(lt(1, 0, c)));
        lowers.push(Some(le(0, 1, -c)));
        lowers.push(Some(lt(0, 1, -c)));
    }
    let mut count = 0;
    for u in &uppers {
        for l in &lowers {
            let start: Vec<_> = u.iter().chain(l).cloned().collect();
            let z = start_zone(1, &start);
            for k in 0..=4 {
                check(&format!("{start:?}, k = {k}"), &z, &[k]).unwrap();
                count += 1;
            }
        }
    }
    assert!(count >= 500, "{count} cases");
}

/// Every two-clock zone from one upper bound on `x₁`, one lower bound on `x₂`
/// and one difference constraint on a small grid, with ceilings in `0..=3`.
#[test]
fn exhaustive_two_clocks_small_grid() {
    let mut cases = 0;
    let gs = |mk: fn(usize, usize, i64) -> OracleConstraint, i, j, cs: &[i64]| {
        let mut v = vec![None];
        v.extend(cs.iter().map(|&c| Some(mk(i, j, c))));
        v
    };
    let ups = [gs(le, 1, 0, &[1, 3]), gs(lt, 1, 0, &[2])].concat();
    let lows = [gs(le, 0, 2, &[-1, -3]), gs(lt, 0, 2, &[-2])].concat();
    let diffs = [gs(le, 1, 2, &[-3, 0, 2]), gs(lt, 2, 1, &[-1, 3])].concat();
    for u in &ups {
        for l in &lows {
            for d in &diffs {
                let start: Vec<_> = u.iter().chain(l).chain(d).cloned().collect();
                if oracle_zone(2, &start).is_empty() {
                    continue;
                }
                let z = start_zone(2, &start);
                for k1 in 0..=3 {
                    for k2 in 0..=3 {
                        check(&format!("{start:?} {k1} {k2}"), &z, &[k1, k2]).unwrap();
                        cases += 1;
                    }
                }
            }
        }
    }
    assert!(cases >= 1000, "{cases} cases");
}

// ----- random zones, repetition and workspace reuse -----

fn random_zone(rng: &mut SplitMix64, n: usize, max_c: i64) -> Dbm {
    let count = rng.index(3 * n + 2);
    let (cs, _) = random::consistent_constraints(rng, n, count, max_c);
    start_zone(n, &cs)
}

fn random_ceilings(rng: &mut SplitMix64, n: usize, max_c: i64) -> Vec<i32> {
    (0..n)
        .map(|_| i32::try_from(rng.range(0, max_c + 2)).unwrap())
        .collect()
}

/// Random canonical zones and ceilings, then a second extrapolation, with
/// one workspace reused across all dimensions. `E(E(D)) = E(D)` is counted,
/// not asserted (idempotence is not part of the public contract).
#[test]
fn random_zones_match_oracle() {
    let mut ws = Workspace::new();
    let (mut cases, mut idempotent) = (0, 0);
    for seed in random::seeds(600) {
        let mut rng = random::case_rng("extra_m_random_zones", seed);
        let n = rng.index(7);
        let max_c = [3, 10, 50][rng.index(3)];
        let z = random_zone(&mut rng, n, max_c);
        let m = random_ceilings(&mut rng, n, max_c);
        let label = format!("seed {seed} (ORACLE_SEED={seed}) n = {n} M = {m:?}");
        let once = check_with(&label, &z, &m, &mut ws).unwrap();
        let m2 = random_ceilings(&mut rng, n, max_c);
        check_with(&format!("{label} then {m2:?}"), &once, &m2, &mut ws).unwrap();
        let twice = check_with(&format!("{label} twice"), &once, &m, &mut ws).unwrap();
        idempotent += usize::from(twice == once);
        cases += 1;
    }
    eprintln!("extra_m: E(E(D)) = E(D) in {idempotent} of {cases} random cases (not asserted)");
}

/// Random zones near the representable limits: success must agree exactly
/// with the oracle, and `Err(Range)` is allowed only where S§7 allows it.
#[test]
fn random_zones_near_the_limits() {
    let big_c = i64::from(MAX_CONSTANT) / 4;
    for seed in random::seeds(200) {
        let mut rng = random::case_rng("extra_m_random_limits", seed);
        let n = 1 + rng.index(4);
        let z = random_zone(&mut rng, n, big_c);
        let m: Vec<i32> = (0..n)
            .map(|_| match rng.below(3) {
                0 => MAX_CONSTANT - i32::try_from(rng.range(0, 3)).unwrap(),
                1 => i32::try_from(rng.range(0, 4)).unwrap(),
                _ => i32::try_from(rng.range(0, big_c)).unwrap(),
            })
            .collect();
        let _ = check(
            &format!("seed {seed} (ORACLE_SEED={seed}) M = {m:?}"),
            &z,
            &m,
        );
    }
}

/// Random scenarios (constraints, temporal operations, intersections and
/// ExtraM) replayed step by step against the oracle.
#[test]
fn random_scenarios_match_oracle() {
    let (mut extra, mut total) = (0, 0);
    for seed in random::seeds(1000) {
        let mut rng = random::case_rng("extra_m_random_scenarios", seed);
        let mut s = random::scenario(&mut rng, 6, 10);
        let n = s.variables;
        for _ in 0..1 + rng.index(3) {
            let m = (0..n).map(|_| rng.range(0, 8)).collect();
            let at = rng.index(s.ops.len() + 1);
            s.ops.insert(at, Op::ExtrapolateMax(m));
        }
        let steps = replay(&format!("seed {seed} (ORACLE_SEED={seed})\n{s}"), &s);
        assert_eq!(steps, s.ops.len());
        total += steps;
        extra += s
            .ops
            .iter()
            .filter(|op| matches!(op, Op::ExtrapolateMax(_)))
            .count();
    }
    if random::seeds(1000).count() >= 100 {
        assert!(extra >= 1000, "{extra} ExtraM steps of {total}");
    }
}

#[test]
fn fixtures_match_oracle() {
    let mut extra = 0;
    for f in fixtures::all() {
        let steps = replay(&f.name, &f.scenario);
        extra += f.scenario.ops[..steps]
            .iter()
            .filter(|op| matches!(op, Op::ExtrapolateMax(_)))
            .count();
    }
    assert!(extra >= 3, "{extra} ExtraM fixture steps");
}

/// The production result is the closure of the entrywise `norm`: checked
/// directly here by running `normalize` and comparing it with the oracle's
/// per-entry transcription before closure.
#[test]
fn normalize_is_entrywise_norm() {
    for seed in random::seeds(300) {
        let mut rng = random::case_rng("extra_m_normalize", seed);
        let n = rng.index(6);
        let z = random_zone(&mut rng, n, 10);
        let m = random_ceilings(&mut rng, n, 10);
        if z.is_empty() {
            continue;
        }
        let before = observe(&z);
        let mut w = z.into_matrix().unwrap();
        let changed = normalize(&mut w, &mb(&m));
        let k = |i: usize| if i == 0 { 0 } else { m[i - 1] };
        let mut differs = false;
        for i in 0..=n {
            for j in 0..=n {
                let e = before.entry(i, j).unwrap();
                let want = if i == j {
                    e.clone() // Le 0 on a nonempty canonical input
                } else {
                    oracle_norm(e, k(i), k(j))
                };
                assert_eq!(exact(w.get(i, j)), want, "seed {seed} ({i}, {j}) M = {m:?}");
                differs |= want != *e;
            }
        }
        assert_eq!(changed, differs, "seed {seed}: change flag, M = {m:?}");
    }
}

// ----- timing (ignored) -----

/// Norm versus closure cost on a bounded zone: `none` (ceilings above every
/// constant), `few` (`M(x₁) = 0`) and `many` (all ceilings 0); `changed`
/// counts the entries `norm` changes. `pivots_ns` closes the canonical input
/// with `close_pivots` over every clock (the `O(d³)` loop of the changed
/// path), `close_ns` with the scalar `Matrix::close` (for comparison), and
/// `move_ns` is the overhead of moving the storage. Run with
/// `cargo test --release --lib extra_m_timing -- --ignored --nocapture`.
#[test]
#[ignore = "timing benchmark; run explicitly with --release"]
fn extra_m_timing() {
    let samples = 31;
    eprintln!("n\tcase\tchanged\tfull_ns\tnorm_ns\tpivots_ns\tclose_ns\tmove_ns");
    for n in [1usize, 2, 4, 8, 16, 32, 64] {
        let stage = (4096 / (n + 1)).max(16);
        // A bounded zone (every entry finite): i ≤ xᵢ ≤ 50 + 7i and
        // xᵢ − xᵢ₊₁ ≤ 3, so that `norm` and closure see finite entries.
        let mut g = Vec::new();
        for i in 1..=n {
            g.extend([le(i, 0, 50 + 7 * i as i64), le(0, i, -(i as i64))]);
            if i < n {
                g.push(le(i, i + 1, 3));
            }
        }
        let z = start_zone(n, &g);
        let top = (0..=n)
            .flat_map(|i| (0..=n).map(move |j| (i, j)))
            .filter_map(|(i, j)| z.entry(i, j).constant())
            .map(i32::abs)
            .max()
            .unwrap_or(0);
        let cases: [(&str, Vec<i32>); 3] = [
            ("none", vec![top + 1; n]),
            (
                "few",
                (1..=n).map(|x| if x == 1 { 0 } else { top + 1 }).collect(),
            ),
            ("many", vec![0; n]),
        ];
        for (name, m) in cases {
            let b = mb(&m);
            let mut w = z.clone().into_matrix().unwrap();
            let before = observe(&z);
            normalize(&mut w, &b);
            let changed = (0..=n)
                .flat_map(|i| (0..=n).map(move |j| (i, j)))
                .filter(|&(i, j)| exact(w.get(i, j)) != *before.entry(i, j).unwrap())
                .count();
            let mut ws = Workspace::new();
            let full = time_op(&z, stage, samples, |d| {
                d.try_extrapolate_max(&b, &mut ws).unwrap()
            });
            let norm = time_op(&z, stage, samples, |d| {
                let e = d.empty_like();
                let mut w = d.into_matrix().unwrap();
                normalize(&mut w, &b);
                std::hint::black_box(&w);
                e
            });
            let mut flags = Workspace::new();
            let pivots = time_op(&z, stage, samples, |d| {
                let m = d.into_matrix().unwrap();
                flags.reset_touched(m.dimension());
                flags.touched.fill(true);
                m.close_pivots(&flags.touched).unwrap()
            });
            let close = time_op(&z, stage, samples, |d| {
                d.into_matrix().unwrap().close().unwrap()
            });
            let moved = time_op(&z, stage, samples, |d| {
                let e = d.empty_like();
                std::hint::black_box(d.into_matrix());
                e
            });
            eprintln!(
                "{n}\t{name}\t{changed}\t{full:.1}\t{norm:.1}\t{pivots:.1}\t{close:.1}\t{moved:.1}"
            );
        }
    }
}
