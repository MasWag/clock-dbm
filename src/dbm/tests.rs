//! Unit tests for the DBM core, compared with the independent exact oracle
//! in `tests/support/oracle/`.
//!
//! These tests drive the crate-private [`Matrix`] directly, to test the full
//! closure kernel in isolation from the constraint operations of
//! `ops::constraints`. The oracle (`crate::oracle`, compiled only under
//! `cfg(test)`) uses only `super::` paths and dev-dependencies; it never
//! names a production type.
//!
//! Passing tests are additional evidence. The closure contract itself is
//! machine-checked by Creusot (see `verification/PROOF_STATUS.md`).

use super::*;
use crate::bounds::{MAX_CONSTANT, MIN_CONSTANT};
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};
use std::vec;

use crate::oracle;

use oracle::compare::{
    ObservedError, ObservedZone, PRODUCTION_MAX_CONSTANT, RangeExpectation, check_outcome,
    check_public_invariant, classify_range,
};
use oracle::random::{self, SplitMix64};
use oracle::scenario::{Op, Start, le, lt};
use oracle::{ExactBound, OracleConstraint, OracleDbm, fixtures};

// ----- translation between production and oracle -----

fn exact(b: Bound) -> ExactBound {
    ExactBound::from_parts(b.constant().map(i64::from), b.is_strict())
}

/// The production bound for an oracle bound, `None` if its constant is
/// unrepresentable.
fn packed(b: &ExactBound) -> Option<Bound> {
    match b {
        ExactBound::Infinity => Some(Bound::INFINITY),
        ExactBound::Finite { constant, .. } => {
            let c = constant.to_i32()?;
            if b.is_strict() {
                Bound::lt(c).ok()
            } else {
                Bound::le(c).ok()
            }
        }
    }
}

fn observe(z: &Dbm) -> ObservedZone {
    let n = z.variables();
    if z.is_empty() {
        assert_eq!(z.entries.len(), 0, "empty storage must hold no entries");
        ObservedZone::empty(n)
    } else {
        ObservedZone::from_entries(n, z.entries.iter().map(|&b| exact(b)).collect())
    }
}

fn observe_result(r: &Result<Dbm, Error>) -> Result<ObservedZone, ObservedError> {
    match r {
        Ok(z) => Ok(observe(z)),
        Err(Error::Range) => Err(ObservedError::Range),
        Err(e) => panic!("closure returned an argument error {e:?}"),
    }
}

/// `universe(n) ∧ cs`, closed by the production kernel. Panics if a
/// constraint is unrepresentable or out of range (test inputs never are).
fn close_constraints(n: usize, cs: &[OracleConstraint]) -> Result<Dbm, Error> {
    let mut m = Matrix::universe(n).unwrap();
    for c in cs {
        let b = packed(&c.bound).expect("representable test constraint");
        m.tighten(c.i, c.j, b);
    }
    m.close()
}

/// A raw (arbitrary, valid-code) `d × d` matrix, closed by the production kernel.
fn close_raw(n: usize, raw: &[Vec<ExactBound>]) -> Result<Dbm, Error> {
    let mut m = Matrix::universe(n).unwrap();
    for (i, row) in raw.iter().enumerate() {
        for (j, b) in row.iter().enumerate() {
            m.set(i, j, packed(b).expect("representable test entry"));
        }
    }
    m.close()
}

fn max_abs(bounds: impl IntoIterator<Item = ExactBound>) -> BigInt {
    bounds
        .into_iter()
        .filter_map(|b| b.constant().map(BigInt::abs))
        .max()
        .unwrap_or_else(BigInt::zero)
}

/// Compares a production closure with the oracle under the S§7 range rules.
fn check(
    label: &str,
    n: usize,
    input_bound: &BigInt,
    observed: &Result<Dbm, Error>,
    expected: &OracleDbm,
) -> RangeExpectation {
    let range = classify_range(n, input_bound, expected, PRODUCTION_MAX_CONSTANT);
    if let Err(e) = check_outcome(
        &observe_result(observed),
        &Ok(expected.clone()),
        range,
        PRODUCTION_MAX_CONSTANT,
    ) {
        panic!("{label}: {e}");
    }
    range
}

fn check_constraints(label: &str, n: usize, cs: &[OracleConstraint]) -> RangeExpectation {
    let expected = OracleDbm::from_constraints(n, cs).unwrap();
    let bound = max_abs(cs.iter().map(|c| c.bound.clone()));
    check(label, n, &bound, &close_constraints(n, cs), &expected)
}

// ----- constants and storage -----

#[test]
fn literal_constants() {
    const { assert!(MAX_DIMENSION == MAX_VARIABLES + 1) };
}

#[test]
fn constructors_match_oracle() {
    for n in fixtures::DIMENSIONS {
        let bound = BigInt::zero();
        check("zero", n, &bound, &Dbm::zero(n), &OracleDbm::zero(n));
        check(
            "universe",
            n,
            &bound,
            &Dbm::universe(n),
            &OracleDbm::universe(n),
        );
        check("empty", n, &bound, &Dbm::empty(n), &OracleDbm::empty(n));
        let u = Dbm::universe(n).unwrap();
        assert_eq!(u.entries.len(), (n + 1) * (n + 1));
        assert_eq!(Matrix::universe(n).unwrap().publish_canonical(), u);
        assert_eq!(u.clone().into_matrix().unwrap().close(), Ok(u));
        assert!(Dbm::empty(n).unwrap().into_matrix().is_none());
    }
}

#[test]
fn too_many_variables() {
    for n in [MAX_VARIABLES + 1, usize::MAX] {
        let e = Error::TooManyVariables { requested: n };
        assert_eq!(Matrix::universe(n).err(), Some(e));
    }
}

#[test]
fn accessors_and_argument_checks() {
    let z = close_constraints(2, &[le(1, 0, 3), lt(2, 1, -1)]).unwrap();
    assert_eq!(z.entry(1, 0), Bound::le(3).unwrap());
    assert_eq!(z.entry(0, 1), Bound::lt(-1).unwrap()); // x1 > x2 + 1 ≥ 1
    assert_eq!(z.check_clock(Clock::new(2).unwrap()), Ok(2));
    let empty = Dbm::empty(2).unwrap();
    for d in [&z, &empty] {
        assert_eq!(
            d.check_clock(Clock::new(3).unwrap()),
            Err(Error::ClockOutOfRange {
                clock: 3,
                variables: 2
            })
        );
        assert_eq!(d.check_variables(2), Ok(()));
        assert_eq!(
            d.check_variables(3),
            Err(Error::DimensionMismatch {
                expected: 2,
                found: 3
            })
        );
        assert_eq!(d.empty_like(), empty);
    }
}

#[test]
fn matrix_get_set_tighten() {
    let mut m = Matrix::universe(2).unwrap();
    assert_eq!(m.dimension(), 3);
    assert_eq!(m.get(1, 2), Bound::INFINITY);
    m.tighten(1, 2, Bound::le(4).unwrap());
    m.tighten(1, 2, Bound::le(7).unwrap()); // looser: no effect
    assert_eq!(m.get(1, 2), Bound::le(4).unwrap());
    m.set(1, 2, Bound::lt(9).unwrap()); // set may loosen
    assert_eq!(m.get(1, 2), Bound::lt(9).unwrap());
    assert_eq!(m.get(2, 1), Bound::INFINITY);
}

// ----- deterministic closure cases -----

#[test]
fn satisfiable_strict_inequalities() {
    // 0 < x < 1 (real clocks): nonempty.
    assert_eq!(
        check_constraints("0<x<1", 1, &[lt(0, 1, 0), lt(1, 0, 1)]),
        RangeExpectation::MustSucceed
    );
    // 0 < x < y < 1.
    let z = close_constraints(2, &[lt(0, 1, 0), lt(1, 2, 0), lt(2, 0, 1)]).unwrap();
    assert!(!z.is_empty());
    check_constraints("x<y<1", 2, &[lt(0, 1, 0), lt(1, 2, 0), lt(2, 0, 1)]);
}

#[test]
fn strict_zero_contradictions() {
    let cases: &[(&str, usize, Vec<OracleConstraint>)] = &[
        ("x<0", 1, vec![lt(1, 0, 0)]),
        ("x-y<0 & y-x<=0", 2, vec![lt(1, 2, 0), le(2, 1, 0)]),
        ("x<1 & x>1", 1, vec![lt(1, 0, 1), lt(0, 1, -1)]),
        ("x<=1 & x>1", 1, vec![le(1, 0, 1), lt(0, 1, -1)]),
        ("x-x<0", 1, vec![lt(1, 1, 0)]),
        ("x0-x0<0", 0, vec![lt(0, 0, 0)]),
    ];
    for (label, n, cs) in cases {
        let z = close_constraints(*n, cs).unwrap();
        assert_eq!(z, Dbm::empty(*n).unwrap(), "{label}");
        check_constraints(label, *n, cs);
    }
}

#[test]
fn inconsistent_triangle_cycles() {
    // x1 - x2 ≤ 1, x2 - x3 ≤ 1, x3 - x1 ≤ -3: cycle weight -1.
    let cyc = [le(1, 2, 1), le(2, 3, 1), le(3, 1, -3)];
    assert!(close_constraints(3, &cyc).unwrap().is_empty());
    check_constraints("weak cycle", 3, &cyc);
    // Weight exactly 0 with one strict edge: empty. All weak: nonempty.
    let strict = [le(1, 2, 1), lt(2, 3, 1), le(3, 1, -2)];
    assert!(close_constraints(3, &strict).unwrap().is_empty());
    check_constraints("strict zero cycle", 3, &strict);
    let weak = [le(1, 2, 1), le(2, 3, 1), le(3, 1, -2)];
    assert!(!close_constraints(3, &weak).unwrap().is_empty());
    check_constraints("weak zero cycle", 3, &weak);
}

#[test]
fn multiple_guards_and_zero_clocks() {
    // Guards on four clocks, redundant and tightening ones mixed.
    let gs = [
        le(1, 0, 5),
        le(0, 1, -2),
        lt(2, 1, 1),
        le(3, 0, 10),
        le(3, 0, 7),
        le(4, 3, 0),
        lt(0, 4, -1),
        le(2, 2, 3), // i == j, satisfiable: no effect
    ];
    check_constraints("guards", 4, &gs);
    // n = 0: the one-point zone; only x0 - x0 can be constrained.
    check_constraints("n=0 trivial", 0, &[le(0, 0, 5)]);
    assert_eq!(
        close_constraints(0, &[le(0, 0, 5)]).unwrap(),
        Dbm::zero(0).unwrap()
    );
    assert_eq!(Dbm::zero(0).unwrap(), Dbm::universe(0).unwrap());
}

#[test]
fn raw_inputs_are_normalized() {
    // n = 0 with a loose diagonal [∞].
    let r = close_raw(0, &[vec![ExactBound::Infinity]]).unwrap();
    assert_eq!(r, Dbm::zero(0).unwrap());
    // A positive reference row and loose diagonals (x0 - x1 ≤ 5, x1 - x1 ≤ 3).
    let raw = oracle::parse_matrix(&["<=0 <=5", "<=4 <=3"]);
    let expected = OracleDbm::from_matrix(1, raw.clone());
    check("raw", 1, &BigInt::from(5), &close_raw(1, &raw), &expected);
    // An all-∞ matrix is the universe.
    let raw = vec![vec![ExactBound::Infinity; 3]; 3];
    assert_eq!(close_raw(2, &raw).unwrap(), Dbm::universe(2).unwrap());
}

#[test]
fn constraint_fixtures_match_oracle() {
    let mut checked = 0;
    for f in fixtures::all() {
        let n = f.scenario.variables;
        let mut cs = match &f.scenario.start {
            Start::Zero => (1..=n).map(|i| le(i, 0, 0)).collect(),
            Start::Universe => vec![],
            Start::Constraints(cs) => cs.clone(),
            Start::Empty => continue,
        };
        // Only constraint-type steps can be expressed as one closure.
        let mut expressible = true;
        for op in &f.scenario.ops {
            match op {
                Op::Constrain(c) => cs.push(c.clone()),
                Op::ConstrainAll(more) | Op::Intersect(more) => cs.extend(more.iter().cloned()),
                _ => expressible = false,
            }
        }
        if !expressible {
            continue;
        }
        let expected = f.scenario.final_zone().unwrap();
        let observed = close_constraints(n, &cs);
        let bound = max_abs(cs.iter().map(|c| c.bound.clone()));
        check(&f.name, n, &bound, &observed, &expected);
        if let Ok(z) = &observed {
            assert_eq!(z.is_empty(), f.final_empty, "{}", f.name);
        }
        checked += 1;
    }
    assert!(checked >= 15, "only {checked} fixtures were expressible");
}

// ----- numerical limits -----

#[test]
fn range_limits() {
    let max = i64::from(MAX_CONSTANT);
    let min = i64::from(MIN_CONSTANT);
    // Exactly representable at the limit: x = MAX.
    let at = [le(1, 0, max), le(0, 1, min)];
    let z = close_constraints(1, &at).unwrap();
    assert_eq!(z.entry(1, 0), Bound::le(MAX_CONSTANT).unwrap());
    assert_eq!(z.entry(0, 1), Bound::le(MIN_CONSTANT).unwrap());
    check_constraints("x=MAX", 1, &at);
    // x - y ≤ MAX and y ≤ MAX: x ≤ 2·MAX is unrepresentable, so the closure
    // must fail with Range rather than saturate to ∞.
    let over = [le(1, 2, max), le(2, 0, max)];
    assert_eq!(close_constraints(2, &over), Err(Error::Range));
    assert_eq!(
        check_constraints("2*MAX", 2, &over),
        RangeExpectation::MustFailRange
    );
    // y ≥ x + MAX and x ≥ MAX: the oracle fixture of the same shape.
    let lower = [le(0, 1, -max), le(1, 2, -max)];
    assert_eq!(close_constraints(2, &lower), Err(Error::Range));
    // A contradiction among large constants is still emptiness, not an error:
    // x ≥ MAX and x < MAX.
    let contra = [le(0, 1, min), lt(1, 0, max)];
    assert!(close_constraints(1, &contra).unwrap().is_empty());
    check_constraints("x>=MAX & x<MAX", 1, &contra);
    // x > MAX - 1 (strict lower bound near the limit): nonempty.
    check_constraints("x>MAX-1", 1, &[lt(0, 1, min + 1)]);
}

// ----- randomized differential tests -----

fn random_bound(rng: &mut SplitMix64, max_c: i64) -> ExactBound {
    if rng.chance(1, 4) {
        return ExactBound::Infinity;
    }
    let c = rng.range(-max_c, max_c);
    if rng.chance(1, 2) {
        ExactBound::lt(c)
    } else {
        ExactBound::le(c)
    }
}

#[test]
fn random_raw_matrices_match_oracle() {
    let (mut nonempty, mut empty) = (0, 0);
    for seed in random::seeds(600) {
        let mut rng = random::case_rng("random_raw_matrices_match_oracle", seed);
        let n = rng.index(6);
        let d = n + 1;
        // Mostly loose matrices so a good share stays nonempty.
        let raw: Vec<Vec<ExactBound>> = (0..d)
            .map(|i| {
                (0..d)
                    .map(|j| {
                        if i == j && rng.chance(3, 4) {
                            ExactBound::le_zero()
                        } else if i == 0 || rng.chance(1, 2) {
                            let b = random_bound(&mut rng, 8);
                            if i == 0 { b } else { b.add(&ExactBound::le(4)) }
                        } else {
                            ExactBound::Infinity
                        }
                    })
                    .collect()
            })
            .collect();
        let expected = OracleDbm::from_matrix(n, raw.clone());
        let bound = max_abs(raw.iter().flatten().cloned());
        let label = format!("seed {seed} (ORACLE_SEED={seed}), n = {n}");
        check(&label, n, &bound, &close_raw(n, &raw), &expected);
        if expected.is_empty() {
            empty += 1;
        } else {
            nonempty += 1;
        }
    }
    if random::seeds(600).count() >= 100 {
        assert!(
            nonempty >= 50 && empty >= 50,
            "{nonempty} nonempty, {empty} empty"
        );
    }
}

#[test]
fn random_constraint_sets_match_oracle() {
    for seed in random::seeds(400) {
        let mut rng = random::case_rng("random_constraint_sets_match_oracle", seed);
        let n = rng.index(6);
        let count = rng.index(3 * n + 3);
        let label = format!("seed {seed} (ORACLE_SEED={seed}), n = {n}");
        let (cs, u) = random::consistent_constraints(&mut rng, n, count, 9);
        check_constraints(&format!("consistent {label}"), n, &cs);
        let z = close_constraints(n, &cs).unwrap();
        assert!(!z.is_empty(), "{label}: hidden witness {u:?}");
        let cs = random::inconsistent_constraints(&mut rng, n, count, 9);
        assert!(close_constraints(n, &cs).unwrap().is_empty(), "{label}");
        check_constraints(&format!("inconsistent {label}"), n, &cs);
        let cs: Vec<_> = (0..count)
            .map(|_| random::constraint(&mut rng, n, 6))
            .collect();
        check_constraints(&format!("arbitrary {label}"), n, &cs);
    }
}

#[test]
fn random_near_limit_constants() {
    // Constants near ±MAX_CONSTANT: results may be unrepresentable, which must
    // be Err(Range) (never ∞, never a wrapped value); representable results
    // must match the oracle exactly.
    let max = PRODUCTION_MAX_CONSTANT;
    let (mut ranges, mut oks) = (0, 0);
    for seed in random::seeds(400) {
        let mut rng = random::case_rng("random_near_limit_constants", seed);
        let n = rng.index(4) + 1;
        let count = rng.index(2 * n + 2) + 1;
        let cs: Vec<OracleConstraint> = (0..count)
            .map(|_| {
                let i = rng.index(n + 1);
                let j = rng.index(n + 1);
                let mag = max - rng.range(0, 3) - if rng.chance(1, 2) { max / 2 } else { 0 };
                let c = if rng.chance(1, 2) { mag } else { -mag };
                if rng.chance(1, 2) {
                    lt(i, j, c)
                } else {
                    le(i, j, c)
                }
            })
            .collect();
        let label = format!("seed {seed} (ORACLE_SEED={seed}), n = {n}");
        check_constraints(&label, n, &cs);
        match close_constraints(n, &cs) {
            Err(_) => ranges += 1,
            Ok(_) => oks += 1,
        }
    }
    if random::seeds(400).count() >= 100 {
        assert!(ranges >= 10 && oks >= 10, "{ranges} range errors, {oks} ok");
    }
}

#[test]
fn every_closure_result_is_canonical_or_empty() {
    // `check_outcome` already checks Inv; this also exercises the debug check
    // of `publish_canonical` on the same matrices.
    for seed in random::seeds(200) {
        let mut rng = random::case_rng("every_closure_result_is_canonical_or_empty", seed);
        let n = rng.index(5);
        let (cs, _) = random::consistent_constraints(&mut rng, n, 2 * n + 1, 7);
        let z = close_constraints(n, &cs).unwrap();
        check_public_invariant(&observe(&z), None).unwrap();
        assert_eq!(check_canonical(&z.entries, z.dimension()), Ok(()));
        assert_eq!(z.clone().into_matrix().unwrap().publish_canonical(), z);
    }
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "publish_canonical")]
fn publish_canonical_rejects_noncanonical() {
    let mut m = Matrix::universe(2).unwrap();
    m.set(1, 0, Bound::le(1).unwrap());
    m.set(2, 1, Bound::le(1).unwrap()); // (2,0) = ∞ > (2,1) + (1,0)
    let _ = m.publish_canonical();
}

#[test]
fn check_canonical_detects_each_violation() {
    let le0 = Bound::LE_ZERO;
    let inf = Bound::INFINITY;
    // Diagonal not Le 0.
    assert!(check_canonical(&[le0, le0, le0, Bound::lt(0).unwrap()], 2).is_err());
    // Reference row allows a negative clock.
    assert!(check_canonical(&[le0, Bound::le(1).unwrap(), inf, le0], 2).is_err());
    // A triangle whose sum underflows the supported range:
    // (0,2) = Le(-M) is looser than (0,1) + (1,2) = Le(-2M).
    let m = Bound::le(MIN_CONSTANT).unwrap();
    assert!(check_canonical(&[le0, m, m, inf, le0, m, inf, inf, le0], 3).is_err());
    // An overflowing sum is looser than any bound: no violation.
    let p = Bound::le(MAX_CONSTANT).unwrap();
    assert!(check_canonical(&[le0, le0, le0, p, le0, p, p, p, le0], 3).is_ok());
    // Universe is canonical.
    assert!(check_canonical(&[le0, le0, inf, le0], 2).is_ok());
}

#[test]
fn equality_is_entrywise() {
    // The hand-written, branch-free `PartialEq` agrees with
    // comparing the variable count and every packed entry.
    let entrywise = |a: &Dbm, b: &Dbm| a.variables == b.variables && a.entries[..] == b.entries[..];
    let mut zones = Vec::new();
    for n in [0usize, 1, 2, 5] {
        zones.push(Dbm::empty(n).unwrap());
        zones.push(Dbm::universe(n).unwrap());
        zones.push(Dbm::zero(n).unwrap());
        if n >= 1 {
            // Differs from universe(n) only in the last entry of row n.
            let mut m = Matrix::universe(n).unwrap();
            m.tighten(n, 0, Bound::le(7).unwrap());
            zones.push(m.close().unwrap());
        }
    }
    for a in &zones {
        for b in &zones {
            assert_eq!(a == b, entrywise(a, b), "{a:?} vs {b:?}");
        }
        assert_eq!(a, &a.clone());
    }
}
