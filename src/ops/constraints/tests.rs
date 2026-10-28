//! Differential tests of constraint insertion against the independent exact
//! oracle (`tests/support/oracle/`) and the proved full-closure kernel in
//! `dbm.rs`.
//!
//! Every successful incremental result also passes the debug-build
//! canonicity check of `Matrix::publish_canonical`. Passing tests are
//! evidence, not a formal proof of the incremental algorithm.

use super::*;
use crate::bounds::{Clock, MAX_CONSTANT, MIN_CONSTANT};
use crate::dbm::{Matrix, Workspace};
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};
use std::vec;

use crate::ops::test_support::{
    assert_outcome, con, cons, exact, max_abs, observe, observe_result, packed, start_zone, time_op,
};
use crate::oracle;

use oracle::compare::{
    ObservedError, ObservedZone, PRODUCTION_MAX_CONSTANT, RangeExpectation, check_outcome,
    classify_range,
};
use oracle::random::{self, SplitMix64};
use oracle::scenario::{Op, Start, le, lt};
use oracle::{ExactBound, OracleConstraint, OracleDbm, OracleError, fixtures};

/// The certified reference: tighten every entry, then full closure.
fn full_closure(z: &Dbm, gs: &[OracleConstraint]) -> Result<Dbm, Error> {
    if z.is_empty() {
        return Ok(z.clone());
    }
    z.clone().constrain_all_by_closure(&cons(gs))
}

/// A single constraint must fail with `Err(Range)` exactly when the exact
/// result is unrepresentable (module documentation, "Range exactness").
fn exact_range(expected: &Result<OracleDbm, OracleError>) -> RangeExpectation {
    match expected {
        Ok(e) if e.max_abs_constant() > BigInt::from(PRODUCTION_MAX_CONSTANT) => {
            RangeExpectation::MustFailRange
        }
        _ => RangeExpectation::MustSucceed,
    }
}

/// `try_constrain` on `universe(n) ∧ start` against the oracle (with the
/// exact range rule) and against the full closure.
fn check_single(label: &str, n: usize, start: &[OracleConstraint], g: &OracleConstraint) {
    let z = start_zone(n, start);
    let expected = OracleDbm::from_constraints(n, start).unwrap().constrain(g);
    let observed = z.clone().try_constrain(con(g));
    assert_outcome(label, &observed, &expected, exact_range(&expected));
    if let (Ok(a), Ok(b)) = (&observed, &full_closure(&z, std::slice::from_ref(g))) {
        assert_eq!(a, b, "{label}: incremental and full closure differ");
    }
}

/// `try_constrain_all` with both strategies and `try_from_constraints`
/// against the oracle, under the S§7 range rules.
fn check_batch(label: &str, n: usize, start: &[OracleConstraint], gs: &[OracleConstraint]) {
    let z = start_zone(n, start);
    let expected = OracleDbm::from_constraints(n, start)
        .unwrap()
        .constrain_all(gs);
    let bound = max_abs(start.iter().chain(gs));
    let range = match &expected {
        Ok(e) => classify_range(n, &bound, e, PRODUCTION_MAX_CONSTANT),
        Err(_) => RangeExpectation::MustSucceed,
    };
    let cs = cons(gs);
    let inc = z.clone().constrain_all_with(&cs, Strategy::Incremental);
    let full = z.clone().constrain_all_with(&cs, Strategy::FullClosure);
    let public = z.clone().try_constrain_all(&cs, &mut Workspace::new());
    assert_outcome(&format!("{label} [incremental]"), &inc, &expected, range);
    assert_outcome(&format!("{label} [full closure]"), &full, &expected, range);
    assert_outcome(&format!("{label} [public]"), &public, &expected, range);
    if let (Ok(a), Ok(b)) = (&inc, &full) {
        assert_eq!(a, b, "{label}: strategies differ");
    }
    if start.is_empty() {
        let from = Dbm::try_from_constraints(n, &cs, &mut Workspace::new());
        assert_outcome(
            &format!("{label} [from_constraints]"),
            &from,
            &expected,
            range,
        );
    }
}

// ----- single constraints -----

#[test]
fn implied_constraints_return_the_input() {
    // x ≤ 3 ∧ x − y < 1 (strict-bound regression).
    let a = [le(1, 0, 3), lt(1, 2, 1)];
    let z = start_zone(2, &a);
    for g in [
        le(1, 0, 3),
        le(1, 0, 5),
        lt(1, 0, 4),
        le(1, 2, 1),
        lt(1, 2, 1),
    ] {
        assert_eq!(z.clone().try_constrain(con(&g)), Ok(z.clone()), "{g:?}");
        check_single("implied", 2, &a, &g);
    }
    // Diagonal and nonnegativity constraints are always implied.
    for g in [le(1, 1, 0), le(2, 2, 7), le(0, 1, 0), le(0, 0, 0)] {
        assert_eq!(z.clone().try_constrain(con(&g)), Ok(z.clone()), "{g:?}");
    }
}

#[test]
fn weak_and_strict_tightening() {
    // §8.1: A ∧ (x ≥ 3) propagates strictness: B[0][y] = Lt (−2).
    let a = [le(1, 0, 3), lt(1, 2, 1)];
    let b = start_zone(2, &a).try_constrain(con(&le(0, 1, -3))).unwrap();
    assert_eq!(b.entry(0, 2), Bound::lt(-2).unwrap());
    assert_eq!(b.entry(0, 1), Bound::le(-3).unwrap());
    check_single("x>=3", 2, &a, &le(0, 1, -3));
    for g in [
        lt(1, 0, 3),
        le(1, 0, 2),
        lt(2, 1, 0),
        le(2, 0, 1),
        lt(0, 2, -1),
    ] {
        check_single("tighten", 2, &a, &g);
    }
}

#[test]
fn immediate_contradictions_are_empty() {
    let e = |n, start: &[OracleConstraint], g: OracleConstraint| {
        let z = start_zone(n, start).try_constrain(con(&g)).unwrap();
        assert!(z.is_empty(), "{start:?} ∧ {g:?}");
        assert_eq!(z.variables(), n);
        check_single("contradiction", n, start, &g);
    };
    // §8.2: x < 0; x ≤ 0 ∧ x > 0 (strict zero cycle); B ∧ y ≤ 2.
    e(1, &[], lt(1, 0, 0));
    e(1, &[le(1, 0, 0)], lt(0, 1, 0));
    e(2, &[le(1, 0, 3), lt(1, 2, 1), le(0, 1, -3)], le(2, 0, 2));
    // x − x < 0 and the reference clock against itself.
    e(1, &[], lt(1, 1, 0));
    e(1, &[], le(1, 1, -1));
    e(0, &[], lt(0, 0, 0));
    // A cycle closed through a third clock: x − y ≤ −1, y − z ≤ −1, z − x < 2.
    e(3, &[le(1, 2, -1), le(2, 3, -1)], lt(3, 1, 2));
    // ... but with ≤ 2 it is the single point of the cycle, nonempty.
    let z = start_zone(3, &[le(1, 2, -1), le(2, 3, -1)])
        .try_constrain(con(&le(3, 1, 2)))
        .unwrap();
    assert!(!z.is_empty());
}

#[test]
fn argument_errors_precede_emptiness() {
    let bad = Constraint::new(Clock::new(3).unwrap(), Clock::ZERO, Bound::LE_ZERO);
    let ok = Constraint::new(Clock::new(1).unwrap(), Clock::ZERO, Bound::LE_ZERO);
    let err = Err(Error::ClockOutOfRange {
        clock: 3,
        variables: 2,
    });
    let mut ws = Workspace::new();
    for z in [Dbm::empty(2).unwrap(), Dbm::universe(2).unwrap()] {
        assert_eq!(z.clone().try_constrain(bad), err);
        let rev = Constraint::new(Clock::ZERO, Clock::new(3).unwrap(), Bound::LE_ZERO);
        assert_eq!(z.clone().try_constrain(rev), err);
        assert_eq!(z.clone().try_constrain_all(&[ok, bad], &mut ws), err);
        assert_eq!(z.clone().try_constrain_all(&[bad, ok], &mut ws), err);
        for s in [Strategy::Incremental, Strategy::FullClosure] {
            assert_eq!(z.clone().constrain_all_with(&[ok, ok, bad], s), err);
        }
    }
    // An empty zone stays empty (and keeps its dimension) on valid input.
    let e = Dbm::empty(2).unwrap();
    assert_eq!(e.clone().try_constrain(ok), Ok(e.clone()));
    assert_eq!(e.clone().try_constrain_all(&[ok], &mut ws), Ok(e.clone()));
    // Argument errors of try_from_constraints, in order.
    assert_eq!(
        Dbm::try_from_constraints(crate::MAX_VARIABLES + 1, &[bad], &mut ws),
        Err(Error::TooManyVariables {
            requested: crate::MAX_VARIABLES + 1
        })
    );
    assert_eq!(Dbm::try_from_constraints(2, &[ok, bad], &mut ws), err);
}

#[test]
fn zero_clocks() {
    let mut ws = Workspace::new();
    let u = Dbm::universe(0).unwrap();
    assert_eq!(Dbm::try_from_constraints(0, &[], &mut ws), Ok(u.clone()));
    assert_eq!(u.clone().try_constrain(con(&le(0, 0, 0))), Ok(u.clone()));
    assert_eq!(u.clone().try_constrain(con(&le(0, 0, 4))), Ok(u.clone()));
    assert!(
        u.clone()
            .try_constrain(con(&lt(0, 0, 0)))
            .unwrap()
            .is_empty()
    );
    check_batch("n=0", 0, &[], &[le(0, 0, 3), lt(0, 0, 1)]);
    check_batch("n=0 empty", 0, &[], &[le(0, 0, 3), lt(0, 0, 0)]);
}

// ----- several constraints -----

/// Every permutation of `v`.
fn permutations<T: Clone>(v: &[T]) -> Vec<Vec<T>> {
    if v.len() <= 1 {
        return vec![v.to_vec()];
    }
    let mut out = Vec::new();
    for k in 0..v.len() {
        let mut rest = v.to_vec();
        let x = rest.remove(k);
        for mut p in permutations(&rest) {
            p.insert(0, x.clone());
            out.push(p);
        }
    }
    out
}

#[test]
fn shared_clocks_in_every_order() {
    // Guards over shared clocks x, y, z; one satisfiable and one
    // contradictory conjunction (the contradiction needs three of them).
    let sat = [
        le(1, 0, 5),
        lt(0, 2, -1),
        le(2, 1, 2),
        lt(3, 1, 0),
        le(0, 3, -1),
    ];
    let unsat = [le(1, 2, -1), le(2, 3, -1), lt(3, 1, 2), le(1, 0, 9)];
    let mut ws = Workspace::new();
    for (label, gs) in [("sat", &sat[..]), ("unsat", &unsat[..])] {
        let reference = Dbm::try_from_constraints(3, &cons(gs), &mut ws).unwrap();
        for p in permutations(gs) {
            check_batch(label, 3, &[], &p);
            let cs = cons(&p);
            for s in [Strategy::Incremental, Strategy::FullClosure] {
                let z = Dbm::universe(3).unwrap().constrain_all_with(&cs, s);
                assert_eq!(z.as_ref(), Ok(&reference), "{label} {p:?} {s:?}");
            }
            // One at a time through try_constrain.
            let mut z = Dbm::universe(3).unwrap();
            for c in &cs {
                z = z.try_constrain(*c).unwrap();
            }
            assert_eq!(z, reference, "{label} {p:?} sequential");
        }
        assert_eq!(reference.is_empty(), label == "unsat");
    }
    // Repeated and implied constraints change nothing.
    let mut doubled = sat.to_vec();
    doubled.extend(sat.iter().cloned());
    doubled.push(le(1, 0, 100));
    check_batch("multiplicity", 3, &[], &doubled);
}

#[test]
fn batch_contradicting_the_input_is_empty() {
    // The input has x ≤ 3; the third guard x > 3 contradicts it on its own
    // and empties the batch before any closure work, whatever the strategy.
    let start = [le(1, 0, 3), lt(1, 2, 1)];
    let gs = [le(2, 0, 9), lt(0, 2, -1), lt(0, 1, -3), le(1, 2, 0)];
    let z = start_zone(2, &start);
    for s in [Strategy::Incremental, Strategy::FullClosure] {
        let r = z.clone().constrain_all_with(&cons(&gs), s).unwrap();
        assert!(r.is_empty() && r.variables() == 2, "{s:?}");
    }
    for p in permutations(&gs) {
        check_batch("contradicts input", 2, &start, &p);
    }
}

#[test]
fn exhaustive_one_clock() {
    // n = 1 (d = 2) takes the special case of `constrain_one`: after the
    // implied/contradiction tests, only (i, j) changes. Check it against the
    // oracle for every start zone built from bounds on x and every guard
    // over small constants, both strictnesses and every index pair.
    let bounds = |c: i64| {
        [
            le(0, 0, 0),
            le(1, 0, c),
            lt(1, 0, c),
            le(0, 1, -c),
            lt(0, 1, -c),
        ]
    };
    let mut starts: Vec<Vec<OracleConstraint>> = vec![vec![]];
    for c in -1..=3 {
        for g in bounds(c) {
            starts.push(vec![g.clone()]);
            for h in bounds(c + 1) {
                starts.push(vec![g.clone(), h]);
            }
        }
    }
    let mut checked = 0;
    for start in &starts {
        if OracleDbm::from_constraints(1, start).unwrap().is_empty() {
            continue;
        }
        for (i, j) in [(0, 1), (1, 0), (0, 0), (1, 1)] {
            for c in -4..=4 {
                for g in [le(i, j, c), lt(i, j, c)] {
                    check_single("one clock", 1, start, &g);
                    checked += 1;
                }
            }
        }
    }
    assert!(checked > 1000, "{checked}");
}

#[test]
fn constraint_fixtures_match_oracle() {
    let mut ws = Workspace::new();
    let mut checked = 0;
    for f in fixtures::all() {
        let n = f.scenario.variables;
        let mut z = match &f.scenario.start {
            Start::Zero => Dbm::zero(n),
            Start::Universe => Dbm::universe(n),
            Start::Empty => Dbm::empty(n),
            Start::Constraints(cs) => Dbm::try_from_constraints(n, &cons(cs), &mut ws),
        };
        let expressible = f
            .scenario
            .ops
            .iter()
            .all(|op| matches!(op, Op::Constrain(_) | Op::ConstrainAll(_)));
        if !expressible {
            continue;
        }
        for op in &f.scenario.ops {
            z = match (z, op) {
                (Ok(cur), Op::Constrain(g)) => cur.try_constrain(con(g)),
                (Ok(cur), Op::ConstrainAll(gs)) => cur.try_constrain_all(&cons(gs), &mut ws),
                (other, _) => other,
            };
        }
        let expected = f
            .scenario
            .final_zone()
            .map_err(|e| panic!("{}: {e:?}", f.name));
        assert_outcome(&f.name, &z, &expected, exact_range(&expected));
        checked += 1;
    }
    assert!(checked >= 10, "only {checked} fixtures were expressible");
}

// ----- randomized differential tests -----

#[test]
fn random_single_constraints_match_oracle() {
    let (mut implied, mut empty, mut tightened) = (0, 0, 0);
    for seed in random::seeds(1500) {
        let mut rng = random::case_rng("random_single_constraints_match_oracle", seed);
        let n = rng.index(7);
        let count = rng.index(2 * n + 2);
        let (start, _) = random::consistent_constraints(&mut rng, n, count, 9);
        let g = random::constraint(&mut rng, n, 9);
        let label = format!("seed {seed} (ORACLE_SEED={seed}), n = {n}, {g:?}");
        check_single(&label, n, &start, &g);
        let z = start_zone(n, &start);
        match z.clone().try_constrain(con(&g)).unwrap() {
            r if r == z => implied += 1,
            r if r.is_empty() => empty += 1,
            _ => tightened += 1,
        }
    }
    if random::seeds(1500).count() >= 100 {
        assert!(
            implied >= 50 && empty >= 50 && tightened >= 50,
            "{implied} implied, {empty} empty, {tightened} tightened"
        );
    }
}

fn shuffle<T>(rng: &mut SplitMix64, v: &mut [T]) {
    for k in (1..v.len()).rev() {
        v.swap(k, rng.index(k + 1));
    }
}

#[test]
fn random_batches_match_oracle_in_any_order() {
    for seed in random::seeds(500) {
        let mut rng = random::case_rng("random_batches_match_oracle_in_any_order", seed);
        let n = rng.index(6);
        let label = format!("seed {seed} (ORACLE_SEED={seed}), n = {n}");
        let start_count = rng.index(n + 2);
        let (start, _) = random::consistent_constraints(&mut rng, n, start_count, 9);
        let count = rng.index(3 * n + 4);
        let (mut gs, _) = random::consistent_constraints(&mut rng, n, count, 9);
        check_batch(&format!("consistent {label}"), n, &start, &gs);
        shuffle(&mut rng, &mut gs);
        check_batch(&format!("consistent shuffled {label}"), n, &start, &gs);
        let mut gs = random::inconsistent_constraints(&mut rng, n, count, 9);
        check_batch(&format!("inconsistent {label}"), n, &start, &gs);
        shuffle(&mut rng, &mut gs);
        check_batch(&format!("inconsistent shuffled {label}"), n, &start, &gs);
        let gs: Vec<_> = (0..count)
            .map(|_| random::constraint(&mut rng, n, 6))
            .collect();
        check_batch(&format!("arbitrary {label}"), n, &start, &gs);
    }
}

// ----- numerical limits -----

#[test]
fn range_limits_single_constraint() {
    let max = i64::from(MAX_CONSTANT);
    let min = i64::from(MIN_CONSTANT);
    // y ≤ MAX, then x − y ≤ MAX: x ≤ 2·MAX is needed and unrepresentable.
    check_single("2*MAX", 2, &[le(2, 0, max)], &le(1, 2, max));
    assert_eq!(
        start_zone(2, &[le(2, 0, max)]).try_constrain(con(&le(1, 2, max))),
        Err(Error::Range)
    );
    // With x ≤ 5 already present, the same sum is not needed: Ok.
    let z = start_zone(2, &[le(2, 0, max), le(1, 0, 5)])
        .try_constrain(con(&le(1, 2, max)))
        .unwrap();
    assert_eq!(z.entry(1, 0), Bound::le(5).unwrap());
    check_single(
        "2*MAX implied",
        2,
        &[le(2, 0, max), le(1, 0, 5)],
        &le(1, 2, max),
    );
    // x ≥ MAX and y ≥ x + MAX: y ≥ 2·MAX is needed and unrepresentable.
    check_single("lower 2*MAX", 2, &[le(0, 1, min)], &le(1, 2, min));
    // A contradiction among extreme constants is emptiness, not Range:
    // x ≥ MAX, then x < −MAX (the reverse sum is below MIN_CONSTANT).
    let z = start_zone(1, &[le(0, 1, min)])
        .try_constrain(con(&lt(1, 0, min)))
        .unwrap();
    assert!(z.is_empty());
    // x = MAX exactly.
    check_single("x=MAX", 1, &[le(1, 0, max)], &le(0, 1, min));
}

#[test]
fn random_near_limit_constants() {
    let max = PRODUCTION_MAX_CONSTANT;
    let (mut ranges, mut oks) = (0, 0);
    for seed in random::seeds(600) {
        let mut rng = random::case_rng("ops_random_near_limit_constants", seed);
        let n = rng.index(4) + 1;
        let big = |rng: &mut SplitMix64| {
            let i = rng.index(n + 1);
            let j = rng.index(n + 1);
            let mag = max - rng.range(0, 3) - if rng.chance(1, 2) { max / 2 } else { 0 };
            let c = if rng.chance(1, 2) { mag } else { -mag };
            if rng.chance(1, 2) {
                lt(i, j, c)
            } else {
                le(i, j, c)
            }
        };
        let label = format!("seed {seed} (ORACLE_SEED={seed}), n = {n}");
        // A representable start zone, then one more big constraint.
        let mut start = Vec::new();
        for _ in 0..rng.index(n + 1) {
            let g = big(&mut rng);
            let mut next = start.clone();
            next.push(g);
            let e = OracleDbm::from_constraints(n, &next).unwrap();
            if e.max_abs_constant() <= BigInt::from(max) && !e.is_empty() {
                start = next;
            }
        }
        let g = big(&mut rng);
        check_single(&label, n, &start, &g);
        match start_zone(n, &start).try_constrain(con(&g)) {
            Err(_) => ranges += 1,
            Ok(_) => oks += 1,
        }
        let gs: Vec<_> = (0..rng.index(n + 2) + 1).map(|_| big(&mut rng)).collect();
        check_batch(&format!("batch {label}"), n, &start, &gs);
    }
    if random::seeds(600).count() >= 100 {
        assert!(ranges >= 10 && oks >= 10, "{ranges} range errors, {oks} ok");
    }
}

// ----- timing: incremental insertion vs full closure -----

/// A canonical nonempty zone over `n` clocks with many finite entries, and
/// the witness valuation (scaled by 2 to integers) it contains.
fn bench_zone(rng: &mut SplitMix64, n: usize) -> (Dbm, Vec<OracleConstraint>) {
    let (cs, _) = random::consistent_constraints(rng, n, 3 * n, 1000);
    (start_zone(n, &cs), cs)
}

/// Guards of one kind for zone `z`: `implied`, `tighten` (changes the zone,
/// stays nonempty) or `contradiction` (empty, found from the opposite entry).
fn bench_guards(rng: &mut SplitMix64, z: &Dbm, kind: &str, count: usize) -> Vec<Constraint> {
    let n = z.variables();
    let mut out = Vec::new();
    while out.len() < count {
        let i = rng.index(n + 1);
        let j = rng.index(n + 1);
        if i == j {
            continue;
        }
        let (ij, ji) = (z.entry(i, j), z.entry(j, i));
        let c = match kind {
            "implied" => match ij.constant() {
                Some(c) => Bound::le(c + 1).unwrap(),
                None => continue,
            },
            "contradiction" => match ji.constant() {
                // x_i − x_j < −c against x_j − x_i ≤ c (strict zero cycle).
                Some(c) => Bound::lt(-c).unwrap(),
                None => continue,
            },
            _ => {
                // Strictly between −D[j][i] and D[i][j]: tightens, nonempty.
                let hi = ij
                    .constant()
                    .map_or(i64::from(ji.constant().map_or(0, |c| -c)) + 50, i64::from);
                let lo = ji.constant().map_or(hi - 50, |c| -i64::from(c));
                if hi - lo < 2 {
                    continue;
                }
                let c = rng.range(lo + 1, hi - 1) as i32;
                if rng.chance(1, 2) {
                    Bound::lt(c).unwrap()
                } else {
                    Bound::le(c).unwrap()
                }
            }
        };
        let g = Constraint::new(Clock::new(i).unwrap(), Clock::new(j).unwrap(), c);
        let r = z.clone().try_constrain(g).unwrap();
        let ok = match kind {
            "implied" => r == *z,
            "contradiction" => r.is_empty(),
            _ => r != *z && !r.is_empty(),
        };
        if ok {
            out.push(g);
        }
    }
    out
}

/// Prints a Markdown table comparing incremental insertion with the full
/// closure. Run with
/// `cargo test --release --lib bench_incremental_vs_full_closure -- --ignored --nocapture`.
#[test]
#[ignore = "timing benchmark; run explicitly with --release"]
fn bench_incremental_vs_full_closure() {
    if cfg!(debug_assertions) {
        eprintln!("warning: debug build; publish_canonical runs an O(d³) check");
    }
    let samples = 15;
    println!("| n | guard | batch k | incremental (ns) | full closure (ns) | full / incremental |");
    println!("|---:|---|---:|---:|---:|---:|");
    for n in [4usize, 16, 64, 128] {
        let mut rng = random::case_rng("bench", n as u64);
        let (z, _) = bench_zone(&mut rng, n);
        let stage = (4_000_000 / ((n + 1) * (n + 1) * 4)).clamp(8, 4096);
        for kind in ["implied", "tighten", "contradiction"] {
            let gs = bench_guards(&mut rng, &z, kind, 1);
            let g = gs[0];
            let inc = time_op(&z, stage, samples, |d| d.try_constrain(g).unwrap());
            let full = time_op(&z, stage, samples, |d| {
                d.constrain_all_by_closure(&[g]).unwrap()
            });
            println!(
                "| {n} | {kind} | 1 | {inc:.0} | {full:.0} | {:.1} |",
                full / inc
            );
        }
        let mut ks = vec![2, n / 2, n, 2 * n, 4 * n];
        ks.dedup();
        for k in ks {
            // Start zone and guards share one witness, so the conjunction is
            // nonempty; some guards may be implied, as in practice.
            let (all, _) = random::consistent_constraints(&mut rng, n, 3 * n + k, 1000);
            let start = start_zone(n, &all[..3 * n]);
            let gs = cons(&all[3 * n..]);
            let inc = time_op(&start, stage, samples, |d| {
                d.constrain_all_with(&gs, Strategy::Incremental).unwrap()
            });
            let full = time_op(&start, stage, samples, |d| {
                d.constrain_all_with(&gs, Strategy::FullClosure).unwrap()
            });
            println!(
                "| {n} | consistent batch | {k} | {inc:.0} | {full:.0} | {:.2} |",
                full / inc
            );
        }
    }
}

/// Separates the consuming API's fixed costs from the intrinsic cost of the
/// O(1) cases: `consume` moves the staged zone through unchanged (the
/// harness baseline), `drop + ∅` frees the input storage and returns the
/// empty zone (what every contradiction must do under `self`-consuming
/// signatures). Run with
/// `cargo test --release --lib bench_constant_time_paths -- --ignored --nocapture`.
#[test]
#[ignore = "timing benchmark; run explicitly with --release"]
fn bench_constant_time_paths() {
    let samples = 15;
    println!(
        "| n | consume (ns) | drop + ∅ (ns) | implied (ns) | tighten (ns) | contradiction (ns) |"
    );
    println!("|---:|---:|---:|---:|---:|---:|");
    // The first configuration is timed twice; the first pass only warms up
    // the allocator and caches.
    for (pass, n) in [(0, 1usize), (1, 1), (1, 8), (1, 16), (1, 32), (1, 64)] {
        let mut rng = random::case_rng("bench_constant_time_paths", n as u64);
        let (z, _) = bench_zone(&mut rng, n);
        let stage = (4_000_000 / ((n + 1) * (n + 1) * 4)).clamp(8, 4096);
        let implied = bench_guards(&mut rng, &z, "implied", 1)[0];
        let tighten = bench_guards(&mut rng, &z, "tighten", 1)[0];
        let contra = bench_guards(&mut rng, &z, "contradiction", 1)[0];
        let consume = time_op(&z, stage, samples, |d| d);
        let drop_empty = time_op(&z, stage, samples, |d| d.empty_like());
        let imp = time_op(&z, stage, samples, |d| d.try_constrain(implied).unwrap());
        let tig = time_op(&z, stage, samples, |d| d.try_constrain(tighten).unwrap());
        let con = time_op(&z, stage, samples, |d| d.try_constrain(contra).unwrap());
        if pass == 1 {
            println!("| {n} | {consume:.1} | {drop_empty:.1} | {imp:.1} | {tig:.1} | {con:.1} |");
        }
    }
}

/// A representative one-clock workload: each transition
/// copies its source zone (exploration keeps the source), applies a guard of
/// one or two constraints on `x`, and tests emptiness. Compares the copy
/// alone with copy plus guard. Run with
/// `cargo test --release --lib bench_one_clock_workload -- --ignored --nocapture`.
#[test]
#[ignore = "timing benchmark; run explicitly with --release"]
fn bench_one_clock_workload() {
    let mut rng = random::case_rng("bench_one_clock_workload", 1);
    // 64 source zones `a ≤ x ≤ b` (some unbounded above) and 256 guards
    // `x ⋈ c` / `x ⋈ c ∧ x ⋈ c'` with constants in 0..=40: a mix of implied,
    // tightening and disabled (contradicting) guards, as in a one-clock
    // automaton.
    let zones: Vec<Dbm> = (0..64)
        .map(|_| {
            let a = rng.range(0, 20);
            let mut cs = vec![le(0, 1, -a)];
            if rng.chance(3, 4) {
                cs.push(le(1, 0, a + rng.range(0, 20)));
            }
            start_zone(1, &cs)
        })
        .collect();
    let guard = |rng: &mut SplitMix64| {
        let c = rng.range(0, 40);
        match rng.index(4) {
            0 => lt(1, 0, c),
            1 => le(1, 0, c),
            2 => lt(0, 1, -c),
            _ => le(0, 1, -c),
        }
    };
    let guards: Vec<Vec<Constraint>> = (0..256)
        .map(|_| {
            let k = 1 + rng.index(2);
            (0..k).map(|_| con(&guard(&mut rng))).collect()
        })
        .collect();
    let transitions = 1 << 16;
    let run = |f: &mut dyn FnMut(&Dbm, &[Constraint]) -> bool| {
        let t0 = std::time::Instant::now();
        let mut enabled = 0u64;
        for t in 0..transitions {
            enabled += u64::from(f(&zones[t % zones.len()], &guards[(t * 7) % guards.len()]));
        }
        std::hint::black_box(enabled);
        t0.elapsed().as_nanos() as f64 / transitions as f64
    };
    let mut copy = |z: &Dbm, _: &[Constraint]| !std::hint::black_box(z.clone()).is_empty();
    let mut consuming = |z: &Dbm, gs: &[Constraint]| {
        let mut w = z.clone();
        for &g in gs {
            w = w.try_constrain(g).unwrap();
            if w.is_empty() {
                return false;
            }
        }
        true
    };
    // Interleaved rounds, best of each (the first round only warms up).
    let mut best = [f64::INFINITY; 2];
    for round in 0..31 {
        let t = [run(&mut copy), run(&mut consuming)];
        if round > 0 {
            for k in 0..2 {
                best[k] = best[k].min(t[k]);
            }
        }
    }
    println!("| variant | ns per transition |");
    println!("|---|---:|");
    println!("| copy only | {:.1} |", best[0]);
    println!("| copy + guard (consuming API) | {:.1} |", best[1]);
}
