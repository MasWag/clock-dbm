//! Differential tests of the relations and queries against the independent
//! exact oracle (`tests/support/oracle/`).
//!
//! Each query is compared twice: with the oracle's own closed form, and with
//! an independent semantic check built from the oracle's closure
//! (`constrain`, `intersect`), its witnesses and `subset_counterexample`.
//! Every successful intersection also passes the oracle's public-invariant
//! check. Passing tests provide regression evidence; the operation
//! contracts are proved separately with Creusot.

use super::*;
use crate::bounds::{MAX_CONSTANT, MIN_CONSTANT};
use crate::ops::test_support::{assert_outcome, exact, packed, start_zone};
use std::collections::HashSet;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::vec;

use crate::oracle;

use oracle::compare::{PRODUCTION_MAX_CONSTANT, RangeExpectation, classify_range};
use oracle::random::{self, SplitMix64};
use oracle::scenario::{le, lt};
use oracle::valuation::Valuation;
use oracle::{ExactBound, OracleConstraint, OracleDbm, OracleError};

fn clk(i: usize) -> Clock {
    Clock::new(i).unwrap()
}

/// The oracle zone denoted by a production DBM.
fn as_oracle(z: &Dbm) -> OracleDbm {
    match crate::ops::test_support::observe(z).matrix() {
        Some(m) => OracleDbm::from_matrix(z.variables(), m),
        None => OracleDbm::empty(z.variables()),
    }
}

/// A production argument error in the oracle's terms.
fn arg(e: Error) -> OracleError {
    match e {
        Error::DimensionMismatch { expected, found } => {
            OracleError::DimensionMismatch { expected, found }
        }
        Error::ClockOutOfRange { clock, variables } => {
            OracleError::ClockOutOfRange { clock, variables }
        }
        e => panic!("a query returned {e:?}"),
    }
}

fn hash_of(z: &Dbm) -> u64 {
    let mut h = DefaultHasher::new();
    z.hash(&mut h);
    h.finish()
}

fn ws() -> Workspace {
    Workspace::new()
}

/// The production constraint `(i, j, b)`; `b` must be representable.
fn con(i: usize, j: usize, b: &ExactBound) -> Constraint {
    Constraint::new(clk(i), clk(j), packed(b).expect("representable bound"))
}

/// Query bounds for `(i, j)`: `∞`, small constants and the limits in both
/// strictnesses, and the boundary cases of both formulas: `D[i][j]` (for
/// `entails`) and `−D[j][i]` (for `intersects_constraint`), each with its
/// neighbors.
fn query_bounds(z: &Dbm, i: usize, j: usize) -> Vec<ExactBound> {
    let mut cs: Vec<i64> = vec![-1, 0, 1, i64::from(MAX_CONSTANT), i64::from(MIN_CONSTANT)];
    let d = z.dimension();
    if !z.is_empty() && i < d && j < d {
        if let Some(c) = z.entry(i, j).constant() {
            let c = i64::from(c);
            cs.extend([c - 1, c, c + 1]);
        }
        if let Some(c) = z.entry(j, i).constant() {
            let c = -i64::from(c);
            cs.extend([c - 1, c, c + 1]);
        }
    }
    cs.sort_unstable();
    cs.dedup();
    let mut out = vec![ExactBound::Infinity];
    for c in cs {
        out.extend([ExactBound::lt(c), ExactBound::le(c)]);
    }
    out.retain(|b| packed(b).is_some());
    out
}

/// Every query on `z`, for all clock pairs (including one index past the
/// last clock) and their [`query_bounds`].
fn check_queries(label: &str, z: &Dbm) {
    let o = as_oracle(z);
    let n = z.variables();
    for i in 0..=n + 1 {
        for j in 0..=n + 1 {
            let l = format!("{label} ({i},{j})");
            let db = z
                .difference_bound(clk(i), clk(j))
                .map(|b| b.map(exact))
                .map_err(arg);
            assert_eq!(db, o.difference_bound(i, j), "{l} difference_bound");
            if let Ok(Some(b)) = &db {
                // Tightest: it holds, and the next tighter integer bound
                // (`Le c` → `Lt c`, `Lt c` → `Le (c − 1)`) does not.
                let g = OracleConstraint::new(i, j, b.clone());
                assert_eq!(o.constrain(&g).as_ref(), Ok(&o), "{l} bound holds");
                if let Some(c) = b.constant() {
                    let tighter = if b.is_strict() {
                        ExactBound::le(c - 1)
                    } else {
                        ExactBound::lt(c.clone())
                    };
                    let outside = OracleConstraint::new(i, j, tighter).negated().unwrap();
                    assert!(
                        !o.constrain(&outside).unwrap().is_empty(),
                        "{l} not tightest"
                    );
                }
            }
            for b in &query_bounds(z, i, j) {
                let g = OracleConstraint::new(i, j, b.clone());
                let c = con(i, j, b);
                let l = format!("{l} {g}");
                let ent = z.entails(&c).map_err(arg);
                let int = z.intersects_constraint(&c).map_err(arg);
                assert_eq!(ent, o.entails(&g), "{l} entails");
                assert_eq!(int, o.intersects_constraint(&g), "{l} intersects");
                let (Ok(ent), Ok(int)) = (ent, int) else {
                    continue;
                };
                // Independent semantic checks through the oracle's closure.
                let sem_ent = match g.negated() {
                    Some(neg) => o.constrain(&neg).unwrap().is_empty(),
                    None => true,
                };
                let met = o.constrain(&g).unwrap();
                assert_eq!(ent, sem_ent, "{l} entails (semantic)");
                assert_eq!(int, !met.is_empty(), "{l} intersects (semantic)");
                if let Some(w) = met.witness() {
                    assert!(o.contains(&w) && w.satisfies(&g), "{l} witness");
                }
                if !o.is_empty() {
                    assert!(
                        !ent || int,
                        "{l}: a nonempty zone entails only what it meets"
                    );
                }
            }
        }
    }
}

/// Inclusion, equality, hashing and intersection of `a` and `b`, both
/// ways round.
fn check_pair(label: &str, a: &Dbm, b: &Dbm) {
    check_ordered(label, a, b);
    check_ordered(&format!("{label} (swapped)"), b, a);
}

fn check_ordered(label: &str, a: &Dbm, b: &Dbm) {
    let (oa, ob) = (as_oracle(a), as_oracle(b));
    let sub = a.is_subset_of(b).map_err(arg);
    assert_eq!(sub, oa.is_subset_of(&ob), "{label} is_subset_of");
    let inter = a.clone().try_intersect(b, &mut ws());
    let expected = oa.intersect(&ob);
    let Ok(sub) = sub else {
        // Different dimensions: every relation is an argument error, and
        // the zones are unequal (also when both are empty).
        assert_ne!(a.variables(), b.variables());
        assert_ne!(a, b, "{label}");
        let e = Err(Error::DimensionMismatch {
            expected: a.variables(),
            found: b.variables(),
        });
        assert_eq!(inter, e, "{label} try_intersect");
        return;
    };
    let n = a.variables();
    // Inclusion, semantically: a counterexample point, or `a ∩ b = a`.
    match oa.subset_counterexample(&ob) {
        Some(w) => {
            assert!(!sub, "{label}: subset with a counterexample");
            assert!(
                oa.contains(&w) && !ob.contains(&w),
                "{label} counterexample"
            );
        }
        None => {
            assert!(sub, "{label}: not a subset without a counterexample");
            assert_eq!(expected.as_ref(), Ok(&oa), "{label} a ∩ b = a");
        }
    }
    // Equality and hashing: mutual inclusion.
    let eq = sub && b.is_subset_of(a).unwrap();
    assert_eq!(a == b, eq, "{label} ==");
    assert_eq!(a == b, oa == ob, "{label} == vs oracle");
    if a == b {
        assert_eq!(hash_of(a), hash_of(b), "{label} hash");
    }
    // Intersection.
    let expected_zone = expected.as_ref().unwrap();
    let input_bound = oa.max_abs_constant().max(ob.max_abs_constant());
    let range = classify_range(n, &input_bound, expected_zone, PRODUCTION_MAX_CONSTANT);
    assert_outcome(&format!("{label} try_intersect"), &inter, &expected, range);
    if let Ok(r) = &inter {
        assert_eq!(r.variables(), n);
        assert!(r.is_subset_of(a).unwrap() && r.is_subset_of(b).unwrap());
        if let Some(w) = expected_zone.witness() {
            assert!(oa.contains(&w) && ob.contains(&w), "{label} witness");
        }
        if sub {
            assert_eq!(r, a, "{label}: a ⊆ b ⇒ a ∩ b = a");
        }
        if let Ok(s) = b.clone().try_intersect(a, &mut ws()) {
            assert_eq!(&s, r, "{label}: intersection commutes");
        }
        assert_eq!(
            r.clone().try_intersect(r, &mut ws()).as_ref(),
            Ok(r),
            "{label}: idempotent"
        );
    }
}

fn zone(n: usize, cs: &[OracleConstraint]) -> Dbm {
    start_zone(n, cs)
}

// ----- worked examples of empty-zone query behavior -----

#[test]
fn worked_8_3_empty_zone_queries() {
    let e = Dbm::empty(2).unwrap();
    let u = Dbm::universe(2).unwrap();
    let x_lt_0 = Constraint::lt(clk(1), Clock::ZERO, 0).unwrap();
    assert_eq!(e.entails(&x_lt_0), Ok(true));
    assert_eq!(e.intersects_constraint(&x_lt_0), Ok(false));
    assert_eq!(e.difference_bound(clk(1), clk(2)), Ok(None));
    assert_eq!(e.is_subset_of(&u), Ok(true));
    assert_eq!(u.is_subset_of(&e), Ok(false));
    assert_eq!(e, Dbm::empty(2).unwrap());
    assert_ne!(e, Dbm::empty(3).unwrap());
    let e3 = Dbm::empty(3).unwrap();
    let mismatch = Error::DimensionMismatch {
        expected: 2,
        found: 3,
    };
    assert_eq!(e.is_subset_of(&e3), Err(mismatch));
    assert_eq!(e.clone().try_intersect(&e3, &mut ws()), Err(mismatch));
    // Argument checks precede emptiness.
    let bad = Constraint::le(clk(3), Clock::ZERO, 1).unwrap();
    let oob = Error::ClockOutOfRange {
        clock: 3,
        variables: 2,
    };
    assert_eq!(e.entails(&bad), Err(oob));
    assert_eq!(e.intersects_constraint(&bad), Err(oob));
    assert_eq!(e.difference_bound(clk(0), clk(3)), Err(oob));
    assert_eq!(e.difference_bound(clk(3), clk(0)), Err(oob));
    // The universe is not empty: every in-range constraint on it is met.
    assert_eq!(u.intersects_constraint(&x_lt_0), Ok(false));
    assert_eq!(u.entails(&x_lt_0), Ok(false));
    assert_eq!(
        u.difference_bound(clk(1), clk(2)),
        Ok(Some(Bound::INFINITY))
    );
}

#[test]
fn universal_versus_existential() {
    // 0 ≤ x ≤ 10 with x < 5: not entailed, but intersected.
    let z = zone(1, &[le(1, 0, 10)]);
    let x_lt_5 = Constraint::lt(clk(1), Clock::ZERO, 5).unwrap();
    assert_eq!(z.entails(&x_lt_5), Ok(false));
    assert_eq!(z.intersects_constraint(&x_lt_5), Ok(true));
    let x_le_10 = Constraint::le(clk(1), Clock::ZERO, 10).unwrap();
    assert_eq!(z.entails(&x_le_10), Ok(true));
    let x_gt_10 = Constraint::lt(Clock::ZERO, clk(1), -10).unwrap();
    assert_eq!(z.intersects_constraint(&x_gt_10), Ok(false));
    assert_eq!(
        z.difference_bound(clk(1), Clock::ZERO),
        Ok(Some(Bound::le(10).unwrap()))
    );
    assert_eq!(
        z.difference_bound(Clock::ZERO, clk(1)),
        Ok(Some(Bound::LE_ZERO))
    );
    check_queries("0 ≤ x ≤ 10", &z);
}

#[test]
fn strict_and_weak_endpoints() {
    // x ≤ 5 meets x ≥ 5 in a point; x < 5 does not.
    let le5 = zone(1, &[le(1, 0, 5)]);
    let lt5 = zone(1, &[lt(1, 0, 5)]);
    let ge5 = zone(1, &[le(0, 1, -5)]);
    let point = le5.clone().try_intersect(&ge5, &mut ws()).unwrap();
    assert!(!point.is_empty());
    assert_eq!(
        point.difference_bound(clk(1), Clock::ZERO),
        Ok(Some(Bound::le(5).unwrap()))
    );
    assert!(
        lt5.clone()
            .try_intersect(&ge5, &mut ws())
            .unwrap()
            .is_empty()
    );
    // Inclusion distinguishes the endpoints.
    assert_eq!(lt5.is_subset_of(&le5), Ok(true));
    assert_eq!(le5.is_subset_of(&lt5), Ok(false));
    // Queries with equal constants and different strictness.
    let c_lt = Constraint::lt(clk(1), Clock::ZERO, 5).unwrap();
    let c_le = Constraint::le(clk(1), Clock::ZERO, 5).unwrap();
    let c_ge = Constraint::le(Clock::ZERO, clk(1), -5).unwrap();
    let c_gt = Constraint::lt(Clock::ZERO, clk(1), -5).unwrap();
    assert_eq!(le5.entails(&c_le), Ok(true));
    assert_eq!(le5.entails(&c_lt), Ok(false));
    assert_eq!(lt5.entails(&c_lt), Ok(true));
    assert_eq!(le5.intersects_constraint(&c_ge), Ok(true));
    assert_eq!(lt5.intersects_constraint(&c_ge), Ok(false));
    assert_eq!(le5.intersects_constraint(&c_gt), Ok(false));
    for (name, z) in [
        ("le5", &le5),
        ("lt5", &lt5),
        ("ge5", &ge5),
        ("point", &point),
    ] {
        check_queries(name, z);
    }
    check_pair("le5/ge5", &le5, &ge5);
    check_pair("lt5/ge5", &lt5, &ge5);
    check_pair("lt5/le5", &lt5, &le5);
    // Strict-zero diagonal cycle: x − y < 0 and y − x ≤ 0 meet x = y in
    // nothing.
    let a = zone(2, &[lt(1, 2, 0)]);
    let b = zone(2, &[le(2, 1, 0)]);
    assert!(a.clone().try_intersect(&b, &mut ws()).unwrap().is_empty());
    check_pair("strict zero cycle", &a, &b);
}

#[test]
fn unbounded_differences_are_not_empty() {
    let z = zone(2, &[le(1, 2, 3)]).future();
    assert_eq!(
        z.difference_bound(clk(1), Clock::ZERO),
        Ok(Some(Bound::INFINITY))
    );
    assert_eq!(
        z.difference_bound(clk(2), clk(1)),
        Ok(Some(Bound::INFINITY))
    );
    assert_eq!(
        z.difference_bound(clk(1), clk(2)),
        Ok(Some(Bound::le(3).unwrap()))
    );
    let e = Dbm::empty(2).unwrap();
    assert_eq!(e.difference_bound(clk(1), Clock::ZERO), Ok(None));
    // Every constraint meets an unbounded direction; none bounds it.
    let far = Constraint::le(Clock::ZERO, clk(1), -MAX_CONSTANT).unwrap();
    assert_eq!(z.intersects_constraint(&far), Ok(true));
    assert_eq!(z.entails(&far), Ok(false));
    check_queries("unbounded", &z);
}

#[test]
fn intersection_empty_only_through_a_long_cycle() {
    // D: x1 ≤ x2, x3 ≤ x4; E: x2 ≤ x3 − 1, x4 ≤ x1 − 1. Every pairwise test
    // D[i][j] + E[j][i] ≥ Le 0 passes (the opposite entries are ∞), but the
    // cycle x1 → x2 → x3 → x4 → x1 has weight −2: only the closure finds it.
    let a = zone(4, &[le(1, 2, 0), le(3, 4, 0)]);
    let b = zone(4, &[le(2, 3, -1), le(4, 1, -1)]);
    for (i, j) in [(1, 2), (3, 4), (2, 3), (4, 1)] {
        assert!(a.entry(j, i).is_infinite() || b.entry(j, i).is_infinite());
    }
    let r = a.clone().try_intersect(&b, &mut ws()).unwrap();
    assert!(r.is_empty() && r.variables() == 4);
    check_pair("long cycle", &a, &b);
    // The same with a strict-zero cycle: x1 ≤ x2 < x3 ≤ x4 ≤ x1.
    let b = zone(4, &[lt(2, 3, 0), le(4, 1, 0)]);
    assert!(a.clone().try_intersect(&b, &mut ws()).unwrap().is_empty());
    check_pair("long strict-zero cycle", &a, &b);
    // Relaxing it by one makes it nonempty.
    let b = zone(4, &[le(2, 3, 0), le(4, 1, 0)]);
    assert!(!a.clone().try_intersect(&b, &mut ws()).unwrap().is_empty());
    check_pair("long zero cycle", &a, &b);
}

/// A cycle through `len ≥ 4` distinct clocks whose edges alternate between
/// the two zones, with total weight in `−2..=1` (strict or weak), plus a few
/// random constraints satisfied by a hidden valuation. Such intersections
/// are often empty although no single pair of entries contradicts.
#[test]
fn random_alternating_cycles() {
    let mut long_cycles = 0;
    for seed in random::seeds(300) {
        let mut rng = random::case_rng("relations_cycles", seed);
        let n = rng.index(4) + 4;
        // Distinct clocks of the cycle (x0 allowed), in random order.
        let mut clocks: Vec<usize> = (0..=n).collect();
        for k in (1..clocks.len()).rev() {
            clocks.swap(k, rng.index(k + 1));
        }
        let len = 4 + 2 * rng.index((n + 1 - 4) / 2 + 1);
        let cycle = &clocks[..len];
        let total = rng.range(-2, 1);
        let mut sides = [Vec::new(), Vec::new()];
        for (k, &i) in cycle.iter().enumerate() {
            let j = cycle[(k + 1) % len];
            // Weights: random, with the last edge fixing the total.
            let c = if k + 1 < len { rng.range(-3, 3) } else { 0 };
            sides[k % 2].push((i, j, c));
        }
        let sum: i64 = sides.iter().flatten().map(|e| e.2).sum();
        sides[(len - 1) % 2].last_mut().unwrap().2 += total - sum;
        let strict = rng.chance(1, 3);
        let mut cs = [Vec::new(), Vec::new()];
        for (side, edges) in sides.iter().enumerate() {
            for (k, &(i, j, c)) in edges.iter().enumerate() {
                cs[side].push(if strict && k == 0 {
                    lt(i, j, c)
                } else {
                    le(i, j, c)
                });
            }
        }
        let a = zone(n, &cs[0]);
        let b = zone(n, &cs[1]);
        if a.is_empty() || b.is_empty() {
            continue;
        }
        let d = n + 1;
        let pairwise = (0..d).any(|i| {
            (0..d).any(|j| crate::ops::constraints::below_le_zero(a.entry(i, j), b.entry(j, i)))
        });
        let r = a.clone().try_intersect(&b, &mut ws()).unwrap();
        long_cycles += usize::from(r.is_empty() && !pairwise);
        check_pair(&format!("seed {seed} (ORACLE_SEED={seed})"), &a, &b);
    }
    if random::seeds(300).count() >= 100 {
        assert!(
            long_cycles >= 10,
            "{long_cycles} long-cycle empty intersections"
        );
    }
}

#[test]
fn inclusion_is_not_symmetric() {
    let small = zone(2, &[le(1, 0, 2), le(2, 0, 2)]);
    let big = zone(2, &[le(1, 0, 5)]);
    assert_eq!(small.is_subset_of(&big), Ok(true));
    assert_eq!(big.is_subset_of(&small), Ok(false));
    assert_ne!(small, big);
    let both = small.clone().try_intersect(&big, &mut ws()).unwrap();
    assert_eq!(both, small);
    check_pair("small/big", &small, &big);
    // Different constraints, same zone: equal, with equal hashes.
    let a = zone(2, &[le(1, 0, 2), le(2, 1, 0)]);
    let b = zone(2, &[le(1, 0, 2), le(2, 0, 2), le(2, 1, 0)]);
    assert_eq!(a, b);
    assert_eq!(hash_of(&a), hash_of(&b));
    check_pair("same zone", &a, &b);
}

#[test]
fn empty_operands_and_dimensions() {
    for n in [0usize, 1, 2, 5] {
        let e = Dbm::empty(n).unwrap();
        for z in [Dbm::zero(n).unwrap(), Dbm::universe(n).unwrap(), e.clone()] {
            let r = z.clone().try_intersect(&e, &mut ws()).unwrap();
            assert!(r.is_empty() && r.variables() == n);
            let r = e.clone().try_intersect(&z, &mut ws()).unwrap();
            assert!(r.is_empty() && r.variables() == n);
            check_pair(&format!("n{n}"), &z, &e);
            check_queries(&format!("n{n} {z:?}"), &z);
            for m in [0usize, 1, 3] {
                if m != n {
                    for w in [Dbm::empty(m).unwrap(), Dbm::universe(m).unwrap()] {
                        check_pair(&format!("n{n} vs n{m}"), &z, &w);
                    }
                }
            }
        }
    }
    // Hashing respects dimensions of empty zones in practice.
    let set: HashSet<Dbm> = (0..6).map(|n| Dbm::empty(n).unwrap()).collect();
    assert_eq!(set.len(), 6);
}

// ----- exhaustive small cases -----

/// Every distinct nonempty zone over `n ≤ 2` clocks built from one upper,
/// one lower and (for two clocks) one difference constraint per clock or
/// pair, with constants in `0..=2`, both strictnesses, plus `∅`.
fn small_zones(n: usize) -> Vec<Dbm> {
    let opt = |cs: Vec<OracleConstraint>| -> Vec<Option<OracleConstraint>> {
        std::iter::once(None)
            .chain(cs.into_iter().map(Some))
            .collect()
    };
    let mut families: Vec<Vec<Option<OracleConstraint>>> = Vec::new();
    for x in 1..=n {
        families.push(opt(vec![le(x, 0, 1), lt(x, 0, 1), le(x, 0, 2)]));
        families.push(opt(vec![le(0, x, -1), lt(0, x, -1), lt(0, x, 0)]));
    }
    if n == 2 {
        families.push(opt(vec![le(1, 2, 0), lt(1, 2, 0), le(1, 2, 1)]));
        families.push(opt(vec![le(2, 1, 0), lt(2, 1, 1)]));
    }
    let mut out: Vec<Dbm> = vec![Dbm::empty(n).unwrap()];
    let mut picks: Vec<Vec<OracleConstraint>> = vec![vec![]];
    for f in &families {
        picks = picks
            .into_iter()
            .flat_map(|p| {
                f.iter().map(move |c| {
                    let mut p = p.clone();
                    p.extend(c.clone());
                    p
                })
            })
            .collect();
    }
    for p in picks {
        let z = zone(n, &p);
        if !out.contains(&z) {
            out.push(z);
        }
    }
    out
}

#[test]
fn exhaustive_small_zones() {
    for n in 1..=2 {
        let zones = small_zones(n);
        assert!(
            zones.len() >= if n == 1 { 10 } else { 500 },
            "{}",
            zones.len()
        );
        // Every query on every zone; every pair for one clock, and every
        // pair of a fixed stride-chosen subset for two (all pairs would
        // take minutes against the BigInt oracle in a debug build).
        let stride = if n == 1 { 1 } else { 9 };
        let sample: Vec<&Dbm> = zones.iter().step_by(stride).collect();
        for (k, a) in zones.iter().enumerate() {
            check_queries(&format!("n{n} #{k}"), a);
        }
        for (k, a) in sample.iter().enumerate() {
            for (l, b) in sample.iter().enumerate().skip(k) {
                check_pair(&format!("n{n} sample #{k}/#{l}"), a, b);
            }
        }
        // Equality is semantic, and hashing agrees with it.
        let set: HashSet<Dbm> = zones.iter().cloned().collect();
        assert_eq!(set.len(), zones.len());
    }
}

// ----- random zones -----

/// A random zone over `n` clocks: usually nonempty, sometimes empty, and
/// sometimes a tightening of `base` (so that inclusions hold).
fn random_zone(rng: &mut SplitMix64, n: usize, base: Option<&Dbm>) -> Dbm {
    match (rng.below(6), base) {
        (0, _) => {
            let cs = random::inconsistent_constraints(rng, n, 2 * n + 1, 20);
            zone(n, &cs)
        }
        (1 | 2, Some(b)) => {
            let k = rng.index(3) + 1;
            let (cs, _) = random::consistent_constraints(rng, n, k, 20);
            let mut z = b.clone();
            for g in &cs {
                z = z.try_constrain(crate::ops::test_support::con(g)).unwrap();
            }
            z
        }
        _ => {
            let count = rng.index(3 * n + 1);
            let (cs, _) = random::consistent_constraints(rng, n, count, 20);
            zone(n, &cs)
        }
    }
}

#[test]
fn random_zones_match_oracle() {
    for seed in random::seeds(100) {
        let mut rng = random::case_rng("relations_random_zones", seed);
        let n = rng.index(6) + 1;
        let a = random_zone(&mut rng, n, None);
        let b = random_zone(&mut rng, n, Some(&a));
        let label = format!("seed {seed} (ORACLE_SEED={seed})");
        check_queries(&format!("{label} a"), &a);
        check_pair(&label, &a, &b);
        // Different dimensions.
        let m = rng.index(7) + 1;
        if m != n {
            let c = random_zone(&mut rng, m, None);
            check_pair(&format!("{label} dims"), &a, &c);
        }
    }
}

#[test]
fn random_zones_hash_consistently() {
    let mut rng = random::case_rng("relations_hash", 0);
    let mut seen: Vec<(Dbm, OracleDbm)> = Vec::new();
    for _ in 0..300 {
        let n = rng.index(3) + 1;
        let z = random_zone(&mut rng, n, None);
        let o = as_oracle(&z);
        for (w, p) in &seen {
            assert_eq!(&z == w, &o == p);
            if &z == w {
                assert_eq!(hash_of(&z), hash_of(w));
            }
        }
        seen.push((z, o));
    }
}

// ----- arithmetic near the supported range -----

#[test]
fn range_limits() {
    let max = i64::from(MAX_CONSTANT);
    let min = i64::from(MIN_CONSTANT);
    let zones = [
        zone(1, &[le(1, 0, max)]),
        zone(1, &[le(0, 1, min)]),
        zone(1, &[lt(0, 1, min + 1), le(1, 0, max)]),
        zone(2, &[le(1, 2, max - 10), le(2, 1, min + 5)]),
        zone(2, &[le(1, 0, max), le(0, 2, min)]),
        zone(2, &[lt(1, 0, max), lt(0, 1, min + 1), le(2, 0, 3)]),
        zone(
            3,
            &[
                le(1, 0, max),
                le(0, 2, min),
                lt(3, 0, max),
                lt(0, 3, min + 1),
            ],
        ),
    ];
    for (k, a) in zones.iter().enumerate() {
        // No query returns Err(Range), even where b + D[j][i] is out of
        // range in either direction.
        check_queries(&format!("limit #{k}"), a);
        for (l, b) in zones.iter().enumerate() {
            if a.variables() == b.variables() {
                check_pair(&format!("limit #{k}/#{l}"), a, b);
            }
        }
    }
    // x ≥ MAX: the contradiction sums MIN + MIN and MAX + MIN are compared
    // exactly (the first is far below the representable range).
    let z = &zones[1];
    let high = Constraint::le(Clock::ZERO, clk(1), MIN_CONSTANT).unwrap();
    let low = Constraint::le(clk(1), Clock::ZERO, MIN_CONSTANT).unwrap();
    assert_eq!(z.intersects_constraint(&high), Ok(true));
    assert_eq!(z.intersects_constraint(&low), Ok(false));
    assert_eq!(z.entails(&high), Ok(true));
    assert_eq!(z.entails(&low), Ok(false));
}

#[test]
fn intersection_beyond_the_premise() {
    // Wide random zones, so that the S§7.1 premise often fails and the
    // range classification decides what is allowed.
    for seed in random::seeds(200) {
        let mut rng = random::case_rng("relations_near_limit", seed);
        let n = rng.index(4) + 1;
        let big = i64::from(MAX_CONSTANT) / 3;
        // Constants up to about MAX_CONSTANT / 3: representable inputs.
        let mut mk = || random::consistent_constraints(&mut rng, n, 2 * n, big).0;
        let (ca, cb) = (mk(), mk());
        let (Ok(a), Ok(b)) = (build(n, &ca), build(n, &cb)) else {
            continue;
        };
        check_pair(&format!("seed {seed} (ORACLE_SEED={seed})"), &a, &b);
    }
}

/// `universe(n) ∧ cs` one constraint at a time, or `Err(Range)`.
fn build(n: usize, cs: &[OracleConstraint]) -> Result<Dbm, Error> {
    let mut z = Dbm::universe(n)?;
    for g in cs {
        z = z.try_constrain(crate::ops::test_support::con(g))?;
    }
    Ok(z)
}

// ----- point membership, independently of the oracle's matrices -----

#[test]
fn inclusion_against_sampled_points() {
    let mut rng = random::case_rng("relations_points", 0);
    for _ in 0..200 {
        let n = rng.index(3) + 1;
        let a = random_zone(&mut rng, n, None);
        let b = random_zone(&mut rng, n, Some(&a));
        let (oa, ob) = (as_oracle(&a), as_oracle(&b));
        let sub = a.is_subset_of(&b).unwrap();
        let both = as_oracle(&a.clone().try_intersect(&b, &mut ws()).unwrap());
        for _ in 0..40 {
            let u: Valuation = random::valuation(&mut rng, n, 25, 4);
            let (ia, ib) = (oa.contains(&u), ob.contains(&u));
            assert!(!sub || !ia || ib, "a point of a outside b, yet a ⊆ b");
            assert_eq!(both.contains(&u), ia && ib, "intersection membership");
        }
    }
}
