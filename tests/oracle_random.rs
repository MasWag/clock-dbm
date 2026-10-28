//! Seeded randomized self-tests of the exact reference oracle.
//!
//! The closure-based operations are cross-checked against closure-free
//! semantics (direct membership of exact rational points and the `∃t` set
//! equations in `support::oracle::valuation`). Case counts are small by
//! default; `ORACLE_CASES=<n>` scales them up and `ORACLE_SEED=<seed>` replays
//! a single reported case.

mod support;

use num_bigint::BigInt;
use num_rational::BigRational;
use support::oracle::compare::{ObservedZone, check_public_invariant};
use support::oracle::random::{self, SplitMix64, check_scenarios, seeds, shrink};
use support::oracle::scenario::{Op, Scenario, Start, le};
use support::oracle::valuation::{in_free_image, in_future_image, in_past_image, in_reset_image};
use support::oracle::{ExactBound, OracleConstraint, OracleDbm, Valuation};

const MAX_VARIABLES: usize = 4;
const MAX_OPS: usize = 6;

fn gen_scenario(rng: &mut SplitMix64) -> Scenario {
    random::scenario(rng, MAX_VARIABLES, MAX_OPS)
}

fn trace(s: &Scenario) -> Result<Vec<OracleDbm>, String> {
    s.run_oracle()
        .map_err(|e| format!("unexpected argument error {e:?}"))
}

fn ratio(p: i64, q: i64) -> BigRational {
    BigRational::new(p.into(), q.into())
}

/// Sample points: random grid points with denominator `2(n+1)`, the given
/// anchors, and every anchor moved by ±1/(2(n+1)) in one coordinate.
fn sample_points(rng: &mut SplitMix64, n: usize, anchors: &[Valuation]) -> Vec<Valuation> {
    let den = 2 * (n as i64 + 1);
    let mut points: Vec<Valuation> = (0..24)
        .map(|_| random::valuation(rng, n, 10, den))
        .collect();
    for a in anchors {
        points.push(a.clone());
        for x in 1..=n {
            for delta in [ratio(1, den), ratio(-1, den)] {
                let v = a.value(x) + delta;
                if v >= BigRational::from_integer(0.into()) {
                    points.push(a.with_value(x, v));
                }
            }
        }
    }
    points
}

fn invariant(z: &OracleDbm) -> Result<(), String> {
    check_public_invariant(&ObservedZone::from_oracle(z), None)
}

/// Anchors near the image of `op` applied to `prev`.
fn image_anchors(rng: &mut SplitMix64, prev: &OracleDbm, op: &Op) -> Vec<Valuation> {
    let Some(w) = prev.witness() else {
        return Vec::new();
    };
    let t = ratio(rng.range(0, 20), 4);
    let mut out = vec![w.clone(), w.shifted(&t)];
    match op {
        Op::Reset { x, value } => {
            out.push(w.with_value(*x, BigRational::from_integer((*value).into())))
        }
        Op::ResetZero(x) => out.push(w.with_value(*x, ratio(0, 1))),
        Op::Free(x) => out.push(w.with_value(*x, t)),
        Op::Past => {
            // The earliest point of w's trajectory: its smallest clock is 0.
            if let Some(min) = w.values().iter().skip(1).min() {
                out.push(w.shifted(&-min.clone()));
            }
        }
        _ => {}
    }
    out
}

/// Whether `u` is in the image of `op` on `prev`, decided without closure.
/// `None` for ExtraM, which is specified only as `close(norm(..))`.
fn expected_membership(prev: &OracleDbm, op: &Op, u: &Valuation) -> Option<bool> {
    let n = prev.variables();
    Some(match op {
        Op::Constrain(g) => prev.contains(u) && u.satisfies(g),
        Op::ConstrainAll(cs) | Op::Intersect(cs) => prev.contains(u) && u.satisfies_all(cs),
        Op::Future => in_future_image(prev, u),
        Op::Past => in_past_image(prev, u),
        Op::Reset { x, value } => in_reset_image(prev, *x, &BigInt::from(*value), u),
        Op::ResetZero(x) => in_reset_image(prev, *x, &BigInt::from(0), u),
        Op::Free(x) => in_free_image(prev, *x, u),
        Op::ExtrapolateMax(m) => {
            assert_eq!(m.len(), n);
            return None;
        }
    })
}

#[test]
fn operations_satisfy_their_set_equations() {
    check_scenarios(
        "operations_satisfy_their_set_equations",
        300,
        gen_scenario,
        |s, rng| {
            let trace = trace(s)?;
            let n = s.variables;
            invariant(&trace[0])?;
            if let Start::Constraints(cs) = &s.start {
                let anchors: Vec<Valuation> = trace[0].witness().into_iter().collect();
                if let Some(w) = anchors.first()
                    && !w.satisfies_all(cs)
                {
                    return Err(format!("start witness {w} violates the raw constraints"));
                }
                for u in sample_points(rng, n, &anchors) {
                    if trace[0].contains(&u) != u.satisfies_all(cs) {
                        return Err(format!("start zone disagrees with its constraints at {u}"));
                    }
                }
            }
            for (k, op) in s.ops.iter().enumerate() {
                let (prev, next) = (&trace[k], &trace[k + 1]);
                invariant(next).map_err(|e| format!("after {op}: {e}"))?;
                let mut anchors = image_anchors(rng, prev, op);
                anchors.extend(next.witness());
                for u in sample_points(rng, n, &anchors) {
                    let got = next.contains(&u);
                    let ok = match expected_membership(prev, op, &u) {
                        Some(expected) => got == expected,
                        // ExtraM is extensive.
                        None => !prev.contains(&u) || got,
                    };
                    if !ok {
                        return Err(format!(
                            "step {}: {op} gives membership {got} at {u}\nbefore: {prev}after: {next}",
                            k + 1
                        ));
                    }
                }
            }
            Ok(())
        },
    );
}

/// Every grid point `k/(2(n+1))` in `[0, hi]ⁿ`.
fn grid(n: usize, hi: i64) -> Vec<Valuation> {
    let den = 2 * (n as i64 + 1);
    let mut points = vec![Vec::new()];
    for _ in 0..n {
        points = points
            .into_iter()
            .flat_map(|p: Vec<i64>| {
                (0..=hi * den).map(move |k| {
                    let mut p = p.clone();
                    p.push(k);
                    p
                })
            })
            .collect();
    }
    points
        .into_iter()
        .map(|p| Valuation::new(p.into_iter().map(|k| ratio(k, den)).collect()))
        .collect()
}

#[test]
fn emptiness_decisions_are_witnessed() {
    const MAX_C: i64 = 3;
    check_scenarios(
        "emptiness_decisions_are_witnessed",
        200,
        |rng| {
            let variables = rng.index(3);
            let count = rng.index(6) + 1;
            let cs = (0..count)
                .map(|_| random::constraint(rng, variables, MAX_C))
                .collect();
            Scenario {
                variables,
                start: Start::Constraints(cs),
                ops: vec![],
            }
        },
        |s, _| {
            let Start::Constraints(cs) = &s.start else {
                unreachable!()
            };
            let z = &trace(s)?[0];
            match z.witness() {
                Some(w) if !w.satisfies_all(cs) => {
                    Err(format!("witness {w} violates the constraints"))
                }
                Some(_) => Ok(()),
                None => {
                    // Points of a nonempty zone with constants ≤ MAX_C can be
                    // found below n·MAX_C + 1; search the grid there.
                    let hi = s.variables as i64 * MAX_C + 1;
                    match grid(s.variables, hi)
                        .into_iter()
                        .find(|u| u.satisfies_all(cs))
                    {
                        Some(u) => Err(format!(
                            "oracle says empty, but {u} satisfies all constraints"
                        )),
                        None => Ok(()),
                    }
                }
            }
        },
    );
}

#[test]
fn generators_produce_what_they_promise() {
    for seed in seeds(200) {
        let mut rng = random::case_rng("generators", seed);
        let n = rng.index(MAX_VARIABLES + 1);
        let count = rng.index(8);
        let (cs, hidden) = random::consistent_constraints(&mut rng, n, count, 6);
        let z = OracleDbm::from_constraints(n, &cs).unwrap();
        assert!(z.contains(&hidden), "seed {seed}: {hidden} not in\n{z}");
        let bad = random::inconsistent_constraints(&mut rng, n, count, 6);
        assert!(
            OracleDbm::from_constraints(n, &bad).unwrap().is_empty(),
            "seed {seed}: {bad:?}"
        );
        // Same seed, same stream.
        let again = random::scenario(&mut random::case_rng("replay", seed), 4, 6);
        assert_eq!(
            again,
            random::scenario(&mut random::case_rng("replay", seed), 4, 6)
        );
    }
}

#[test]
fn inclusion_and_equality_agree_with_points() {
    check_scenarios(
        "inclusion_and_equality_agree_with_points",
        200,
        gen_scenario,
        |s, rng| {
            let trace = trace(s)?;
            for a in &trace {
                for b in &trace {
                    let subset = a.is_subset_of(b).map_err(|e| format!("{e:?}"))?;
                    if subset {
                        let anchors: Vec<Valuation> = a.witness().into_iter().collect();
                        for u in sample_points(rng, s.variables, &anchors) {
                            if a.contains(&u) && !b.contains(&u) {
                                return Err(format!("claimed subset, but {u} separates\n{a}{b}"));
                            }
                        }
                    } else {
                        match a.subset_counterexample(b) {
                            Some(u) if a.contains(&u) && !b.contains(&u) => {}
                            other => {
                                return Err(format!("no valid counterexample ({other:?})\n{a}{b}"));
                            }
                        }
                    }
                    let both = subset && b.is_subset_of(a).unwrap();
                    if (a == b) != both {
                        return Err(format!("== disagrees with mutual inclusion\n{a}{b}"));
                    }
                }
            }
            Ok(())
        },
    );
}

/// The bound just tighter than `b`, for finite `b`.
fn predecessor(b: &ExactBound) -> ExactBound {
    let c = b.constant().expect("finite").clone();
    if b.is_strict() {
        ExactBound::le(c - 1)
    } else {
        ExactBound::lt(c)
    }
}

#[test]
fn queries_agree_with_witnesses() {
    check_scenarios(
        "queries_agree_with_witnesses",
        200,
        gen_scenario,
        |s, rng| {
            let n = s.variables;
            for z in trace(s)? {
                if z.is_empty() {
                    continue;
                }
                for _ in 0..6 {
                    let g = random::constraint(rng, n, 6);
                    let entails = z.entails(&g).unwrap();
                    match g.negated() {
                        None => {
                            if !entails {
                                return Err(format!("∞ guard {g} not entailed"));
                            }
                        }
                        Some(neg) => match z.constrain(&neg).unwrap().witness() {
                            None if entails => {}
                            Some(w) if !entails && z.contains(&w) && !w.satisfies(&g) => {}
                            other => {
                                return Err(format!(
                                    "entails({g}) = {entails}, but {other:?}\n{z}"
                                ));
                            }
                        },
                    }
                    let intersects = z.intersects_constraint(&g).unwrap();
                    match z.constrain(&g).unwrap().witness() {
                        None if !intersects => {}
                        Some(w) if intersects && z.contains(&w) && w.satisfies(&g) => {}
                        other => {
                            return Err(format!(
                                "intersects({g}) = {intersects}, but {other:?}\n{z}"
                            ));
                        }
                    }
                    // difference_bound is entailed and tight.
                    let b = z.difference_bound(g.i, g.j).unwrap().expect("nonempty");
                    let tighter = if b.is_infinite() {
                        ExactBound::le(z.max_abs_constant() * 2 + 1)
                    } else {
                        predecessor(&b)
                    };
                    if !z
                        .entails(&OracleConstraint::new(g.i, g.j, b.clone()))
                        .unwrap()
                        || z.entails(&OracleConstraint::new(g.i, g.j, tighter))
                            .unwrap()
                    {
                        return Err(format!(
                            "difference_bound({}, {}) = {b} is not tight\n{z}",
                            g.i, g.j
                        ));
                    }
                }
            }
            Ok(())
        },
    );
}

#[test]
fn batches_are_order_and_multiplicity_independent() {
    check_scenarios(
        "batches_are_order_and_multiplicity_independent",
        200,
        gen_scenario,
        |s, rng| {
            let n = s.variables;
            let z = trace(s)?.pop().unwrap();
            let count = rng.index(5) + 1;
            let cs: Vec<OracleConstraint> =
                (0..count).map(|_| random::constraint(rng, n, 6)).collect();
            let batch = z.constrain_all(&cs).unwrap();
            let mut shuffled = cs.clone();
            shuffled.push(cs[rng.index(cs.len())].clone());
            for k in (1..shuffled.len()).rev() {
                let j = rng.index(k + 1);
                shuffled.swap(k, j);
            }
            let folded = cs
                .iter()
                .fold(z.clone(), |acc, g| acc.constrain(g).unwrap());
            let via_intersect = z
                .intersect(&OracleDbm::from_constraints(n, &cs).unwrap())
                .unwrap();
            if z.constrain_all(&shuffled).unwrap() != batch
                || folded != batch
                || via_intersect != batch
            {
                return Err(format!("batch {cs:?} depends on order or grouping\n{z}"));
            }
            Ok(())
        },
    );
}

#[test]
fn algebraic_laws() {
    check_scenarios("algebraic_laws", 200, gen_scenario, |s, rng| {
        let n = s.variables;
        let trace = trace(s)?;
        let other = trace[rng.index(trace.len())].clone();
        for z in &trace {
            let up = z.future();
            let mut laws = vec![
                ("future idempotent", up.future() == up),
                ("D ⊆ D↑", z.is_subset_of(&up).unwrap()),
                (
                    "intersect commutative",
                    z.intersect(&other).unwrap() == other.intersect(z).unwrap(),
                ),
                ("intersect idempotent", z.intersect(z).unwrap() == *z),
            ];
            let ceilings: Vec<BigInt> = (0..n).map(|_| BigInt::from(rng.range(0, 6))).collect();
            laws.push((
                "ExtraM extensive",
                z.is_subset_of(&z.extrapolate_max(&ceilings).unwrap())
                    .unwrap(),
            ));
            if n > 0 {
                let x = rng.index(n) + 1;
                let c = rng.range(0, 6);
                let free = z.free(x).unwrap();
                laws.push(("free idempotent", free.free(x).unwrap() == free));
                laws.push(("D ⊆ free(D)", z.is_subset_of(&free).unwrap()));
                laws.push((
                    "free ∘ reset = free",
                    z.reset(x, c).unwrap().free(x).unwrap() == free,
                ));
                laws.push((
                    "reset ⊆ free",
                    z.reset(x, c).unwrap().is_subset_of(&free).unwrap(),
                ));
            }
            if let Some((name, _)) = laws.iter().find(|(_, holds)| !holds) {
                return Err(format!("law `{name}` fails on\n{z}"));
            }
        }
        Ok(())
    });
}

#[test]
fn shrinker_minimizes_failing_scenarios() {
    let s = Scenario {
        variables: 2,
        start: Start::Constraints(vec![le(1, 0, 5), le(2, 1, -2)]),
        ops: vec![
            Op::Constrain(le(1, 0, 7)),
            Op::Future,
            Op::Free(1),
            Op::ConstrainAll(vec![le(2, 0, 9), le(0, 1, -4)]),
        ],
    };
    let has_future = |s: &Scenario| s.ops.contains(&Op::Future);
    assert_eq!(
        shrink(&s, has_future),
        Scenario {
            variables: 2,
            start: Start::Universe,
            ops: vec![Op::Future],
        }
    );
    let has_positive_guard = |s: &Scenario| {
        s.ops.iter().any(|op| match op {
            Op::Constrain(g) => g.bound.constant().is_some_and(|c| *c >= BigInt::from(1)),
            _ => false,
        })
    };
    assert_eq!(
        shrink(&s, has_positive_guard).ops,
        vec![Op::Constrain(le(1, 0, 1))]
    );
}

#[test]
fn failures_report_seed_and_shrunk_scenario() {
    let result = std::panic::catch_unwind(|| {
        check_scenarios("always_fails", 1, gen_scenario, |_, _| {
            Err("boom".to_string())
        });
    });
    let payload = result.expect_err("the property fails");
    let message = payload
        .downcast_ref::<String>()
        .expect("formatted panic message");
    assert!(message.contains("ORACLE_SEED="), "{message}");
    assert!(message.contains("shrunk scenario"), "{message}");
    // Everything shrinks away when the property always fails.
    assert!(
        message.contains("start: Start::Universe")
            || message.contains("start: Start::Zero")
            || message.contains("start: Start::Empty"),
        "{message}"
    );
    assert!(message.contains("ops: vec![\n    ],"), "{message}");
}
