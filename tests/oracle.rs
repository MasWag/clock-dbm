//! Deterministic regression tests of the exact reference oracle
//! (`tests/support/oracle/`), including the worked examples of
//! the library's regression fixtures.

mod support;

use num_bigint::BigInt;
use support::oracle::compare::{
    ObservedError, ObservedZone, PRODUCTION_MAX_CONSTANT, RangeExpectation, check_outcome,
    check_public_invariant, classify_range, compare_exact, compare_semantic,
};
use support::oracle::scenario::{Op, le, lt};
use support::oracle::{
    ExactBound, OracleConstraint, OracleDbm, OracleError, Valuation, fixtures, parse_matrix,
};

/// Asserts that `z` is nonempty with exactly the matrix `rows`, and that
/// `rows` is itself canonical (so the expectation cannot be vacuous).
#[track_caller]
fn assert_matrix(z: &OracleDbm, rows: &[&str]) {
    let expected = parse_matrix(rows);
    let closed = OracleDbm::from_matrix(expected.len() - 1, expected.clone());
    assert_eq!(
        closed.matrix(),
        Some(&expected),
        "expected matrix is not canonical"
    );
    assert_eq!(z.matrix(), Some(&expected), "got:\n{z}");
}

fn ok(r: Result<OracleDbm, OracleError>) -> OracleDbm {
    r.expect("no argument error")
}

fn final_zone(name: &str) -> OracleDbm {
    fixtures::named(name)
        .scenario
        .final_zone()
        .expect("valid fixture")
}

// ----- bounds -----

#[test]
fn bound_order_is_tightness() {
    let chain = [
        ExactBound::lt(-1),
        ExactBound::le(-1),
        ExactBound::lt(0),
        ExactBound::le(0),
        ExactBound::lt(1),
        ExactBound::le(1),
        ExactBound::le(BigInt::from(1) << 200),
        ExactBound::Infinity,
    ];
    for (a, b) in chain.iter().zip(&chain[1..]) {
        assert!(a < b, "{a} < {b}");
    }
}

#[test]
fn bound_addition_and_negation() {
    assert_eq!(
        ExactBound::le(3).add(&ExactBound::le(-5)),
        ExactBound::le(-2)
    );
    assert_eq!(
        ExactBound::le(3).add(&ExactBound::lt(-5)),
        ExactBound::lt(-2)
    );
    assert_eq!(
        ExactBound::lt(1).add(&ExactBound::le(-1)),
        ExactBound::lt(0)
    );
    assert_eq!(
        ExactBound::lt(1).add(&ExactBound::Infinity),
        ExactBound::Infinity
    );
    assert_eq!(ExactBound::le(3).negate(), Some(ExactBound::lt(-3)));
    assert_eq!(ExactBound::lt(3).negate(), Some(ExactBound::le(-3)));
    assert_eq!(ExactBound::Infinity.negate(), None);
    // No overflow: constants are arbitrary precision.
    let big = ExactBound::le(BigInt::from(i64::MAX));
    assert_eq!(
        big.add(&big).constant(),
        Some(&(BigInt::from(i64::MAX) * 2))
    );
}

#[test]
fn bound_parse_display_round_trip() {
    for t in ["<=0", "<-3", "<=12345678901234567890", "inf"] {
        assert_eq!(ExactBound::parse(t).unwrap().to_string(), t);
    }
    assert!(ExactBound::parse("=3").is_err());
    assert_eq!(ExactBound::from_parts(Some(2), true), ExactBound::lt(2));
    assert_eq!(ExactBound::from_parts(Some(2), false), ExactBound::le(2));
    assert_eq!(ExactBound::from_parts(None, true), ExactBound::Infinity);
}

// ----- constructors and closure -----

#[test]
fn constructors_in_every_fixture_dimension() {
    for n in fixtures::DIMENSIONS {
        let d = n + 1;
        let zero = OracleDbm::zero(n);
        let universe = OracleDbm::universe(n);
        let empty = OracleDbm::empty(n);
        assert_eq!(zero.matrix(), Some(&vec![vec![ExactBound::le(0); d]; d]));
        for i in 0..d {
            for j in 0..d {
                let expected = if i == 0 || i == j {
                    ExactBound::le(0)
                } else {
                    ExactBound::Infinity
                };
                assert_eq!(universe.entry(i, j), Some(&expected));
            }
        }
        assert!(empty.is_empty() && empty.dimension() == d);
        assert!(zero.is_subset_of(&universe).unwrap());
        assert_eq!(n == 0, universe.is_subset_of(&zero).unwrap());
        assert_ne!(empty, OracleDbm::empty(n + 1), "∅_d remembers d");
    }
    assert_eq!(OracleDbm::zero(0), OracleDbm::universe(0));
    assert_ne!(OracleDbm::empty(0), OracleDbm::zero(0));
}

#[test]
fn from_matrix_imposes_nonnegativity_and_diagonal() {
    // n = 0: the one-entry matrix [∞] denotes the one-point zone.
    assert_eq!(OracleDbm::parse(&["inf"]), OracleDbm::zero(0));
    // Only x ≤ 3 is given; x ≥ 0 comes from γ.
    let z = OracleDbm::parse(&["inf inf", "<=3 inf"]);
    assert_matrix(&z, &["<=0 <=0", "<=3 <=0"]);
    // x ≤ −1 contradicts nonnegativity.
    assert!(OracleDbm::parse(&["inf inf", "<=-1 inf"]).is_empty());
}

// ----- S§8.1 strict and non-strict, satisfiable but not entailed -----

#[test]
fn worked_8_1_strict_and_non_strict() {
    let a = final_zone("worked_8_1_a");
    assert_matrix(&a, &["<=0 <=0 <=0", "<=3 <=0 <1", "inf inf <=0"]);

    assert!(a.entails(&le(1, 0, 3)).unwrap());
    assert!(a.entails(&le(1, 2, 1)).unwrap(), "Lt 1 ≼ Le 1");
    assert_eq!(
        a.difference_bound(2, 1).unwrap(),
        Some(ExactBound::Infinity)
    );
    // x − y ≥ 1 is (y, x, Le −1): A[x][y] + Le −1 = Lt 0.
    assert!(!a.intersects_constraint(&le(2, 1, -1)).unwrap());

    // The guard x < 3 is satisfiable but not entailed.
    let guard = lt(1, 0, 3);
    assert!(!a.entails(&guard).unwrap());
    assert!(a.intersects_constraint(&guard).unwrap());
    let counterexample = Valuation::from_ratios(&[(3, 1), (5, 2)]);
    assert!(a.contains(&counterexample) && !counterexample.satisfies(&guard));
    let inside = Valuation::from_integers(&[2, 2]);
    assert!(a.contains(&inside) && inside.satisfies(&guard));
    // The oracle finds such points itself.
    let w = ok(a.constrain(&guard.negated().unwrap()))
        .witness()
        .unwrap();
    assert!(a.contains(&w) && !w.satisfies(&guard), "{w}");
    let w = ok(a.constrain(&guard)).witness().unwrap();
    assert!(a.contains(&w) && w.satisfies(&guard), "{w}");

    // B = A ∧ x ≥ 3: strictness propagates to y > 2.
    let b = final_zone("worked_8_1_b");
    assert_matrix(&b, &["<=0 <=-3 <-2", "<=3 <=0 <1", "inf inf <=0"]);
    assert_eq!(b, ok(a.constrain(&le(0, 1, -3))));
}

// ----- S§8.2 strict-zero contradictions -----

#[test]
fn worked_8_2_strict_zero_contradictions() {
    // universe(1) ∧ x < 0: D[x][x] ≼ Lt 0 + Le 0 = Lt 0, so ∅_2 (not an error).
    let z = final_zone("strict_zero_contradiction");
    assert!(z.is_empty());
    assert_eq!(z, OracleDbm::empty(1));
    assert_ne!(z, OracleDbm::empty(2));

    // x ≤ 0 is the point {x = 0}; adding x > 0 empties it.
    assert_matrix(&final_zone("weak_zero_point"), &["<=0 <=0", "<=0 <=0"]);
    assert!(final_zone("weak_zero_point_then_strict").is_empty());

    // B ∧ y ≤ 2: Lt (−2) + Le 2 = Lt 0, so ∅_3 ...
    assert_eq!(
        final_zone("worked_8_2_strict_propagation_contradiction"),
        OracleDbm::empty(2)
    );
    // ... but with x − y ≤ 1 instead, the sum is Le 0 and {x = 3, y = 2} remains.
    let point = final_zone("worked_8_2_weak_variant_point");
    assert_matrix(&point, &["<=0 <=-3 <=-2", "<=3 <=0 <=1", "<=2 <=-1 <=0"]);
    assert!(point.contains(&Valuation::from_integers(&[3, 2])));
}

// ----- S§8.3 empty-zone queries -----

#[test]
fn worked_8_3_empty_zone_queries() {
    let e = OracleDbm::empty(2);
    let universe = OracleDbm::universe(2);
    assert!(e.is_empty());
    assert!(e.entails(&lt(1, 0, 0)).unwrap());
    assert!(!e.intersects_constraint(&le(1, 0, 5)).unwrap());
    assert_eq!(e.difference_bound(1, 2).unwrap(), None);
    assert!(e.is_subset_of(&universe).unwrap());
    assert!(!universe.is_subset_of(&e).unwrap());
    assert_eq!(e, OracleDbm::empty(2));
    assert_ne!(e, OracleDbm::empty(3));
    assert_eq!(
        e.is_subset_of(&OracleDbm::empty(3)),
        Err(OracleError::DimensionMismatch {
            expected: 2,
            found: 3
        })
    );
    assert_eq!(e.future(), e);
    assert_eq!(e.reset(1, 2), Ok(e.clone()));
    assert_eq!(e.free(1), Ok(e.clone()));
    let m = [BigInt::from(1), BigInt::from(1)];
    assert_eq!(e.extrapolate_max(&m), Ok(e.clone()));
    // Argument checks precede emptiness.
    assert_eq!(
        e.entails(&le(3, 0, 1)),
        Err(OracleError::ClockOutOfRange {
            clock: 3,
            variables: 2
        })
    );
}

#[test]
fn argument_errors() {
    let z = OracleDbm::universe(2);
    let e = OracleDbm::empty(2);
    for d in [&z, &e] {
        assert_eq!(
            d.constrain_all(&[le(1, 0, 1), le(0, 3, 0)]),
            Err(OracleError::ClockOutOfRange {
                clock: 3,
                variables: 2
            })
        );
        assert_eq!(
            d.reset(1, -1),
            Err(OracleError::NegativeConstant {
                value: BigInt::from(-1)
            })
        );
        assert_eq!(d.reset(0, 1), Err(OracleError::ReferenceClock));
        assert_eq!(
            d.free(3),
            Err(OracleError::ClockOutOfRange {
                clock: 3,
                variables: 2
            })
        );
        assert_eq!(
            d.extrapolate_max(&[BigInt::from(1)]),
            Err(OracleError::DimensionMismatch {
                expected: 2,
                found: 1
            })
        );
        assert_eq!(
            d.extrapolate_max(&[BigInt::from(1), BigInt::from(-1)]),
            Err(OracleError::InvalidMaxBounds {
                variable: 2,
                value: BigInt::from(-1)
            })
        );
        assert_eq!(
            d.intersect(&OracleDbm::universe(1)),
            Err(OracleError::DimensionMismatch {
                expected: 2,
                found: 1
            })
        );
        assert_eq!(
            d.difference_bound(0, 4),
            Err(OracleError::ClockOutOfRange {
                clock: 4,
                variables: 2
            })
        );
    }
}

// ----- S§8.4 reset vs free -----

#[test]
fn worked_8_4_reset_versus_free() {
    assert_matrix(
        &final_zone("worked_8_4_point"),
        &["<=0 <=-1 <=-1", "<=1 <=0 <=0", "<=1 <=0 <=0"],
    );
    assert_matrix(
        &final_zone("worked_8_4_reset_zero"),
        &["<=0 <=0 <=-1", "<=0 <=0 <=-1", "<=1 <=1 <=0"],
    );
    assert_matrix(
        &final_zone("worked_8_4_free"),
        &["<=0 <=0 <=-1", "inf <=0 inf", "<=1 <=1 <=0"],
    );
    assert_matrix(
        &final_zone("worked_8_4_reset_two"),
        &["<=0 <=-2 <=-1", "<=2 <=0 <=1", "<=1 <=-1 <=0"],
    );
    let future = final_zone("worked_8_4_reset_then_future");
    assert_matrix(&future, &["<=0 <=0 <=-1", "inf <=0 <=-1", "inf <=1 <=0"]);
    assert_ne!(future, final_zone("worked_8_4_free"));
}

// ----- S§8.5 ExtraM -----

#[test]
fn worked_8_5_extra_m() {
    assert_matrix(
        &final_zone("worked_8_5_extra_m_lower"),
        &["<=0 <-3 <-3", "inf <=0 <=0", "inf <=0 <=0"],
    );
    let h = final_zone("worked_8_5_extra_m_diagonal");
    assert_eq!(h, ok(OracleDbm::from_constraints(2, &[le(2, 0, 1)])));
    assert_matrix(&h, &["<=0 <=0 <=0", "inf <=0 inf", "<=1 <=1 <=0"]);
}

// ----- more regressions -----

#[test]
fn negative_bounds_and_diagonal_guards() {
    // x ≥ 3, y > 1, y − x ≥ 1  ⇒  y ≥ 4.
    let z = final_zone("negative_bounds_diagonal_guard");
    assert_matrix(&z, &["<=0 <=-3 <=-4", "inf <=0 <=-1", "inf inf <=0"]);
    assert!(z.contains(&Valuation::from_integers(&[3, 4])));
    assert!(!z.contains(&Valuation::from_ratios(&[(3, 1), (7, 2)])));
    assert!(final_zone("batch_contradiction").is_empty());
    assert_eq!(final_zone("self_constraints"), OracleDbm::universe(2));
}

#[test]
fn dimension_eight_chains() {
    let point = final_zone("dim8_weak_chain_single_point");
    let only = Valuation::from_integers(&[0, 1, 2, 3, 4, 5, 6, 7]);
    assert!(point.contains(&only));
    assert_eq!(point.witness(), Some(only));
    assert_eq!(
        point.difference_bound(8, 1).unwrap(),
        Some(ExactBound::le(7))
    );
    assert!(final_zone("dim8_weak_chain_strict_contradiction").is_empty());

    let strict = final_zone("dim8_strict_chain");
    // x8 − x1 > 7 accumulates strictness along the chain.
    assert_eq!(
        strict.difference_bound(1, 8).unwrap(),
        Some(ExactBound::lt(-7))
    );
    assert_eq!(
        strict.difference_bound(1, 0).unwrap(),
        Some(ExactBound::lt(1))
    );
    assert!(final_zone("dim8_strict_chain_contradiction").is_empty());
}

#[test]
fn every_fixture_runs_and_matches_its_emptiness() {
    for f in fixtures::all() {
        let trace = f
            .scenario
            .run_oracle()
            .unwrap_or_else(|e| panic!("{}: {e:?}", f.name));
        for (k, z) in trace.iter().enumerate() {
            check_public_invariant(&ObservedZone::from_oracle(z), None)
                .unwrap_or_else(|e| panic!("{} step {k}: {e}", f.name));
        }
        let last = trace.last().unwrap();
        assert_eq!(
            last.is_empty(),
            f.final_empty,
            "{}:\n{}\n{last}",
            f.name,
            f.scenario
        );
        assert_eq!(last.variables(), f.scenario.variables);
        if let Some(w) = last.witness() {
            assert!(last.contains(&w), "{}: witness {w}", f.name);
        }
    }
}

// ----- comparison helpers -----

#[test]
fn compare_exact_reports_differences() {
    let a = final_zone("worked_8_1_a");
    let observed = ObservedZone::from_oracle(&a);
    assert_eq!(compare_exact(&observed, &a), Ok(()));

    let mut wrong = observed.clone();
    wrong.entries.as_mut().unwrap()[5] = ExactBound::le(1); // (1, 2): Lt 1 → Le 1
    let err = compare_exact(&wrong, &a).unwrap_err().to_string();
    assert!(err.contains("(1,2): observed <=1, oracle <1"), "{err}");

    let err = compare_exact(&ObservedZone::empty(2), &a)
        .unwrap_err()
        .to_string();
    assert!(err.contains("emptiness mismatch"), "{err}");
    let err = compare_exact(&ObservedZone::empty(3), &OracleDbm::empty(2))
        .unwrap_err()
        .to_string();
    assert!(err.contains("dimension mismatch"), "{err}");
    assert_eq!(
        compare_exact(&ObservedZone::empty(2), &OracleDbm::empty(2)),
        Ok(())
    );

    // A non-canonical observation of the same zone fails exactly but passes
    // semantically.
    let raw = ObservedZone::from_entries(
        2,
        parse_matrix(&["inf inf inf", "<=3 inf <1", "inf inf inf"])
            .into_iter()
            .flatten()
            .collect(),
    );
    assert!(compare_exact(&raw, &a).is_err());
    assert_eq!(compare_semantic(&raw, &a), Ok(()));
}

#[test]
fn public_invariant_checker_rejects_each_violation() {
    let max = BigInt::from(PRODUCTION_MAX_CONSTANT);
    let check = |rows: &[&str]| {
        let m = parse_matrix(rows);
        let n = m.len() - 1;
        check_public_invariant(
            &ObservedZone::from_entries(n, m.into_iter().flatten().collect()),
            Some(&max),
        )
    };
    assert_eq!(check(&["<=0 <=0", "<=3 <=0"]), Ok(()));
    assert!(
        check(&["<=0 <=0", "<=536870912 <=0"])
            .unwrap_err()
            .starts_with("C1")
    );
    assert!(
        check(&["<=0 <=0", "<=3 <=1"])
            .unwrap_err()
            .starts_with("C2")
    );
    assert!(
        check(&["<=0 <=1", "<=3 <=0"])
            .unwrap_err()
            .starts_with("C3")
    );
    assert!(
        check(&["<=0 <=0 <=0", "<=3 <=0 inf", "<=1 <=1 <=0"])
            .unwrap_err()
            .starts_with("C4")
    );
}

#[test]
fn range_classification() {
    let max = PRODUCTION_MAX_CONSTANT;
    let small = final_zone("worked_8_1_a");
    assert_eq!(
        classify_range(2, &BigInt::from(3), &small, max),
        RangeExpectation::MustSucceed
    );

    let f = fixtures::named("range_large_representable");
    let trace = f.scenario.run_oracle().unwrap();
    let bound = f.scenario.ops[0].input_bound(&trace[0]);
    assert_eq!(bound, BigInt::from(max));
    assert_eq!(
        classify_range(2, &bound, &trace[1], max),
        RangeExpectation::EitherAllowed
    );

    let f = fixtures::named("range_unrepresentable_result");
    let trace = f.scenario.run_oracle().unwrap();
    // y ≥ x + MAX ≥ 2·MAX: exact, but not representable in production.
    assert_eq!(trace[2].entry(0, 2), Some(&ExactBound::le(-2 * max)));
    let bound = f.scenario.ops[1].input_bound(&trace[1]);
    assert_eq!(
        classify_range(2, &bound, &trace[2], max),
        RangeExpectation::MustFailRange
    );
}

#[test]
fn outcome_checks() {
    let max = PRODUCTION_MAX_CONSTANT;
    let a = final_zone("worked_8_1_a");
    let obs = ObservedZone::from_oracle(&a);
    let succeed = RangeExpectation::MustSucceed;
    assert_eq!(
        check_outcome(&Ok(obs.clone()), &Ok(a.clone()), succeed, max),
        Ok(())
    );
    assert!(check_outcome(&Err(ObservedError::Range), &Ok(a.clone()), succeed, max).is_err());
    assert_eq!(
        check_outcome(
            &Err(ObservedError::Range),
            &Ok(a.clone()),
            RangeExpectation::EitherAllowed,
            max
        ),
        Ok(())
    );
    assert!(
        check_outcome(
            &Ok(obs.clone()),
            &Ok(a.clone()),
            RangeExpectation::MustFailRange,
            max
        )
        .is_err()
    );
    let arg = OracleError::ReferenceClock;
    assert_eq!(
        check_outcome(
            &Err(ObservedError::Argument(arg.clone())),
            &Err(arg.clone()),
            succeed,
            max
        ),
        Ok(())
    );
    assert!(check_outcome(&Ok(obs), &Err(arg), succeed, max).is_err());
}

#[test]
fn scenarios_print_as_rust() {
    let f = fixtures::named("worked_8_4_reset_two");
    let text = f.scenario.to_string();
    assert!(text.contains("Op::Constrain(le(1, 0, 1))"), "{text}");
    assert!(text.contains("Op::Reset { x: 1, value: 2 }"), "{text}");
    assert_eq!(
        Op::Intersect(vec![
            lt(1, 2, -3),
            OracleConstraint::new(0, 1, ExactBound::Infinity)
        ])
        .to_string(),
        "Op::Intersect(vec![lt(1, 2, -3), inf(0, 1)])"
    );
}
