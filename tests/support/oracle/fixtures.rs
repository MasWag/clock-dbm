//! Named deterministic scenarios for regression and differential tests.
//!
//! Each fixture records whether its final zone is empty, as worked out by
//! hand; `tests/oracle.rs` checks the oracle against that, and production
//! tests can replay every step.

use super::compare::PRODUCTION_MAX_CONSTANT;
use super::scenario::{Op, Scenario, Start, le, lt};

/// A named scenario with its hand-computed final emptiness.
#[derive(Clone, Debug)]
pub struct Fixture {
    /// Unique name.
    pub name: String,
    /// The steps.
    pub scenario: Scenario,
    /// Whether the final zone is empty.
    pub final_empty: bool,
}

fn fixture(name: &str, variables: usize, start: Start, ops: Vec<Op>, final_empty: bool) -> Fixture {
    Fixture {
        name: name.to_string(),
        scenario: Scenario {
            variables,
            start,
            ops,
        },
        final_empty,
    }
}

/// Dimensions covered by the per-dimension fixtures.
pub const DIMENSIONS: [usize; 5] = [0, 1, 2, 4, 8];

/// All fixtures.
pub fn all() -> Vec<Fixture> {
    let mut out = Vec::new();
    for n in DIMENSIONS {
        out.push(fixture(
            &format!("dim{n}_zero"),
            n,
            Start::Zero,
            vec![],
            false,
        ));
        out.push(fixture(
            &format!("dim{n}_universe"),
            n,
            Start::Universe,
            vec![],
            false,
        ));
        out.push(fixture(
            &format!("dim{n}_empty"),
            n,
            Start::Empty,
            vec![],
            true,
        ));
        out.push(fixture(
            &format!("dim{n}_zero_future_extrapolate"),
            n,
            Start::Zero,
            vec![Op::Future, Op::ExtrapolateMax(vec![2; n])],
            false,
        ));
        // Operations on ∅_d keep ∅_d.
        let mut ops = vec![Op::Future, Op::Constrain(le(n, 0, 5))];
        if n > 0 {
            ops.extend([Op::Reset { x: 1, value: 2 }, Op::Free(n)]);
        }
        out.push(fixture(
            &format!("dim{n}_empty_stays_empty"),
            n,
            Start::Empty,
            ops,
            true,
        ));
    }

    // Dimension 0: only x0 − x0 can be constrained.
    out.push(fixture(
        "dim0_trivial_guard",
        0,
        Start::Zero,
        vec![Op::Constrain(le(0, 0, 0))],
        false,
    ));
    out.push(fixture(
        "dim0_strict_zero_guard",
        0,
        Start::Zero,
        vec![Op::Constrain(lt(0, 0, 0))],
        true,
    ));

    // Strict-zero contradictions (S§8.2).
    out.push(fixture(
        "strict_zero_contradiction",
        1,
        Start::Universe,
        vec![Op::Constrain(lt(1, 0, 0))],
        true,
    ));
    out.push(fixture(
        "weak_zero_point_then_strict",
        1,
        Start::Universe,
        vec![Op::Constrain(le(1, 0, 0)), Op::Constrain(lt(0, 1, 0))],
        true,
    ));
    out.push(fixture(
        "weak_zero_point",
        1,
        Start::Universe,
        vec![Op::Constrain(le(1, 0, 0))],
        false,
    ));

    // S§8.1: A = universe(2) ∧ x ≤ 3 ∧ x − y < 1, then B = A ∧ x ≥ 3.
    let a = Start::Constraints(vec![le(1, 0, 3), lt(1, 2, 1)]);
    out.push(fixture("worked_8_1_a", 2, a.clone(), vec![], false));
    out.push(fixture(
        "worked_8_1_b",
        2,
        a.clone(),
        vec![Op::Constrain(le(0, 1, -3))],
        false,
    ));
    out.push(fixture(
        "worked_8_2_strict_propagation_contradiction",
        2,
        a,
        vec![Op::Constrain(le(0, 1, -3)), Op::Constrain(le(2, 0, 2))],
        true,
    ));
    out.push(fixture(
        "worked_8_2_weak_variant_point",
        2,
        Start::Constraints(vec![le(1, 0, 3), le(1, 2, 1)]),
        vec![Op::Constrain(le(0, 1, -3)), Op::Constrain(le(2, 0, 2))],
        false,
    ));

    // Negative bounds and diagonal guards: x ≥ 3, y > 1, y − x ≥ 1.
    out.push(fixture(
        "negative_bounds_diagonal_guard",
        2,
        Start::Universe,
        vec![Op::ConstrainAll(vec![
            le(0, 1, -3),
            lt(0, 2, -1),
            le(1, 2, -1),
        ])],
        false,
    ));
    out.push(fixture(
        "batch_contradiction",
        2,
        Start::Universe,
        vec![Op::ConstrainAll(vec![
            le(1, 0, 2),
            le(0, 2, -3),
            le(2, 1, 0),
        ])],
        true,
    ));
    out.push(fixture(
        "self_constraints",
        2,
        Start::Universe,
        vec![Op::ConstrainAll(vec![le(1, 1, 5), le(2, 2, 0)])],
        false,
    ));

    // Dimension 8 chains: x_{k+1} − x_k ≥ 1.
    let chain = |strict: bool| -> Vec<_> {
        (1..8)
            .map(|k| {
                if strict {
                    lt(k, k + 1, -1)
                } else {
                    le(k, k + 1, -1)
                }
            })
            .collect()
    };
    let mut weak = chain(false);
    weak.push(le(8, 0, 7));
    out.push(fixture(
        "dim8_weak_chain_single_point",
        8,
        Start::Constraints(weak.clone()),
        vec![],
        false,
    ));
    let mut weak_contra = weak;
    weak_contra.push(lt(0, 1, 0)); // x1 > 0
    out.push(fixture(
        "dim8_weak_chain_strict_contradiction",
        8,
        Start::Constraints(weak_contra),
        vec![],
        true,
    ));
    let mut strict = chain(true);
    strict.push(le(8, 0, 8));
    out.push(fixture(
        "dim8_strict_chain",
        8,
        Start::Constraints(strict.clone()),
        vec![],
        false,
    ));
    let mut strict_contra = strict;
    strict_contra.push(le(0, 1, -1)); // x1 ≥ 1 forces x8 > 8
    out.push(fixture(
        "dim8_strict_chain_contradiction",
        8,
        Start::Constraints(strict_contra),
        vec![],
        true,
    ));

    // Reset vs free (S§8.4) on D = zero(2)↑ ∧ x ≤ 1 ∧ x ≥ 1.
    let d = || {
        vec![
            Op::Future,
            Op::Constrain(le(1, 0, 1)),
            Op::Constrain(le(0, 1, -1)),
        ]
    };
    let with = |extra: Vec<Op>| -> Vec<Op> { d().into_iter().chain(extra).collect() };
    out.push(fixture("worked_8_4_point", 2, Start::Zero, d(), false));
    out.push(fixture(
        "worked_8_4_reset_zero",
        2,
        Start::Zero,
        with(vec![Op::ResetZero(1)]),
        false,
    ));
    out.push(fixture(
        "worked_8_4_free",
        2,
        Start::Zero,
        with(vec![Op::Free(1)]),
        false,
    ));
    out.push(fixture(
        "worked_8_4_reset_two",
        2,
        Start::Zero,
        with(vec![Op::Reset { x: 1, value: 2 }]),
        false,
    ));
    out.push(fixture(
        "worked_8_4_reset_then_future",
        2,
        Start::Zero,
        with(vec![Op::ResetZero(1), Op::Future]),
        false,
    ));

    // Mixed temporal sequence in dimension 4.
    out.push(fixture(
        "dim4_temporal_mix",
        4,
        Start::Zero,
        vec![
            Op::Future,
            Op::Constrain(le(1, 0, 5)),
            Op::Reset { x: 2, value: 3 },
            Op::Free(3),
            Op::Future,
            Op::Constrain(lt(4, 1, 2)),
            Op::Intersect(vec![le(0, 3, -1), le(3, 4, 0)]),
        ],
        false,
    ));

    // ExtraM (S§8.5).
    out.push(fixture(
        "worked_8_5_extra_m_lower",
        2,
        Start::Zero,
        vec![
            Op::Future,
            Op::Constrain(le(0, 1, -5)),
            Op::ExtrapolateMax(vec![3, 3]),
        ],
        false,
    ));
    out.push(fixture(
        "worked_8_5_extra_m_diagonal",
        2,
        Start::Constraints(vec![le(1, 2, 4), le(2, 0, 1)]),
        vec![Op::ExtrapolateMax(vec![3, 3])],
        false,
    ));

    // Near the production range: x ≥ MAX is representable, but y ≥ x + MAX
    // makes the exact canonical result unrepresentable.
    let max = PRODUCTION_MAX_CONSTANT;
    out.push(fixture(
        "range_large_representable",
        2,
        Start::Universe,
        vec![Op::Constrain(le(0, 1, -max))],
        false,
    ));
    out.push(fixture(
        "range_unrepresentable_result",
        2,
        Start::Universe,
        vec![Op::Constrain(le(0, 1, -max)), Op::Constrain(le(1, 2, -max))],
        false,
    ));
    out
}

/// The fixture called `name`. Panics if there is none.
pub fn named(name: &str) -> Fixture {
    all()
        .into_iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no fixture named {name:?}"))
}
