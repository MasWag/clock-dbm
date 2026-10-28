//! Translation between production values and the independent exact oracle
//! (`tests/support/oracle/`), shared by the differential tests of
//! `ops::constraints`, `ops::temporal`, `ops::relations` and `ops::extra_m`.

use crate::bounds::{Bound, Clock, Constraint, Variable};
use crate::dbm::{Dbm, Workspace};
use crate::error::Error;
use crate::ops::extra_m::MaxBounds;
use crate::oracle;
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};

use oracle::compare::{
    ObservedError, ObservedZone, PRODUCTION_MAX_CONSTANT, RangeExpectation, check_outcome,
    classify_range,
};
use oracle::scenario::{Op, Scenario, Start};
use oracle::{ExactBound, OracleConstraint, OracleDbm, OracleError};

pub(crate) fn exact(b: Bound) -> ExactBound {
    ExactBound::from_parts(b.constant().map(i64::from), b.is_strict())
}

pub(crate) fn packed(b: &ExactBound) -> Option<Bound> {
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

/// The production constraint for an oracle constraint (representable,
/// indices within `MAX_VARIABLES`).
pub(crate) fn con(g: &OracleConstraint) -> Constraint {
    Constraint::new(
        Clock::new(g.i).unwrap(),
        Clock::new(g.j).unwrap(),
        packed(&g.bound).expect("representable test constraint"),
    )
}

pub(crate) fn cons(gs: &[OracleConstraint]) -> Vec<Constraint> {
    gs.iter().map(con).collect()
}

pub(crate) fn observe(z: &Dbm) -> ObservedZone {
    let n = z.variables();
    if z.is_empty() {
        ObservedZone::empty(n)
    } else {
        let d = n + 1;
        let entries = (0..d * d).map(|x| exact(z.entry(x / d, x % d))).collect();
        ObservedZone::from_entries(n, entries)
    }
}

pub(crate) fn observe_result(r: &Result<Dbm, Error>) -> Result<ObservedZone, ObservedError> {
    match r {
        Ok(z) => Ok(observe(z)),
        Err(Error::Range) => Err(ObservedError::Range),
        Err(Error::ClockOutOfRange { clock, variables }) => {
            Err(ObservedError::Argument(OracleError::ClockOutOfRange {
                clock: *clock,
                variables: *variables,
            }))
        }
        Err(Error::DimensionMismatch { expected, found }) => {
            Err(ObservedError::Argument(OracleError::DimensionMismatch {
                expected: *expected,
                found: *found,
            }))
        }
        Err(Error::NegativeConstant { value }) => {
            Err(ObservedError::Argument(OracleError::NegativeConstant {
                value: BigInt::from(*value),
            }))
        }
        Err(Error::InvalidMaxBounds { variable, value }) => {
            Err(ObservedError::Argument(OracleError::InvalidMaxBounds {
                variable: *variable,
                value: BigInt::from(*value),
            }))
        }
        Err(e) => panic!("unexpected error {e:?}"),
    }
}

pub(crate) fn max_abs<'a>(gs: impl IntoIterator<Item = &'a OracleConstraint>) -> BigInt {
    gs.into_iter()
        .filter_map(|g| g.bound.constant().map(BigInt::abs))
        .max()
        .unwrap_or_else(BigInt::zero)
}

/// `universe(n) ∧ start`, built one constraint at a time and checked
/// against the oracle. (The full closure of `dbm.rs` is conservative: it
/// reports `Err(Range)` for any unrepresentable intermediate sum, even one
/// that is not needed, so it cannot build every representable start zone.)
pub(crate) fn start_zone(n: usize, start: &[OracleConstraint]) -> Dbm {
    let mut z = Dbm::universe(n).unwrap();
    for g in start {
        z = z
            .try_constrain(con(g))
            .expect("test start zones are representable");
    }
    let expected = OracleDbm::from_constraints(n, start);
    assert_outcome(
        "start zone",
        &Ok(z.clone()),
        &expected,
        RangeExpectation::MustSucceed,
    );
    z
}

#[track_caller]
pub(crate) fn assert_outcome(
    label: &str,
    observed: &Result<Dbm, Error>,
    expected: &Result<OracleDbm, OracleError>,
    range: RangeExpectation,
) {
    if let Err(e) = check_outcome(
        &observe_result(observed),
        expected,
        range,
        PRODUCTION_MAX_CONSTANT,
    ) {
        panic!("{label}: {e}");
    }
}

/// One timed configuration: median nanoseconds per operation of `run` over
/// `samples` samples, each consuming `batch` staged clones of `z`.
pub(crate) fn time_op(
    z: &Dbm,
    batch: usize,
    samples: usize,
    mut run: impl FnMut(Dbm) -> Dbm,
) -> f64 {
    let mut times = Vec::with_capacity(samples);
    let warmup = 5;
    for s in 0..samples + warmup {
        let mut staged: Vec<Option<Dbm>> = (0..batch).map(|_| Some(z.clone())).collect();
        let mut out: Vec<Dbm> = Vec::with_capacity(batch);
        let t0 = std::time::Instant::now();
        for slot in &mut staged {
            out.push(run(slot.take().unwrap()));
        }
        let dt = t0.elapsed().as_nanos() as f64 / batch as f64;
        std::hint::black_box(&out);
        if s >= warmup {
            times.push(dt);
        }
    }
    times.sort_by(f64::total_cmp);
    times[times.len() / 2]
}

// ----- scenario replay (shared by the operation tests) -----

pub(crate) fn var(x: usize) -> Variable {
    Variable::new(x).unwrap()
}

/// The oracle zone denoted by a production DBM (for membership tests).
pub(crate) fn as_oracle(z: &Dbm) -> OracleDbm {
    match observe(z).matrix() {
        Some(m) => OracleDbm::from_matrix(z.variables(), m),
        None => OracleDbm::empty(z.variables()),
    }
}

/// The oracle zone `universe(n) ∧ start`.
pub(crate) fn oracle_zone(n: usize, start: &[OracleConstraint]) -> OracleDbm {
    OracleDbm::from_constraints(n, start).unwrap()
}

/// Applies a scenario operation in production.
pub(crate) fn apply(z: Dbm, op: &Op) -> Result<Dbm, Error> {
    match op {
        Op::Constrain(g) => z.try_constrain(cons(std::slice::from_ref(g))[0]),
        Op::ConstrainAll(gs) => z.try_constrain_all(&cons(gs), &mut Workspace::new()),
        Op::Future => Ok(z.future()),
        Op::Past => Ok(z.past()),
        Op::Reset { x, value } => z.try_reset(var(*x), i32::try_from(*value).unwrap()),
        Op::ResetZero(x) => z.try_reset_zero(var(*x)),
        Op::Free(x) => z.try_free(var(*x)),
        Op::Intersect(gs) => {
            let n = z.variables();
            let e = Dbm::try_from_constraints(n, &cons(gs), &mut Workspace::new())?;
            z.try_intersect(&e, &mut Workspace::new())
        }
        Op::ExtrapolateMax(m) => {
            let m: Vec<i32> = m.iter().map(|&c| i32::try_from(c).unwrap()).collect();
            z.try_extrapolate_max(&MaxBounds::new(m)?, &mut Workspace::new())
        }
    }
}

/// The production start zone of a scenario.
pub(crate) fn initial(s: &Scenario) -> Dbm {
    let n = s.variables;
    match &s.start {
        Start::Zero => Dbm::zero(n).unwrap(),
        Start::Universe => Dbm::universe(n).unwrap(),
        Start::Empty => Dbm::empty(n).unwrap(),
        Start::Constraints(cs) => {
            Dbm::try_from_constraints(n, &cons(cs), &mut Workspace::new()).unwrap()
        }
    }
}

/// Replays `s` in production and compares every step with the oracle under
/// the S§7 range rules. Returns the number of steps compared (fewer than
/// `s.ops.len` only after an error).
pub(crate) fn replay(label: &str, s: &Scenario) -> usize {
    let n = s.variables;
    let mut z = initial(s);
    let mut cur = s.initial().unwrap();
    assert_outcome(
        &format!("{label} start"),
        &Ok(z.clone()),
        &Ok(cur.clone()),
        RangeExpectation::MustSucceed,
    );
    let mut steps = 0;
    for (k, op) in s.ops.iter().enumerate() {
        let expected = op.apply(&cur);
        let range = match &expected {
            Ok(e) => classify_range(n, &op.input_bound(&cur), e, PRODUCTION_MAX_CONSTANT),
            Err(_) => RangeExpectation::MustSucceed,
        };
        let observed = apply(z, op);
        assert_outcome(
            &format!("{label} step {} {op:?}", k + 1),
            &observed,
            &expected,
            range,
        );
        steps += 1;
        match (observed, expected) {
            (Ok(next), Ok(e)) => {
                z = next;
                cur = e;
            }
            _ => break,
        }
    }
    steps
}
