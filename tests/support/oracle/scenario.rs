//! A small replayable language of operation sequences.
//!
//! Fixtures and random cases are [`Scenario`]s, so a production differential
//! test can replay exactly the same steps against `clock_dbm::Dbm` and compare
//! each step with [`Scenario::run_oracle`]. `Display` prints a scenario as
//! Rust source using [`le`], [`lt`] and [`inf`], so a failing random case can
//! be pasted into `tests/oracle.rs` as a regression.

use std::fmt;

use num_bigint::BigInt;

use super::bound::ExactBound;
use super::zone::{OracleConstraint, OracleDbm, OracleError};

/// `xᵢ − xⱼ ≤ c`.
pub fn le(i: usize, j: usize, c: i64) -> OracleConstraint {
    OracleConstraint::le(i, j, c)
}

/// `xᵢ − xⱼ < c`.
pub fn lt(i: usize, j: usize, c: i64) -> OracleConstraint {
    OracleConstraint::lt(i, j, c)
}

/// `xᵢ − xⱼ < ∞` (no constraint).
pub fn inf(i: usize, j: usize) -> OracleConstraint {
    OracleConstraint::new(i, j, ExactBound::Infinity)
}

/// The initial zone of a scenario.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Start {
    /// `zero(n)`.
    Zero,
    /// `universe(n)`.
    Universe,
    /// `empty(n)`.
    Empty,
    /// `universe(n) ∧ cs` (production: `try_from_constraints`).
    Constraints(Vec<OracleConstraint>),
}

/// One updating operation (S§5.2–5.5, S§5.8).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Op {
    /// `try_constrain`.
    Constrain(OracleConstraint),
    /// `try_constrain_all`.
    ConstrainAll(Vec<OracleConstraint>),
    /// `try_intersect` with `universe(n) ∧ cs`.
    Intersect(Vec<OracleConstraint>),
    /// `future`.
    Future,
    /// `past`.
    Past,
    /// `try_reset(x, value)`.
    Reset {
        /// Clock index (≥ 1).
        x: usize,
        /// Reset value.
        value: i64,
    },
    /// `try_reset_zero(x)`.
    ResetZero(usize),
    /// `try_free(x)`.
    Free(usize),
    /// `try_extrapolate_max` with these ceilings `M(x₁)…M(xₙ)`.
    ExtrapolateMax(Vec<i64>),
}

impl Op {
    /// Applies the operation in the oracle.
    pub fn apply(&self, d: &OracleDbm) -> Result<OracleDbm, OracleError> {
        match self {
            Op::Constrain(g) => d.constrain(g),
            Op::ConstrainAll(cs) => d.constrain_all(cs),
            Op::Intersect(cs) => d.intersect(&OracleDbm::from_constraints(d.variables(), cs)?),
            Op::Future => Ok(d.future()),
            Op::Past => Ok(d.past()),
            Op::Reset { x, value } => d.reset(*x, *value),
            Op::ResetZero(x) => d.reset_zero(*x),
            Op::Free(x) => d.free(*x),
            Op::ExtrapolateMax(ceilings) => {
                let ceilings: Vec<BigInt> = ceilings.iter().map(|&c| c.into()).collect();
                d.extrapolate_max(&ceilings)
            }
        }
    }

    /// `B` of S§7.1 for applying this operation to `d`: the largest absolute
    /// finite constant among `d`, the constraints (or the closed other zone of
    /// an intersection), the reset value and the ceilings.
    pub fn input_bound(&self, d: &OracleDbm) -> BigInt {
        let mut bound = d.max_abs_constant();
        let mut include = |c: BigInt| {
            let c = if c < BigInt::from(0) { -c } else { c };
            if c > bound {
                bound = c;
            }
        };
        match self {
            Op::Constrain(g) => g
                .bound
                .constant()
                .cloned()
                .into_iter()
                .for_each(&mut include),
            Op::ConstrainAll(cs) => cs
                .iter()
                .filter_map(|g| g.bound.constant().cloned())
                .for_each(&mut include),
            Op::Intersect(cs) => {
                if let Ok(other) = OracleDbm::from_constraints(d.variables(), cs) {
                    include(other.max_abs_constant());
                }
            }
            Op::Future | Op::Past | Op::ResetZero(_) | Op::Free(_) => {}
            Op::Reset { value, .. } => include((*value).into()),
            Op::ExtrapolateMax(ceilings) => ceilings.iter().for_each(|&c| include(c.into())),
        }
        bound
    }
}

/// A start zone plus a sequence of operations on `variables` clocks.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Scenario {
    /// Number of actual clocks.
    pub variables: usize,
    /// Initial zone.
    pub start: Start,
    /// Operations applied in order.
    pub ops: Vec<Op>,
}

/// An argument error at a given step (0 is the start, `k` is `ops[k − 1]`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct StepError {
    /// The failing step.
    pub step: usize,
    /// The error.
    pub error: OracleError,
}

impl Scenario {
    /// The initial zone.
    pub fn initial(&self) -> Result<OracleDbm, OracleError> {
        let n = self.variables;
        match &self.start {
            Start::Zero => Ok(OracleDbm::zero(n)),
            Start::Universe => Ok(OracleDbm::universe(n)),
            Start::Empty => Ok(OracleDbm::empty(n)),
            Start::Constraints(cs) => OracleDbm::from_constraints(n, cs),
        }
    }

    /// Every intermediate zone: `trace[0]` is the start and `trace[k]` the
    /// result of `ops[k − 1]`.
    pub fn run_oracle(&self) -> Result<Vec<OracleDbm>, StepError> {
        let mut trace = vec![
            self.initial()
                .map_err(|error| StepError { step: 0, error })?,
        ];
        for (k, op) in self.ops.iter().enumerate() {
            let next = op
                .apply(trace.last().expect("trace is nonempty"))
                .map_err(|error| StepError { step: k + 1, error })?;
            trace.push(next);
        }
        Ok(trace)
    }

    /// The final zone.
    pub fn final_zone(&self) -> Result<OracleDbm, StepError> {
        Ok(self.run_oracle()?.pop().expect("trace is nonempty"))
    }
}

fn constraint_code(g: &OracleConstraint) -> String {
    match &g.bound {
        ExactBound::Infinity => format!("inf({}, {})", g.i, g.j),
        b => {
            let f = if b.is_strict() { "lt" } else { "le" };
            let c = b.constant().expect("finite");
            format!("{f}({}, {}, {c})", g.i, g.j)
        }
    }
}

fn constraints_code(cs: &[OracleConstraint]) -> String {
    let items: Vec<String> = cs.iter().map(constraint_code).collect();
    format!("vec![{}]", items.join(", "))
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Op::Constrain(g) => write!(f, "Op::Constrain({})", constraint_code(g)),
            Op::ConstrainAll(cs) => write!(f, "Op::ConstrainAll({})", constraints_code(cs)),
            Op::Intersect(cs) => write!(f, "Op::Intersect({})", constraints_code(cs)),
            Op::Future => write!(f, "Op::Future"),
            Op::Past => write!(f, "Op::Past"),
            Op::Reset { x, value } => write!(f, "Op::Reset {{ x: {x}, value: {value} }}"),
            Op::ResetZero(x) => write!(f, "Op::ResetZero({x})"),
            Op::Free(x) => write!(f, "Op::Free({x})"),
            Op::ExtrapolateMax(m) => write!(f, "Op::ExtrapolateMax(vec!{m:?})"),
        }
    }
}

impl fmt::Display for Scenario {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let start = match &self.start {
            Start::Zero => "Start::Zero".to_string(),
            Start::Universe => "Start::Universe".to_string(),
            Start::Empty => "Start::Empty".to_string(),
            Start::Constraints(cs) => format!("Start::Constraints({})", constraints_code(cs)),
        };
        writeln!(f, "Scenario {{")?;
        writeln!(f, "    variables: {},", self.variables)?;
        writeln!(f, "    start: {start},")?;
        writeln!(f, "    ops: vec![")?;
        for op in &self.ops {
            writeln!(f, "        {op},")?;
        }
        writeln!(f, "    ],")?;
        write!(f, "}}")
    }
}
