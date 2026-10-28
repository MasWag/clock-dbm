//! Comparing a production result against the oracle.
//!
//! Production tests translate their `Dbm` into an [`ObservedZone`] (via
//! [`ExactBound::from_parts`]) and their errors into [`ObservedError`]; this
//! module never names a production type.

use std::fmt;

use num_bigint::BigInt;

use super::bound::{ExactBound, Matrix};
use super::zone::{OracleDbm, OracleError, write_matrix};

/// Production `MAX_CONSTANT`: `2²⁹ − 1`. Copied, not
/// imported, so the oracle stays independent of the production crate.
pub const PRODUCTION_MAX_CONSTANT: i64 = (1 << 29) - 1;

/// A zone as observed through the production API.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ObservedZone {
    /// Number of actual clocks.
    pub variables: usize,
    /// Row-major `(n+1)²` entries, or `None` for the empty zone.
    pub entries: Option<Vec<ExactBound>>,
}

impl ObservedZone {
    /// The empty zone with `variables` clocks.
    pub fn empty(variables: usize) -> ObservedZone {
        ObservedZone {
            variables,
            entries: None,
        }
    }

    /// A nonempty zone from row-major entries. Panics on a length mismatch.
    pub fn from_entries(variables: usize, entries: Vec<ExactBound>) -> ObservedZone {
        let d = variables + 1;
        assert_eq!(entries.len(), d * d, "expected {} entries", d * d);
        ObservedZone {
            variables,
            entries: Some(entries),
        }
    }

    /// The oracle zone seen as an observation (useful for self-tests).
    pub fn from_oracle(z: &OracleDbm) -> ObservedZone {
        ObservedZone {
            variables: z.variables(),
            entries: z.matrix().map(|m| m.iter().flatten().cloned().collect()),
        }
    }

    /// Entry `(i, j)`; `None` if empty.
    pub fn entry(&self, i: usize, j: usize) -> Option<&ExactBound> {
        let d = self.variables + 1;
        self.entries.as_ref().map(|e| &e[i * d + j])
    }

    /// The entries as a square matrix; `None` if empty.
    pub fn matrix(&self) -> Option<Matrix> {
        let d = self.variables + 1;
        self.entries
            .as_ref()
            .map(|e| e.chunks(d).map(<[ExactBound]>::to_vec).collect())
    }
}

impl fmt::Display for ObservedZone {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.matrix() {
            None => writeln!(f, "empty zone (variables = {})", self.variables),
            Some(m) => {
                writeln!(f, "zone (variables = {}):", self.variables)?;
                write_matrix(f, &m)
            }
        }
    }
}

/// Checks the public invariant `Inv` (S§3) by brute force: C1 (every finite
/// constant within `±max_constant`, if given), C2 (diagonal `Le 0`), C3
/// (`D[0][i] ≼ Le 0`) and C4 (triangle inequality). C5 follows from C2 and C4.
pub fn check_public_invariant(
    z: &ObservedZone,
    max_constant: Option<&BigInt>,
) -> Result<(), String> {
    let Some(m) = z.matrix() else {
        return Ok(());
    };
    let d = m.len();
    let le0 = ExactBound::le_zero();
    for i in 0..d {
        for j in 0..d {
            let b = &m[i][j];
            if let (Some(c), Some(max)) = (b.constant(), max_constant)
                && (c > max || -c > *max)
            {
                return Err(format!("C1: entry ({i},{j}) = {b} is out of range\n{z}"));
            }
            if i == j && *b != le0 {
                return Err(format!("C2: diagonal ({i},{i}) = {b}, expected <=0\n{z}"));
            }
            if i == 0 && *b > le0 {
                return Err(format!(
                    "C3: entry (0,{j}) = {b} allows a negative clock\n{z}"
                ));
            }
            for k in 0..d {
                let via = m[i][k].add(&m[k][j]);
                if *b > via {
                    return Err(format!(
                        "C4: ({i},{j}) = {b} is looser than ({i},{k}) + ({k},{j}) = {via}\n{z}"
                    ));
                }
            }
        }
    }
    Ok(())
}

/// A failed comparison, with both sides printed.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ZoneMismatch {
    /// Human-readable description, including matrices and differing entries.
    pub message: String,
}

impl fmt::Display for ZoneMismatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

fn mismatch(message: String) -> Result<(), ZoneMismatch> {
    Err(ZoneMismatch { message })
}

/// Compares a canonical production zone with the oracle entry by entry.
///
/// Valid only for observations that claim to satisfy `Inv`: by Theorem 3.1
/// two canonical nonempty matrices of one dimension denote the same zone iff
/// they are equal. Dimensions are compared first, so `∅_2` never matches
/// `∅_3`.
pub fn compare_exact(observed: &ObservedZone, expected: &OracleDbm) -> Result<(), ZoneMismatch> {
    if observed.variables != expected.variables() {
        return mismatch(format!(
            "dimension mismatch: observed {} variables, oracle {}\nobserved: {observed}oracle: {expected}",
            observed.variables,
            expected.variables()
        ));
    }
    match (observed.matrix(), expected.matrix()) {
        (None, None) => Ok(()),
        (Some(_), None) | (None, Some(_)) => mismatch(format!(
            "emptiness mismatch\nobserved: {observed}oracle: {expected}"
        )),
        (Some(o), Some(e)) => {
            let diffs: Vec<String> = (0..o.len())
                .flat_map(|i| (0..o.len()).map(move |j| (i, j)))
                .filter(|&(i, j)| o[i][j] != e[i][j])
                .map(|(i, j)| format!("  ({i},{j}): observed {}, oracle {}", o[i][j], e[i][j]))
                .collect();
            if diffs.is_empty() {
                Ok(())
            } else {
                mismatch(format!(
                    "entry mismatch\n{}\nobserved: {observed}oracle: {expected}",
                    diffs.join("\n")
                ))
            }
        }
    }
}

/// Compares the *zones* denoted, for observations that need not be canonical
/// (for example a raw matrix before closure). The observation is closed by
/// the oracle first.
pub fn compare_semantic(observed: &ObservedZone, expected: &OracleDbm) -> Result<(), ZoneMismatch> {
    let closed = match observed.matrix() {
        None => OracleDbm::empty(observed.variables),
        Some(m) => OracleDbm::from_matrix(observed.variables, m),
    };
    compare_exact(&ObservedZone::from_oracle(&closed), expected).map_err(|e| ZoneMismatch {
        message: format!("semantic {}", e.message),
    })
}

/// What the production contract (S§7, S§7.1) allows for range failures.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RangeExpectation {
    /// The exact result is unrepresentable, so `Err(Range)` is mandatory
    /// (production never saturates or clamps).
    MustFailRange,
    /// The S§7.1 premise `2(n+1)B ≤ MAX_CONSTANT` holds, so the operation
    /// must succeed. (The premise lemma itself is not yet proved; S§7.1.)
    MustSucceed,
    /// Either the exact result or `Err(Range)` is allowed, depending on the
    /// production algorithm's intermediate values.
    EitherAllowed,
}

/// Classifies one production operation on `variables` clocks whose inputs
/// have finite constants bounded by `input_bound` (`B` of S§7.1) and whose
/// exact result is `result`.
pub fn classify_range(
    variables: usize,
    input_bound: &BigInt,
    result: &OracleDbm,
    max_constant: i64,
) -> RangeExpectation {
    let max = BigInt::from(max_constant);
    if result.max_abs_constant() > max {
        RangeExpectation::MustFailRange
    } else if BigInt::from(2 * (variables as u64 + 1)) * input_bound <= max {
        RangeExpectation::MustSucceed
    } else {
        RangeExpectation::EitherAllowed
    }
}

/// A production error, translated by the differential test.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ObservedError {
    /// Production `Error::Range`.
    Range,
    /// Any production argument error, translated into the oracle's terms.
    Argument(OracleError),
}

/// Checks a whole production outcome against the oracle outcome and the
/// range expectation. A successful observation is compared with
/// [`compare_exact`] after checking `Inv` within `max_constant`.
pub fn check_outcome(
    observed: &Result<ObservedZone, ObservedError>,
    expected: &Result<OracleDbm, OracleError>,
    range: RangeExpectation,
    max_constant: i64,
) -> Result<(), ZoneMismatch> {
    match (observed, expected) {
        (Err(ObservedError::Argument(o)), Err(e)) if o == e => Ok(()),
        (_, Err(e)) => mismatch(format!(
            "oracle reports argument error {e:?}, production gave {observed:?}"
        )),
        (Err(ObservedError::Argument(o)), Ok(_)) => mismatch(format!(
            "production reports argument error {o:?}, the oracle accepts the call"
        )),
        (Err(ObservedError::Range), Ok(e)) => match range {
            RangeExpectation::MustSucceed => mismatch(format!(
                "production returned Err(Range) although the S§7.1 premise holds\noracle: {e}"
            )),
            _ => Ok(()),
        },
        (Ok(o), Ok(e)) => {
            if range == RangeExpectation::MustFailRange {
                return mismatch(format!(
                    "the exact result is unrepresentable, so production must return Err(Range)\nobserved: {o}oracle: {e}"
                ));
            }
            check_public_invariant(o, Some(&BigInt::from(max_constant)))
                .map_err(|message| ZoneMismatch { message })?;
            compare_exact(o, e)
        }
    }
}
