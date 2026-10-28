//! The crate-wide error type.

use creusot_std::prelude::{Clone, DeepModel, PartialEq, *};

/// An invalid argument or an unrepresentable bound in a zone operation.
///
/// **An inconsistent zone is not an error:** it is returned as `Ok` with
/// `Dbm::is_empty` equal to `true`. [`Error::Range`] instead indicates
/// that exact finite arithmetic required a constant outside the supported
/// range. Do not interpret `Range` as an empty zone or silently clamp it.
///
/// Argument validation precedes emptiness checks, so invalid arguments
/// are rejected even for empty input zones.
#[derive(Clone, Copy, PartialEq, Eq, Debug, DeepModel)]
#[non_exhaustive]
pub enum Error {
    /// Exact arithmetic would leave `[MIN_CONSTANT, MAX_CONSTANT]`.
    /// This is **not** emptiness and **not** "unsatisfiable".
    Range,
    /// More than `MAX_VARIABLES` clocks requested.
    TooManyVariables {
        /// The number of actual clocks requested.
        requested: usize,
    },
    /// Two operands (DBM/DBM, DBM/MaxBounds) disagree on the number of variables.
    DimensionMismatch {
        /// The number of variables of the receiver.
        expected: usize,
        /// The number of variables of the other operand.
        found: usize,
    },
    /// A clock index ≥ dimension of the DBM it is used with.
    ClockOutOfRange {
        /// The offending clock index.
        clock: usize,
        /// The number of actual clocks of the DBM.
        variables: usize,
    },
    /// Reset to a negative value (clocks are nonnegative).
    NegativeConstant {
        /// The rejected reset value.
        value: i32,
    },
    /// A `MaxBounds` ceiling is negative or unrepresentable.
    InvalidMaxBounds {
        /// The (1-based) actual clock whose ceiling is invalid.
        variable: usize,
        /// The rejected ceiling.
        value: i32,
    },
}

// Message formatting only; it computes no bound and is not part of the
// verified kernel (see verification/PROOF_STATUS.md).
#[cfg(not(creusot))]
impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Error::Range => f.write_str("bound constant outside the representable range"),
            Error::TooManyVariables { requested } => {
                write!(f, "too many clock variables requested: {requested}")
            }
            Error::DimensionMismatch { expected, found } => {
                write!(
                    f,
                    "dimension mismatch: expected {expected} variables, found {found}"
                )
            }
            Error::ClockOutOfRange { clock, variables } => {
                write!(
                    f,
                    "clock index {clock} out of range for {variables} variables"
                )
            }
            Error::NegativeConstant { value } => {
                write!(f, "negative reset value {value}")
            }
            Error::InvalidMaxBounds { variable, value } => {
                write!(f, "invalid maximal constant {value} for clock x{variable}")
            }
        }
    }
}

#[cfg(not(creusot))]
impl std::error::Error for Error {}
