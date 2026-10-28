//! Exact DBM bounds `Lt c`, `Le c` (with `c` an arbitrary-precision integer)
//! and `∞` (S§1).

use std::cmp::Ordering;
use std::fmt;

use num_bigint::BigInt;
use num_rational::BigRational;

/// Whether a finite bound is strict (`<`) or weak (`≤`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Strictness {
    /// `x < c`.
    Strict,
    /// `x ≤ c`.
    Weak,
}

/// An unpacked DBM bound. Unlike the production `Bound`, it has no range
/// limit and no encoding: the constant and the strictness are stored as is.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ExactBound {
    /// `Lt constant` or `Le constant`.
    Finite {
        /// The integer constant `c`.
        constant: BigInt,
        /// `Strict` for `Lt c`, `Weak` for `Le c`.
        strictness: Strictness,
    },
    /// `∞`: no constraint.
    Infinity,
}

/// A square matrix of bounds, indexed `[row i][column j]` for `xᵢ − xⱼ`.
pub type Matrix = Vec<Vec<ExactBound>>;

impl ExactBound {
    /// `Le c`.
    pub fn le(c: impl Into<BigInt>) -> ExactBound {
        ExactBound::Finite {
            constant: c.into(),
            strictness: Strictness::Weak,
        }
    }

    /// `Lt c`.
    pub fn lt(c: impl Into<BigInt>) -> ExactBound {
        ExactBound::Finite {
            constant: c.into(),
            strictness: Strictness::Strict,
        }
    }

    /// `Le 0`, the normalized diagonal.
    pub fn le_zero() -> ExactBound {
        ExactBound::le(0)
    }

    /// Builds a bound from production-style parts: `None` is `∞` (and
    /// `strict` is ignored), `Some(c)` is `Lt c` if `strict` else `Le c`.
    /// Differential tests use this to translate production bounds without the
    /// oracle naming any production type.
    pub fn from_parts(constant: Option<i64>, strict: bool) -> ExactBound {
        match constant {
            None => ExactBound::Infinity,
            Some(c) if strict => ExactBound::lt(c),
            Some(c) => ExactBound::le(c),
        }
    }

    /// The constant of a finite bound; `None` for `∞`.
    pub fn constant(&self) -> Option<&BigInt> {
        match self {
            ExactBound::Finite { constant, .. } => Some(constant),
            ExactBound::Infinity => None,
        }
    }

    /// True for `Lt c`; false for `Le c` and `∞`.
    pub fn is_strict(&self) -> bool {
        matches!(
            self,
            ExactBound::Finite {
                strictness: Strictness::Strict,
                ..
            }
        )
    }

    /// True for `∞`.
    pub fn is_infinite(&self) -> bool {
        matches!(self, ExactBound::Infinity)
    }

    /// Exact bound addition (S§1.3): `∞` absorbs, and the sum is strict if
    /// either summand is strict.
    pub fn add(&self, other: &ExactBound) -> ExactBound {
        match (self, other) {
            (ExactBound::Infinity, _) | (_, ExactBound::Infinity) => ExactBound::Infinity,
            (
                ExactBound::Finite {
                    constant: a,
                    strictness: sa,
                },
                ExactBound::Finite {
                    constant: b,
                    strictness: sb,
                },
            ) => {
                let strictness = if *sa == Strictness::Weak && *sb == Strictness::Weak {
                    Strictness::Weak
                } else {
                    Strictness::Strict
                };
                ExactBound::Finite {
                    constant: a + b,
                    strictness,
                }
            }
        }
    }

    /// The complement (Isabelle `neg_dbm_entry`): `r ⊭ b ⟺ −r ⊨ negate(b)`.
    /// `Le c ↦ Lt (−c)`, `Lt c ↦ Le (−c)`. `∞` has an empty complement, so
    /// the result is `None`.
    pub fn negate(&self) -> Option<ExactBound> {
        match self {
            ExactBound::Finite {
                constant,
                strictness: Strictness::Weak,
            } => Some(ExactBound::lt(-constant)),
            ExactBound::Finite {
                constant,
                strictness: Strictness::Strict,
            } => Some(ExactBound::le(-constant)),
            ExactBound::Infinity => None,
        }
    }

    /// `sat(r, b)` (S§1.1) for an exact rational `r`.
    pub fn sat(&self, r: &BigRational) -> bool {
        match self {
            ExactBound::Infinity => true,
            ExactBound::Finite {
                constant,
                strictness,
            } => {
                let c = BigRational::from_integer(constant.clone());
                match strictness {
                    Strictness::Strict => *r < c,
                    Strictness::Weak => *r <= c,
                }
            }
        }
    }

    /// Parses `<=c` (`Le c`), `<c` (`Lt c`) or `inf`. This is also the
    /// `Display` format, so printed matrices can be pasted back into tests.
    pub fn parse(token: &str) -> Result<ExactBound, String> {
        let token = token.trim();
        if token == "inf" {
            return Ok(ExactBound::Infinity);
        }
        let (rest, strict) = if let Some(rest) = token.strip_prefix("<=") {
            (rest, false)
        } else if let Some(rest) = token.strip_prefix('<') {
            (rest, true)
        } else {
            return Err(format!("bad bound {token:?}: expected <=c, <c or inf"));
        };
        let constant: BigInt = rest
            .parse()
            .map_err(|e| format!("bad bound {token:?}: {e}"))?;
        Ok(if strict {
            ExactBound::lt(constant)
        } else {
            ExactBound::le(constant)
        })
    }
}

/// The tightness order (S§1.2, Isabelle `dbm_lt`): smaller is tighter.
/// `Lt c < Le c < Lt (c+1)`, and every finite bound is below `∞`.
impl Ord for ExactBound {
    fn cmp(&self, other: &ExactBound) -> Ordering {
        fn rank(s: Strictness) -> u8 {
            match s {
                Strictness::Strict => 0,
                Strictness::Weak => 1,
            }
        }
        match (self, other) {
            (ExactBound::Infinity, ExactBound::Infinity) => Ordering::Equal,
            (ExactBound::Infinity, _) => Ordering::Greater,
            (_, ExactBound::Infinity) => Ordering::Less,
            (
                ExactBound::Finite {
                    constant: a,
                    strictness: sa,
                },
                ExactBound::Finite {
                    constant: b,
                    strictness: sb,
                },
            ) => a.cmp(b).then(rank(*sa).cmp(&rank(*sb))),
        }
    }
}

impl PartialOrd for ExactBound {
    fn partial_cmp(&self, other: &ExactBound) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for ExactBound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            ExactBound::Infinity => "inf".to_string(),
            ExactBound::Finite {
                constant,
                strictness: Strictness::Weak,
            } => format!("<={constant}"),
            ExactBound::Finite {
                constant,
                strictness: Strictness::Strict,
            } => format!("<{constant}"),
        };
        // Pad as a unit so matrices line up.
        f.pad(&text)
    }
}

/// Parses a square matrix written one row per string, with whitespace-separated
/// bounds in the [`ExactBound::parse`] format. Panics on malformed input,
/// because a malformed literal is a bug in the test itself.
///
/// ```text
/// parse_matrix(&[
///     "<=0  <=0  <=0",
///     "<=3  <=0  <1",
///     "inf  inf  <=0",
/// ])
/// ```
pub fn parse_matrix(rows: &[&str]) -> Matrix {
    let matrix: Matrix = rows
        .iter()
        .map(|row| {
            row.split_whitespace()
                .map(|t| ExactBound::parse(t).unwrap_or_else(|e| panic!("{e}")))
                .collect()
        })
        .collect();
    let d = matrix.len();
    assert!(d >= 1, "a DBM has dimension at least 1");
    for (i, row) in matrix.iter().enumerate() {
        assert_eq!(
            row.len(),
            d,
            "row {i} has {} entries, expected {d}",
            row.len()
        );
    }
    matrix
}
