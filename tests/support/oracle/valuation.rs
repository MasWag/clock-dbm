//! Exact rational valuations and closure-free semantic checks.
//!
//! Nothing here runs Floyd–Warshall. Membership is checked constraint by
//! constraint, and the images of `future`, `past`, `free` and `reset` are
//! decided from their set equations (S§5.3–5.5) with an exact one-dimensional interval
//! solver. Randomized tests use these to cross-check the closure-based
//! operations in `zone.rs`.

use std::fmt;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use super::bound::{ExactBound, Matrix, Strictness};
use super::zone::{OracleConstraint, OracleDbm};

/// A valuation `u : {x₁..xₙ} → ℚ≥0`, stored with `u(x₀) = 0` at index 0.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Valuation {
    values: Vec<BigRational>,
}

impl Valuation {
    /// `u(xᵢ) = clocks[i − 1]`. Panics on a negative value.
    pub fn new(clocks: Vec<BigRational>) -> Valuation {
        let mut values = vec![BigRational::zero()];
        values.extend(clocks);
        Valuation::with_reference(values)
    }

    /// Like [`Valuation::new`] but `values[0]` is the reference clock.
    pub fn with_reference(values: Vec<BigRational>) -> Valuation {
        assert!(!values.is_empty() && values[0].is_zero(), "u(x0) must be 0");
        assert!(
            values.iter().all(|v| !v.is_negative()),
            "clocks are nonnegative: {values:?}"
        );
        Valuation { values }
    }

    /// Integer-valued clocks.
    pub fn from_integers(clocks: &[i64]) -> Valuation {
        Valuation::new(
            clocks
                .iter()
                .map(|&c| BigRational::from_integer(c.into()))
                .collect(),
        )
    }

    /// Clocks given as `(numerator, denominator)` pairs.
    pub fn from_ratios(clocks: &[(i64, i64)]) -> Valuation {
        Valuation::new(
            clocks
                .iter()
                .map(|&(p, q)| BigRational::new(p.into(), q.into()))
                .collect(),
        )
    }

    /// Number of actual clocks.
    pub fn variables(&self) -> usize {
        self.values.len() - 1
    }

    /// `u(xᵢ)`; index 0 is the reference clock (always 0).
    pub fn value(&self, i: usize) -> &BigRational {
        &self.values[i]
    }

    /// All values, reference clock first.
    pub fn values(&self) -> &[BigRational] {
        &self.values
    }

    /// `u[x := v]`. Panics if `x == 0` or `v < 0`.
    pub fn with_value(&self, x: usize, v: BigRational) -> Valuation {
        assert!(x != 0, "cannot assign the reference clock");
        let mut values = self.values.clone();
        values[x] = v;
        Valuation::with_reference(values)
    }

    /// `u + t` on every actual clock. Panics if a value becomes negative.
    pub fn shifted(&self, t: &BigRational) -> Valuation {
        let mut values = self.values.clone();
        for v in values.iter_mut().skip(1) {
            *v += t;
        }
        Valuation::with_reference(values)
    }

    /// `u ⊨ g`. Panics if `g` names a clock outside `u`.
    pub fn satisfies(&self, g: &OracleConstraint) -> bool {
        g.bound.sat(&(&self.values[g.i] - &self.values[g.j]))
    }

    /// `u ⊨ g` for every `g`.
    pub fn satisfies_all(&self, cs: &[OracleConstraint]) -> bool {
        cs.iter().all(|g| self.satisfies(g))
    }

    /// `u ⊨ xᵢ − xⱼ ⋈ m[i][j]` for every entry of a (possibly unclosed)
    /// matrix of matching dimension.
    pub fn satisfies_matrix(&self, m: &Matrix) -> bool {
        assert_eq!(m.len(), self.values.len(), "matrix dimension mismatch");
        m.iter().enumerate().all(|(i, row)| {
            row.iter()
                .enumerate()
                .all(|(j, b)| b.sat(&(&self.values[i] - &self.values[j])))
        })
    }
}

impl fmt::Display for Valuation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, v) in self.values.iter().enumerate().skip(1) {
            if i > 1 {
                write!(f, ", ")?;
            }
            write!(f, "x{i} = {v}")?;
        }
        write!(f, ")")
    }
}

/// An exact interval of rationals with optional strict or weak endpoints.
#[derive(Clone, Debug)]
pub struct Interval {
    lower: Option<(BigRational, Strictness)>,
    upper: Option<(BigRational, Strictness)>,
}

impl Interval {
    /// `(−∞, ∞)`.
    pub fn unbounded() -> Interval {
        Interval {
            lower: None,
            upper: None,
        }
    }

    /// Intersect with `t > v` (if `strict`) or `t ≥ v`.
    pub fn at_least(&mut self, v: BigRational, strict: bool) {
        let s = strictness(strict);
        let tighter = match &self.lower {
            None => true,
            Some((w, ws)) => {
                v > *w || (v == *w && s == Strictness::Strict && *ws == Strictness::Weak)
            }
        };
        if tighter {
            self.lower = Some((v, s));
        }
    }

    /// Intersect with `t < v` (if `strict`) or `t ≤ v`.
    pub fn at_most(&mut self, v: BigRational, strict: bool) {
        let s = strictness(strict);
        let tighter = match &self.upper {
            None => true,
            Some((w, ws)) => {
                v < *w || (v == *w && s == Strictness::Strict && *ws == Strictness::Weak)
            }
        };
        if tighter {
            self.upper = Some((v, s));
        }
    }

    /// Some element of the interval, or `None` if it is empty.
    pub fn pick(&self) -> Option<BigRational> {
        let one = BigRational::from_integer(BigInt::from(1));
        match (&self.lower, &self.upper) {
            (None, None) => Some(BigRational::zero()),
            (Some((lo, Strictness::Weak)), None) => Some(lo.clone()),
            (Some((lo, Strictness::Strict)), None) => Some(lo + one),
            (None, Some((hi, Strictness::Weak))) => Some(hi.clone()),
            (None, Some((hi, Strictness::Strict))) => Some(hi - one),
            (Some((lo, ls)), Some((hi, hs))) => {
                if lo < hi {
                    Some((lo + hi) / BigRational::from_integer(BigInt::from(2)))
                } else if lo == hi && *ls == Strictness::Weak && *hs == Strictness::Weak {
                    Some(lo.clone())
                } else {
                    None
                }
            }
        }
    }

    /// True if the interval contains no rational.
    pub fn is_empty(&self) -> bool {
        self.pick().is_none()
    }
}

fn strictness(strict: bool) -> Strictness {
    if strict {
        Strictness::Strict
    } else {
        Strictness::Weak
    }
}

/// Decides `∃t ≥ 0. v(t) ∈ γ(m)` exactly, where `vᵢ(t) = offsets[i] +
/// slopes[i]·t` (index 0 must be the constant 0) and `γ` includes `v ≥ 0`.
/// `m` need not be canonical.
pub fn exists_t(m: &Matrix, offsets: &[BigRational], slopes: &[i64]) -> bool {
    let d = m.len();
    assert!(
        offsets.len() == d && slopes.len() == d,
        "dimension mismatch"
    );
    assert!(offsets[0].is_zero() && slopes[0] == 0, "x0 is fixed at 0");
    let mut t = Interval::unbounded();
    t.at_least(BigRational::zero(), false);
    // Adds `slope·t + rest ⋈ c`; returns false if it fails independently of t.
    let mut add = |slope: i64, rest: BigRational, bound: &ExactBound| -> bool {
        let Some(c) = bound.constant() else {
            return true;
        };
        if slope == 0 {
            return bound.sat(&rest);
        }
        let rhs = BigRational::from_integer(c.clone()) - rest;
        let strict = bound.is_strict();
        // Dividing by a negative slope flips the direction.
        match slope.signum() {
            1 => {
                t.at_most(rhs / BigRational::from_integer(slope.into()), strict);
                true
            }
            _ => {
                t.at_least(rhs / BigRational::from_integer(slope.into()), strict);
                true
            }
        }
    };
    for i in 1..d {
        // vᵢ ≥ 0  ⟺  −vᵢ ≤ 0
        if !add(-slopes[i], -offsets[i].clone(), &ExactBound::le_zero()) {
            return false;
        }
    }
    for i in 0..d {
        for j in 0..d {
            if !add(slopes[i] - slopes[j], &offsets[i] - &offsets[j], &m[i][j]) {
                return false;
            }
        }
    }
    !t.is_empty()
}

/// `u ∈ { v + t | v ∈ γ(D), t ≥ 0 }` (S§5.3), decided without closure.
pub fn in_future_image(d: &OracleDbm, u: &Valuation) -> bool {
    let Some(m) = d.matrix() else {
        return false;
    };
    // v = u − t on every actual clock.
    let slopes: Vec<i64> = (0..d.dimension())
        .map(|i| if i == 0 { 0 } else { -1 })
        .collect();
    exists_t(m, u.values(), &slopes)
}

/// `u ∈ { v ≥ 0 | ∃t ≥ 0. v + t ∈ γ(D) }` (past), decided without closure.
pub fn in_past_image(d: &OracleDbm, u: &Valuation) -> bool {
    let Some(m) = d.matrix() else {
        return false;
    };
    // u + t on every actual clock.
    let slopes: Vec<i64> = (0..d.dimension())
        .map(|i| if i == 0 { 0 } else { 1 })
        .collect();
    exists_t(m, u.values(), &slopes)
}

/// `u ∈ { v[x := t] | v ∈ γ(D), t ≥ 0 }` (S§5.5), decided without closure.
///
/// `u` is in the image iff some `t ≥ 0` puts `u[x := t]` into `γ(D)`.
pub fn in_free_image(d: &OracleDbm, x: usize, u: &Valuation) -> bool {
    let Some(m) = d.matrix() else {
        return false;
    };
    let mut offsets = u.values().to_vec();
    offsets[x] = BigRational::zero();
    let mut slopes = vec![0; d.dimension()];
    slopes[x] = 1;
    exists_t(m, &offsets, &slopes)
}

/// `u ∈ { v[x := c] | v ∈ γ(D) }` (S§5.4), decided without closure.
pub fn in_reset_image(d: &OracleDbm, x: usize, c: &BigInt, u: &Valuation) -> bool {
    *u.value(x) == BigRational::from_integer(c.clone()) && in_free_image(d, x, u)
}
