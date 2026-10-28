//! Exact canonical-or-empty zones and the reference operations of S§5.
//!
//! Every result is produced by [`OracleDbm::close`], a literal transcription
//! of S§4 (`close`): impose nonnegativity, tighten the diagonal, run textbook
//! Floyd–Warshall to completion, then test the diagonal. Operations first
//! build the raw matrix given by the spec's formula and then close it; there
//! are no incremental closures.

use std::fmt;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use super::bound::{ExactBound, Matrix, parse_matrix};
use super::valuation::{Interval, Valuation};

/// The constraint `xᵢ − xⱼ ⋈ c` (S§2.2). Index 0 is the reference clock.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct OracleConstraint {
    /// Row index `i`.
    pub i: usize,
    /// Column index `j`.
    pub j: usize,
    /// The bound on `xᵢ − xⱼ`.
    pub bound: ExactBound,
}

impl OracleConstraint {
    /// `xᵢ − xⱼ ⋈ bound`.
    pub fn new(i: usize, j: usize, bound: ExactBound) -> OracleConstraint {
        OracleConstraint { i, j, bound }
    }

    /// `xᵢ − xⱼ ≤ c`.
    pub fn le(i: usize, j: usize, c: impl Into<BigInt>) -> OracleConstraint {
        OracleConstraint::new(i, j, ExactBound::le(c))
    }

    /// `xᵢ − xⱼ < c`.
    pub fn lt(i: usize, j: usize, c: impl Into<BigInt>) -> OracleConstraint {
        OracleConstraint::new(i, j, ExactBound::lt(c))
    }

    /// The complement constraint, `xⱼ − xᵢ ⋈' −c`; `None` for an `∞` bound,
    /// whose complement is empty.
    pub fn negated(&self) -> Option<OracleConstraint> {
        Some(OracleConstraint::new(self.j, self.i, self.bound.negate()?))
    }
}

impl fmt::Display for OracleConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{} - x{} {}", self.i, self.j, self.bound)
    }
}

/// Argument errors. The oracle computes exactly, so it has no
/// `Range` error; see [`super::compare::classify_range`] for the production
/// range contract.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum OracleError {
    /// Two operands disagree on the number of variables.
    DimensionMismatch {
        /// Variables of the receiver.
        expected: usize,
        /// Variables of the other operand.
        found: usize,
    },
    /// A clock index greater than the number of variables.
    ClockOutOfRange {
        /// The offending index.
        clock: usize,
        /// Variables of the DBM.
        variables: usize,
    },
    /// Reset or free on index 0. The production API cannot express this
    /// (`Variable` excludes 0), so differential tests never expect it.
    ReferenceClock,
    /// Reset to a negative value (S§5.4).
    NegativeConstant {
        /// The rejected value.
        value: BigInt,
    },
    /// A negative ExtraM ceiling. The production upper limit
    /// (`MAX_CONSTANT`) is a range restriction the oracle does not model.
    InvalidMaxBounds {
        /// The 1-based variable index.
        variable: usize,
        /// The rejected value.
        value: BigInt,
    },
}

/// A zone over `variables` nonnegative real clocks, always canonical or
/// empty (S§3). The empty zone remembers its dimension.
///
/// Fields are private and every constructor goes through `close`, so the
/// derived `PartialEq` is semantic equality (Theorem 3.1).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct OracleDbm {
    variables: usize,
    /// `None` is `∅_d`; otherwise a canonical `d × d` matrix.
    matrix: Option<Matrix>,
}

impl OracleDbm {
    // ----- constructors (S§5.1) -----

    /// `{ u | ∀i. u(xᵢ) = 0 }`.
    pub fn zero(variables: usize) -> OracleDbm {
        let d = variables + 1;
        OracleDbm::close(variables, vec![vec![ExactBound::le_zero(); d]; d])
    }

    /// `{ u | u ≥ 0 }`.
    pub fn universe(variables: usize) -> OracleDbm {
        let d = variables + 1;
        let mut m = vec![vec![ExactBound::Infinity; d]; d];
        for j in 0..d {
            m[0][j] = ExactBound::le_zero();
            m[j][j] = ExactBound::le_zero();
        }
        OracleDbm::close(variables, m)
    }

    /// `∅_{variables+1}`.
    pub fn empty(variables: usize) -> OracleDbm {
        OracleDbm {
            variables,
            matrix: None,
        }
    }

    /// The zone denoted by an arbitrary (not necessarily canonical) `d × d`
    /// matrix, `γ(raw)` over nonnegative valuations. Panics if `raw` is not
    /// square of dimension `variables + 1`.
    pub fn from_matrix(variables: usize, raw: Matrix) -> OracleDbm {
        let d = variables + 1;
        assert_eq!(raw.len(), d, "matrix has {} rows, expected {d}", raw.len());
        for (i, row) in raw.iter().enumerate() {
            assert_eq!(
                row.len(),
                d,
                "row {i} has {} entries, expected {d}",
                row.len()
            );
        }
        OracleDbm::close(variables, raw)
    }

    /// [`OracleDbm::from_matrix`] on a [`parse_matrix`] literal.
    pub fn parse(rows: &[&str]) -> OracleDbm {
        let m = parse_matrix(rows);
        OracleDbm::from_matrix(m.len() - 1, m)
    }

    /// `universe(variables) ∧ cs`.
    pub fn from_constraints(
        variables: usize,
        cs: &[OracleConstraint],
    ) -> Result<OracleDbm, OracleError> {
        OracleDbm::universe(variables).constrain_all(cs)
    }

    // ----- accessors -----

    /// Number of actual clocks `n`.
    pub fn variables(&self) -> usize {
        self.variables
    }

    /// Matrix dimension `n + 1`.
    pub fn dimension(&self) -> usize {
        self.variables + 1
    }

    /// True for `∅_d`.
    pub fn is_empty(&self) -> bool {
        self.matrix.is_none()
    }

    /// The canonical matrix; `None` for `∅_d`.
    pub fn matrix(&self) -> Option<&Matrix> {
        self.matrix.as_ref()
    }

    /// The canonical entry `(i, j)`; `None` for `∅_d`. Panics if out of range.
    pub fn entry(&self, i: usize, j: usize) -> Option<&ExactBound> {
        self.matrix.as_ref().map(|m| &m[i][j])
    }

    /// Largest absolute value of a finite constant; zero for `∅_d`.
    pub fn max_abs_constant(&self) -> BigInt {
        let mut max = BigInt::zero();
        for row in self.matrix.iter().flatten() {
            for c in row.iter().filter_map(ExactBound::constant) {
                if c.abs() > max {
                    max = c.abs();
                }
            }
        }
        max
    }

    // ----- closure (S§4) -----

    /// `close` of S§4 on a raw matrix.
    fn close(variables: usize, mut m: Matrix) -> OracleDbm {
        let d = variables + 1;
        let le0 = ExactBound::le_zero();
        // Step 0: γ ranges over nonnegative valuations only, so `x₀ − xᵢ ≤ 0`
        // holds throughout γ and may be added (establishes WInv).
        for i in 1..d {
            m[0][i] = m[0][i].clone().min(le0.clone());
        }
        // Step 1: `xᵢ − xᵢ = 0` always satisfies `Le 0`.
        for i in 0..d {
            m[i][i] = m[i][i].clone().min(le0.clone());
        }
        // Step 2: Floyd–Warshall, run to completion (constants are unbounded,
        // so there is nothing to gain from an early exit).
        for k in 0..d {
            for i in 0..d {
                for j in 0..d {
                    let via_k = m[i][k].add(&m[k][j]);
                    if via_k < m[i][j] {
                        m[i][j] = via_k;
                    }
                }
            }
        }
        // Step 3: a negative diagonal entry means the zone is empty (S§3.2).
        if (0..d).any(|i| m[i][i] < le0) {
            OracleDbm::empty(variables)
        } else {
            OracleDbm {
                variables,
                matrix: Some(m),
            }
        }
    }

    // ----- argument checks -----

    fn check_clock(&self, clock: usize) -> Result<(), OracleError> {
        if clock > self.variables {
            Err(OracleError::ClockOutOfRange {
                clock,
                variables: self.variables,
            })
        } else {
            Ok(())
        }
    }

    fn check_variable(&self, x: usize) -> Result<(), OracleError> {
        if x == 0 {
            return Err(OracleError::ReferenceClock);
        }
        self.check_clock(x)
    }

    fn check_dimension(&self, other_variables: usize) -> Result<(), OracleError> {
        if self.variables != other_variables {
            Err(OracleError::DimensionMismatch {
                expected: self.variables,
                found: other_variables,
            })
        } else {
            Ok(())
        }
    }

    // ----- constraints and intersection (S§5.2) -----

    /// `γ(D) ∩ ⟦g⟧`.
    pub fn constrain(&self, g: &OracleConstraint) -> Result<OracleDbm, OracleError> {
        self.constrain_all(std::slice::from_ref(g))
    }

    /// `γ(D) ∩ ⋂ₘ ⟦gₘ⟧`. All indices are validated first.
    pub fn constrain_all(&self, cs: &[OracleConstraint]) -> Result<OracleDbm, OracleError> {
        for g in cs {
            self.check_clock(g.i)?;
            self.check_clock(g.j)?;
        }
        let Some(m) = &self.matrix else {
            return Ok(self.clone());
        };
        let mut raw = m.clone();
        for g in cs {
            raw[g.i][g.j] = raw[g.i][g.j].clone().min(g.bound.clone());
        }
        Ok(OracleDbm::close(self.variables, raw))
    }

    /// `γ(D) ∩ γ(E)`: entrywise `min`, then close (Isabelle `And`).
    pub fn intersect(&self, other: &OracleDbm) -> Result<OracleDbm, OracleError> {
        self.check_dimension(other.variables)?;
        let (Some(a), Some(b)) = (&self.matrix, &other.matrix) else {
            return Ok(OracleDbm::empty(self.variables));
        };
        let raw = a
            .iter()
            .zip(b)
            .map(|(ra, rb)| {
                ra.iter()
                    .zip(rb)
                    .map(|(x, y)| x.clone().min(y.clone()))
                    .collect()
            })
            .collect();
        Ok(OracleDbm::close(self.variables, raw))
    }

    // ----- temporal operations (S§5.3–5.5) -----

    /// `{ u + t | u ∈ γ(D), t ≥ 0 }`: drop the upper bounds `D[i][0]`.
    pub fn future(&self) -> OracleDbm {
        let Some(m) = &self.matrix else {
            return self.clone();
        };
        let mut raw = m.clone();
        for row in raw.iter_mut().skip(1) {
            row[0] = ExactBound::Infinity;
        }
        OracleDbm::close(self.variables, raw)
    }

    /// `{ v ≥ 0 | ∃t ≥ 0. v + t ∈ γ(D) }`: relax the lower bounds `D[0][j]`
    /// to `≤ 0` and close again (full closure, independent of the
    /// production row-minimum kernel).
    pub fn past(&self) -> OracleDbm {
        let Some(m) = &self.matrix else {
            return self.clone();
        };
        let mut raw = m.clone();
        for entry in raw[0].iter_mut().skip(1) {
            *entry = ExactBound::le_zero();
        }
        OracleDbm::close(self.variables, raw)
    }

    /// `{ u[x := c] | u ∈ γ(D) }` for `c ≥ 0` (Isabelle `reset_canonical`).
    pub fn reset(&self, x: usize, value: impl Into<BigInt>) -> Result<OracleDbm, OracleError> {
        let value = value.into();
        self.check_variable(x)?;
        if value.is_negative() {
            return Err(OracleError::NegativeConstant { value });
        }
        let Some(m) = &self.matrix else {
            return Ok(self.clone());
        };
        let mut raw = m.clone();
        for j in 0..self.dimension() {
            raw[x][j] = ExactBound::le(value.clone()).add(&m[0][j]);
            raw[j][x] = ExactBound::le(-value.clone()).add(&m[j][0]);
        }
        raw[x][x] = ExactBound::le_zero();
        Ok(OracleDbm::close(self.variables, raw))
    }

    /// `reset(D, x, 0)`.
    pub fn reset_zero(&self, x: usize) -> Result<OracleDbm, OracleError> {
        self.reset(x, 0)
    }

    /// `{ u[x := t] | u ∈ γ(D), t ≥ 0 }`; the dimension is unchanged.
    pub fn free(&self, x: usize) -> Result<OracleDbm, OracleError> {
        self.check_variable(x)?;
        let Some(m) = &self.matrix else {
            return Ok(self.clone());
        };
        let mut raw = m.clone();
        for j in 0..self.dimension() {
            raw[x][j] = ExactBound::Infinity;
            raw[j][x] = m[j][0].clone();
        }
        raw[x][x] = ExactBound::le_zero();
        Ok(OracleDbm::close(self.variables, raw))
    }

    // ----- relations and queries (S§5.6–5.7) -----

    /// `γ(D) ⊆ γ(E)`.
    pub fn is_subset_of(&self, other: &OracleDbm) -> Result<bool, OracleError> {
        self.check_dimension(other.variables)?;
        Ok(match (&self.matrix, &other.matrix) {
            (None, _) => true,
            (Some(_), None) => false,
            (Some(a), Some(b)) => a
                .iter()
                .flatten()
                .zip(b.iter().flatten())
                .all(|(x, y)| x <= y),
        })
    }

    /// `γ(D) ⊆ ⟦g⟧`; `true` on `∅_d`.
    pub fn entails(&self, g: &OracleConstraint) -> Result<bool, OracleError> {
        self.check_clock(g.i)?;
        self.check_clock(g.j)?;
        Ok(match &self.matrix {
            None => true,
            Some(m) => m[g.i][g.j] <= g.bound,
        })
    }

    /// `γ(D) ∩ ⟦g⟧ ≠ ∅`; `false` on `∅_d`.
    pub fn intersects_constraint(&self, g: &OracleConstraint) -> Result<bool, OracleError> {
        self.check_clock(g.i)?;
        self.check_clock(g.j)?;
        Ok(match &self.matrix {
            None => false,
            Some(m) => m[g.j][g.i].add(&g.bound) >= ExactBound::le_zero(),
        })
    }

    /// The tightest `b` with `γ(D) ⊆ ⟦(i, j, b)⟧`; `None` on `∅_d`.
    pub fn difference_bound(&self, i: usize, j: usize) -> Result<Option<ExactBound>, OracleError> {
        self.check_clock(i)?;
        self.check_clock(j)?;
        Ok(self.entry(i, j).cloned())
    }

    // ----- ExtraM (S§5.8) -----

    /// `close(norm(D, k, n))` with Isabelle's `norm`, `k(0) = 0` and
    /// `k(i) = ceilings[i − 1]`.
    pub fn extrapolate_max(&self, ceilings: &[BigInt]) -> Result<OracleDbm, OracleError> {
        if let Some((index, value)) = ceilings.iter().enumerate().find(|(_, v)| v.is_negative()) {
            return Err(OracleError::InvalidMaxBounds {
                variable: index + 1,
                value: value.clone(),
            });
        }
        self.check_dimension(ceilings.len())?;
        let Some(m) = &self.matrix else {
            return Ok(self.clone());
        };
        let k = |i: usize| {
            if i == 0 {
                BigInt::zero()
            } else {
                ceilings[i - 1].clone()
            }
        };
        let d = self.dimension();
        let mut raw = m.clone();
        for i in 0..d {
            for j in 0..d {
                raw[i][j] = if i == j {
                    norm_diag(&m[i][j])
                } else {
                    // Isabelle uses k i = 0 for the reference row/column.
                    let ub = k(i);
                    let lb = -k(j);
                    norm_lower(norm_upper(m[i][j].clone(), ub), lb)
                };
            }
        }
        Ok(OracleDbm::close(self.variables, raw))
    }

    // ----- semantic test aids -----

    /// `u ∈ γ(D)`, checked directly on the matrix entries. Panics if `u` has a
    /// different number of variables.
    pub fn contains(&self, u: &Valuation) -> bool {
        assert_eq!(
            u.variables(),
            self.variables,
            "valuation dimension mismatch"
        );
        match &self.matrix {
            None => false,
            Some(m) => u.satisfies_matrix(m),
        }
    }

    /// Some exact point of `γ(D)`; `None` iff `D` is empty.
    ///
    /// Clocks are fixed one at a time inside the interval allowed by the
    /// already fixed ones. Canonicity guarantees the interval is nonempty;
    /// this panics otherwise, which would be an oracle bug. Callers should
    /// still check the witness against the *raw* inputs.
    pub fn witness(&self) -> Option<Valuation> {
        let m = self.matrix.as_ref()?;
        let mut values = vec![BigRational::zero()];
        for k in 1..self.dimension() {
            let mut interval = Interval::unbounded();
            for (j, v) in values.iter().enumerate() {
                // x_k − v_j ⋈ m[k][j]  ⇒  x_k ⋈ v_j + c
                if let Some(c) = m[k][j].constant() {
                    interval.at_most(
                        v + BigRational::from_integer(c.clone()),
                        m[k][j].is_strict(),
                    );
                }
                // v_j − x_k ⋈ m[j][k]  ⇒  x_k ⋗ v_j − c
                if let Some(c) = m[j][k].constant() {
                    interval.at_least(
                        v - BigRational::from_integer(c.clone()),
                        m[j][k].is_strict(),
                    );
                }
            }
            let v = interval.pick().unwrap_or_else(|| {
                panic!("oracle bug: no value for x{k} extends {values:?}\n{self}")
            });
            values.push(v);
        }
        Some(Valuation::with_reference(values))
    }

    /// A point of `γ(D) \ γ(E)`, or `None` if `γ(D) ⊆ γ(E)`. Built from the
    /// first entry with `D[i][j] ≻ E[i][j]` as a witness of `D ∧ ¬(i, j, E[i][j])`.
    pub fn subset_counterexample(&self, other: &OracleDbm) -> Option<Valuation> {
        assert_eq!(self.variables, other.variables, "dimension mismatch");
        let a = self.matrix.as_ref()?;
        let Some(b) = &other.matrix else {
            return self.witness();
        };
        let d = self.dimension();
        let (i, j) = (0..d)
            .flat_map(|i| (0..d).map(move |j| (i, j)))
            .find(|&(i, j)| a[i][j] > b[i][j])?;
        let outside = OracleConstraint::new(i, j, b[i][j].clone())
            .negated()
            .expect("a bound strictly tighter than another is finite");
        let w = self
            .constrain(&outside)
            .expect("indices are in range")
            .witness()
            .unwrap_or_else(|| panic!("oracle bug: D[{i}][{j}] is not tight\n{self}"));
        Some(w)
    }
}

/// `norm_upper e t = (if Le t ≺ e then ∞ else e)`.
fn norm_upper(e: ExactBound, t: BigInt) -> ExactBound {
    if ExactBound::le(t) < e {
        ExactBound::Infinity
    } else {
        e
    }
}

/// `norm_lower e t = (if e ≺ Lt t then Lt t else e)`.
fn norm_lower(e: ExactBound, t: BigInt) -> ExactBound {
    let lt = ExactBound::lt(t);
    if e < lt { lt } else { e }
}

/// `norm_diag e = (if e ≺ Le 0 then Lt 0 else if e = Le 0 then e else ∞)`.
fn norm_diag(e: &ExactBound) -> ExactBound {
    let le0 = ExactBound::le_zero();
    if *e < le0 {
        ExactBound::lt(0)
    } else if *e == le0 {
        le0
    } else {
        ExactBound::Infinity
    }
}

/// Writes a labelled matrix (`x0` is the reference clock).
pub(crate) fn write_matrix(f: &mut fmt::Formatter<'_>, m: &Matrix) -> fmt::Result {
    let width = m
        .iter()
        .flatten()
        .map(|b| b.to_string().len())
        .max()
        .unwrap_or(0)
        .max(3);
    write!(f, "{:>4}", "")?;
    for j in 0..m.len() {
        write!(f, "  {:>width$}", format!("x{j}"))?;
    }
    writeln!(f)?;
    for (i, row) in m.iter().enumerate() {
        write!(f, "{:>4}", format!("x{i}"))?;
        for b in row {
            write!(f, "  {b:>width$}")?;
        }
        writeln!(f)?;
    }
    Ok(())
}

impl fmt::Display for OracleDbm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.matrix {
            None => writeln!(
                f,
                "empty zone (variables = {}, dimension = {})",
                self.variables,
                self.dimension()
            ),
            Some(m) => {
                writeln!(f, "zone (variables = {}):", self.variables)?;
                write_matrix(f, m)
            }
        }
    }
}
