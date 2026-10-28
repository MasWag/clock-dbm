//! Comparing zones and querying clock constraints.
//!
//! [`Dbm::entails`](crate::Dbm::entails) checks whether **every** valuation
//! satisfies a constraint, whereas
//! [`Dbm::intersects_constraint`](crate::Dbm::intersects_constraint) asks
//! whether **some** valuation satisfies it. The former is true on an empty
//! zone (vacuously), and the latter is false.
//!
//! [`Dbm::is_subset_of`](crate::Dbm::is_subset_of) tests inclusion of zones;
//! [`Dbm::try_intersect`](crate::Dbm::try_intersect) constructs their
//! intersection; and [`Dbm::difference_bound`](crate::Dbm::difference_bound)
//! returns a tight bound on a clock difference.

// Source-level implementation and proof notes (not part of public API Rustdoc).
// Relations and queries: intersection, inclusion and constraint queries.
//
// Notation: `d` is the matrix dimension including reference clock zero;
// `γ(D)` is the set of nonnegative-real valuations represented by `D`,
// `⟦g⟧` is the set satisfying guard `g`, and `∅_d` is the empty
// zone of dimension `d`. `Le c` means `<= c`, `Lt c` means `< c`;
// `a ≼ b` means `a` is at least as tight as `b`, and `a ≺ b` means
// strictly tighter.
//
// Throughout, `D` and `E` are public DBMs, so each is `∅_d` or canonical
// and nonempty (the public invariant), and `g = (i, j, b)` is the
// constraint `xᵢ − xⱼ ⋈ b`. Every method validates its arguments first
// (dimension, then clock indices), also on empty zones, and only then looks
// at emptiness. An argument error is never reported as `false`, and no query
// returns `Err(Range)`.
//
// # Queries: closed forms on canonical matrices
//
// | Method | `∅_d` | Canonical nonempty `D` | Cost |
// |---|---|---|---|
// | `is_subset_of(D, E)` | `true` | `E = ∅_d`: `false`; else `∀ i,j. D[i][j] ≼ E[i][j]` | `O(d²)` |
// | `entails(D, g)` | `true` | `D[i][j] ≼ b` | `O(1)` |
// | `intersects_constraint(D, g)` | `false` | `¬(b + D[j][i] ≺ Le 0)` | `O(1)` |
// | `difference_bound(D, i, j)` | `None` | `Some(D[i][j])` (`∞` if unbounded) | `O(1)` |
//
// None of them closes, copies or allocates.
//
// - **Inclusion**: for a canonical, nonempty `D`, `γ(D) ⊆ γ(E)`
//   iff `D ≤ E` entrywise. Only `D` needs to be
//   canonical; `E` is canonical anyway. The scan is `Dbm::entries_le`.
// - **Entailment and `difference_bound`**: each entry of a canonical,
//   nonempty DBM is the tightest bound of its difference over the zone
//   (by tightness of canonical entries). So `γ(D) ⊆ ⟦g⟧` iff `D[i][j] ≼ b`.
// - **Constraint intersection**: `D ∧ g` is empty iff its closure finds a
//   negative cycle. In a canonical `D`, the only new cycle is `i → j → i`
//   through the new edge, so the test is the
//   contradiction test of constraint insertion, `ops::constraints::
//   below_le_zero`. The sum is compared exactly and never
//   stored, so an unrepresentable sum is not an error.
//
// # Intersection: pointwise minimum, then closure over the touched clocks
//
// `try_intersect` moves `self`'s storage into a working matrix `W` and
// takes the entrywise minimum with `other`:
//
// 1. **Minimum** (`Matrix::meet`): every entry that `E` strictly tightens
//    marks both of its clocks as touched. If a tightened entry contradicts
//    the current opposite entry (`W[i][j] + W[j][i] ≺ Le 0`, the exact test
//    `below_le_zero`), the result is `∅_d` at once: a negative 2-cycle.
// 2. **Closure over the touched clocks** (`Matrix::close_pivots`):
//    Floyd–Warshall with only the touched clocks as pivots, each row relaxed
//    by the proved, vectorized `Matrix::relax_row`. A negative diagonal
//    gives `∅_d`.
//
// *Why the restricted closure is the closure.* Call an entry of `W`
// *changed* if `E` tightened it; its endpoints are touched. Take any walk
// in `W`. A run of consecutive unchanged edges has weight at least the
// entry of the canonical `D` between its ends, which is at least `W`'s
// entry there; so it can be replaced by that single edge without
// increasing the weight. After this, no two consecutive edges are
// unchanged, so every intermediate vertex is an endpoint of a changed edge,
// i.e. touched. Floyd–Warshall over any pivot set computes the shortest
// walks whose intermediate vertices are pivots, so it yields the closure.
// A negative cycle of `W` contains a changed edge (cycles of `D` are
// nonnegative), so it reduces the same way to a negative cycle through
// touched pivots, and a diagonal entry becomes negative. The minimum of two
// canonical matrices is **not** canonical in general, so some closure is
// required; with nothing touched, `W = D` already is canonical.
//
// *As proved, without walks:*
// - `proof::min_closed`: `W` already satisfies the triangle inequality
//   through every untouched clock;
// - `proof::pivot_keep`: a full pivot step keeps every triangle that
//   holds and adds its own.
//
// So `Matrix::close_pivots` ends with the triangle inequality through every
// clock, i.e. canonical. Each relaxation preserves the zone, so a negative
// diagonal means emptiness. By `canonical_unique`, the result equals the
// full closure.
//
// Cost: `O(d²)` for the minimum plus `O(p·d²)` for `p` touched clocks (a
// guard-like `E` touches few clocks). The storage is reused, and the
// touched flags live in the `Workspace`: no allocation once the workspace
// has grown. An empty operand short-circuits after the dimension check.
//
// # Equality and hashing
//
// `PartialEq`/`Eq`/`Hash` on `Dbm` are those of `dbm.rs`: structural on
// the canonical storage, which is semantic equality.
//
// - **Machine-checked:** `Dbm::eq_semantic` proves that `==` holds
//   iff the two DBMs have the same number of variables and denote the same
//   zone. Different dimensions are unequal, also for empty zones.
// - **By construction, not machine-checked:** `Hash` is derived over the
//   same fields that `==` compares, so equal DBMs hash alike.
// - **Outside the verified subset:** `std::hash::Hasher` has no Creusot
//   specification. No hashing abstraction or trusted specification is
//   added for it.
//
// # Verification status
//
// Every method of this module is machine-checked with Creusot v0.14.0 on
// the shipped code, with termination. The same holds for the kernels
// `Dbm::entries_le`, `Matrix::meet` and `Matrix::close_pivots`, and for
// `Workspace::reset_touched`. The contracts are stated over nonnegative real
// valuations (`Dbm::zone`):
//
// - `is_subset_of`: `γ(self) ⊆ γ(other)`;
// - `entails` / `intersects_constraint`: universal and existential
//   satisfaction of the constraint;
// - `difference_bound`: the canonical entry, the tightest bound (`∞`
//   included), and `None` exactly on `∅_d`;
// - `try_intersect`: `γ(self) ∩ γ(other)`, with `∅_d` exactly when it is
//   empty, through negative cycles of any length;
// - errors: the exact argument errors (checked before emptiness), and
//   `Range` only with its provenance (`proof::mrange_failure`).
//
// The lemmas are in `relations/proof.rs` (`entry_tight`,
// `subset_pointwise`, `meets`) and `dbm/proof.rs` (`min_closed`,
// `pivot_keep`, `relax_row_full`). They rest on `tight`, the `edge` lemmas
// and `canonical_unique`. See `verification/PROOF_STATUS.md`. The
// exact-oracle tests in `relations/tests.rs` remain as regression tests.

// `?` is not a terminating call for Creusot; keep the style of `dbm.rs`.
#![allow(clippy::question_mark)]

use crate::bounds::{Bound, Clock, Constraint};
#[cfg(creusot)]
use crate::bounds::{order_refines, sat};
#[cfg(creusot)]
use crate::dbm::Matrix;
use crate::dbm::{Dbm, Workspace, tighter};
use crate::error::Error;
use crate::ops::constraints::below_le_zero;
#[cfg(creusot)]
use crate::ops::constraints::clock_error;
#[cfg(creusot)]
use crate::ops::constraints::proof::{csat, valid};
use creusot_std::prelude::*;

impl Dbm {
    /// Returns the zone of valuations that belong to **both** input zones.
    ///
    /// The inputs must have the same number of actual clocks. An empty
    /// intersection is a successful **empty zone**, not an error.
    /// On success the result is canonical or empty, and no partial update
    /// becomes visible.
    ///
    /// When either input is empty, the result is empty. The `ws`
    /// parameter does not affect the result.
    ///
    /// # Errors
    ///
    /// - [`Error::DimensionMismatch`] if `other` has a different clock
    ///   count, even if either zone is empty;
    /// - [`Error::Range`] if closure needs a finite bound beyond the
    ///   supported integer range. This is not an empty-zone result.
    ///
    /// # Complexity
    ///
    /// `O(d³)` time in the worst case for matrix dimension
    /// `d = self.dimension()`. An empty operand returns immediately.
    /// The workspace reuses scratch storage across calls.
    #[check(terminates)]
    #[ensures(match result {
        Ok(r) => other.variables_logic() == self.variables_logic()
            && r.variables_logic() == self.variables_logic()
            && forall<u: crate::dbm::proof::Val> r.zone(u) == (self.zone(u) && other.zone(u)),
        Err(e) => if other.variables_logic() != self.variables_logic() {
            match e {
                Error::DimensionMismatch { expected, found } =>
                    expected@ == self.variables_logic() && found@ == other.variables_logic(),
                _ => false,
            }
        } else {
            e == Error::Range && !self.is_empty_logic() && !other.is_empty_logic()
                && crate::dbm::proof::mrange_failure(
                    crate::dbm::proof::bmin_mat(self.mmat(), other.mmat()),
                    self.variables_logic() + 1)
        },
    })]
    // Exactness: when `self` is entrywise at most `other`, the meet
    // tightens nothing, no pivot is closed and the result is not `Err`.
    #[ensures(other.variables_logic() == self.variables_logic()
        && !self.is_empty_logic() && !other.is_empty_logic()
        && (forall<i: Int, j: Int>
            0 <= i && i <= self.variables_logic() && 0 <= j && j <= self.variables_logic() ==>
                self.at(i, j).deep_model() <= other.at(i, j).deep_model())
        ==> match result { Ok(_) => true, Err(_) => false })]
    pub fn try_intersect(self, other: &Dbm, ws: &mut Workspace) -> Result<Dbm, Error> {
        match self.check_variables(other.variables()) {
            Ok(()) => {}
            Err(e) => return Err(e),
        }
        snapshot!(self.model());
        snapshot!(other.model());
        let min = snapshot!(crate::dbm::proof::bmin_mat(self.mmat(), other.mmat()));
        let empty = self.empty_like();
        if other.is_empty() {
            return Ok(empty);
        }
        let mut m = match self.into_matrix() {
            Some(m) => m,
            None => return Ok(empty),
        };
        let w0 = snapshot!(m);
        snapshot!(w0.model());
        ws.reset_touched(m.dimension());
        if !m.meet(other, &mut ws.touched) {
            return Ok(empty);
        }
        snapshot!(Matrix::meet_ready(*w0, *other, m, ws.touched@));
        let w1 = snapshot!(m);
        let r = m.close_pivots(&ws.touched);
        proof_assert!(match r {
            Err(_) => {
                w1.range_failure_model();
                crate::dbm::proof::mrange_failure_meq(w1.mmat(), *min, w1.dim_logic());
                true
            }
            Ok(_) => true,
        });
        r
    }
}

impl Dbm {
    /// Tests whether **every valuation of this zone** also belongs to
    /// `other`.
    ///
    /// An empty zone is a subset of every zone of the same clock count;
    /// a nonempty zone is not a subset of an empty zone.
    ///
    /// # Errors
    ///
    /// [`Error::DimensionMismatch`] if the two zones have different
    /// numbers of actual clocks, even when either zone is empty.
    ///
    /// # Complexity
    ///
    /// `O(d²)` time in the worst case for matrix dimension
    /// `d = self.dimension()`; empty-zone cases take `O(1)`.
    #[check(terminates)]
    #[ensures(match result {
        Ok(b) => other.variables_logic() == self.variables_logic()
            && b == forall<u: crate::dbm::proof::Val> self.zone(u) ==> other.zone(u),
        Err(e) => other.variables_logic() != self.variables_logic() && match e {
            Error::DimensionMismatch { expected, found } =>
                expected@ == self.variables_logic() && found@ == other.variables_logic(),
            _ => false,
        },
    })]
    pub fn is_subset_of(&self, other: &Dbm) -> Result<bool, Error> {
        match self.check_variables(other.variables()) {
            Ok(()) => {}
            Err(e) => return Err(e),
        }
        snapshot!(self.model());
        snapshot!(other.model());
        if self.is_empty() {
            Ok(true)
        } else if other.is_empty() {
            Ok(false)
        } else {
            let d = snapshot!(self.variables_logic() + 1);
            proof_assert!(forall<i: Int, j: Int> 0 <= i && i < *d && 0 <= j && j < *d ==> {
                order_refines(self.at(i, j), other.at(i, j));
                (self.at(i, j).deep_model() <= other.at(i, j).deep_model())
                    == self.mmat()[i][j].le(other.mmat()[i][j])
            });
            snapshot!(proof::subset_pointwise(self.mmat(), other.mmat(), *d));
            Ok(self.entries_le(other))
        }
    }

    /// Returns whether **every** valuation in this zone satisfies `c`.
    ///
    /// The result is `true` precisely when all nonnegative-real clock
    /// valuations allowed by this zone satisfy `c`. This is different
    /// from asking whether **some** valuation satisfies it; for that,
    /// use [`Dbm::intersects_constraint`]. An empty zone entails every
    /// well-formed constraint (vacuously).
    ///
    /// # Example
    ///
    /// ```
    /// use clock_dbm::{Clock, Constraint, Dbm};
    /// # fn main() -> Result<(), clock_dbm::Error> {
    /// let x = Clock::new(1).unwrap();
    /// let z = Dbm::universe(1)?
    ///     .try_constrain(Constraint::le(x, Clock::ZERO, 10)?)?;
    /// let x_below_five = Constraint::lt(x, Clock::ZERO, 5)?;
    /// assert!(!z.entails(&x_below_five)?);
    /// assert!(z.intersects_constraint(&x_below_five)?);
    /// assert!(z.entails(&Constraint::le(x, Clock::ZERO, 10)?)?);
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// # Errors
    ///
    /// [`Error::ClockOutOfRange`] if a clock of `c` is not a clock of this
    /// DBM, also when the DBM is empty.
    ///
    /// # Complexity
    ///
    /// `O(1)` time; the query does not build a new zone.

    #[check(terminates)]
    #[ensures(match result {
        Ok(b) => valid(*c, self.variables_logic())
            && b == forall<u: crate::dbm::proof::Val> self.zone(u) ==> csat(*c, u),
        Err(e) => !valid(*c, self.variables_logic()) && clock_error(*c, self.variables_logic(), e),
    })]
    pub fn entails(&self, c: &Constraint) -> Result<bool, Error> {
        let (i, j) = match self.check_constraint(*c) {
            Ok(ij) => ij,
            Err(e) => return Err(e),
        };
        snapshot!(self.model());
        if self.is_empty() {
            return Ok(true);
        }
        let e = self.entry(i, j);
        let b = c.bound();
        snapshot!(order_refines(e, b));
        snapshot!(proof::entry_tight(self.mmat(), self.variables_logic() + 1, i@, j@, b@));
        Ok(!tighter(b, e))
    }

    /// Tests whether **at least one valuation** in this zone satisfies
    /// the difference constraint `c`.
    ///
    /// Equivalently, this asks whether restricting the zone by `c` would
    /// produce a nonempty result. Unlike [`Dbm::entails`], which checks
    /// **every** valuation, this returns `false` on an empty zone.
    ///
    /// # Errors
    ///
    /// [`Error::ClockOutOfRange`] if a clock in `c` is not among this
    /// zone's clocks, even when the zone is empty.
    ///
    /// # Complexity
    ///
    /// `O(1)` time; the query does not build a new zone.
    #[check(terminates)]
    #[ensures(match result {
        Ok(b) => valid(*c, self.variables_logic())
            && b == exists<u: crate::dbm::proof::Val> self.zone(u) && csat(*c, u),
        Err(e) => !valid(*c, self.variables_logic()) && clock_error(*c, self.variables_logic(), e),
    })]
    pub fn intersects_constraint(&self, c: &Constraint) -> Result<bool, Error> {
        let (i, j) = match self.check_constraint(*c) {
            Ok(ij) => ij,
            Err(e) => return Err(e),
        };
        snapshot!(self.model());
        if self.is_empty() {
            return Ok(false);
        }
        snapshot!(proof::meets(self.mmat(), self.variables_logic() + 1, i@, j@, c@.2));
        Ok(!below_le_zero(c.bound(), self.entry(j, i)))
    }

    /// Returns the tightest bound on `clock i - clock j` that holds for
    /// **every valuation** of this zone.
    ///
    /// On a nonempty canonical zone this returns the corresponding
    /// stored difference bound. [`Bound::INFINITY`] means that the
    /// difference has no finite upper bound. For an empty zone, this
    /// returns `None`, since every bound is vacuously satisfied.
    ///
    /// # Errors
    ///
    /// [`Error::ClockOutOfRange`] if `i` or `j` is outside this
    /// zone's clock range (checking `i` first), even for an empty zone.
    ///
    /// # Complexity
    ///
    /// `O(1)` time.
    #[check(terminates)]
    #[ensures(match result {
        Ok(None) => i@ <= self.variables_logic() && j@ <= self.variables_logic()
            && self.is_empty_logic(),
        Ok(Some(b)) => i@ <= self.variables_logic() && j@ <= self.variables_logic()
            && !self.is_empty_logic() && b == self.at(i@, j@)
            && forall<c: crate::bounds::BoundModel> b@.le(c) ==
                forall<u: crate::dbm::proof::Val> self.zone(u) ==> sat(c, u[i@] - u[j@]),
        Err(e) => match e {
            Error::ClockOutOfRange { clock, variables } =>
                variables@ == self.variables_logic()
                    && if i@ > self.variables_logic() { clock@ == i@ }
                       else { j@ > self.variables_logic() && clock@ == j@ },
            _ => false,
        },
    })]
    pub fn difference_bound(&self, i: Clock, j: Clock) -> Result<Option<Bound>, Error> {
        let i = match self.check_clock(i) {
            Ok(i) => i,
            Err(e) => return Err(e),
        };
        let j = match self.check_clock(j) {
            Ok(j) => j,
            Err(e) => return Err(e),
        };
        snapshot!(self.model());
        if self.is_empty() {
            return Ok(None);
        }
        let b = self.entry(i, j);
        proof_assert!(forall<c: crate::bounds::BoundModel> {
            proof::entry_tight(self.mmat(), self.variables_logic() + 1, i@, j@, c);
            true
        });
        Ok(Some(b))
    }
}

#[cfg(creusot)]
pub(crate) mod proof;

#[cfg(test)]
mod tests;
