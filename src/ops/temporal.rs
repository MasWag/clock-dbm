//! Operations for time elapse and changes to clock values.
//!
//! - [`Dbm::future`](crate::Dbm::future) advances **all** clocks by the same
//!   nonnegative delay.
//! - [`Dbm::past`](crate::Dbm::past) is its backward counterpart: the
//!   valuations from which some common nonnegative delay leads into the zone.
//! - [`Dbm::try_reset`](crate::Dbm::try_reset) (or
//!   [`Dbm::try_reset_zero`](crate::Dbm::try_reset_zero)) assigns a constant
//!   value to one clock, leaving the others unchanged.
//! - [`Dbm::try_free`](crate::Dbm::try_free) removes restrictions on one
//!   clock's value while retaining the clock and the values of the others.
//!
//! All four transformations preserve the number of actual clocks.

// Source-level implementation and proof notes (not part of public API Rustdoc).
// Temporal operations: future (delay), past (time predecessors), clock
// reset and clock free.
//
// Notation: `γ(D)` denotes the set of nonnegative-real valuations
// represented by DBM `D`; `∅_d` denotes the empty zone of matrix
// dimension `d` (including the reference clock fixed at zero).
// `Le c` and `Lt c` mean `<= c` and `< c`; `a ≼ b` means
// bound `a` is at least as tight as bound `b`.
//
// Each operation moves the input's storage into a working matrix, rewrites
// entries in place (`O(d)` of them from the **original** reference row and
// column; `O(d²)` reads for past, which rewrites row 0 only), and publishes
// the result with `Matrix::publish_canonical`. There is no closure, no
// scratch memory and no copy. Empty inputs are returned
// unchanged (`∅_d` keeps its dimension), after the arguments are validated.
//
// Throughout, `D` is the canonical, nonempty input with `d = n + 1`, `k` is
// the index of the selected actual clock, and `R` is the result.
//
// # Future: `γ(R) = { u + t | u ∈ γ(D), t ≥ 0 }`
//
// `R[i][0] = ∞` for `i ∈ 1..d`; every other entry is unchanged. All actual
// clocks advance by the **same** delay, so the differences `xᵢ − xⱼ`
// (`i, j ≥ 1`) and the lower bounds `D[0][j]` stay; only the upper bounds go.
//
// *Canonicity.* Row 0 and the diagonal are unchanged (C2, C3). A triangle
// `R[i][j] ≼ R[i][l] + R[l][j]` whose left side is a changed entry `(i, 0)`
// has a right side containing `R[i][0]` (`l = 0`) or `R[l][0]` with `l ≥ 1`
// (otherwise `l = 0` and `R[0][0] = Le 0` with `R[i][0]` again), and that is
// `∞`. A triangle whose left side is unchanged only lost tightness on its
// right side. The corresponding correctness properties are proved below.
//
// # Past: `γ(R) = { v ≥ 0 | ∃t ≥ 0. v + t ∈ γ(D) }`
//
// ```text
// R[0][j] = min(Le 0, D[1][j], …, D[n][j])   (every j; R[0][0] = Le 0)
// ```
//
// and every other entry is unchanged. Upper bounds `D[i][0]` and the
// differences `D[i][j]` (`i, j ≥ 1`) are invariant under a common delay,
// so they stay. Lower bounds `D[0][j]` disappear, but **not** to `Le 0`:
// the result must stay canonical, and `xⱼ ≥ 0` together with
// `xᵢ − xⱼ ≼ D[i][j]` still bounds `−xⱼ` by `D[i][j]` (for example,
// `x − y ≥ 5` and `y ≥ 0` give `x ≥ 5`). This is row 0 of the closure of
// "`D` with row 0 relaxed to `Le 0`", and a single step `0 → i → j`
// suffices: a longer path `0 → i → l → j` is dominated by
// `D[i][j] ≼ D[i][l] + D[l][j]`.
//
// *Why exact.* `v + t ∈ γ(D)` constrains `t` by `t ≼ D[i][0] − vᵢ` and
// `−t ≼ D[0][j] + vⱼ`. Eliminating `t ≥ 0` (Fourier–Motzkin) leaves
// `vᵢ ≼ D[i][0]` and `vᵢ − vⱼ ≼ D[i][0] + D[0][j]`, which the canonical
// `D[i][j]` already implies. So `γ(R)` is "nonnegative, `D`'s upper bounds
// and differences" (`proof::down_zone`; the hard direction builds `t` with
// `proof::rewind`).
//
// *Canonicity.* Row-0 triangles: `R[0][j] ≼ R[0][l] + D[l][j]` because
// `R[0][l]` is `Le 0` or some `D[k][l]`, and `D[k][l] + D[l][j] ≽ D[k][j]`.
// Triangles through `l = 0`: `D[i][j] ≼ D[i][0] + R[0][j]` because
// `R[0][j]` is `Le 0` or `D[k][j]`, and `D[i][k] ≼ D[i][0] + D[0][k] ≼
// D[i][0]` (`proof::down_canonical`).
//
// *In-place order.* Row 0 `:= Le 0` (`Matrix::fill_row`), then for
// `i = 1, …, n`: row 0 `:= min(row 0, row i)` (`Matrix::relax_row` through
// `Le 0`, a contiguous, vectorized pass). Row 0 is never a source, so every
// row read is the input's. `Le 0 + b = b` is representable for every valid
// `b`, so the overflow flag of `relax_row` is provably never set. `O(d²)`
// time, no allocation, cannot fail.
//
// # Reset: `γ(R) = { u[xₖ := c] | u ∈ γ(D) }`, `c ≥ 0`
//
// ```text
// R[k][j] = Le c + D[0][j]     (j ≠ k)
// R[i][k] = Le (−c) + D[i][0]  (i ≠ k)
// R[k][k] = Le 0
// ```
//
// and every other entry is unchanged (the canonical reset transformation).
// The new value of `xₖ` is `c = c + x₀`, so its relation to every other
// clock is that clock's relation to `x₀`, shifted by `c`. The other clocks
// keep their values and mutual differences (`R` agrees with `D` off row and
// column `k`).
//
// *In-place order.* Two whole-line updates, each a single pass over the
// `d` entries: row `k := Le c + row 0` (`Matrix::add_weak_to_row`, a
// contiguous, vectorized loop), then column `k := Le(−c) + column 0`
// (`Matrix::add_weak_to_column`), both over **all** indices. The row pass
// reads row 0, which it does not write. The column pass reads column 0, of
// which the row pass changed only `D[k][0]`, now `Le c`; the column pass
// reads it only for `i = k` and writes `R[k][k] = Le c + Le(−c) = Le 0`.
// It writes `R[0][k] = Le(−c) + D[0][0] = Le(−c)`, the value the row pass
// read for `j = k` and overwrote. So every other entry is computed from `D`,
// and the diagonal needs no separate store. (The opposite pass order would
// be equally correct: then the row pass reads the updated `R[0][k] =
// Le(−c)`. What matters, and what the proof checks, is that the second pass
// reads exactly one entry written by the first, and that it yields `Le 0`.)
//
// *Range.* `c > MAX_CONSTANT` is rejected with `Err(Range)` before any
// write (after the argument and emptiness checks). Otherwise every sum is
// representable, so the kernel adds without range checks
// (`bounds::add_weak`, whose precondition is this claim):
//
// - row `k`: `D[0][j]` is a valid bound `≼ Le 0` (C3), so its constant lies
//   in `[MIN_CONSTANT, 0]` and `c + D[0][j]` in `[MIN_CONSTANT + c, c]`;
// - column `k`: for `i ≥ 1`, `D[i][0]` is `∞` or `≽ Le 0`, because
//   `D[i][0] + D[0][i] ≽ D[i][i] = Le 0` (C4, C2) and `D[0][i] ≼ Le 0`;
//   so a finite `D[i][0] − c` lies in `[−c, MAX_CONSTANT − c]`.
//
// Both facts follow from C2–C4 of the `Dbm` type invariant alone
// (`proof::reset_representable`), not from the linear range premise of
// the representability conditions. Hence `Err(Range)` is returned **iff**
// the input is nonempty and `c > MAX_CONSTANT`, which is exactly when the
// result (`R[k][0] = Le c`) is unrepresentable. An earlier version added
// with `Bound::checked_add` and propagated its (unreachable) error; the
// per-entry range checks made reset about 2× slower than without them in a
// hot-cache loop.
//
// # Free: `γ(R) = { u[xₖ := t] | u ∈ γ(D), t ≥ 0 }`
//
// ```text
// R[k][j] = ∞        (j ≠ k)
// R[i][k] = D[i][0]  (i ≠ k; so R[0][k] = D[0][0] = Le 0)
// R[k][k] = Le 0
// ```
//
// and every other entry is unchanged. `xₖ` keeps
// its coordinate and only `xₖ ≥ 0`: free is **not** a reset (a reset pins
// `xₖ`) and does not remove the clock.
//
// *Why.* The projection of a canonical DBM onto the clocks other than `xₖ`
// is its submatrix (Fourier–Motzkin elimination over a closed system), so
// the unchanged entries are exactly the constraints on the other clocks.
// For `xₖ = t ≥ 0` the tightest bounds are `xᵢ − t ≤ xᵢ − 0`, i.e.
// `R[i][k] = R[i][0]`, and `t` has no upper bound. Canonicity: a triangle
// through `k` reads `R[i][k] + R[k][j] = D[i][0] + ∞` unless `j = k`, and
// `R[i][k] = D[i][0] ≼ D[i][l] + D[l][0] = R[i][l] + R[l][k]` for `l ≠ k`.
// Both facts are proved directly here
// (`proof::project`, `proof::free_zone`, `proof::free_canonical`).
//
// *In-place order.* Column `k := column 0` over all rows
// (`Matrix::copy_column`), then row `k := ∞` (`Matrix::fill_row`), then
// `R[k][k] := Le 0`. The copy reads column 0 before the row fill changes
// `D[k][0]`; the entry it writes in row `k` is overwritten by the fill.
//
// # Future, in place
//
// Column 0 `:= ∞` over all rows (`Matrix::fill_column`), then
// `R[0][0] := Le 0`. Future, reset and free are `O(d)`, past is `O(d²)`;
// none of them runs a closure.
//
// # Errors
//
// Argument errors come first, also for empty inputs: `ClockOutOfRange`,
// then (reset) `NegativeConstant`. Then an empty input returns `Ok(∅_d)`.
// Only then can reset fail with `Range`. Future and past never fail, and
// free never fails on a valid clock. On `Err` the consumed input is dropped.
//
// # Verification status
//
// Creusot proves every function of this module on the shipped bodies
//, with `#[check(terminates)]`; the lemmas are in
// `temporal/proof.rs`, the primitives in `dbm.rs` and `bounds.rs`. There
// is no `#[trusted]`, `assume` or admitted lemma.
//
// - **Semantics** over nonnegative real valuations: `future` denotes
//   `{ u + t | u ∈ γ(D), t ≥ 0 }` (a common delay, `x₀` stays 0), `try_reset`
//   `{ u[x := c] | u ∈ γ(D) }`, `try_free` `{ u[x := t] | u ∈ γ(D), t ≥ 0 }`
//   (the clock is kept), `past` `{ v ≥ 0 | ∃t ≥ 0. v + t ∈ γ(D) }`. The
//   model of each kernel is `proof::up`, `proof::reset`, `proof::free` and
//   `proof::down`; the proofs show that the in-place updates compute it
//   exactly (including the two-pass order of reset and the loop of past)
//   and that it is canonical, which discharges `publish_canonical`.
// - **The hard direction** of each set equation constructs a witness with
//   the one-clock extension of `dbm::proof` (`extend`): `proof::project`
//   (the projection of a canonical DBM is its submatrix; free and reset),
//   `proof::unshift` (future) and `proof::rewind` (past).
// - **Errors and range:** exactly the order above; `Err(Range)` iff the
//   input is nonempty and `c > MAX_CONSTANT`; `∅_d` keeps its dimension; no
//   partially updated matrix escapes (`Range` is decided before any write).
//
// The exact-oracle tests (`temporal/tests.rs`) remain as regression tests.
// See `verification/PROOF_STATUS.md`.

// `?` is not a terminating call for Creusot; keep the style of `dbm.rs`.
#![allow(clippy::question_mark)]

use crate::bounds::{Bound, Clock, Variable};
#[cfg(creusot)]
use crate::bounds::{MAX_CONSTANT, neg_in_range, variable_not_zero, view_representable};
use crate::dbm::Dbm;
#[cfg(creusot)]
use crate::dbm::proof::{meq, meq_transfer};
use crate::error::Error;
#[cfg(creusot)]
use creusot_std::logic::real::Real;
use creusot_std::prelude::*;

impl Dbm {
    /// Computes the **future** of this zone by allowing time to elapse.
    ///
    /// The result contains exactly those valuations obtained by taking a
    /// valuation of this zone and advancing **all actual clocks by the same
    /// nonnegative real delay**. The reference clock remains zero.
    /// Differences between actual clocks are preserved; individual upper
    /// bounds on clocks are removed.
    ///
    /// The clock count is unchanged. An empty zone remains empty,
    /// and this operation cannot fail.
    ///
    /// # Complexity
    ///
    /// `O(d)` time, where `d` is the number of actual clocks plus the
    /// reference clock. The owned matrix is updated without allocation.
    #[check(terminates)]
    #[ensures(result.variables_logic() == self.variables_logic())]
    #[ensures(result.is_empty_logic() == self.is_empty_logic())]
    #[ensures(forall<v: crate::dbm::proof::Val> result.zone(v) ==
        exists<u: crate::dbm::proof::Val, t: Real> Real::from_int(0) <= t && self.zone(u)
            && proof::shifted(u, t, v, self.variables_logic() + 1))]
    pub fn future(self) -> Dbm {
        let z = snapshot!(self);
        snapshot!(self.model());
        let empty = self.empty_like();
        let mut m = match self.into_matrix() {
            Some(m) => m,
            None => return empty,
        };
        snapshot!(m.dim_pos());
        let d = snapshot!(m.dim_logic());
        let f = snapshot!(m.mmat());
        let m0 = snapshot!(m);
        snapshot!(m0.model());
        snapshot!(proof::up_canonical(*f, *d));
        snapshot!(proof::up_zone(*f, *d));
        m.fill_column(0, Bound::INFINITY);
        m.set(0, 0, Bound::LE_ZERO);
        snapshot!(m.model());
        proof_assert!(meq(m.mmat(), proof::up(*f), *d));
        snapshot!(meq_transfer(m.mmat(), proof::up(*f), *d));
        proof_assert!(forall<v: crate::dbm::proof::Val> m.zone(v) ==
            exists<u: crate::dbm::proof::Val, t: Real> Real::from_int(0) <= t && z.zone(u)
                && proof::shifted(u, t, v, *d));
        m.publish_canonical()
    }

    /// Computes the **past** of this zone: every valuation from which this
    /// zone can be reached by letting time elapse.
    ///
    /// For a zone `Z` over `n` clocks the result is
    ///
    /// ```text
    /// past(Z) = { v ∈ (ℝ≥0)ⁿ | there is a real t ≥ 0 with v + t ∈ Z },
    /// ```
    ///
    /// where `v + t` advances **all actual clocks by the same delay** `t`
    /// (the reference clock stays zero). Upper bounds on clocks and all
    /// differences between actual clocks are kept. Lower bounds on single
    /// clocks are relaxed, but only as far as nonnegativity and the
    /// difference constraints allow: the past of `{x − y ≥ 5, y ≥ 3}` is
    /// `{x − y ≥ 5}`, in which `x ≥ 5` still holds because `y ≥ 0`.
    ///
    /// The clock count is unchanged and `Z ⊆ past(Z)`. An empty zone stays
    /// empty with the same clock count, and this operation cannot fail.
    ///
    /// # Complexity
    ///
    /// `O(d²)` time, where `d` is the number of actual clocks plus the
    /// reference clock. The owned matrix is updated without allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use clock_dbm::{Clock, Constraint, Dbm};
    ///
    /// let x = Clock::new(1).unwrap();
    /// let y = Clock::new(2).unwrap();
    /// // { x − y ≥ 5, 3 ≤ y ≤ 4 }
    /// let z = Dbm::universe(2)?
    ///     .try_constrain(Constraint::le(y, x, -5)?)?
    ///     .try_constrain(Constraint::le(Clock::ZERO, y, -3)?)?
    ///     .try_constrain(Constraint::le(y, Clock::ZERO, 4)?)?;
    /// let p = z.clone().past();
    /// assert!(z.is_subset_of(&p)?);
    /// // The past keeps x − y ≥ 5 and y ≤ 4, so x ≥ 5 still holds.
    /// let expected = Dbm::universe(2)?
    ///     .try_constrain(Constraint::le(y, x, -5)?)?
    ///     .try_constrain(Constraint::le(y, Clock::ZERO, 4)?)?;
    /// assert_eq!(p, expected);
    /// let x_ge_5 = Dbm::universe(2)?.try_constrain(Constraint::le(Clock::ZERO, x, -5)?)?;
    /// assert!(p.is_subset_of(&x_ge_5)?);
    /// # Ok::<(), clock_dbm::Error>(())
    /// ```
    #[check(terminates)]
    #[ensures(result.variables_logic() == self.variables_logic())]
    #[ensures(result.is_empty_logic() == self.is_empty_logic())]
    #[ensures(forall<v: crate::dbm::proof::Val> result.zone(v) ==
        (crate::dbm::proof::valuation(self.variables_logic() + 1, v)
            && exists<u: crate::dbm::proof::Val, t: Real> Real::from_int(0) <= t && self.zone(u)
                && proof::shifted(v, t, u, self.variables_logic() + 1)))]
    pub fn past(self) -> Dbm {
        let z = snapshot!(self);
        snapshot!(self.model());
        let empty = self.empty_like();
        let mut m = match self.into_matrix() {
            Some(m) => m,
            None => return empty,
        };
        snapshot!(m.dim_pos());
        let d = snapshot!(m.dim_logic());
        let f = snapshot!(m.mmat());
        let m0 = snapshot!(m);
        snapshot!(m0.model());
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < *d && 0 <= j && j < *d ==> {
            view_representable(m0.at(i, j)); f[i][j].representable()
        });
        snapshot!(proof::down_canonical(*f, *d));
        snapshot!(proof::down_zone(*f, *d));
        // Row 0 := Le 0, then row 0 := min(row 0, row i) for every actual
        // clock i (`relax_row` through `Le 0`). Row 0 is never a source, so
        // every row i ≥ 1 is still the input's.
        m.fill_row(0, Bound::LE_ZERO);
        let dim = m.dimension();
        let mut i: usize = 1;
        #[invariant(1 <= i@ && i@ <= *d && m.dim_logic() == *d)]
        #[invariant(forall<k: Int, l: Int> 1 <= k && k < *d && 0 <= l && l < *d ==>
            m.at(k, l) == m0.at(k, l))]
        #[invariant(forall<l: Int> 0 <= l && l < *d ==> m.at(0, l)@ == proof::pmin(*f, i@, l))]
        #[variant(*d - i@)]
        while i < dim {
            let before = snapshot!(m);
            proof_assert!(forall<l: Int> 0 <= l && l < *d ==>
                before.at(i@, l)@ == f[i@][l] && f[i@][l].representable());
            let overflow = m.relax_row(0, i, Bound::LE_ZERO);
            proof_assert!(forall<l: Int> 0 <= l && l < *d ==> {
                proof::relax_le_zero(before.at(0, l)@, f[i@][l], m.at(0, l)@);
                m.at(0, l)@ == proof::pmin(*f, i@ + 1, l)
            });
            proof_assert!(!overflow);
            // Unreachable: `Le 0 + b` is representable for every valid `b`.
            debug_assert!(!overflow);
            i += 1;
        }
        snapshot!(m.model());
        proof_assert!(meq(m.mmat(), proof::down(*f, *d), *d));
        snapshot!(meq_transfer(m.mmat(), proof::down(*f, *d), *d));
        proof_assert!(forall<v: crate::dbm::proof::Val> m.zone(v) ==
            (crate::dbm::proof::valuation(*d, v)
                && exists<u: crate::dbm::proof::Val, t: Real> Real::from_int(0) <= t && z.zone(u)
                    && proof::shifted(v, t, u, *d)));
        m.publish_canonical()
    }

    /// Resets actual clock `x` to zero in every valuation of this zone.
    ///
    /// All other clock values are preserved. This is equivalent to
    /// [`Dbm::try_reset`] with `value = 0`. It preserves the clock count
    /// and leaves an empty zone empty.
    ///
    /// # Errors
    ///
    /// [`Error::ClockOutOfRange`] if `x` is not one of this zone's actual
    /// clocks, even when the zone is empty. No arithmetic range error occurs.
    ///
    /// # Complexity
    ///
    /// `O(d)` time, where `d` includes the reference clock.
    #[check(terminates)]
    #[ensures(match result {
        Ok(r) => x@ <= self.variables_logic()
            && r.variables_logic() == self.variables_logic()
            && r.is_empty_logic() == self.is_empty_logic()
            && forall<v: crate::dbm::proof::Val> r.zone(v) ==
                exists<u: crate::dbm::proof::Val> self.zone(u) && v[x@] == Real::from_int(0)
                    && proof::agree_except(u, v, self.variables_logic() + 1, x@),
        Err(e) => x@ > self.variables_logic() && match e {
            Error::ClockOutOfRange { clock, variables } =>
                clock@ == x@ && variables@ == self.variables_logic(),
            _ => false,
        },
    })]
    pub fn try_reset_zero(self, x: Variable) -> Result<Dbm, Error> {
        self.try_reset(x, 0)
    }

    /// Resets actual clock `x` to the specified nonnegative integer.
    ///
    /// Each valuation of the result is obtained from a valuation of this
    /// zone by setting `x = value` and leaving every other clock unchanged.
    /// The clock count is unchanged; an empty zone stays empty after
    /// argument validation.
    ///
    /// # Errors
    ///
    /// In the following order:
    ///
    /// - [`Error::ClockOutOfRange`] if `x` is not an actual clock of this
    ///   zone;
    /// - [`Error::NegativeConstant`] if `value` is negative;
    /// - [`Error::Range`] if the input zone is nonempty and `value`
    ///   exceeds [`crate::MAX_CONSTANT`].
    ///
    /// Clock and negativity checks also apply to empty zones, but an
    /// empty zone accepts an otherwise valid value above `MAX_CONSTANT`
    /// because no bound needs to be stored.
    ///
    /// # Complexity
    ///
    /// `O(d)` time, where `d` includes the reference clock.
    #[check(terminates)]
    #[ensures(match result {
        Ok(r) => x@ <= self.variables_logic() && 0 <= value@
            && (self.is_empty_logic() || value@ <= MAX_CONSTANT@)
            && r.variables_logic() == self.variables_logic()
            && r.is_empty_logic() == self.is_empty_logic()
            && forall<v: crate::dbm::proof::Val> r.zone(v) ==
                exists<u: crate::dbm::proof::Val> self.zone(u) && v[x@] == Real::from_int(value@)
                    && proof::agree_except(u, v, self.variables_logic() + 1, x@),
        Err(e) => match e {
            Error::ClockOutOfRange { clock, variables } => x@ > self.variables_logic()
                && clock@ == x@ && variables@ == self.variables_logic(),
            Error::NegativeConstant { value: v } =>
                x@ <= self.variables_logic() && value@ < 0 && v == value,
            Error::Range => x@ <= self.variables_logic() && 0 <= value@
                && !self.is_empty_logic() && MAX_CONSTANT@ < value@,
            _ => false,
        },
    })]
    pub fn try_reset(self, x: Variable, value: i32) -> Result<Dbm, Error> {
        let z = snapshot!(self);
        snapshot!(self.model());
        snapshot!(variable_not_zero(x));
        let k = match self.check_clock(Clock::from(x)) {
            Ok(k) => k,
            Err(e) => return Err(e),
        };
        if value < 0 {
            return Err(Error::NegativeConstant { value });
        }
        let empty = self.empty_like();
        let mut m = match self.into_matrix() {
            Some(m) => m,
            None => return Ok(empty),
        };
        snapshot!(if crate::bounds::BoundModel::in_range(value@) { neg_in_range(value@) });
        let (up, down) = match (Bound::le(value), Bound::le(-value)) {
            (Ok(up), Ok(down)) => (up, down),
            _ => return Err(Error::Range),
        };
        proof_assert!(value@ <= MAX_CONSTANT@);
        snapshot!(m.dim_pos());
        let d = snapshot!(m.dim_logic());
        let f = snapshot!(m.mmat());
        let m0 = snapshot!(m);
        snapshot!(m0.model());
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < *d && 0 <= j && j < *d ==> {
            view_representable(m0.at(i, j)); f[i][j].representable()
        });
        snapshot!(proof::reset_representable(*f, *d, value@));
        snapshot!(proof::cancel(value@));
        snapshot!(proof::reset_canonical(*f, *d, k@, value@));
        snapshot!(proof::reset_zone(*f, *d, k@, value@));
        // Row k from row 0, then column k from column 0 (which by then
        // reads R[k][0] = Le c, so R[k][k] = Le c + Le(−c) = Le 0). Every
        // sum is representable by proof::reset_representable.
        m.add_weak_to_row(k, 0, up);
        let m1 = snapshot!(m);
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < *d && 0 <= j && j < *d ==>
        m1.at(i, j)@ == if i == k@ {
            crate::bounds::BoundModel::Le(value@).add(f[0][j])
        } else {
            f[i][j]
        });
        proof_assert!(forall<i: Int> 0 <= i && i < *d ==>
            down@.add_in_range(m1.at(i, 0)@));
        m.add_weak_to_column(k, 0, down);
        let m2 = snapshot!(m);
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < *d && 0 <= j && j < *d ==>
        m2.at(i, j)@ == if j == k@ {
            crate::bounds::BoundModel::Le(-value@).add(m1.at(i, 0)@)
        } else {
            m1.at(i, j)@
        });
        snapshot!(m.model());
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < *d && 0 <= j && j < *d ==>
            m.mmat()[i][j] == m2.at(i, j)@);
        proof_assert!(meq(m.mmat(), proof::reset(*f, k@, value@), *d));
        snapshot!(meq_transfer(m.mmat(), proof::reset(*f, k@, value@), *d));
        proof_assert!(forall<v: crate::dbm::proof::Val> m.zone(v) ==
            exists<u: crate::dbm::proof::Val> z.zone(u) && v[k@] == Real::from_int(value@)
                && proof::agree_except(u, v, *d, k@));
        Ok(m.publish_canonical())
    }

    /// Forgets the constraints on actual clock `x` while retaining it.
    ///
    /// The result contains exactly those valuations obtained by taking a
    /// valuation of this zone, leaving the other clocks unchanged, and
    /// choosing **any nonnegative real value** for `x`. Unlike resetting,
    /// this does not fix `x` to a constant or remove it from the zone.
    /// The clock count is unchanged, and an empty zone stays empty.
    ///
    /// # Errors
    ///
    /// [`Error::ClockOutOfRange`] if `x` is not an actual clock of this
    /// zone, even when the zone is empty.
    ///
    /// # Complexity
    ///
    /// `O(d)` time, where `d` includes the reference clock.
    #[check(terminates)]
    #[ensures(match result {
        Ok(r) => x@ <= self.variables_logic()
            && r.variables_logic() == self.variables_logic()
            && r.is_empty_logic() == self.is_empty_logic()
            && forall<v: crate::dbm::proof::Val> r.zone(v) ==
                exists<u: crate::dbm::proof::Val> self.zone(u) && Real::from_int(0) <= v[x@]
                    && proof::agree_except(u, v, self.variables_logic() + 1, x@),
        Err(e) => x@ > self.variables_logic() && match e {
            Error::ClockOutOfRange { clock, variables } =>
                clock@ == x@ && variables@ == self.variables_logic(),
            _ => false,
        },
    })]
    pub fn try_free(self, x: Variable) -> Result<Dbm, Error> {
        snapshot!(self.model());
        snapshot!(variable_not_zero(x));
        let k = match self.check_clock(Clock::from(x)) {
            Ok(k) => k,
            Err(e) => return Err(e),
        };
        let empty = self.empty_like();
        let mut m = match self.into_matrix() {
            Some(m) => m,
            None => return Ok(empty),
        };
        snapshot!(m.dim_pos());
        let d = snapshot!(m.dim_logic());
        let f = snapshot!(m.mmat());
        let m0 = snapshot!(m);
        snapshot!(m0.model());
        snapshot!(proof::free_canonical(*f, *d, k@));
        snapshot!(proof::free_zone(*f, *d, k@));
        m.copy_column(k, 0);
        m.fill_row(k, Bound::INFINITY);
        m.set(k, k, Bound::LE_ZERO);
        snapshot!(m.model());
        proof_assert!(meq(m.mmat(), proof::free(*f, k@), *d));
        snapshot!(meq_transfer(m.mmat(), proof::free(*f, k@), *d));
        Ok(m.publish_canonical())
    }
}

#[cfg(creusot)]
mod proof;

#[cfg(test)]
mod tests;
