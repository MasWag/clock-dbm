//! Maximal-constant extrapolation (ExtraM).
//!
//! [`MaxBounds`] supplies a ceiling for each clock;
//! [`Dbm::try_extrapolate_max`](crate::Dbm::try_extrapolate_max) uses these
//! ceilings to overapproximate a zone. This retains all original valuations,
//! but may introduce others. Reachability preservation requires additional
//! assumptions on the timed automaton, including appropriate ceilings and
//! restrictions on guards, invariants, and resets.

// Source-level implementation and proof notes (not part of public API Rustdoc).
// ExtraM: maximal-constant extrapolation.
//
// Notation: `D[i][j]` bounds the difference between clocks `i` and `j`,
// with clock zero fixed at zero. `γ(D)` is the set of nonnegative-real
// valuations represented by `D`, and `∅_d` is the empty zone of matrix
// dimension `d`. `Le c` means `<= c`, `Lt c` means `< c`, and `∞` means
// no restriction. The strict order `a ≺ b` means `a` is tighter than `b`;
// `a ≼ b` also allows equal bounds. The dimension includes the reference
// clock.
//
// For a canonical DBM `D` and ceilings `M(x₁) … M(xₙ)`,
//
// ```text
// ExtraM(D, M) = close(norm(D, k, n)),   k(0) = 0,  k(i) = M(xᵢ)
// ```
//
// where `norm` is the entrywise normalization defined below:
//
// ```text
// norm_upper e t = (if Le t ≺ e then ∞ else e)
// norm_lower e t = (if e ≺ Lt t then Lt t else e)
// norm_diag  e   = (if e ≺ Le 0 then Lt 0 else if e = Le 0 then e else ∞)
// norm D k n i j = let ub = (if i > 0 then k i else 0); lb = (if j > 0 then −k j else 0) in
//                  if i ≠ j then norm_lower (norm_upper (D i j) ub) lb else norm_diag (D i j)
// ```
//
// An upper bound looser than `Le k(i)` becomes `∞`; then a lower bound
// tighter than `Lt (−k(j))` becomes `Lt (−k(j))`. Since `k(0) = 0`, the
// reference row and column use the thresholds `Le 0` and `Lt 0`.
// On a nonempty public input the diagonal is `Le 0`, which
// `norm_diag` keeps.
//
// # Algorithm
//
// 1. Check the dimension of `bounds` (also for empty inputs). An empty
//    input is returned as `∅_d`.
// 2. Move the storage into the working matrix and apply `norm` entrywise,
//    in place. The thresholds `Le k(i)` and `Lt (−k(i))` are representable
//    because `0 ≤ k(i) ≤ MAX_CONSTANT` and `MIN_CONSTANT = −MAX_CONSTANT`;
//    `norm` only compares and copies bounds, so it does no range-checked
//    arithmetic.
// 3. Recanonicalize:
//    - **Some entry changed:** a *full* closure, `Matrix::close_pivots`
//      with every clock selected as a pivot, i.e.
//      Floyd–Warshall over all pivots with the proved, vectorized
//      `Matrix::relax_row`. It returns `∅_d`, the canonical form, or
//      `Err(Range)` when a sum that would tighten an entry is
//      unrepresentable. With every pivot selected, its precondition
//      `pivot_ready` asks only for a `Le 0` diagonal and a reference row
//      `≼ Le 0`. `norm` keeps both on a canonical nonempty input:
//      `norm_diag` keeps `Le 0`, the reference row's upper threshold `Le 0`
//      never fires, and its lower rule yields `Lt (−k(j)) ≼ Le 0` because
//      `k(j) ≥ 0` (by the normalization bounds). It computes the same
//      closure as the scalar `Matrix::close` (`canonical_unique`), about
//      2.7× faster at 64 clocks.
//    - **No entry changed:** the working matrix *is* the canonical,
//      nonempty input, which is its own closure (`canonical_unique`), so it
//      is published as is with `Matrix::publish_canonical` (debug builds
//      re-check canonicity). This shortcut keeps the common case
//      "no ceiling exceeded" at
//      `O(d²)` instead of `O(d³)`.
//
// `norm` **weakens** entries, so the canonical input's triangle
// inequalities no longer hold in general: an entry set to `∞` can be
// re-derived by closure through others. The incremental closure of
// `ops::constraints`, which repairs a matrix after *tightening*, does not
// apply, and neither does restricting the pivots to the clocks of changed
// entries (the argument for intersection, `ops::relations`, needs
// unchanged entries to be at least as tight as the canonical input's).
// So every clock is a pivot. `Err(Range)` is genuine: for example,
// with `k(1) = 5`, `D[1][2] = Le 3`, `D[2][0] = Le (MAX_CONSTANT − 1)` and
// `D[1][0] = Le 100`, `norm` drops `D[1][0]` to `∞` and the closure
// re-derives `Le (MAX_CONSTANT + 2)`, which is unrepresentable. Range
// failure is never reported as emptiness, and no bound is saturated.
//
// The `Workspace` holds the pivot flags (all set by
// `Workspace::select_all`), so repeated calls do not allocate once it has
// grown to the dimension.
//
// # Errors
//
// `MaxBounds::new` rejects a vector longer than `MAX_VARIABLES`
// (`TooManyVariables`), then the first ceiling outside `[0, MAX_CONSTANT]`
// (`InvalidMaxBounds`). `try_extrapolate_max` returns `DimensionMismatch`
// when `bounds.variables() ≠ self.variables()`, also for an empty input;
// then `Ok(∅_d)` for an empty input; then `Err(Range)` if closure (step 3)
// leaves the representable range. On `Err` the consumed input is dropped
// (the input is consumed).
//
// # Supported abstraction
//
// This module implements maximal-constant extrapolation (ExtraM).
// LU-bound extrapolation and other advanced abstractions are not yet part
// of the public API and are reserved for future work.
//
// # What is (not) claimed
//
// ExtraM is extensive (`γ(D) ⊆ γ(ExtraM(D, M))`) and its result is
// canonical or empty. Idempotence is **not** claimed.
// ExtraM does not by itself preserve reachability: that needs the
// automaton-level assumptions (diagonal-free guards
// and invariants, ceilings covering every compared constant, constant
// resets). With diagonal constraints it is unsound for reachability.
//
// # Verification status
//
// Creusot v0.14.0 machine-checks every item of this module on the shipped
// code, with termination, no panic and no arithmetic overflow. The
// contracts are stated over nonnegative real valuations (`Dbm::zone`):
//
// - `norm_upper`, `norm_lower`, `norm_diag`, `thresholds` and `normalize`
//   compute the specified `norm` exactly (`proof::norm_entry`, an entrywise
//   definition over `BoundModel`): `W[i][j] = norm(D, k)[i][j]` for every
//   entry, upper rule before lower rule, `k(0) = 0`, exact strictness and
//   `∞`. `normalize` returns `true` iff some entry changed (as a packed
//   code), so `false` means the matrix is bit-identical to the input;
// - `MaxBounds`: the type invariant `0 ≤ M(x) ≤ MAX_CONSTANT`, the exact
//   errors of `new` in their order, `variables`, `get` and `k`;
// - `try_extrapolate_max`: the errors in their order (`DimensionMismatch`
//   before emptiness, `Range` only with the provenance
//   `proof::mrange_failure` of the exact closure of `norm(D, M)`, never as
//   emptiness), and on success `γ(result) = γ(norm(D, M))` (`∅_d` for an
//   empty input), `γ(D) ⊆ γ(result)`, and uniqueness: every valid `Dbm` of
//   that dimension and zone equals the result, so it **is**
//   `close(norm(D, M))`. Both paths are proved as shipped: the unchanged
//   path publishes the canonical input without closure; the changed path
//   runs the all-pivot `Matrix::close_pivots` (`pivot_ready` from
//   `proof::norm_ready` and `Matrix::full_pivot_ready`, not the
//   touched-pivot argument of intersection).
//
// The lemmas are in `extra_m/proof.rs` (`norm_weakens`, `norm_extensive`,
// `norm_ready`, `norm_range`). Idempotence, the linear range premise
// and reachability preservation are **not** proved.
// See `verification/PROOF_STATUS.md`. The exact-oracle tests in
// `extra_m/tests.rs` remain as regression tests.

// `?` is not a terminating call for Creusot; keep the style of `dbm.rs`.
#![allow(clippy::question_mark)]

use crate::bounds::{Bound, MAX_CONSTANT, Variable};
#[cfg(creusot)]
use crate::bounds::{BoundModel, order_refines, view_injective};
#[cfg(creusot)]
use crate::dbm::proof::{meq, meq_transfer, mrange_failure, mrange_failure_meq};
use crate::dbm::{Dbm, MAX_VARIABLES, Matrix, Workspace, same, tighter};
use crate::error::Error;
#[cfg(creusot)]
use creusot_std::logic::Mapping;
use creusot_std::{
    invariant::Invariant,
    prelude::{Clone, PartialEq, *},
};

/// Per-clock maximal constants for [`Dbm::try_extrapolate_max`] (ExtraM).
///
/// The slice passed to [`MaxBounds::new`] contains ceilings for actual
/// clocks 1 through `n` in order. The reference clock's ceiling is
/// implicitly zero. Values must lie in `[0, MAX_CONSTANT]`.
///
/// ExtraM overapproximates a zone. Applying it does **not** alone guarantee
/// timed-automata reachability preservation: that requires restrictions on
/// guards, invariants, and clock resets.
///
/// # Example
///
/// ```
/// use clock_dbm::{MaxBounds, Variable};
/// # fn main() -> Result<(), clock_dbm::Error> {
/// let ceilings = MaxBounds::new(vec![5, 8])?;
/// assert_eq!(ceilings.variables(), 2);
/// assert_eq!(ceilings.get(Variable::new(2).unwrap()), Some(8));
/// # Ok(())
/// # }
/// ```
#[derive(PartialEq, Eq, Debug)]
// `Hash` is not translated by Creusot (std's `Hasher` has no specs); it is
// derived from the same field as `Eq`, so it is consistent with it.
#[cfg_attr(not(creusot), derive(Hash))]
pub struct MaxBounds {
    ceilings: Box<[i32]>,
}

/// A valid ceiling: `0 ≤ c ≤ MAX_CONSTANT`.
#[logic(open)]
pub(crate) fn valid_ceiling(c: i32) -> bool {
    pearlite! { 0 <= c@ && c@ <= MAX_CONSTANT@ }
}

impl Invariant for MaxBounds {
    #[logic(open(self))]
    fn invariant(self) -> bool {
        pearlite! {
            self.ceilings@.len() <= MAX_VARIABLES@
                && forall<p: Int> 0 <= p && p < self.ceilings@.len() ==>
                    valid_ceiling(self.ceilings@[p])
        }
    }
}

// Written out like `Dbm`'s: `Box<[i32]>::clone` has no creusot-std
// specification. Not `check(terminates)`, also like `Dbm`'s: `to_vec` is
// not a terminating call for Creusot.
impl Clone for MaxBounds {
    #[ensures(result.ceilings_logic() == self.ceilings_logic())]
    fn clone(&self) -> MaxBounds {
        let ceilings = self.ceilings.to_vec().into_boxed_slice();
        proof_assert!(ceilings@.ext_eq(self.ceilings@));
        MaxBounds { ceilings }
    }
}

impl DeepModel for MaxBounds {
    type DeepModelTy = Seq<Int>;

    #[logic(open(self))]
    fn deep_model(self) -> Seq<Int> {
        pearlite! { *self.ceilings.deep_model() }
    }
}

impl MaxBounds {
    /// Logical ceilings, `M(x_{p+1})` at index `p`.
    #[logic(open(self))]
    pub(crate) fn ceilings_logic(self) -> Seq<i32> {
        pearlite! { self.ceilings@ }
    }

    /// Logical number of actual clocks.
    #[logic(open(self))]
    pub(crate) fn variables_logic(self) -> Int {
        pearlite! { self.ceilings@.len() }
    }

    /// `k`: `k(i) = M(xᵢ)` for `1 ≤ i ≤ n`, and `0` elsewhere, in particular
    /// `k(0) = 0` for the reference clock.
    #[logic(open(self))]
    pub(crate) fn kmap(self) -> Mapping<Int, Int> {
        pearlite! {
            |i: Int| if 1 <= i && i <= self.ceilings@.len() { self.ceilings@[i - 1]@ } else { 0 }
        }
    }

    /// The ceilings are valid and `k` is nonnegative.
    #[logic]
    #[requires(inv(self))]
    #[ensures(self.variables_logic() <= MAX_VARIABLES@)]
    #[ensures(forall<i: Int> 0 <= self.kmap()[i] && self.kmap()[i] <= MAX_CONSTANT@)]
    #[ensures(self.kmap()[0] == 0)]
    pub(crate) fn model(self) {}

    /// Creates maximal constants for actual clocks 1, 2, ..., in the
    /// order supplied: `ceilings[0]` is the ceiling for clock 1.
    ///
    /// # Errors
    ///
    /// In this order:
    ///
    /// - [`Error::TooManyVariables`] if `ceilings.len() > MAX_VARIABLES`;
    /// - [`Error::InvalidMaxBounds`] for the first ceiling that is negative
    /// or greater than [`MAX_CONSTANT`], with its 1-based clock index.
    ///
    /// Proved: exactly these errors in this order; on success the
    /// ceilings are stored as given.
    ///
    /// # Complexity
    ///
    /// `O(n)` time for `n = ceilings.len()`.
    #[check(terminates)]
    #[ensures(match result {
        Ok(b) => ceilings@.len() <= MAX_VARIABLES@ && b.ceilings_logic() == ceilings@,
        Err(e) => if ceilings@.len() > MAX_VARIABLES@ {
            match e {
                Error::TooManyVariables { requested } => requested@ == ceilings@.len(),
                _ => false,
            }
        } else {
            exists<p: Int> 0 <= p && p < ceilings@.len() && !valid_ceiling(ceilings@[p])
                && (forall<q: Int> 0 <= q && q < p ==> valid_ceiling(ceilings@[q]))
                && match e {
                    Error::InvalidMaxBounds { variable, value } =>
                        variable@ == p + 1 && value == ceilings@[p],
                    _ => false,
                }
        },
    })]
    #[allow(
        clippy::manual_range_contains,
        reason = "`RangeInclusive::contains` is not a terminating call for Creusot"
    )]
    pub fn new(ceilings: Vec<i32>) -> Result<MaxBounds, Error> {
        if ceilings.len() > MAX_VARIABLES {
            return Err(Error::TooManyVariables {
                requested: ceilings.len(),
            });
        }
        let mut p: usize = 0;
        #[invariant(p@ <= ceilings@.len())]
        #[invariant(forall<q: Int> 0 <= q && q < p@ ==> valid_ceiling(ceilings@[q]))]
        #[variant(ceilings@.len() - p@)]
        while p < ceilings.len() {
            let value = ceilings[p];
            if value < 0 || value > MAX_CONSTANT {
                return Err(Error::InvalidMaxBounds {
                    variable: p + 1,
                    value,
                });
            }
            p += 1;
        }
        Ok(MaxBounds {
            ceilings: ceilings.into_boxed_slice(),
        })
    }

    /// The number of actual clocks.
    #[check(terminates)]
    #[ensures(result@ == self.variables_logic())]
    pub fn variables(&self) -> usize {
        self.ceilings.len()
    }

    /// Returns the ceiling for actual clock `x`, or `None` if it is
    /// outside the range covered by these bounds.
    ///
    /// # Complexity
    ///
    /// `O(1)` time.
    #[check(terminates)]
    #[ensures(match result {
        Some(c) => x@ <= self.variables_logic() && c == self.ceilings_logic()[x@ - 1],
        None => x@ > self.variables_logic(),
    })]
    pub fn get(&self, x: Variable) -> Option<i32> {
        let p = x.index() - 1;
        if p < self.ceilings.len() {
            Some(self.ceilings[p])
        } else {
            None
        }
    }

    /// `k(i)`: `0` for the reference clock, `M(xᵢ)` otherwise (`i ≤ n`).
    #[check(terminates)]
    #[requires(i@ <= self.variables_logic())]
    #[ensures(result@ == self.kmap()[i@])]
    #[ensures(valid_ceiling(result))]
    fn k(&self, i: usize) -> i32 {
        if i == 0 { 0 } else { self.ceilings[i - 1] }
    }
}

/// `norm_upper e t = (if Le t ≺ e then ∞ else e)`, with `up = Le t`.
#[check(terminates)]
#[ensures(forall<t: Int> up@ == BoundModel::Le(t) ==> result@ == proof::norm_upper(e@, t))]
fn norm_upper(e: Bound, up: Bound) -> Bound {
    snapshot!(order_refines(up, e));
    if tighter(up, e) { Bound::INFINITY } else { e }
}

/// `norm_lower e t = (if e ≺ Lt t then Lt t else e)`, with `low = Lt t`.
#[check(terminates)]
#[ensures(forall<t: Int> low@ == BoundModel::Lt(t) ==> result@ == proof::norm_lower(e@, t))]
fn norm_lower(e: Bound, low: Bound) -> Bound {
    snapshot!(order_refines(e, low));
    if tighter(e, low) { low } else { e }
}

/// `norm_diag e = (if e ≺ Le 0 then Lt 0 else if e = Le 0 then e else ∞)`.
#[check(terminates)]
#[ensures(result@ == proof::norm_diag(e@))]
fn norm_diag(e: Bound) -> Bound {
    snapshot!(order_refines(e, Bound::LE_ZERO));
    snapshot!(view_injective(e, Bound::LE_ZERO));
    if tighter(e, Bound::LE_ZERO) {
        Bound::LT_ZERO
    } else if same(e, Bound::LE_ZERO) {
        e
    } else {
        Bound::INFINITY
    }
}

/// `(Le k, Lt (−k))` for a validated ceiling `0 ≤ k ≤ MAX_CONSTANT`; both
/// are representable because `MIN_CONSTANT = −MAX_CONSTANT`.
#[check(terminates)]
#[requires(valid_ceiling(k))]
#[ensures(result.0@ == BoundModel::Le(k@) && result.1@ == BoundModel::Lt(-k@))]
fn thresholds(k: i32) -> (Bound, Bound) {
    match (Bound::le(k), Bound::lt(-k)) {
        (Ok(up), Ok(low)) => (up, low),
        _ => unreachable!(),
    }
}

impl Dbm {
    /// Computes **ExtraM**, a maximal-constant overapproximation of this zone.
    ///
    /// `bounds` supplies a nonnegative integer ceiling for each actual
    /// clock, in clock-index order. The reference clock (index zero) has
    /// ceiling zero. The operation relaxes difference bounds using these
    /// ceilings and returns the canonical zone represented by the result.
    ///
    /// More precisely, let `D[i][j]` be the stored bound on
    /// `clock i - clock j`, and let `k(i)` be clock `i`'s ceiling,
    /// with `k(0) = 0`. For each off-diagonal entry `e = D[i][j]`:
    ///
    /// ```text
    /// e' = if Le(k(i)) ≺ e then ∞ else e
    /// normalized[i][j] = if e' ≺ Lt(-k(j)) then Lt(-k(j)) else e'
    /// ```
    ///
    /// `Le(c)` means `<= c`, `Lt(c)` means `< c`, `∞` means no
    /// restriction, and `a ≺ b` means bound `a` is strictly tighter
    /// than bound `b`. On a nonempty input the diagonal remains `<= 0`.
    /// The result is the canonical closure of this normalized matrix.
    ///
    /// **Every valuation of the original zone remains in the result**,
    /// although the result may contain additional valuations. It is always
    /// canonical or empty on success; an empty input stays empty.
    ///
    /// This overapproximation does **not**, by itself, guarantee
    /// timed-automata reachability preservation. Standard applications
    /// require suitable ceilings and restrictions on guards, invariants
    /// and resets; diagonal constraints are not covered. Idempotence is
    /// not claimed. LU-bound and other advanced abstractions are not
    /// implemented.
    ///
    /// The `ws` parameter does not affect the result.
    ///
    /// # Errors
    ///
    /// - [`Error::DimensionMismatch`] if `bounds` describes a different
    ///   number of clocks, including when this zone is empty;
    /// - [`Error::Range`] if closure of a changed matrix requires a
    ///   finite bound outside the supported range. This is not an empty
    ///   result, and no partially updated zone is returned.
    ///
    /// # Complexity
    ///
    /// Normalization takes `O(d²)` for `d = self.dimension()`. If
    /// an entry changes, canonicalization can take `O(d³)` in the worst
    /// case. Otherwise the operation takes `O(d²)`.
    #[check(terminates)]
    #[ensures(match result {
        Ok(r) => bounds.variables_logic() == self.variables_logic()
            && r.variables_logic() == self.variables_logic()
            && (self.is_empty_logic() ==> r.is_empty_logic())
            && (!self.is_empty_logic() ==> forall<u: crate::dbm::proof::Val> r.zone(u) ==
                crate::dbm::proof::mzone(proof::norm(self.mmat(), bounds.kmap()),
                    self.variables_logic() + 1, u))
            && (forall<u: crate::dbm::proof::Val> self.zone(u) ==> r.zone(u))
            && forall<z: Dbm> inv(z) && z.variables_logic() == r.variables_logic()
                && (forall<u: crate::dbm::proof::Val> z.zone(u) == r.zone(u))
                ==> z.deep_model() == r.deep_model(),
        Err(e) => if bounds.variables_logic() != self.variables_logic() {
            match e {
                Error::DimensionMismatch { expected, found } =>
                    expected@ == self.variables_logic() && found@ == bounds.variables_logic(),
                _ => false,
            }
        } else {
            e == Error::Range && !self.is_empty_logic()
                && mrange_failure(proof::norm(self.mmat(), bounds.kmap()),
                    self.variables_logic() + 1)
        },
    })]
    pub fn try_extrapolate_max(self, bounds: &MaxBounds, ws: &mut Workspace) -> Result<Dbm, Error> {
        if let Err(e) = self.check_variables(bounds.variables()) {
            return Err(e);
        }
        snapshot!(self.model());
        snapshot!(bounds.model());
        let z0 = snapshot!(self);
        let nf = snapshot!(proof::norm(self.mmat(), bounds.kmap()));
        snapshot!(proof::norm_extensive(
            self.mmat(),
            bounds.kmap(),
            self.variables_logic() + 1
        ));
        let empty = self.empty_like();
        let mut m = match self.into_matrix() {
            Some(m) => m,
            None => {
                proof_assert!(forall<z: Dbm> inv(z) && z.variables_logic() == empty.variables_logic()
                && (forall<u: crate::dbm::proof::Val> z.zone(u) == empty.zone(u)) ==> {
                    Dbm::eq_semantic(z, empty);
                    z.deep_model() == empty.deep_model()
                });
                return Ok(empty);
            }
        };
        let w0 = snapshot!(m);
        let d = snapshot!(m.dim_logic());
        snapshot!(w0.model());
        let changed = normalize(&mut m, bounds);
        snapshot!(m.model());
        proof_assert!(meq(m.mmat(), *nf, *d));
        snapshot!(meq_transfer(m.mmat(), *nf, *d));
        let r = if changed {
            // Normalization may break canonicity, so close through every pivot.
            snapshot!(proof::norm_ready(w0.mmat(), bounds.kmap(), *d));
            ws.select_all(m.dimension());
            snapshot!(Matrix::full_pivot_ready(m, ws.touched@));
            let w1 = snapshot!(m);
            let r = m.close_pivots(&ws.touched);
            proof_assert!(match r {
                Err(_) => {
                    w1.range_failure_model();
                    mrange_failure_meq(w1.mmat(), *nf, *d);
                    true
                }
                Ok(_) => true,
            });
            r
        } else {
            // `norm` changed no entry: the matrix is the canonical input.
            proof_assert!(forall<a: Int, b: Int> 0 <= a && a < *d && 0 <= b && b < *d ==> {
                view_injective(m.at(a, b), w0.at(a, b));
                m.at(a, b)@ == w0.at(a, b)@
            });
            proof_assert!(meq(m.mmat(), w0.mmat(), *d));
            snapshot!(meq_transfer(m.mmat(), w0.mmat(), *d));
            Ok(m.publish_canonical())
        };
        proof_assert!(match r {
            Ok(y) => forall<z: Dbm> inv(z) && z.variables_logic() == y.variables_logic()
                && (forall<u: crate::dbm::proof::Val> z.zone(u) == y.zone(u)) ==> {
                    Dbm::eq_semantic(z, y);
                    z.deep_model() == y.deep_model()
                },
            Err(_) => true,
        });
        proof_assert!(forall<u: crate::dbm::proof::Val> z0.zone(u) ==>
            crate::dbm::proof::mzone(*nf, *d, u));
        r
    }
}

/// `W := norm(W, k, n)` entrywise, in place (`bounds.variables() + 1 =
/// m.dimension()`). Only compares and copies bounds. Returns whether some
/// entry changed; if not, `W` is exactly as before.
///
/// Proved: every entry becomes `norm_entry` of the old one (upper
/// rule before lower rule, `k(0) = 0`, `norm_diag` on the diagonal), and
/// the result is `true` iff some entry differs from before.
#[check(terminates)]
#[requires(bounds.variables_logic() + 1 == m.dim_logic())]
#[ensures((^m).dim_logic() == m.dim_logic())]
#[ensures(forall<a: Int, b: Int>
    0 <= a && a < m.dim_logic() && 0 <= b && b < m.dim_logic() ==>
        (^m).at(a, b)@ == proof::norm_entry(m.at(a, b)@, bounds.kmap(), a, b))]
#[ensures(result == exists<a: Int, b: Int>
    0 <= a && a < m.dim_logic() && 0 <= b && b < m.dim_logic() && (^m).at(a, b).deep_model() != m.at(a, b).deep_model())]
fn normalize(m: &mut Matrix, bounds: &MaxBounds) -> bool {
    let m0 = snapshot!(*m);
    let k = snapshot!(bounds.kmap());
    snapshot!(bounds.model());
    let mut changed = false;
    let d = m.dimension();
    let mut i: usize = 0;
    #[invariant(i@ <= d@ && m.dim_logic() == d@)]
    #[invariant(forall<a: Int, b: Int> 0 <= a && a < d@ && 0 <= b && b < d@ ==>
        if a < i@ {
            m.at(a, b)@ == proof::norm_entry(m0.at(a, b)@, *k, a, b)
        } else {
            m.at(a, b) == m0.at(a, b)
        })]
    #[invariant(changed == exists<a: Int, b: Int>
        0 <= a && a < i@ && 0 <= b && b < d@ && m.at(a, b).deep_model() != m0.at(a, b).deep_model())]
    #[variant(d@ - i@)]
    while i < d {
        let (up, _) = thresholds(bounds.k(i));
        let mut j: usize = 0;
        #[invariant(j@ <= d@ && m.dim_logic() == d@)]
        #[invariant(forall<a: Int, b: Int> 0 <= a && a < d@ && 0 <= b && b < d@ ==>
            if a < i@ || (a == i@ && b < j@) {
                m.at(a, b)@ == proof::norm_entry(m0.at(a, b)@, *k, a, b)
            } else {
                m.at(a, b) == m0.at(a, b)
            })]
        #[invariant(changed == exists<a: Int, b: Int>
            0 <= a && a < d@ && 0 <= b && b < d@ && (a < i@ || (a == i@ && b < j@))
                && m.at(a, b).deep_model() != m0.at(a, b).deep_model())]
        #[variant(d@ - j@)]
        while j < d {
            let e = m.get(i, j);
            let normed = if i == j {
                norm_diag(e)
            } else {
                let (_, low) = thresholds(bounds.k(j));
                norm_lower(norm_upper(e, up), low)
            };
            proof_assert!(normed@ == proof::norm_entry(e@, *k, i@, j@));
            snapshot!(view_injective(normed, e));
            if !same(normed, e) {
                m.set(i, j, normed);
                changed = true;
            }
            j += 1;
        }
        i += 1;
    }
    changed
}

#[cfg(creusot)]
mod proof;

#[cfg(test)]
mod tests;
