//! Constructing zones and applying clock constraints.
//!
//! [`Dbm::try_from_constraints`](crate::Dbm::try_from_constraints) starts
//! from all nonnegative valuations. Use
//! [`Dbm::try_constrain`](crate::Dbm::try_constrain) to add one guard to an
//! existing zone, or [`Dbm::try_constrain_all`](crate::Dbm::try_constrain_all)
//! to add several. Contradictory guards produce an empty zone rather than
//! an error; the method pages describe argument and arithmetic errors.

// Incremental closure is specified in docs/algorithms.md; the lemmas that
// justify each step of `close_edge` are in `constraints/proof.rs`.

#![allow(clippy::question_mark)]

use crate::bounds::{Bound, BoundModel, Constraint};
#[cfg(creusot)]
use crate::bounds::{order_refines, relax_needed, sat, view_representable};
#[cfg(creusot)]
use crate::dbm::proof::{
    edge, edge_canonical, edge_ok, edge_zone, mcanonical, meq, meq_transfer, valuation,
};
use crate::dbm::{Dbm, Matrix, Workspace, tighter};
use crate::error::Error;
use creusot_std::prelude::{Clone, *};
#[cfg(creusot)]
use proof::{all_valid, conj, csat, edge_unrepresentable, single_range_failure, valid};

// ----- range-failure provenance of a batch (specification only) -----

/// The incremental strategy failed at constraint `t`: `z` denotes the input
/// conjoined with the constraints before `t`, and the exact closure of `z`
/// with constraint `t` has an unrepresentable entry.
#[logic(open(crate))]
pub(crate) fn incremental_failure_at(d0: Dbm, cs: Seq<Constraint>, t: Int, z: Dbm) -> bool {
    pearlite! {
        0 <= t && t < cs.len() && !z.is_empty_logic()
            && mcanonical(z.mmat(), z.variables_logic() + 1)
            && z.variables_logic() == d0.variables_logic()
            && (forall<u: crate::dbm::proof::Val> z.zone(u) == (d0.zone(u) && conj(cs, t, u)))
            && single_range_failure(z.mmat(), z.variables_logic() + 1,
                cs[t]@.0, cs[t]@.1, cs[t]@.2)
    }
}

/// The full-closure strategy failed: `m` is the input with every constraint
/// tightened in, and its closure left the representable range.
#[logic(open(crate))]
pub(crate) fn closure_failure_at(d0: Dbm, cs: Seq<Constraint>, m: Matrix) -> bool {
    pearlite! {
        m.dim_logic() == d0.variables_logic() + 1
            && (forall<u: crate::dbm::proof::Val> m.zone(u) == (d0.zone(u) && conj(cs, cs.len(), u)))
            && m.range_failure_logic()
    }
}

/// Why a batch returned `Err(Range)`: exact arithmetic of
/// one of the two strategies left the representable range.
#[logic(open(crate))]
pub(crate) fn batch_range_failure(d0: Dbm, cs: Seq<Constraint>) -> bool {
    pearlite! {
        (exists<t: Int, z: Dbm> incremental_failure_at(d0, cs, t, z))
            || exists<m: Matrix> closure_failure_at(d0, cs, m)
    }
}

/// Some constraint of `cs` contradicts `d0` by itself (`b + D[j][i] ≺ Le 0`):
/// the pre-pass of `constrain_all_with` returns `∅_d`.
#[logic(open(crate))]
pub(crate) fn some_contradiction(d0: Dbm, cs: Seq<Constraint>) -> bool {
    pearlite! {
        exists<t: Int> 0 <= t && t < cs.len()
            && !edge_ok(d0.mmat(), cs[t]@.0, cs[t]@.1, cs[t]@.2)
    }
}

/// Every constraint of `cs` is implied by `d0` (`D[i][j] ≼ b`): incremental
/// insertion leaves `d0` unchanged.
#[logic(open(crate))]
pub(crate) fn all_implied(d0: Dbm, cs: Seq<Constraint>) -> bool {
    pearlite! {
        forall<t: Int> 0 <= t && t < cs.len() ==> d0.mmat()[cs[t]@.0][cs[t]@.1].le(cs[t]@.2)
    }
}

/// The error of the first invalid constraint (`check_constraint`).
#[logic(open(crate))]
pub(crate) fn clock_error(c: Constraint, n: Int, e: Error) -> bool {
    pearlite! {
        match e {
            Error::ClockOutOfRange { clock, variables } => variables@ == n
                && if c@.0 > n { clock@ == c@.0 } else { c@.1 > n && clock@ == c@.1 },
            _ => false,
        }
    }
}

/// `e` is the error of the first invalid constraint of `cs`.
#[logic(open(crate))]
pub(crate) fn first_clock_error(cs: Seq<Constraint>, n: Int, e: Error) -> bool {
    pearlite! {
        exists<t: Int> 0 <= t && t < cs.len() && !valid(cs[t], n)
            && (forall<s: Int> 0 <= s && s < t ==> valid(cs[s], n))
            && clock_error(cs[t], n, e)
    }
}

/// `cs` and `ds` contain the same constraints, in any order and with any
/// multiplicity.
#[logic(open(crate))]
pub(crate) fn same_constraints(cs: Seq<Constraint>, ds: Seq<Constraint>) -> bool {
    pearlite! {
        (forall<t: Int> 0 <= t && t < cs.len() ==> exists<s: Int> 0 <= s && s < ds.len() && ds[s] == cs[t])
            && forall<s: Int> 0 <= s && s < ds.len() ==> exists<t: Int> 0 <= t && t < cs.len() && cs[t] == ds[s]
    }
}

/// Order independence of batches: two successful
/// results of `try_constrain_all` on the same input, whose constraint lists
/// contain the same constraints (a permutation, or with repetitions), are
/// equal values, not only equal zones (by Theorem 3.1, `Dbm::eq_semantic`).
#[logic]
#[requires(inv(r1) && inv(r2) && r1.variables_logic() == r2.variables_logic())]
#[requires(same_constraints(cs, ds))]
#[requires(forall<u: crate::dbm::proof::Val> r1.zone(u) == (d0.zone(u) && conj(cs, cs.len(), u)))]
#[requires(forall<u: crate::dbm::proof::Val> r2.zone(u) == (d0.zone(u) && conj(ds, ds.len(), u)))]
#[ensures(r1.deep_model() == r2.deep_model())]
#[allow(dead_code, reason = "a theorem: checked by Creusot, never called")]
pub(crate) fn batch_order_independent(
    d0: Dbm,
    cs: Seq<Constraint>,
    ds: Seq<Constraint>,
    r1: Dbm,
    r2: Dbm,
) {
    pearlite! {
        proof_assert!(forall<u: crate::dbm::proof::Val> conj(cs, cs.len(), u) == conj(ds, ds.len(), u));
        r1.eq_semantic(r2)
    }
}

// ----- the full-closure path -----

impl Dbm {
    /// `close(self ∧ cs)` by tightening every entry and running the full
    /// closure of `dbm.rs`. The indices must already be validated.
    #[check(terminates)]
    #[requires(all_valid(cs@, self.variables_logic()))]
    #[ensures(match result {
        Ok(z) => z.variables_logic() == self.variables_logic()
            && forall<u: crate::dbm::proof::Val> z.zone(u) == (self.zone(u) && conj(cs@, cs@.len(), u)),
        Err(e) => e == Error::Range && exists<m: Matrix> closure_failure_at(self, cs@, m),
    })]
    fn constrain_all_by_closure(self, cs: &[Constraint]) -> Result<Dbm, Error> {
        let orig = snapshot!(self);
        let n = snapshot!(self.variables_logic());
        snapshot!(self.model());
        let empty = self.empty_like();
        let mut m = match self.into_matrix() {
            Some(m) => m,
            None => return Ok(empty),
        };
        snapshot!(m.model());
        let mut t: usize = 0;
        #[invariant(t@ <= cs@.len())]
        #[invariant(m.dim_logic() == *n + 1)]
        #[invariant(forall<u: crate::dbm::proof::Val> m.zone(u) == (orig.zone(u) && conj(cs@, t@, u)))]
        #[variant(cs@.len() - t@)]
        while t < cs.len() {
            let c = cs[t];
            let (i, j, b) = (c.i().index(), c.j().index(), c.bound());
            let before = snapshot!(m);
            snapshot!(before.model());
            m.tighten(i, j, b);
            snapshot!(m.model());
            snapshot!(order_refines(b, before.at(i@, j@)));
            snapshot!(crate::bounds::le_total(b@, before.at(i@, j@)@));
            snapshot!(crate::dbm::proof::bmin_spec(before.at(i@, j@)@, b@));
            proof_assert!(m.at(i@, j@)@ == crate::dbm::proof::bmin(before.at(i@, j@)@, b@));
            proof_assert!(forall<k: Int, l: Int> 0 <= k && k <= *n && 0 <= l && l <= *n ==>
            m.mmat()[k][l] == if k == i@ && l == j@ {
                crate::dbm::proof::bmin(before.mmat()[i@][j@], b@)
            } else {
                before.mmat()[k][l]
            });
            snapshot!(proof::tighten_zone(before.mmat(), m.mmat(), *n + 1, i@, j@, b@));
            t += 1;
        }
        let last = snapshot!(m);
        match m.close() {
            Ok(z) => Ok(z),
            Err(e) => {
                proof_assert!(closure_failure_at(*orig, cs@, *last));
                Err(e)
            }
        }
    }
}

// ----- the incremental algorithm -----

/// The constant sum of two finite bounds, exactly (`as`: a lossless
/// widening that, unlike `i64::from`, has a Creusot specification).
#[check(terminates)]
#[ensures(match (a@, b@) {
    (BoundModel::Lt(x) | BoundModel::Le(x), BoundModel::Lt(y) | BoundModel::Le(y)) =>
        result@ == x + y,
    _ => true,
})]
#[allow(clippy::cast_lossless)]
fn constant_sum(a: Bound, b: Bound) -> i64 {
    snapshot!(view_representable(a));
    snapshot!(view_representable(b));
    a.constant().unwrap_or(0) as i64 + b.constant().unwrap_or(0) as i64
}

/// Whether `a + b ≺ Le 0`, decided exactly. An unrepresentable finite sum
/// is not an error here, because it is only compared, never stored.
#[check(terminates)]
#[ensures(result == !BoundModel::Le(0).le(a@.add(b@)))]
pub(crate) fn below_le_zero(a: Bound, b: Bound) -> bool {
    if a.is_infinite() || b.is_infinite() {
        return false;
    }
    match a.checked_add(b) {
        Ok(s) => {
            snapshot!(order_refines(s, Bound::LE_ZERO));
            tighter(s, Bound::LE_ZERO)
        }
        // |sum| > MAX_CONSTANT ≥ 1, so its sign decides.
        Err(_) => constant_sum(a, b) < 0,
    }
}

/// `Some(a + b)` if that finite sum is strictly tighter than `cur`, `None`
/// if it is not. `Err(Range)` only if it is tighter but unrepresentable,
/// i.e. the result entry itself would be unrepresentable. Used once per row
/// for the row-skip test; whole rows use `Matrix::relax_row`.
#[check(terminates)]
#[requires(a@ != BoundModel::Inf && b@ != BoundModel::Inf)]
#[ensures(match result {
    Ok(Some(s)) => s@ == a@.add(b@) && !cur@.le(a@.add(b@)),
    Ok(None) => cur@.le(a@.add(b@)),
    Err(e) => e == Error::Range && !cur@.le(a@.add(b@)) && !a@.add(b@).representable(),
})]
fn relax(cur: Bound, a: Bound, b: Bound) -> Result<Option<Bound>, Error> {
    snapshot!(view_representable(cur));
    match a.checked_add(b) {
        Ok(s) => {
            snapshot!(order_refines(s, cur));
            snapshot!(crate::bounds::le_total(s@, cur@));
            Ok(if tighter(s, cur) { Some(s) } else { None })
        }
        // Below MIN_CONSTANT: tighter than every bound. Above MAX_CONSTANT:
        // tighter than ∞ only.
        Err(e) => {
            if constant_sum(a, b) < 0 || cur.is_infinite() {
                Err(e)
            } else {
                Ok(None)
            }
        }
    }
}

/// Closes the canonical matrix `m` after tightening entry `(i, j)` to `b`,
/// using two row-update phases. The new bound must be strictly tighter and
/// consistent with the original zone (`b + D[j][i] ≽ Le 0`), with `i ≠ j`.
/// On `Err(Range)`, the partially updated matrix must be discarded.
#[check(terminates)]
#[requires(m.canonical_logic())]
#[requires(i@ < m.dim_logic() && j@ < m.dim_logic())]
#[requires(!m.mmat()[i@][j@].le(b@) && edge_ok(m.mmat(), i@, j@, b@))]
#[ensures((^m).dim_logic() == m.dim_logic())]
#[ensures(match result {
    Ok(()) => forall<k: Int, l: Int> 0 <= k && k < m.dim_logic() && 0 <= l && l < m.dim_logic() ==>
        (^m).at(k, l)@ == edge(m.mmat(), i@, j@, b@)[k][l],
    Err(e) => e == Error::Range && edge_unrepresentable(m.mmat(), m.dim_logic(), i@, j@, b@),
})]
fn close_edge(m: &mut Matrix, i: usize, j: usize, b: Bound) -> Result<(), Error> {
    let d = m.dimension();
    let m0 = snapshot!(*m);
    let f = snapshot!(m.mmat());
    let e = snapshot!(edge(*f, i@, j@, b@));
    snapshot!(m0.model());
    snapshot!(proof::tighten_distinct(*f, d@, i@, j@, b@));
    debug_assert!(i < d && j < d && i != j);
    // D'[i][l] = min(D[i][l], b ⊕ D[j][l]).
    snapshot!(proof::phase1(*f, d@, i@, j@, b@));
    if m.relax_row(i, j, b) {
        return Err(Error::Range);
    }
    proof_assert!(forall<l: Int> 0 <= l && l < d@ ==> {
        proof::relax_min(f[i@][l], b@, f[j@][l], m.at(i@, l)@); m.at(i@, l)@ == e[i@][l]
    });
    // Row `i` is final; every other row is still the input's until its turn.
    let mut k: usize = 0;
    #[invariant(k@ <= d@ && m.dim_logic() == d@)]
    #[invariant(forall<k2: Int, l: Int> 0 <= k2 && k2 < d@ && 0 <= l && l < d@ ==>
        if k2 == i@ || k2 < k@ { m.at(k2, l)@ == e[k2][l] } else { m.at(k2, l) == m0.at(k2, l) })]
    #[variant(d@ - k@)]
    while k < d {
        proof_assert!(f[k@][i@] == BoundModel::Inf ==> {
            proof::infinite_row(*f, i@, j@, b@, k@); true
        });
        proof_assert!(f[k@][j@].le(f[k@][i@].add(b@)) ==> {
            proof::skip(*f, d@, i@, j@, b@, k@); true
        });
        proof_assert!(!f[k@][j@].le(f[k@][i@].add(b@)) && !f[k@][i@].add(b@).representable() ==> {
            proof::skip_test_unrepresentable(*f, d@, i@, j@, b@, k@); true
        });
        snapshot!(proof::phase2(*f, d@, i@, j@, b@, k@));
        proof_assert!(forall<l: Int> 0 <= l && l < d@
        && relax_needed(f[k@][l], f[k@][i@], e[i@][l]) && !f[k@][i@].add_in_range(e[i@][l]) ==> {
            proof::add_repr(f[k@][i@], e[i@][l]);
            proof::edge_unrep_intro(*f, d@, i@, j@, b@, k@, l);
            true
        });
        let before = snapshot!(*m);
        let ki = m.get(k, i);
        if k != i && !ki.is_infinite() {
            // Update unless D[k][i] ⊕ b ≽ D[k][j].
            let tightens = match relax(m.get(k, j), ki, b) {
                Ok(s) => s.is_some(),
                Err(e) => return Err(e),
            };
            if tightens {
                // D'[k][l] = min(D[k][l], D[k][i] ⊕ D'[i][l]).
                if m.relax_row(k, i, ki) {
                    return Err(Error::Range);
                }
                proof_assert!(forall<l: Int> 0 <= l && l < d@ ==> {
                    proof::relax_min(f[k@][l], f[k@][i@], e[i@][l], m.at(k@, l)@);
                    m.at(k@, l)@ == e[k@][l]
                });
            }
        }
        proof_assert!(forall<k2: Int, l: Int> 0 <= k2 && k2 < d@ && k2 != k@ && 0 <= l && l < d@ ==>
            m.at(k2, l) == before.at(k2, l));
        k += 1;
    }
    Ok(())
}

/// `close(z ∧ xᵢ − xⱼ ⋈ b)` for validated indices.
#[check(terminates)]
#[requires(i@ <= z.variables_logic() && j@ <= z.variables_logic())]
#[ensures(match result {
    Ok(r) => r.variables_logic() == z.variables_logic()
        && (forall<u: crate::dbm::proof::Val> r.zone(u) == (z.zone(u) && sat(b@, u[i@] - u[j@])))
        && (!r.is_empty_logic() ==> meq(r.mmat(), edge(z.mmat(), i@, j@, b@), z.variables_logic() + 1)),
    Err(e) => e == Error::Range && !z.is_empty_logic()
        && single_range_failure(z.mmat(), z.variables_logic() + 1, i@, j@, b@),
})]
// An implied constraint returns the input itself.
#[ensures(!z.is_empty_logic() && z.mmat()[i@][j@].le(b@) ==> result == Ok(z))]
fn constrain_one(z: Dbm, i: usize, j: usize, b: Bound) -> Result<Dbm, Error> {
    let dd = snapshot!(z.variables_logic() + 1);
    let f = snapshot!(z.mmat());
    snapshot!(z.model());
    if z.is_empty() {
        return Ok(z);
    }
    // Implied: D[i][j] ≼ b.
    if !tighter(b, z.entry(i, j)) {
        snapshot!(order_refines(b, z.at(i@, j@)));
        snapshot!(crate::bounds::le_total(b@, f[i@][j@]));
        snapshot!(proof::implied(*f, *dd, i@, j@, b@));
        return Ok(z);
    }
    snapshot!(order_refines(b, z.at(i@, j@)));
    snapshot!(crate::bounds::le_total(b@, f[i@][j@]));
    // Contradiction: the cycle i → j → i is negative.
    if below_le_zero(b, z.entry(j, i)) {
        snapshot!(proof::contradiction(*f, *dd, i@, j@, b@));
        return Ok(z.empty_like());
    }
    snapshot!(edge_canonical(*f, *dd, i@, j@, b@));
    snapshot!(edge_zone(*f, *dd, i@, j@, b@));
    let n = z.variables();
    let mut m = match z.into_matrix() {
        Some(m) => m,
        // Unreachable: `z` is nonempty.
        None => return Dbm::empty(n),
    };
    // One actual clock (d = 2): after the two tests above, the closure
    // changes only (i, j). The other off-diagonal entry gains
    // `b + D[j][i] ≽ Le 0` and each diagonal entry `D[j][i] + b ≽ Le 0`, so
    // neither tightens (the remaining entries are unchanged at `dim ≤ 2`).
    if m.dimension() == 2 {
        snapshot!(m.model());
        snapshot!(proof::one_clock(*f, *dd, i@, j@, b@));
        m.set(i, j, b);
        snapshot!(m.model());
        proof_assert!(meq(m.mmat(), edge(*f, i@, j@, b@), *dd));
        snapshot!(meq_transfer(m.mmat(), edge(*f, i@, j@, b@), *dd));
        return Ok(m.publish_canonical());
    }
    match close_edge(&mut m, i, j, b) {
        Ok(()) => {
            snapshot!(m.model());
            proof_assert!(meq(m.mmat(), edge(*f, i@, j@, b@), *dd));
            snapshot!(meq_transfer(m.mmat(), edge(*f, i@, j@, b@), *dd));
            Ok(m.publish_canonical())
        }
        Err(e) => Err(e),
    }
}

/// How `try_constrain_all` closes a batch.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Strategy {
    /// One incremental closure per constraint.
    Incremental,
    /// Tighten every entry, then one full closure.
    FullClosure,
}

impl Strategy {
    /// `k` incremental closures cost at most `k·d²` (vectorized row
    /// updates, usually far fewer rows), one full closure `d³` (scalar).
    /// Measured on consistent random batches, incremental insertion stays
    /// 3–5× faster than full closure up to `k = 4d` for `n ≥ 16` (on one
    /// Apple Silicon host); in the worst case (every guard rewriting every
    /// row) it can do up to about 4× the entry updates of one full closure.
    #[check(terminates)]
    #[requires(dimension@ <= 46_340)]
    #[ensures(result == if constraints@ <= 4 * dimension@ {
        Strategy::Incremental
    } else {
        Strategy::FullClosure
    })]
    pub(crate) fn choose(dimension: usize, constraints: usize) -> Strategy {
        if constraints <= 4 * dimension {
            Strategy::Incremental
        } else {
            Strategy::FullClosure
        }
    }
}

impl Dbm {
    /// The indices of `c`, or `Err(ClockOutOfRange)` (checked also on `∅_d`).
    #[check(terminates)]
    #[ensures(match result {
        Ok((i, j)) => valid(c, self.variables_logic()) && i@ == c@.0 && j@ == c@.1,
        Err(e) => !valid(c, self.variables_logic()) && clock_error(c, self.variables_logic(), e),
    })]
    pub(crate) fn check_constraint(&self, c: Constraint) -> Result<(usize, usize), Error> {
        let i = match self.check_clock(c.i()) {
            Ok(i) => i,
            Err(e) => return Err(e),
        };
        match self.check_clock(c.j()) {
            Ok(j) => Ok((i, j)),
            Err(e) => Err(e),
        }
    }

    /// Restricts this zone by a difference constraint `c`.
    ///
    /// The result contains **exactly those valuations of this zone that
    /// satisfy `c`**. It is canonical or empty on success. Inconsistent
    /// constraints produce a successful empty zone, not an error.
    ///
    /// # Errors
    ///
    /// - [`Error::ClockOutOfRange`] if either clock in `c` is outside
    ///   this zone's clock range, including when the zone is empty;
    /// - [`Error::Range`] if an exact finite bound needed for the result
    ///   lies outside the representable integer range. Such a bound is
    ///   never saturated, and no partially updated zone is returned.
    ///
    /// # Complexity
    ///
    /// For `d = self.dimension()`, an implied or directly contradictory
    /// constraint is handled in `O(1)` time. Otherwise the worst-case cost
    /// is `O(d²)`.
    #[check(terminates)]
    #[ensures(match result {
        Ok(r) => valid(c, self.variables_logic())
            && r.variables_logic() == self.variables_logic()
            && (forall<u: crate::dbm::proof::Val> r.zone(u) == (self.zone(u) && csat(c, u)))
            && (!r.is_empty_logic() ==> meq(r.mmat(), edge(self.mmat(), c@.0, c@.1, c@.2),
                self.variables_logic() + 1)),
        Err(e) => if valid(c, self.variables_logic()) {
            e == Error::Range && !self.is_empty_logic()
                && single_range_failure(self.mmat(), self.variables_logic() + 1, c@.0, c@.1, c@.2)
        } else {
            clock_error(c, self.variables_logic(), e)
        },
    })]
    pub fn try_constrain(self, c: Constraint) -> Result<Dbm, Error> {
        match self.check_constraint(c) {
            Ok((i, j)) => constrain_one(self, i, j, c.bound()),
            Err(e) => Err(e),
        }
    }

    /// Restricts this zone by the conjunction of all constraints in `cs`.
    ///
    /// The result contains **exactly those valuations of this zone that
    /// satisfy every constraint in `cs`**. An inconsistent conjunction
    /// produces a successful empty zone, not an error. When successful,
    /// the resulting zone is independent of the order and repetition of
    /// the constraints.
    ///
    /// All clock indices are checked before modification. Intermediate
    /// [`Error::Range`] results can depend on the computation order even
    /// when the final mathematical zone would be the same. No partial
    /// result is returned. `ws` does not affect the result.
    ///
    /// # Errors
    ///
    /// - [`Error::ClockOutOfRange`] if any constraint names a clock
    ///   outside this zone, even if the zone is empty;
    /// - [`Error::Range`] if an exact intermediate finite bound
    ///   cannot be represented.
    ///
    /// # Complexity
    ///
    /// For `k = cs.len()` and `d = self.dimension()`, checking arguments
    /// and immediate contradictions costs `O(k)`. The selected strategy then
    /// takes at most `O(k d²)` for `k <= 4d`, or `O(k + d³)` for
    /// larger batches. `ws` is currently unused.
    #[check(terminates)]
    #[ensures(match result {
        Ok(r) => all_valid(cs@, self.variables_logic())
            && r.variables_logic() == self.variables_logic()
            && forall<u: crate::dbm::proof::Val> r.zone(u) == (self.zone(u) && conj(cs@, cs@.len(), u)),
        Err(e) => if all_valid(cs@, self.variables_logic()) {
            e == Error::Range && !self.is_empty_logic() && batch_range_failure(self, cs@)
        } else {
            first_clock_error(cs@, self.variables_logic(), e)
        },
    })]
    // Exactness of the early returns: a contradiction found by the
    // pre-pass, or a batch of implied constraints inserted incrementally,
    // never yields `Err`.
    #[ensures(all_valid(cs@, self.variables_logic()) && !self.is_empty_logic()
        && (some_contradiction(self, cs@)
            || (cs@.len() <= 4 * (self.variables_logic() + 1) && all_implied(self, cs@)))
        ==> match result { Ok(_) => true, Err(_) => false })]
    pub fn try_constrain_all(self, cs: &[Constraint], ws: &mut Workspace) -> Result<Dbm, Error> {
        let _ = ws;
        snapshot!(self.model());
        let strategy = Strategy::choose(self.dimension(), cs.len());
        self.constrain_all_with(cs, strategy)
    }

    /// `try_constrain_all` with an explicit strategy (also used by tests).
    #[check(terminates)]
    #[ensures(match result {
        Ok(r) => all_valid(cs@, self.variables_logic())
            && r.variables_logic() == self.variables_logic()
            && forall<u: crate::dbm::proof::Val> r.zone(u) == (self.zone(u) && conj(cs@, cs@.len(), u)),
        Err(e) => if all_valid(cs@, self.variables_logic()) {
            e == Error::Range && !self.is_empty_logic() && batch_range_failure(self, cs@)
        } else {
            first_clock_error(cs@, self.variables_logic(), e)
        },
    })]
    // Exactness of the early returns: a contradiction found by the
    // pre-pass, or a batch of implied constraints inserted incrementally,
    // never yields `Err`.
    #[ensures(all_valid(cs@, self.variables_logic()) && !self.is_empty_logic()
        && (some_contradiction(self, cs@)
            || (strategy == Strategy::Incremental && all_implied(self, cs@)))
        ==> match result { Ok(_) => true, Err(_) => false })]
    pub(crate) fn constrain_all_with(
        self,
        cs: &[Constraint],
        strategy: Strategy,
    ) -> Result<Dbm, Error> {
        let orig = snapshot!(self);
        let n = snapshot!(self.variables_logic());
        snapshot!(self.model());
        let mut t: usize = 0;
        #[invariant(t@ <= cs@.len())]
        #[invariant(forall<s: Int> 0 <= s && s < t@ ==> valid(cs@[s], *n))]
        #[variant(cs@.len() - t@)]
        while t < cs.len() {
            if let Err(e) = self.check_constraint(cs[t]) {
                return Err(e);
            }
            t += 1;
        }
        if self.is_empty() {
            return Ok(self);
        }
        // O(k) pre-pass: a constraint that contradicts the input on its own
        // (`b + D[j][i] ≺ Le 0`) empties the whole conjunction.
        let mut t: usize = 0;
        #[invariant(t@ <= cs@.len())]
        #[invariant(forall<s: Int> 0 <= s && s < t@ ==>
            edge_ok(orig.mmat(), cs@[s]@.0, cs@[s]@.1, cs@[s]@.2))]
        #[variant(cs@.len() - t@)]
        while t < cs.len() {
            let c = cs[t];
            if below_le_zero(c.bound(), self.entry(c.j().index(), c.i().index())) {
                snapshot!(proof::contradiction(orig.mmat(), *n + 1, c@.0, c@.1, c@.2));
                proof_assert!(forall<u: crate::dbm::proof::Val> !(orig.zone(u) && csat(c, u)));
                return Ok(self.empty_like());
            }
            t += 1;
        }
        match strategy {
            Strategy::FullClosure => self.constrain_all_by_closure(cs),
            Strategy::Incremental => {
                let mut z = self;
                let mut t: usize = 0;
                #[invariant(t@ <= cs@.len())]
                #[invariant(z.variables_logic() == *n)]
                #[invariant(forall<u: crate::dbm::proof::Val> z.zone(u) == (orig.zone(u) && conj(cs@, t@, u)))]
                #[invariant(all_implied(*orig, cs@) ==> z == *orig)]
                #[variant(cs@.len() - t@)]
                while t < cs.len() && !z.is_empty() {
                    let c = cs[t];
                    let before = snapshot!(z);
                    snapshot!(before.model());
                    z = match constrain_one(z, c.i().index(), c.j().index(), c.bound()) {
                        Ok(z) => z,
                        Err(e) => {
                            proof_assert!(incremental_failure_at(*orig, cs@, t@, *before));
                            return Err(e);
                        }
                    };
                    t += 1;
                }
                snapshot!(z.model());
                Ok(z)
            }
        }
    }

    /// Constructs the zone of all nonnegative-real clock valuations
    /// satisfying **every constraint in `cs`**.
    ///
    /// The new zone has `variables` actual clocks plus the fixed
    /// reference clock at zero. With no constraints, it is the universe
    /// of all nonnegative valuations. An inconsistent set of constraints
    /// gives a successful empty zone. The result is canonical or empty.
    /// `ws` is used as temporary workspace; it has no semantic effect.
    ///
    /// # Errors
    ///
    /// - [`Error::TooManyVariables`] if `variables` exceeds
    ///   [`MAX_VARIABLES`];
    /// - [`Error::ClockOutOfRange`] if a constraint refers to a clock
    ///   outside the new zone;
    /// - [`Error::Range`] if exact closure requires an unrepresentable
    ///   finite intermediate bound.
    ///
    /// [`MAX_VARIABLES`]: crate::MAX_VARIABLES
    ///
    /// # Complexity
    ///
    /// For `d = variables + 1` and `k = cs.len()`, allocating the
    /// initial universe takes `O(d²)`. Applying the constraints costs at
    /// most `O(k d²)` for `k <= 4d`, or `O(k + d³)` for larger batches.
    #[check(terminates)]
    #[ensures(match result {
        Ok(r) => variables@ <= crate::MAX_VARIABLES@ && all_valid(cs@, variables@)
            && r.variables_logic() == variables@
            && forall<u: crate::dbm::proof::Val> r.zone(u) ==
                (valuation(variables@ + 1, u) && conj(cs@, cs@.len(), u)),
        Err(e) => if variables@ > crate::MAX_VARIABLES@ {
            e == Error::TooManyVariables { requested: variables }
        } else if all_valid(cs@, variables@) {
            e == Error::Range && exists<z: Dbm> !z.is_empty_logic()
                && z.variables_logic() == variables@
                && (forall<u: crate::dbm::proof::Val> z.zone(u) == valuation(variables@ + 1, u))
                && batch_range_failure(z, cs@)
        } else {
            first_clock_error(cs@, variables@, e)
        },
    })]
    pub fn try_from_constraints(
        variables: usize,
        cs: &[Constraint],
        ws: &mut Workspace,
    ) -> Result<Dbm, Error> {
        match Dbm::universe(variables) {
            Ok(z) => {
                snapshot!(z.model());
                z.try_constrain_all(cs, ws)
            }
            Err(e) => Err(e),
        }
    }
}

#[cfg(creusot)]
pub(crate) mod proof;

#[cfg(test)]
mod tests;
