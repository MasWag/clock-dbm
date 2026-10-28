//! Shared zones with copy-on-write updates.
//!
//! Cloning a [`SharedDbm`] is cheap: handles share a zone until an update
//! needs to change it. Existing snapshots remain unchanged, and an update
//! can reuse uniquely owned storage. Sharing uses single-threaded `Rc`,
//! not `Arc`; to move a zone to another thread, convert it to an owned
//! [`Dbm`] with [`SharedDbm::into_dbm`].
//!
//! Shared and owned zones have the same mathematical operations. The
//! [`SharedDbm`] API explains when copying can affect performance.

// Source-level implementation and proof notes (not part of public API Rustdoc).
// Shared canonical zones with copy-on-write updates.
//
// A shared zone contains valuations of nonnegative-real clocks.
// The notation `∅_d` below means an empty zone with matrix dimension
// `d`, including the fixed reference clock.
//
// [`SharedDbm`] is a reference-counted handle to an immutable [`Dbm`]
// snapshot. Cloning it copies a pointer, not the `(n+1)²` matrix, so a
// model checker can keep many states that share zones. Every operation has
// exactly the result of the [`Dbm`] operation of the same name, including
// every error; only the cost differs.
//
// # Copy-on-write
//
// An update takes `self` by value. If this handle is the only one, the
// matrix is updated in place by the [`Dbm`] kernel, with no copy and no new
// allocation. Otherwise the kernel updates a copy of the matrix, which gets
// a new handle only on `Ok`, so the other handles keep their snapshot. On
// `Err` the handle and any copy are dropped: no other handle changes and no
// partial matrix is published. Published zones stay canonical or empty, as
// for `Dbm`.
//
// Updates whose result is already known from the operands return without
// copying, also for a shared handle. They are exactly the cases in which
// the `Dbm` kernel itself returns before any bound arithmetic, so no
// `Err(Range)` can be skipped:
//
// - an empty input (`∅_d` stays `∅_d`; argument errors are still reported);
// - [`try_constrain`](SharedDbm::try_constrain) with an implied constraint
//   (the same handle) or a constraint that contradicts the zone (a new
//   `∅_d`, without copying the matrix);
// - [`try_constrain_all`](SharedDbm::try_constrain_all) with a constraint
//   that contradicts the zone by itself, or with a batch of implied
//   constraints that the kernel inserts incrementally;
// - [`try_intersect`](SharedDbm::try_intersect) with an empty operand, or,
//   for a shared handle, when `self ⊆ other` (an `O(d²)` comparison instead
//   of an `O(d²)` copy).
//
// # `Rc`, not `Arc`
//
// Zone-graph exploration, the intended use, commonly runs on one
// thread, and every clone and drop of a handle touches the reference count.
// `Rc` keeps those non-atomic. A `SharedDbm` is therefore not `Send`; use
// [`SharedDbm::into_dbm`] to move a zone to another thread.
//
// # Workspace
//
// The operations that take a [`Workspace`] borrow it for one call only, as
// for `Dbm`: one workspace per thread or exploration loop serves
// owned and shared zones of any dimension. Sharing needs no extra scratch
// memory.
//
// # Verification status
//
// Creusot checks this module (details and the trusted
// base in `verification/PROOF_STATUS.md`):
//
// - every operation satisfies the contract of the [`Dbm`] operation of the
//   same name on the zone of the handle, including every error, for
//   unique and shared handles alike (both branches of `Rc::get_mut`);
// - where a shortcut returns without the kernel, the kernel's contract is
//   proved to allow only that outcome: it excludes `Err` there, and equal
//   zones mean equal storage (canonical uniqueness);
// - every handle holds a canonical-or-empty `Dbm`; `Clone`, `From<Dbm>`,
//   `into_dbm` and `as_dbm` preserve the zone, and `==` is `Dbm`'s,
//   whatever the pointers.
//
// Trusted: creusot-std's model of `Rc<T>` as a value of type `T`, and the
// specifications of `Rc::get_mut`, `Rc::strong_count` and
// `Rc::unwrap_or_clone` in `src/shared/rc_spec.rs`, which restate the
// standard library's documentation. Snapshot isolation follows from that
// model, because updates write through `Rc::get_mut` only. `Hash` is
// outside Creusot's subset (as for `Dbm`) and covered by tests.
//
// ```
// use clock_dbm::{Clock, Constraint, SharedDbm, Variable};
//
// let x = Variable::new(1).unwrap();
// let z = SharedDbm::zero(1)?.future();
// let snapshot = z.clone(); // no matrix copy
// let z = z.try_constrain(Constraint::le(x.into(), Clock::ZERO, 5)?)?; // detaches
// assert!(snapshot.is_subset_of(&z).is_ok_and(|b| !b));
// assert!(z.is_subset_of(&snapshot)?);
// # Ok::<(), clock_dbm::Error>(())
// ```

use std::convert::Infallible;
use std::rc::Rc;

use crate::bounds::{Bound, Clock, Constraint, Variable};
#[cfg(creusot)]
use crate::bounds::{le_total, order_refines};
#[cfg(creusot)]
use crate::dbm::proof::{Val, edge_ok};
use crate::dbm::{Dbm, Workspace, tighter};
use crate::error::Error;
#[cfg(creusot)]
use crate::ops::constraints::proof::{all_valid, conj, contradiction, csat, implied, valid};
use crate::ops::constraints::{Strategy, below_le_zero};
#[cfg(creusot)]
use crate::ops::constraints::{all_implied, some_contradiction};
use crate::ops::extra_m::MaxBounds;
#[cfg(creusot)]
use crate::ops::relations::proof::subset_pointwise;
use creusot_std::prelude::*;

#[cfg(creusot)]
mod proof;
#[cfg(creusot)]
mod rc_spec;

/// An immutable zone snapshot with cheap cloning and copy-on-write updates.
///
/// Cloning a `SharedDbm` takes `O(1)` time: it shares the underlying
/// [`Dbm`] rather than copying the matrix. A consuming update reuses unique
/// storage or copies a shared matrix (up to `O(d²)` entries for matrix
/// dimension `d`). No update mutates an existing snapshot. Equality and
/// hashing are semantic and independent of pointer identity.
///
/// `SharedDbm` uses `Rc` and is **not** `Send`. To transfer a zone between
/// threads, first convert it into an owned [`Dbm`] with
/// [`SharedDbm::into_dbm`].
///
/// # Example
///
/// ```
/// use clock_dbm::{Clock, Constraint, SharedDbm};
/// # fn main() -> Result<(), clock_dbm::Error> {
/// let x = Clock::new(1).unwrap();
/// let original = SharedDbm::universe(1)?;
/// let branch = original.clone().try_constrain(Constraint::lt(x, Clock::ZERO, 5)?)?;
/// assert!(branch.is_subset_of(&original)?);
/// assert!(!original.entails(&Constraint::lt(x, Clock::ZERO, 5)?)?);
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
// `Hash` is not translated by Creusot (see `Dbm`). `Rc` hashes the `Dbm` it
// points to, so this is `Dbm`'s hash, consistent with the `PartialEq` below.
#[cfg_attr(not(creusot), derive(Hash))]
#[cfg_attr(not(creusot), allow(clippy::derived_hash_with_manual_eq))]
pub struct SharedDbm(Rc<Dbm>);

impl View for SharedDbm {
    type ViewTy = Dbm;

    /// The zone this handle denotes.
    #[logic(open(self))]
    fn view(self) -> Dbm {
        pearlite! { *self.0@ }
    }
}

/// Every handle denotes a valid `Dbm`: canonical or empty.
impl Invariant for SharedDbm {
    #[logic(open(self))]
    fn invariant(self) -> bool {
        pearlite! { self@.invariant() }
    }
}

impl DeepModel for SharedDbm {
    type DeepModelTy = (Int, Seq<Int>);

    /// That of the zone: independent of the pointer.
    #[logic(open(self))]
    fn deep_model(self) -> (Int, Seq<Int>) {
        pearlite! { self@.deep_model() }
    }
}

/// The view of the result of a shared update.
#[logic(open(self))]
fn lift<E>(r: Result<SharedDbm, E>) -> Result<Dbm, E> {
    pearlite! {
        match r {
            Ok(s) => Ok(s@),
            Err(e) => Err(e),
        }
    }
}

/// `r` and `s` are the same outcome: equal zones (`Dbm`'s `Eq`) or the same
/// error.
#[logic(open(self))]
fn same_outcome(r: Result<Dbm, Error>, s: Result<Dbm, Error>) -> bool {
    pearlite! {
        match (r, s) {
            (Ok(a), Ok(b)) => a.deep_model() == b.deep_model(),
            (Err(e), Err(f)) => e == f,
            _ => false,
        }
    }
}

/// Canonical uniqueness (`Dbm::eq_semantic`) for every pair of valid DBMs:
/// equal zones mean equal storage, so outcomes of the kernel's contract
/// that agree on the zone are one outcome.
#[logic(prophetic)]
#[ensures(forall<a: Dbm, b: Dbm> inv(a) && inv(b) && a.variables_logic() == b.variables_logic()
    && (forall<u: Val> a.zone(u) == b.zone(u)) ==> a.deep_model() == b.deep_model())]
fn unique_zones() {
    pearlite! {
        proof_assert!(forall<a: Dbm, b: Dbm> inv(a) && inv(b)
            && a.variables_logic() == b.variables_logic() ==> {
                a.eq_semantic(b);
                true
            });
    }
}

impl Clone for SharedDbm {
    /// Copies the pointer, not the matrix.
    #[check(terminates)]
    #[ensures(result@ == self@)]
    fn clone(&self) -> SharedDbm {
        SharedDbm(Rc::clone(&self.0))
    }
}

// Written out instead of derived, with the same code as std's `Rc` equality
// for `T: Eq`: handles that share storage are equal without a comparison.
impl PartialEq for SharedDbm {
    #[ensures(result == (self.deep_model() == other.deep_model()))]
    fn eq(&self, other: &SharedDbm) -> bool {
        Rc::ptr_eq(&self.0, &other.0) || *self.0 == *other.0
    }
}

impl Eq for SharedDbm {}

impl From<Dbm> for SharedDbm {
    /// Wraps `z` without copying its matrix.
    #[check(terminates)]
    #[ensures(result@ == z)]
    fn from(z: Dbm) -> SharedDbm {
        SharedDbm(Rc::new(z))
    }
}

impl AsRef<Dbm> for SharedDbm {
    #[check(terminates)]
    #[ensures(*result == self@)]
    fn as_ref(&self) -> &Dbm {
        &self.0
    }
}

// Each operation is specified by the contract of the `Dbm` operation of the
// same name, applied to the zone of the handle: `Dbm::op.postcondition(args,
// result)` is that operation's `ensures`, including every error case.
impl SharedDbm {
    /// Creates a shared zone in which all actual clocks equal zero.
    ///
    /// # Errors
    ///
    /// [`Error::TooManyVariables`] if the requested clock count is too large.
    ///
    /// # Complexity
    ///
    /// `O(d²)` time and space for `d = variables + 1`.
    #[check(terminates)]
    #[ensures(Dbm::zero.postcondition((variables,), lift(result)))]
    pub fn zero(variables: usize) -> Result<SharedDbm, Error> {
        match Dbm::zero(variables) {
            Ok(z) => Ok(SharedDbm::from(z)),
            Err(e) => Err(e),
        }
    }

    /// Creates a shared zone containing all nonnegative-real clock valuations.
    ///
    /// # Errors
    ///
    /// [`Error::TooManyVariables`] if the requested clock count is too large.
    ///
    /// # Complexity
    ///
    /// `O(d²)` time and space for `d = variables + 1`.
    #[check(terminates)]
    #[ensures(Dbm::universe.postcondition((variables,), lift(result)))]
    pub fn universe(variables: usize) -> Result<SharedDbm, Error> {
        match Dbm::universe(variables) {
            Ok(z) => Ok(SharedDbm::from(z)),
            Err(e) => Err(e),
        }
    }

    /// Creates a shared empty zone with the requested number of actual clocks.
    /// The empty zone contains no valuations but retains its clock count.
    ///
    /// # Errors
    ///
    /// [`Error::TooManyVariables`] if the clock count is too large.
    ///
    /// # Complexity
    ///
    /// `O(1)` time, without allocating a matrix.
    #[check(terminates)]
    #[ensures(Dbm::empty.postcondition((variables,), lift(result)))]
    pub fn empty(variables: usize) -> Result<SharedDbm, Error> {
        match Dbm::empty(variables) {
            Ok(z) => Ok(SharedDbm::from(z)),
            Err(e) => Err(e),
        }
    }

    /// Creates a shared zone containing exactly the nonnegative-real
    /// valuations satisfying all constraints in `cs`. An inconsistent set returns
    /// an empty zone. `ws` does not affect the mathematical result.
    ///
    /// # Errors
    ///
    /// [`Error::TooManyVariables`], [`Error::ClockOutOfRange`], or
    /// [`Error::Range`] for an invalid clock count, invalid constraint index,
    /// or unrepresentable finite intermediate bound, respectively.
    ///
    /// # Complexity
    ///
    /// For `d = variables + 1` and `k = cs.len()`, constructing the
    /// universe takes `O(d²)`. Applying the constraints takes at most
    /// `O(k d²)` for `k <= 4d`, or `O(k + d³)` for larger batches.
    #[check(terminates)]
    #[ensures(Dbm::try_from_constraints.postcondition((variables, cs, ws), lift(result)))]
    pub fn try_from_constraints(
        variables: usize,
        cs: &[Constraint],
        ws: &mut Workspace,
    ) -> Result<SharedDbm, Error> {
        match Dbm::try_from_constraints(variables, cs, ws) {
            Ok(z) => Ok(SharedDbm::from(z)),
            Err(e) => Err(e),
        }
    }

    /// Converts this zone into an owned [`Dbm`], copying the matrix only
    /// if another shared handle still references it.
    ///
    /// # Complexity
    ///
    /// `O(1)` for a unique handle; `O(d²)` if another handle shares
    /// its matrix, where `d = self.dimension()`.
    #[ensures(result == self@)]
    pub fn into_dbm(self) -> Dbm {
        Rc::unwrap_or_clone(self.0)
    }

    /// Borrows the underlying canonical or empty [`Dbm`] without copying.
    ///
    /// # Complexity
    ///
    /// `O(1)` time.
    #[check(terminates)]
    #[ensures(*result == self@)]
    pub fn as_dbm(&self) -> &Dbm {
        &self.0
    }

    /// Returns the number of actual clocks, excluding the reference clock.
    ///
    /// # Complexity
    ///
    /// `O(1)` time.
    #[check(terminates)]
    #[ensures(Dbm::variables.postcondition((&self@,), result))]
    pub fn variables(&self) -> usize {
        self.0.variables()
    }

    /// Returns the number of actual clocks plus the reference clock.
    ///
    /// # Complexity
    ///
    /// `O(1)` time.
    #[check(terminates)]
    #[ensures(Dbm::dimension.postcondition((&self@,), result))]
    pub fn dimension(&self) -> usize {
        self.0.dimension()
    }

    /// Returns whether this zone contains no clock valuations.
    ///
    /// # Complexity
    ///
    /// `O(1)` time.
    #[check(terminates)]
    #[ensures(Dbm::is_empty.postcondition((&self@,), result))]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Tests whether every valuation in this zone also belongs to `other`.
    /// An empty zone is a subset of every zone of the same dimension.
    ///
    /// # Errors
    ///
    /// [`Error::DimensionMismatch`] for differing clock counts, including empty zones.
    ///
    /// # Complexity
    ///
    /// `O(d²)` in the worst case for matrix dimension
    /// `d = self.dimension()`; empty-zone cases take `O(1)`.
    #[check(terminates)]
    #[ensures(Dbm::is_subset_of.postcondition((&self@, &other@), result))]
    pub fn is_subset_of(&self, other: &SharedDbm) -> Result<bool, Error> {
        self.0.is_subset_of(&other.0)
    }

    /// Tests whether **every** valuation in this zone satisfies `c`.
    /// This returns `true` for an empty zone (vacuously), unlike
    /// [`SharedDbm::intersects_constraint`].
    ///
    /// # Errors
    ///
    /// [`Error::ClockOutOfRange`] if `c` references a clock outside this zone.
    ///
    /// # Complexity
    ///
    /// `O(1)` time.
    #[check(terminates)]
    #[ensures(Dbm::entails.postcondition((&self@, c), result))]
    pub fn entails(&self, c: &Constraint) -> Result<bool, Error> {
        self.0.entails(c)
    }

    /// Tests whether **some** valuation in this zone satisfies `c`.
    /// This returns `false` for an empty zone, unlike [`SharedDbm::entails`].
    ///
    /// # Errors
    ///
    /// [`Error::ClockOutOfRange`] if `c` references a clock outside this zone.
    ///
    /// # Complexity
    ///
    /// `O(1)` time.
    #[check(terminates)]
    #[ensures(Dbm::intersects_constraint.postcondition((&self@, c), result))]
    pub fn intersects_constraint(&self, c: &Constraint) -> Result<bool, Error> {
        self.0.intersects_constraint(c)
    }

    /// Returns the tightest bound on the difference `clock i - clock j`
    /// satisfied by all valuations in this zone. Returns `None` for an
    /// empty zone or [`Bound::INFINITY`] for an unbounded difference.
    ///
    /// # Errors
    ///
    /// [`Error::ClockOutOfRange`] if either clock index is outside this zone.
    ///
    /// # Complexity
    ///
    /// `O(1)` time.
    #[check(terminates)]
    #[ensures(Dbm::difference_bound.postcondition((&self@, i, j), result))]
    pub fn difference_bound(&self, i: Clock, j: Clock) -> Result<Option<Bound>, Error> {
        self.0.difference_bound(i, j)
    }

    /// Returns the zone of valuations that satisfy this zone and `c`.
    /// An inconsistent constraint returns an empty zone. Other snapshots
    /// remain unchanged.
    ///
    /// # Errors
    ///
    /// [`Error::ClockOutOfRange`] for an invalid clock index, or
    /// [`Error::Range`] if exact closure needs an unrepresentable finite bound.
    ///
    /// # Complexity
    ///
    /// `O(1)` for an implied or directly contradictory constraint;
    /// otherwise `O(d²)` in the worst case, including any copy of
    /// a shared matrix, where `d = self.dimension()`.
    #[ensures(Dbm::try_constrain.postcondition((self@, c), lift(result)))]
    // The shortcuts: every outcome the kernel's contract allows is this one.
    #[ensures(valid(c, self@.variables_logic())
        && (self@.is_empty_logic() || self@.mmat()[c@.0][c@.1].le(c@.2)
            || !edge_ok(self@.mmat(), c@.0, c@.1, c@.2))
        ==> forall<r: Result<Dbm, Error>> Dbm::try_constrain.postcondition((self@, c), r)
            ==> same_outcome(r, lift(result)))]
    pub fn try_constrain(self, c: Constraint) -> Result<SharedDbm, Error> {
        let z = &*self.0;
        proof_assert!({
            unique_zones();
            true
        });
        let (i, j) = z.check_constraint(c)?;
        let b = c.bound();
        let f = snapshot!(z.mmat());
        let dd = snapshot!(z.variables_logic() + 1);
        snapshot!(z.model());
        // The two O(1) tests of `constrain_one`, in the same order.
        if z.is_empty() || !tighter(b, z.entry(i, j)) {
            proof_assert!(z.is_empty_logic() || {
                order_refines(b, z.at(i@, j@));
                le_total(b@, f[i@][j@]);
                implied(*f, *dd, i@, j@, b@);
                true
            });
            return Ok(self);
        }
        snapshot!(order_refines(b, z.at(i@, j@)));
        if below_le_zero(b, z.entry(j, i)) {
            snapshot!(contradiction(*f, *dd, i@, j@, b@));
            let e = z.empty_like();
            snapshot!(e.model());
            return Ok(SharedDbm::from(e));
        }
        self.update(|z| z.try_constrain(c))
    }

    /// Restricts the zone to valuations satisfying every constraint
    /// in `cs`. An inconsistent conjunction returns an empty zone.
    /// Other snapshots remain unchanged; `ws` cannot affect the result.
    ///
    /// # Errors
    ///
    /// [`Error::ClockOutOfRange`] for an invalid clock index, or
    /// [`Error::Range`] for an unrepresentable finite intermediate bound.
    ///
    /// # Complexity
    ///
    /// Let `d = self.dimension()` and `k = cs.len()`. After `O(k)`
    /// argument and contradiction checks, the selected strategy takes
    /// at most `O(k d²)` for `k <= 4d` or `O(k + d³)` for larger batches.
    /// Updating a shared matrix may also require an `O(d²)` copy.
    #[ensures(Dbm::try_constrain_all.postcondition((self@, cs, ws), lift(result)))]
    // The shortcuts: every outcome the kernel's contract allows is this one.
    #[ensures(all_valid(cs@, self@.variables_logic())
        && (self@.is_empty_logic() || some_contradiction(self@, cs@)
            || (cs@.len() <= 4 * (self@.variables_logic() + 1) && all_implied(self@, cs@)))
        ==> forall<r: Result<Dbm, Error>> Dbm::try_constrain_all.postcondition((self@, cs, ws), r)
            ==> same_outcome(r, lift(result)))]
    pub fn try_constrain_all(
        self,
        cs: &[Constraint],
        ws: &mut Workspace,
    ) -> Result<SharedDbm, Error> {
        let z = &*self.0;
        proof_assert!({
            unique_zones();
            true
        });
        let n = snapshot!(z.variables_logic());
        let f = snapshot!(z.mmat());
        snapshot!(z.model());
        // The checks of `Dbm::constrain_all_with` before any update, in the
        // same order: indices, emptiness, single-constraint contradiction.
        let mut t: usize = 0;
        #[invariant(t@ <= cs@.len())]
        #[invariant(forall<s: Int> 0 <= s && s < t@ ==> valid(cs@[s], *n))]
        #[variant(cs@.len() - t@)]
        while t < cs.len() {
            z.check_constraint(cs[t])?;
            t += 1;
        }
        if z.is_empty() {
            return Ok(self);
        }
        let mut t: usize = 0;
        #[invariant(t@ <= cs@.len())]
        #[invariant(forall<s: Int> 0 <= s && s < t@ ==>
            edge_ok(*f, cs@[s]@.0, cs@[s]@.1, cs@[s]@.2))]
        #[variant(cs@.len() - t@)]
        while t < cs.len() {
            let c = cs[t];
            if below_le_zero(c.bound(), z.entry(c.j().index(), c.i().index())) {
                snapshot!(contradiction(*f, *n + 1, c@.0, c@.1, c@.2));
                proof_assert!(forall<u: Val> !(z.zone(u) && csat(c, u)));
                let e = z.empty_like();
                snapshot!(e.model());
                return Ok(SharedDbm::from(e));
            }
            t += 1;
        }
        // Incremental insertion leaves the matrix untouched when every
        // constraint is implied; a full closure might still report `Range`.
        if matches!(
            Strategy::choose(z.dimension(), cs.len()),
            Strategy::Incremental
        ) {
            let mut t: usize = 0;
            #[invariant(t@ <= cs@.len())]
            #[invariant(forall<u: Val> z.zone(u) ==> conj(cs@, t@, u))]
            #[variant(cs@.len() - t@)]
            while t < cs.len() {
                let c = cs[t];
                let b = c.bound();
                if tighter(b, z.entry(c.i().index(), c.j().index())) {
                    break;
                }
                snapshot!(order_refines(b, z.at(c@.0, c@.1)));
                snapshot!(le_total(c@.2, f[c@.0][c@.1]));
                snapshot!(implied(*f, *n + 1, c@.0, c@.1, c@.2));
                t += 1;
            }
            if t == cs.len() {
                return Ok(self);
            }
        }
        self.update(|z| z.try_constrain_all(cs, ws))
    }

    /// Returns the zone of valuations present in both input zones.
    /// An empty intersection is a successful empty result. Other snapshots
    /// remain unchanged.
    ///
    /// # Errors
    ///
    /// [`Error::DimensionMismatch`] for differing clock counts, or
    /// [`Error::Range`] if exact closure needs an unrepresentable finite
    /// bound. `ws` only reuses temporary storage.
    ///
    /// # Complexity
    ///
    /// `O(d³)` in the worst case for matrix dimension
    /// `d = self.dimension()`. Updating a shared matrix may add an
    /// `O(d²)` copy; certain no-change cases avoid copying.
    #[ensures(Dbm::try_intersect.postcondition((self@, &other@, ws), lift(result)))]
    // The shortcuts: every outcome the kernel's contract allows is this one.
    #[ensures(other@.variables_logic() == self@.variables_logic()
        && (self@.is_empty_logic() || other@.is_empty_logic()
            || forall<i: Int, j: Int>
                0 <= i && i <= self@.variables_logic() && 0 <= j && j <= self@.variables_logic()
                ==> self@.at(i, j).deep_model() <= other@.at(i, j).deep_model())
        ==> forall<r: Result<Dbm, Error>> Dbm::try_intersect.postcondition((self@, &other@, ws), r)
            ==> same_outcome(r, lift(result)))]
    pub fn try_intersect(self, other: &SharedDbm, ws: &mut Workspace) -> Result<SharedDbm, Error> {
        let z = &*self.0;
        let o = &*other.0;
        proof_assert!({
            unique_zones();
            true
        });
        z.check_variables(o.variables())?;
        snapshot!(z.model());
        snapshot!(o.model());
        if z.is_empty() {
            return Ok(self);
        }
        if o.is_empty() {
            return Ok(SharedDbm::from(z.empty_like()));
        }
        // With `self ⊆ other` the kernel's meet tightens nothing, so it
        // closes over no pivot and returns `self` unchanged. Only worth
        // checking when the alternative is a copy.
        if Rc::strong_count(&self.0) > 1 && (Rc::ptr_eq(&self.0, &other.0) || z.entries_le(o)) {
            let d = snapshot!(z.variables_logic() + 1);
            proof_assert!(forall<i: Int, j: Int> 0 <= i && i < *d && 0 <= j && j < *d ==> {
                order_refines(z.at(i, j), o.at(i, j));
                (z.at(i, j).deep_model() <= o.at(i, j).deep_model())
                    == z.mmat()[i][j].le(o.mmat()[i][j])
            });
            snapshot!(subset_pointwise(z.mmat(), o.mmat(), *d));
            return Ok(self);
        }
        self.update(|z| z.try_intersect(o, ws))
    }

    /// Computes all valuations obtained by advancing every actual clock
    /// by the **same nonnegative real delay**. The reference clock remains
    /// zero and an empty zone remains empty. This operation cannot fail.
    ///
    /// # Complexity
    ///
    /// `O(d)` when uniquely owned; `O(d²)` when a shared matrix
    /// must first be copied, where `d = self.dimension()`.
    #[ensures(Dbm::future.postcondition((self@,), result@))]
    pub fn future(self) -> SharedDbm {
        let Ok(z) = self.update(|z| Ok::<_, Infallible>(z.future()));
        z
    }

    /// Computes all valuations from which this zone can be reached by
    /// advancing every actual clock by the **same nonnegative real delay**:
    /// `{ v ≥ 0 | v + t lies in this zone for some real t ≥ 0 }`. Upper
    /// bounds and differences between actual clocks are kept; lower bounds
    /// are relaxed only as far as nonnegativity and the differences allow.
    /// The reference clock remains zero, the clock count is unchanged, an
    /// empty zone remains empty, and other handles to the same zone are not
    /// affected. This operation cannot fail.
    ///
    /// # Complexity
    ///
    /// `O(d²)` whether uniquely owned or shared (a shared matrix is first
    /// copied in `O(d²)`), where `d = self.dimension()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use clock_dbm::{Clock, Constraint, SharedDbm};
    ///
    /// let x = Clock::new(1).unwrap();
    /// let z = SharedDbm::universe(1)?.try_constrain(Constraint::le(Clock::ZERO, x, -3)?)?;
    /// let snapshot = z.clone();
    /// let p = z.past(); // x ≥ 3 becomes x ≥ 0
    /// assert_eq!(p, SharedDbm::universe(1)?);
    /// assert!(snapshot.is_subset_of(&p)?);
    /// assert_ne!(snapshot, p);
    /// # Ok::<(), clock_dbm::Error>(())
    /// ```
    #[ensures(Dbm::past.postcondition((self@,), result@))]
    pub fn past(self) -> SharedDbm {
        let Ok(z) = self.update(|z| Ok::<_, Infallible>(z.past()));
        z
    }

    /// Sets clock `x` to zero in every valuation, preserving all
    /// other clock values. An empty zone remains empty.
    ///
    /// # Errors
    ///
    /// [`Error::ClockOutOfRange`] if `x` is not an actual clock of this zone.
    ///
    /// # Complexity
    ///
    /// `O(d)` when uniquely owned, or `O(d²)` if the matrix
    /// must be copied because it is shared, where `d = self.dimension()`.
    #[ensures(Dbm::try_reset_zero.postcondition((self@, x), lift(result)))]
    pub fn try_reset_zero(self, x: Variable) -> Result<SharedDbm, Error> {
        self.update(|z| z.try_reset_zero(x))
    }

    /// Sets clock `x` to `value` in every valuation, keeping all
    /// other clock values unchanged. An empty zone remains empty.
    ///
    /// # Errors
    ///
    /// In order: [`Error::ClockOutOfRange`] if `x` is invalid,
    /// [`Error::NegativeConstant`] if `value` is negative, and
    /// [`Error::Range`] if the zone is nonempty and `value` exceeds
    /// [`crate::MAX_CONSTANT`].
    ///
    /// # Complexity
    ///
    /// `O(d)` when uniquely owned, or `O(d²)` if the matrix
    /// must be copied because it is shared, where `d = self.dimension()`.
    #[ensures(Dbm::try_reset.postcondition((self@, x, value), lift(result)))]
    pub fn try_reset(self, x: Variable, value: i32) -> Result<SharedDbm, Error> {
        self.update(|z| z.try_reset(x, value))
    }

    /// Allows clock `x` to take **any nonnegative real value** while
    /// keeping the values of all other clocks unchanged. The clock remains
    /// part of the zone; an empty zone remains empty.
    ///
    /// # Errors
    ///
    /// [`Error::ClockOutOfRange`] if `x` is not an actual clock of this zone.
    ///
    /// # Complexity
    ///
    /// `O(d)` when uniquely owned, or `O(d²)` if the matrix
    /// must be copied because it is shared, where `d = self.dimension()`.
    #[ensures(Dbm::try_free.postcondition((self@, x), lift(result)))]
    pub fn try_free(self, x: Variable) -> Result<SharedDbm, Error> {
        self.update(|z| z.try_free(x))
    }

    /// Returns a canonical maximal-constant overapproximation
    /// using the ceilings in `bounds`. Every original valuation remains
    /// possible, but additional valuations may appear. Reachability preservation
    /// requires the usual automaton-level restrictions on guards, invariants,
    /// resets and ceilings. An empty zone remains empty.
    ///
    /// # Errors
    ///
    /// [`Error::DimensionMismatch`] if the ceilings cover a different clock
    /// count, or [`Error::Range`] if closure needs an unrepresentable finite
    /// bound. `ws` only reuses temporary storage.
    ///
    /// # Complexity
    ///
    /// For `d = self.dimension()`, normalization takes `O(d²)`;
    /// closure can take `O(d³)` if an entry changes. A shared matrix
    /// may also require an `O(d²)` copy before updating.
    #[ensures(Dbm::try_extrapolate_max.postcondition((self@, bounds, ws), lift(result)))]
    pub fn try_extrapolate_max(
        self,
        bounds: &MaxBounds,
        ws: &mut Workspace,
    ) -> Result<SharedDbm, Error> {
        self.update(|z| z.try_extrapolate_max(bounds, ws))
    }

    /// Applies a consuming `Dbm` operation to the zone of this handle. If
    /// the handle is unique (`Rc::get_mut`), the zone is moved out (leaving
    /// an unallocated `∅_d` placeholder), updated in place by the kernel and
    /// moved back, so the handle keeps its `Rc` allocation. Otherwise the
    /// kernel updates a copy, which gets a new `Rc` only on `Ok`. On `Err`
    /// the handle, with its placeholder or its share, is dropped.
    ///
    /// `Rc::make_mut` would do the same, but its `CloneToUninit` bound
    /// leaves no sound way to tie its copy to `Dbm::clone`'s contract
    /// in the pinned verification environment; `get_mut` needs no such bound.
    // The `Dbm` behind a handle is valid (`inv`); `Rc`'s abstract invariant
    // only exposes that through `Deref` and `get_mut`.
    #[requires(forall<z: Dbm> z == self@ && inv(z) ==> f.precondition((z,)))]
    #[ensures(f.postcondition_once((self@,), lift(result)))]
    fn update<E, F: FnOnce(Dbm) -> Result<Dbm, E>>(mut self, f: F) -> Result<SharedDbm, E> {
        match Rc::get_mut(&mut self.0) {
            Some(slot) => {
                let placeholder = slot.empty_like();
                match f(std::mem::replace(slot, placeholder)) {
                    Ok(z) => {
                        *slot = z;
                        Ok(self)
                    }
                    Err(e) => Err(e),
                }
            }
            None => match f(Dbm::clone(&self.0)) {
                Ok(z) => Ok(SharedDbm::from(z)),
                Err(e) => Err(e),
            },
        }
    }

    /// Whether two handles share storage (tests only; not equality).
    #[cfg(test)]
    pub(crate) fn ptr_eq(&self, other: &SharedDbm) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

#[cfg(test)]
mod tests;
