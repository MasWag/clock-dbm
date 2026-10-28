//! Canonical zones, constructors, and workspaces.
//!
//! Use [`Dbm::zero`] for an all-zero valuation, [`Dbm::universe`] for all
//! nonnegative valuations, [`Dbm::empty`] for an empty zone, or
//! [`Dbm::try_from_constraints`] to construct a constrained zone.
//!
//! An inconsistent guard produces a successful empty zone; invalid arguments
//! and arithmetic range failures instead return an error. Every successful
//! transformation returns a canonical or empty zone. [`Workspace`] is
//! reusable temporary storage for operations that request it.

// Source-level implementation and proof notes (not part of public API Rustdoc).
// Canonical DBM storage, constructors, the private working matrix and full
// Floyd–Warshall closure.
//
// A DBM over `n` nonnegative-real clocks has matrix dimension `n + 1`,
// including the reference clock fixed at zero. `∅_d` denotes an empty
// zone with matrix dimension `d`.
//
// # Storage
//
// A [`Dbm`] over `n` actual clocks is a flat, row-major buffer of `(n+1)²`
// packed [`Bound`]s: entry `(i, j)` (the bound on `xᵢ − xⱼ`, index 0 being
// the reference clock) lives at `i·(n+1) + j`. The
// empty zone `∅_{n+1}` keeps `n` and stores **no** entries, so
// `is_empty()` is `entries.is_empty()` and `Eq`/`Hash` compare
// dimension plus canonical matrix.
//
// Every public `Dbm` is either empty or canonical and nonempty.
// Operations work on a crate-private `Matrix` that may be temporarily
// noncanonical. The only ways back to a `Dbm`
// are `Matrix::close` (full closure) and `Matrix::publish_canonical`
// (for in-place kernels that preserve canonicity). A working matrix is never
// returned to a caller; on `Err` it is dropped.
//
// # Interface for `ops::*`
//
// Operation modules add `impl Dbm` blocks in their own files using
// only: `Dbm::into_matrix`, `Dbm::entry`, `Dbm::check_clock`,
// `Dbm::check_variables`, `Dbm::empty_like`, and the `Matrix` methods
// `universe`, `dimension`, `get`, `set`, `tighten`, `relax_row`, `close`
// and `publish_canonical`. The temporal operations also use the
// whole-row/column updates `add_weak_to_row`, `add_weak_to_column`,
// `copy_column`, `fill_column` and `fill_row`, proved with exact frame
// conditions. The relations use `Dbm::entries_le`, `Matrix::meet`,
// `Matrix::close_pivots` and `Workspace::reset_touched`, proved with
// `Matrix::meet_ready` and the touched-pivot lemmas of `dbm/proof.rs`.
// ExtraM uses `Matrix::close_pivots` with every pivot selected
// (`Workspace::select_all`, `Matrix::full_pivot_ready`) and the equality
// helper `same` for exact bound equality.
//
// # Verification status
//
// Creusot proves this module, on the shipped bodies:
//
// - **safety:** no panic (every index is in bounds), no arithmetic overflow
//   (index arithmetic stays below `d²`, B5), termination, and the exact
//   frame conditions of `get`/`set`/`tighten`;
// - **public invariant:** every [`Dbm`] is empty or canonical (C2–C4;
//   C1 is the
//   `Bound` invariant; C5 follows by `proof::canonical_nonempty`). Every
//   constructor, `Clone`, `Matrix::close` and `Matrix::publish_canonical`
//   (under its `canonical` precondition) establish it;
// - **closure correctness:** `Matrix::close` returns a `Dbm`
//   with exactly the matrix's zone over nonnegative real valuations (so
//   `∅_d` iff that zone is empty, strict-zero cycles included), or
//   `Err(Range)` only when an exact intermediate sum is unrepresentable;
//   `Err(Range)` is impossible when every finite input constant has
//   magnitude `≤ B` with `B · 2^d ≤ MAX_CONSTANT`;
// - **semantic equality:** two valid DBMs with
//   the same number of variables have equal storage, i.e. `==`, iff they
//   denote the same zone (`Dbm::eq_semantic`). The core is the uniqueness
//   of canonical forms, `proof::canonical_unique`.
//
// The ghost layer is `dbm/proof.rs`. The linear range premise of
// a proposed linear sufficient-range premise is **not** proved; see `verification/PROOF_STATUS.md`.

// `?` and the default `PartialOrd::lt` are not terminating calls for Creusot,
// so this module matches on `Result` and compares bounds through `tighter`.
#![allow(clippy::question_mark)]

use crate::bounds::{Bound, BoundModel, Clock, add_weak, add_weak_row, relax_row};
#[cfg(creusot)]
use crate::bounds::{relax_entry, relax_needed};
#[cfg(creusot)]
use proof::{cell, cell_all, cell_read, cell_set};
// Lemmas (logic functions) exist only under Creusot.
#[cfg(creusot)]
use crate::bounds::{
    add_comm_unit, add_sound, below_le_zero_unsat, le_total, le_trans, order_refines,
    view_injective,
};
use crate::error::Error;
use crate::ops::constraints::below_le_zero;
#[cfg(creusot)]
use creusot_std::logic::real::Real;
use creusot_std::{
    invariant::{Invariant, inv},
    prelude::{Clone, Default, PartialEq, *},
};

/// Maximum number of actual clocks supported by a DBM. The reference
/// clock is additional and does not count toward this limit.
pub const MAX_VARIABLES: usize = 46_339;

/// Largest matrix dimension, `MAX_VARIABLES + 1` (a literal for Creusot,
/// checked by a unit test). Used only in specifications.
#[cfg_attr(not(creusot), allow(dead_code))]
const MAX_DIMENSION: usize = 46_340;

/// `a ≺ b`: `a` is strictly tighter than `b` (B2: the code order). Written
/// with the verified `Ord::cmp`.
#[check(terminates)]
#[ensures(result == (a.deep_model() < b.deep_model()))]
pub(crate) fn tighter(a: Bound, b: Bound) -> bool {
    matches!(a.cmp(&b), core::cmp::Ordering::Less)
}

/// `a = b` (the derived `Eq`), written with the verified `Ord::cmp` like
/// [`tighter`], because the derived `PartialEq` is not a terminating call
/// for Creusot. Used by ExtraM.
#[check(terminates)]
#[ensures(result == (a.deep_model() == b.deep_model()))]
#[cfg_attr(not(creusot), allow(dead_code))]
pub(crate) fn same(a: Bound, b: Bound) -> bool {
    matches!(a.cmp(&b), core::cmp::Ordering::Equal)
}

// ----- index arithmetic (B5) -----

/// The square of a dimension fits comfortably in `usize` (and in `u32`).
#[logic]
#[requires(0 <= d && d <= MAX_DIMENSION@)]
#[ensures(0 <= d * d && d * d <= MAX_DIMENSION@ * MAX_DIMENSION@)]
#[ensures(MAX_DIMENSION@ * MAX_DIMENSION@ < usize::MAX@)]
fn square_fits(d: Int) {
    pearlite! { proof_assert!(d * d <= d * MAX_DIMENSION@); }
}

/// In-bounds coordinates map into the flat storage.
#[logic]
#[requires(0 <= i && i < d && 0 <= j && j < d)]
#[ensures(0 <= i * d && i * d + j < d * d)]
fn index_in_bounds(d: Int, i: Int, j: Int) {
    pearlite! { proof_assert!(i * d + d <= d * d); }
}

/// Row-major index arithmetic is injective on in-bounds coordinates.
#[logic]
#[requires(0 <= i && i < d && 0 <= j && j < d)]
#[requires(0 <= k && k < d && 0 <= l && l < d)]
#[ensures((i * d + j == k * d + l) == (i == k && j == l))]
fn index_injective(d: Int, i: Int, j: Int, k: Int, l: Int) {
    pearlite! {
        if i < k {
            proof_assert!(i * d + d <= k * d);
        } else if k < i {
            proof_assert!(k * d + d <= i * d);
        }
    }
}

/// Rows are contiguous and ordered: entry `(k, l)` lies before, inside or
/// after row `r` according to `k` versus `r`.
#[logic]
#[requires(0 <= l && l < d && 0 <= k && 0 <= r)]
#[ensures(k < r ==> k * d + l < r * d)]
#[ensures(r < k ==> r * d + d <= k * d + l)]
#[ensures(k == r ==> r * d <= k * d + l && k * d + l < r * d + d)]
fn row_cmp(d: Int, k: Int, l: Int, r: Int) {
    pearlite! {
        if k < r {
            proof_assert!(k * d + d <= r * d);
        } else if r < k {
            proof_assert!(r * d + d <= k * d);
        }
    }
}

/// Every flat index of a `d × d` matrix is `i·d + j` for in-bounds `i, j`.
#[logic]
#[requires(1 <= d && 0 <= x && x < d * d)]
#[ensures(0 <= x.div_euclid(d) && x.div_euclid(d) < d)]
#[ensures(0 <= x.rem_euclid(d) && x.rem_euclid(d) < d)]
#[ensures(x == x.div_euclid(d) * d + x.rem_euclid(d))]
fn index_cover(d: Int, x: Int) {
    pearlite! {
        if x.div_euclid(d) >= d {
            proof_assert!(x.div_euclid(d) * d >= d * d);
        }
    }
}

/// Storages with equal entries have equal codes (B1 per flat index).
#[logic]
#[requires(1 <= d && s.len() == d * d && t.len() == d * d && 0 <= x && x < d * d)]
#[requires(inv(s[x]) && inv(t[x]))]
#[requires(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
    proof::ent(s, d, i, j) == proof::ent(t, d, i, j))]
#[ensures(s[x].deep_model() == t[x].deep_model())]
fn flat_eq_at(s: Seq<Bound>, t: Seq<Bound>, d: Int, x: Int) {
    pearlite! {
        index_cover(d, x);
        proof::ent_read(s, d, x.div_euclid(d), x.rem_euclid(d));
        proof::ent_read(t, d, x.div_euclid(d), x.rem_euclid(d));
        view_injective(s[x], t[x])
    }
}

/// `e[dst + l] := min(e[dst + l], via + e[src + l])` for `l < n`
/// (`bounds::relax_row` on two disjoint ranges of one slice); every other
/// element is unchanged.
#[check(terminates)]
#[requires(dst@ + n@ <= e@.len() && src@ + n@ <= e@.len())]
#[requires(dst@ + n@ <= src@ || src@ + n@ <= dst@)]
#[requires(n@ <= u32::MAX@)]
#[requires(via@ != BoundModel::Inf)]
#[ensures((^e)@.len() == e@.len())]
#[ensures(forall<x: Int> 0 <= x && x < e@.len() ==>
    if dst@ <= x && x < dst@ + n@ {
        relax_entry(e@[x]@, via@, e@[src@ + (x - dst@)]@, (^e)@[x]@)
    } else {
        (^e)@[x] == e@[x]
    })]
#[ensures(result ==> exists<l: Int> 0 <= l && l < n@
    && relax_needed(e@[dst@ + l]@, via@, e@[src@ + l]@) && !via@.add_in_range(e@[src@ + l]@))]
#[ensures(!result ==> forall<l: Int> 0 <= l && l < n@ ==>
    !(relax_needed(e@[dst@ + l]@, via@, e@[src@ + l]@) && !via@.add_in_range(e@[src@ + l]@)))]
#[inline]
fn relax_range(e: &mut [Bound], dst: usize, src: usize, n: usize, via: Bound) -> bool {
    let old = snapshot!(e@);
    if dst < src {
        let (lo, hi) = e.split_at_mut(src);
        let row = &mut lo[dst..dst + n];
        let from = &hi[..n];
        let r = relax_row(row, via, from);
        proof_assert!(forall<l: Int> 0 <= l && l < n@ ==> (^lo)@[dst@ + l] == (^row)@[l]);
        proof_assert!(forall<x: Int> 0 <= x && x < src@ && (x < dst@ || dst@ + n@ <= x) ==>
            (^lo)@[x] == old[x]);
        proof_assert!(forall<x: Int> 0 <= x && x < (^hi)@.len() ==> (^hi)@[x] == old[src@ + x]);
        r
    } else {
        let (lo, hi) = e.split_at_mut(dst);
        let row = &mut hi[..n];
        let from = &lo[src..src + n];
        let r = relax_row(row, via, from);
        proof_assert!(forall<l: Int> 0 <= l && l < n@ ==> (^hi)@[l] == (^row)@[l]);
        proof_assert!(forall<x: Int> n@ <= x && x < (^hi)@.len() ==> (^hi)@[x] == old[dst@ + x]);
        proof_assert!(forall<x: Int> 0 <= x && x < dst@ ==> (^lo)@[x] == old[x]);
        r
    }
}

// ----- the public zone -----

/// A canonical difference-bound matrix representing a set of clock valuations.
///
/// Each actual clock has a nonnegative real value; clock zero is the fixed
/// reference clock. Each matrix entry bounds the difference between two
/// clocks. A canonical matrix records the tightest implied bounds, while
/// an empty DBM represents no possible valuations.
///
/// Construct with [`Dbm::zero`], [`Dbm::universe`], [`Dbm::empty`], or
/// [`Dbm::try_from_constraints`]. Every successful transformation returns a
/// canonical zone or an explicit empty zone. The number of actual clocks
/// remains fixed; the reference clock has index 0 and is not counted in
/// [`Dbm::variables`].
///
/// Two DBMs compare equal when they have the same number of clocks and
/// represent the same zone, even if constructed from different constraints.
/// Hashing is consistent with that equality.
///
/// # Example
///
/// ```
/// use clock_dbm::{Clock, Constraint, Dbm};
/// # fn main() -> Result<(), clock_dbm::Error> {
/// let x = Clock::new(1).unwrap();
/// let z = Dbm::universe(1)?
///     .try_constrain(Constraint::le(x, Clock::ZERO, 4)?)?;
/// assert!(!z.is_empty());
/// assert_eq!(z.variables(), 1);
/// assert_eq!(z.dimension(), 2);
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
// `Hash` is not translated by Creusot (see `bounds.rs`). It is derived from
// the same fields that the written-out `PartialEq` compares (`variables`,
// then every entry), so `a == b ⇒ hash(a) == hash(b)`.
#[cfg_attr(not(creusot), derive(Hash))]
#[cfg_attr(not(creusot), allow(clippy::derived_hash_with_manual_eq))]
pub struct Dbm {
    variables: u32,
    /// Row-major `(variables+1)²` entries, or none for the empty zone.
    entries: Box<[Bound]>,
}

// Written out instead of derived: creusot-std's `Clone` for `Box<[T]>` does
// not state the length, which the `Dbm` invariant needs; `to_vec` does.
impl Clone for Dbm {
    #[ensures(result == *self)]
    fn clone(&self) -> Dbm {
        let entries = self.entries.to_vec().into_boxed_slice();
        proof_assert!(entries@.ext_eq(self.entries@));
        Dbm {
            variables: self.variables,
            entries,
        }
    }
}

impl DeepModel for Dbm {
    type DeepModelTy = (Int, Seq<Int>);

    /// The number of variables and the packed codes; `Eq` works on it.
    #[logic(open(self))]
    fn deep_model(self) -> (Int, Seq<Int>) {
        pearlite! { (self.variables@, *self.entries.deep_model()) }
    }
}

// Written out instead of derived: the derived comparison of `Box<[Bound]>`
// is an element-by-element loop with an early exit (std's `memcmp`
// specialization covers primitive integers only), which made `==` the
// dominant cost of small-zone transitions (benchmark investigation). This branch-free
// accumulation vectorizes. It compares the same fields as the derive, so it
// stays consistent with the derived `Hash`.
impl PartialEq for Dbm {
    // Not `#[check(terminates)]`: like the derive it replaces, it calls
    // `Bound`'s derived `eq`, which Creusot does not mark as terminating.
    #[ensures(result == (self.deep_model() == other.deep_model()))]
    // The explicit, non-short-circuiting `&` keeps the loop branch-free.
    #[allow(clippy::assign_op_pattern)]
    fn eq(&self, other: &Dbm) -> bool {
        if self.variables != other.variables || self.entries.len() != other.entries.len() {
            return false;
        }
        let (a, b) = (&*self.entries, &*other.entries);
        let mut eq = true;
        let mut l: usize = 0;
        #[invariant(l@ <= a@.len() && a@.len() == b@.len())]
        #[invariant(eq == forall<k: Int> 0 <= k && k < l@ ==>
            a@[k].deep_model() == b@[k].deep_model())]
        #[variant(a@.len() - l@)]
        while l < a.len() {
            eq = eq & (a[l] == b[l]);
            l += 1;
        }
        proof_assert!(eq == (*self.entries.deep_model()).ext_eq(*other.entries.deep_model()));
        eq
    }
}

impl Eq for Dbm {}

impl Invariant for Dbm {
    #[logic(open(self))]
    fn invariant(self) -> bool {
        pearlite! {
            self.variables@ <= MAX_VARIABLES@
                && (self.entries@.len() == 0
                    || proof::canonical(self.entries@, self.variables@ + 1))
        }
    }
}

/// Checks `variables ≤ MAX_VARIABLES` and returns the dimension.
#[check(terminates)]
#[ensures(match result {
    Ok(d) => variables@ <= MAX_VARIABLES@ && d@ == variables@ + 1,
    Err(e) => variables@ > MAX_VARIABLES@ && e == Error::TooManyVariables { requested: variables },
})]
fn checked_dimension(variables: usize) -> Result<usize, Error> {
    if variables <= MAX_VARIABLES {
        Ok(variables + 1)
    } else {
        Err(Error::TooManyVariables {
            requested: variables,
        })
    }
}

/// `d²` entries all equal to `fill`.
#[check(terminates)]
#[requires(1 <= d@ && d@ <= MAX_DIMENSION@)]
#[ensures(result@.len() == d@ * d@)]
#[ensures(forall<x: Int> 0 <= x && x < result@.len() ==> result@[x] == fill)]
fn filled(d: usize, fill: Bound) -> Box<[Bound]> {
    snapshot!(square_fits(d@));
    let len = d * d;
    // A push loop rather than `vec![fill; len]`: creusot-std does not mark
    // `vec::from_elem` as terminating.
    let mut v = Vec::with_capacity(len);
    #[invariant(v@.len() <= len@)]
    #[invariant(forall<x: Int> 0 <= x && x < v@.len() ==> v@[x] == fill)]
    #[variant(len@ - v@.len())]
    while v.len() < len {
        v.push(fill);
    }
    v.into_boxed_slice()
}

/// The entries of `universe`: `Le 0` on row 0 and the diagonal, `∞` elsewhere.
#[check(terminates)]
#[requires(1 <= d@ && d@ <= MAX_DIMENSION@)]
#[ensures(result@.len() == d@ * d@)]
#[ensures(forall<i: Int, j: Int> 0 <= i && i < d@ && 0 <= j && j < d@ ==>
    proof::ent(result@, d@, i, j) == proof::universe_entry(i, j))]
fn universe_entries(d: usize) -> Box<[Bound]> {
    let mut e = filled(d, Bound::INFINITY);
    let len = snapshot!(d@ * d@);
    proof_assert!(forall<a: Int, b: Int> 0 <= a && a < d@ && 0 <= b && b < d@ ==> {
        proof::ent_read(e@, d@, a, b); proof::ent(e@, d@, a, b) == BoundModel::Inf
    });
    let mut i: usize = 0;
    #[invariant(i@ <= d@)]
    #[invariant(e@.len() == *len)]
    #[invariant(inv(e))]
    #[invariant(forall<a: Int, b: Int> 0 <= a && a < d@ && 0 <= b && b < d@ ==>
        proof::ent(e@, d@, a, b) == if (a == 0 && b < i@) || (a == b && a < i@) {
            BoundModel::Le(0)
        } else {
            BoundModel::Inf
        })]
    #[variant(d@ - i@)]
    while i < d {
        snapshot!(index_in_bounds(d@, 0, i@));
        snapshot!(index_in_bounds(d@, i@, i@));
        snapshot!(proof::ent_set_ref(e@, d@, i@, Bound::LE_ZERO));
        let prev = snapshot!(e@);
        e[i] = Bound::LE_ZERO;
        proof_assert!(e@.ext_eq(prev.set(i@, Bound::LE_ZERO)));
        snapshot!(proof::ent_set(e@, d@, i@, i@, Bound::LE_ZERO));
        let prev = snapshot!(e@);
        e[i * d + i] = Bound::LE_ZERO;
        proof_assert!(e@.ext_eq(prev.set(i@ * d@ + i@, Bound::LE_ZERO)));
        i += 1;
    }
    e
}

/// An empty boxed slice (no allocation).
#[check(terminates)]
#[ensures(result@.len() == 0)]
fn no_entries() -> Box<[Bound]> {
    Vec::new().into_boxed_slice()
}

impl Dbm {
    /// Logical entry `(i, j)` of a nonempty DBM.
    #[logic(open(self))]
    pub(crate) fn at(self, i: Int, j: Int) -> Bound {
        pearlite! { self.entries@[i * (self.variables@ + 1) + j] }
    }

    /// Logical number of actual clocks.
    #[logic(open(self))]
    pub(crate) fn variables_logic(self) -> Int {
        pearlite! { self.variables@ }
    }

    /// Logical emptiness.
    #[logic(open(self))]
    pub(crate) fn is_empty_logic(self) -> bool {
        pearlite! { self.entries@.len() == 0 }
    }

    /// `u ∈ γ(self)`: never for the empty zone, otherwise
    /// `u` is a nonnegative valuation satisfying every entry.
    #[logic(open(self))]
    pub(crate) fn zone(self, u: proof::Val) -> bool {
        pearlite! { !self.is_empty_logic() && proof::zone(self.entries@, self.variables@ + 1, u) }
    }

    /// The model matrix of the storage (meaningful when nonempty).
    #[logic(open(self))]
    pub(crate) fn mmat(self) -> proof::MMat {
        pearlite! { proof::mat(self.entries@, self.variables@ + 1) }
    }

    /// A valid DBM in model terms: its entries are `mmat`, its zone is
    /// `mzone(mmat)` unless empty, a nonempty DBM is canonical, and it is
    /// empty iff its zone is (Inv C5).
    #[logic]
    #[requires(inv(self))]
    #[ensures(self.variables_logic() <= MAX_VARIABLES@)]
    #[ensures(!self.is_empty_logic() ==> forall<i: Int, j: Int>
        0 <= i && i <= self.variables_logic() && 0 <= j && j <= self.variables_logic() ==>
            self.at(i, j)@ == self.mmat()[i][j] && inv(self.at(i, j)))]
    #[ensures(forall<u: proof::Val> self.zone(u) ==
        (!self.is_empty_logic() && proof::mzone(self.mmat(), self.variables_logic() + 1, u)))]
    #[ensures(!self.is_empty_logic() ==> proof::mcanonical(self.mmat(), self.variables_logic() + 1))]
    #[ensures(self.is_empty_logic() == forall<u: proof::Val> !self.zone(u))]
    pub(crate) fn model(self) {
        pearlite! {
            let d = self.variables@ + 1;
            proof::mat_bridge(self.entries@, d);
            if !self.is_empty_logic() {
                proof::canonical_nonempty(self.entries@, d);
                proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> {
                    proof::ent_read(self.entries@, d, i, j); index_in_bounds(d, i, j); true
                });
            }
        }
    }

    /// Semantic equality (Theorem 3.1, B6–B7): two valid DBMs with the same
    /// number of variables have equal storage (the `Eq` of [`Dbm`]) iff they
    /// denote the same zone.
    #[logic]
    #[requires(inv(self) && inv(other))]
    #[requires(self.variables_logic() == other.variables_logic())]
    #[ensures((self.deep_model() == other.deep_model()) ==
        forall<u: proof::Val> self.zone(u) == other.zone(u))]
    pub(crate) fn eq_semantic(self, other: Dbm) {
        pearlite! {
            let d = self.variables@ + 1;
            let s = self.entries@;
            let t = other.entries@;
            self.model();
            other.model();
            if s.len() != 0 && t.len() != 0 {
                proof_assert!(s.len() == d * d && t.len() == d * d);
                proof_assert!(forall<x: Int> 0 <= x && x < s.len() ==> inv(s[x]) && inv(t[x]));
                if forall<u: proof::Val> self.zone(u) == other.zone(u) {
                    proof::canonical_unique(self.mmat(), other.mmat(), d);
                    proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
                        proof::ent(s, d, i, j) == proof::ent(t, d, i, j));
                    proof_assert!(forall<x: Int> 0 <= x && x < s.len() ==> {
                        flat_eq_at(s, t, d, x); s[x].deep_model() == t[x].deep_model()
                    });
                    proof_assert!((*self.entries.deep_model()).ext_eq(*other.entries.deep_model()));
                }
                if self.deep_model() == other.deep_model() {
                    proof_assert!(forall<x: Int> 0 <= x && x < s.len() ==> {
                        view_injective(s[x], t[x]); s[x]@ == t[x]@
                    });
                    proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> {
                        proof::ent_read(s, d, i, j); proof::ent_read(t, d, i, j);
                        self.mmat()[i][j] == other.mmat()[i][j]
                    });
                    proof::meq_transfer(self.mmat(), other.mmat(), d);
                }
            } else if s.len() == 0 && t.len() == 0 {
                proof_assert!((*self.entries.deep_model()).ext_eq(*other.entries.deep_model()));
            }
        }
    }

    /// Constructs the zone containing only the all-zero clock valuation.
    ///
    /// Each of the `variables` actual clocks is exactly zero.
    ///
    /// # Errors
    ///
    /// [`Error::TooManyVariables`] if `variables` exceeds [`MAX_VARIABLES`].
    ///
    /// # Complexity
    ///
    /// Constructing the matrix takes `O(d²)` time and space, where
    /// `d = variables + 1` includes the reference clock.
    #[check(terminates)]
    #[ensures(match result {
        Ok(z) => z.variables_logic() == variables@ && !z.is_empty_logic(),
        Err(e) => variables@ > MAX_VARIABLES@ && e == Error::TooManyVariables { requested: variables },
    })]
    pub fn zero(variables: usize) -> Result<Dbm, Error> {
        let d = match checked_dimension(variables) {
            Ok(d) => d,
            Err(e) => return Err(e),
        };
        let entries = filled(d, Bound::LE_ZERO);
        snapshot!(proof::zero_canonical(entries@, d@));
        Ok(Dbm {
            variables: variables as u32,
            entries,
        })
    }

    /// Constructs the zone of **all nonnegative-real valuations** of the
    /// specified number of actual clocks, without any other constraints.
    ///
    /// # Errors
    ///
    /// [`Error::TooManyVariables`] if `variables` exceeds [`MAX_VARIABLES`].
    ///
    /// # Complexity
    ///
    /// Constructing the matrix takes `O(d²)` time and space, where
    /// `d = variables + 1` includes the reference clock.
    #[check(terminates)]
    #[ensures(match result {
        Ok(z) => z.variables_logic() == variables@ && !z.is_empty_logic()
            && forall<u: proof::Val> z.zone(u) == proof::valuation(variables@ + 1, u),
        Err(e) => variables@ > MAX_VARIABLES@ && e == Error::TooManyVariables { requested: variables },
    })]
    pub fn universe(variables: usize) -> Result<Dbm, Error> {
        let d = match checked_dimension(variables) {
            Ok(d) => d,
            Err(e) => return Err(e),
        };
        let entries = universe_entries(d);
        snapshot!(proof::universe_canonical(entries@, d@));
        snapshot!(proof::universe_zone(entries@, d@));
        Ok(Dbm {
            variables: variables as u32,
            entries,
        })
    }

    /// Constructs an empty zone with the specified number of actual clocks.
    ///
    /// The empty zone contains no clock valuations but remembers its
    /// clock count. Empty zones with different clock counts are distinct.
    ///
    /// # Errors
    ///
    /// [`Error::TooManyVariables`] if `variables` exceeds [`MAX_VARIABLES`].
    ///
    /// # Complexity
    ///
    /// `O(1)` time and no matrix allocation; the empty zone retains its
    /// clock count.
    #[check(terminates)]
    #[ensures(match result {
        Ok(z) => z.variables_logic() == variables@ && z.is_empty_logic(),
        Err(e) => variables@ > MAX_VARIABLES@ && e == Error::TooManyVariables { requested: variables },
    })]
    pub fn empty(variables: usize) -> Result<Dbm, Error> {
        if variables > MAX_VARIABLES {
            return Err(Error::TooManyVariables {
                requested: variables,
            });
        }
        Ok(Dbm {
            variables: variables as u32,
            entries: no_entries(),
        })
    }

    /// Returns the number of actual clocks (excluding the reference clock).
    ///
    /// # Complexity
    ///
    /// `O(1)` time.
    #[check(terminates)]
    #[ensures(result@ == self.variables_logic())]
    pub fn variables(&self) -> usize {
        self.variables as usize
    }

    /// Returns the matrix dimension: the actual clock count plus one for
    /// the reference clock.
    ///
    /// # Complexity
    ///
    /// `O(1)` time.
    #[check(terminates)]
    #[ensures(result@ == self.variables_logic() + 1)]
    pub fn dimension(&self) -> usize {
        self.variables as usize + 1
    }

    /// Whether the zone is empty.
    ///
    /// # Complexity
    ///
    /// `O(1)` time.
    #[check(terminates)]
    #[ensures(result == self.is_empty_logic())]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

// ----- crate-private interface for `ops::*` -----

#[allow(dead_code, reason = "crate-private interface for ops::*")]
impl Dbm {
    /// The empty zone with the same number of variables.
    #[check(terminates)]
    #[ensures(result.variables_logic() == self.variables_logic() && result.is_empty_logic())]
    pub(crate) fn empty_like(&self) -> Dbm {
        Dbm {
            variables: self.variables,
            entries: no_entries(),
        }
    }

    /// Entry `(i, j)` of a nonempty DBM, i.e. the canonical (tightest) bound
    /// on `xᵢ − xⱼ`. The caller has validated the indices (for example with
    /// [`Dbm::check_clock`]) and handled the empty case.
    #[check(terminates)]
    #[requires(!self.is_empty_logic())]
    #[requires(i@ <= self.variables_logic() && j@ <= self.variables_logic())]
    #[ensures(result == self.at(i@, j@))]
    pub(crate) fn entry(&self, i: usize, j: usize) -> Bound {
        let d = self.variables as usize + 1;
        snapshot!(square_fits(d@));
        snapshot!(index_in_bounds(d@, i@, j@));
        self.entries[i * d + j]
    }

    /// The index of `c` if it names a clock of this DBM (`0..=variables`),
    /// otherwise `Err(ClockOutOfRange)`. Checked also for empty DBMs.
    #[check(terminates)]
    #[ensures(match result {
        Ok(i) => i@ == c@ && i@ <= self.variables_logic(),
        Err(e) => c@ > self.variables_logic() && match e {
            Error::ClockOutOfRange { clock, variables } =>
                clock@ == c@ && variables@ == self.variables_logic(),
            _ => false,
        },
    })]
    pub(crate) fn check_clock(&self, c: Clock) -> Result<usize, Error> {
        let i = c.index();
        if i <= self.variables as usize {
            Ok(i)
        } else {
            Err(Error::ClockOutOfRange {
                clock: i,
                variables: self.variables as usize,
            })
        }
    }

    /// `Err(DimensionMismatch)` unless `found` equals `self.variables()`.
    #[check(terminates)]
    #[ensures(match result {
        Ok(()) => found@ == self.variables_logic(),
        Err(e) => found@ != self.variables_logic() && match e {
            Error::DimensionMismatch { expected, found: f } =>
                expected@ == self.variables_logic() && f == found,
            _ => false,
        },
    })]
    pub(crate) fn check_variables(&self, found: usize) -> Result<(), Error> {
        if found == self.variables as usize {
            Ok(())
        } else {
            Err(Error::DimensionMismatch {
                expected: self.variables as usize,
                found,
            })
        }
    }

    /// The working matrix of a nonempty DBM (moves the storage, no copy);
    /// `None` for the empty zone.
    #[check(terminates)]
    #[ensures(match result {
        Some(m) => !self.is_empty_logic() && m.dim_logic() == self.variables_logic() + 1
            && m.mmat() == self.mmat()
            && forall<i: Int, j: Int> 0 <= i && i < m.dim_logic() && 0 <= j && j < m.dim_logic()
                ==> m.at(i, j) == self.at(i, j),
        None => self.is_empty_logic(),
    })]
    pub(crate) fn into_matrix(self) -> Option<Matrix> {
        if self.entries.is_empty() {
            None
        } else {
            Some(Matrix {
                dim: self.variables as usize + 1,
                entries: self.entries,
            })
        }
    }
}

// ----- the private working matrix -----

/// A crate-private, possibly noncanonical working matrix (`WInv`):
/// `dim × dim` valid bounds, row-major, `dim ≥ 1`.
///
/// It is never stored in a `Dbm` or returned to a caller except through
/// [`Matrix::close`] or [`Matrix::publish_canonical`].
pub(crate) struct Matrix {
    dim: usize,
    entries: Box<[Bound]>,
}

impl Invariant for Matrix {
    #[logic(open(self))]
    fn invariant(self) -> bool {
        pearlite! {
            1 <= self.dim@ && self.dim@ <= MAX_DIMENSION@
                && self.entries@.len() == self.dim@ * self.dim@
        }
    }
}

// These helpers implement the private interface used by operation modules.
#[allow(dead_code, reason = "crate-private interface for ops::*")]
impl Matrix {
    /// Logical entry `(i, j)`.
    #[logic(open(self))]
    pub(crate) fn at(self, i: Int, j: Int) -> Bound {
        pearlite! { self.entries@[i * self.dim@ + j] }
    }

    /// Logical dimension.
    #[logic(open(self))]
    pub(crate) fn dim_logic(self) -> Int {
        pearlite! { self.dim@ }
    }

    /// `u ∈ γ(self)` over nonnegative valuations.
    #[logic(open(self))]
    pub(crate) fn zone(self, u: proof::Val) -> bool {
        pearlite! { proof::zone(self.entries@, self.dim@, u) }
    }

    /// The model matrix.
    #[logic(open(self))]
    pub(crate) fn mmat(self) -> proof::MMat {
        pearlite! { proof::mat(self.entries@, self.dim@) }
    }

    /// A valid working matrix in model terms: its entries are `mmat`, and
    /// its zone and canonicity are those of `mmat`.
    #[logic]
    #[requires(inv(self))]
    #[ensures(forall<i: Int, j: Int>
        0 <= i && i < self.dim_logic() && 0 <= j && j < self.dim_logic() ==>
            self.at(i, j)@ == self.mmat()[i][j] && inv(self.at(i, j)))]
    #[ensures(forall<u: proof::Val> self.zone(u) == proof::mzone(self.mmat(), self.dim_logic(), u))]
    #[ensures(self.canonical_logic() == proof::mcanonical(self.mmat(), self.dim_logic()))]
    pub(crate) fn model(self) {
        pearlite! {
            let d = self.dim@;
            proof::mat_bridge(self.entries@, d);
            proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> {
                proof::ent_read(self.entries@, d, i, j); index_in_bounds(d, i, j); true
            });
        }
    }

    /// Whether the working matrix satisfies the canonicality conditions.
    #[logic(open(self))]
    pub(crate) fn canonical_logic(self) -> bool {
        pearlite! { proof::canonical(self.entries@, self.dim@) }
    }

    /// Whether closure of this matrix needs an unrepresentable finite sum
    /// (characterized by `proof::range_failure`).
    #[logic(open(self))]
    pub(crate) fn range_failure_logic(self) -> bool {
        pearlite! { proof::range_failure(self.entries@, self.dim@) }
    }

    /// Every finite constant of the matrix lies in `[−b, b]`.
    #[logic(open(self))]
    pub(crate) fn bounded_logic(self, b: Int) -> bool {
        pearlite! { proof::bounded(self.entries@, self.dim@, b) }
    }

    /// The working matrix of [`Dbm::universe`]. `Err(TooManyVariables)` if
    /// `variables > MAX_VARIABLES`. Intended as the starting point of
    /// `try_from_constraints`: tighten entries, then [`Matrix::close`].
    #[check(terminates)]
    #[ensures(match result {
        Ok(m) => m.dim_logic() == variables@ + 1,
        Err(e) => variables@ > MAX_VARIABLES@ && e == Error::TooManyVariables { requested: variables },
    })]
    pub(crate) fn universe(variables: usize) -> Result<Matrix, Error> {
        let d = match checked_dimension(variables) {
            Ok(d) => d,
            Err(e) => return Err(e),
        };
        Ok(Matrix {
            dim: d,
            entries: universe_entries(d),
        })
    }

    /// The dimension `n + 1`.
    #[check(terminates)]
    #[ensures(result@ == self.dim_logic())]
    pub(crate) fn dimension(&self) -> usize {
        self.dim
    }

    /// Row `a := min(row a, via + row c)` entrywise, skipping infinite
    /// entries of row `c` (`bounds::relax_row`); every other row is
    /// unchanged. Returns `true` iff some needed sum is unrepresentable (that
    /// entry is left unchanged). One row of an incremental closure
    /// (`ops::constraints`), `O(d)` and vectorizable.
    #[check(terminates)]
    #[requires(a@ < self.dim_logic() && c@ < self.dim_logic() && a@ != c@)]
    #[requires(via@ != BoundModel::Inf)]
    #[ensures((^self).dim_logic() == self.dim_logic())]
    #[ensures(forall<k: Int, l: Int>
        0 <= k && k < self.dim_logic() && 0 <= l && l < self.dim_logic() ==>
        if k == a@ {
            relax_entry(self.at(a@, l)@, via@, self.at(c@, l)@, (^self).at(a@, l)@)
        } else {
            (^self).at(k, l) == self.at(k, l)
        })]
    #[ensures(result ==> exists<l: Int> 0 <= l && l < self.dim_logic()
        && relax_needed(self.at(a@, l)@, via@, self.at(c@, l)@)
        && !via@.add_in_range(self.at(c@, l)@))]
    #[ensures(!result ==> forall<l: Int> 0 <= l && l < self.dim_logic() ==>
        !(relax_needed(self.at(a@, l)@, via@, self.at(c@, l)@)
            && !via@.add_in_range(self.at(c@, l)@)))]
    #[inline]
    pub(crate) fn relax_row(&mut self, a: usize, c: usize, via: Bound) -> bool {
        let d = self.dim;
        snapshot!(square_fits(d@));
        snapshot!(index_in_bounds(d@, a@, 0));
        snapshot!(index_in_bounds(d@, c@, 0));
        proof_assert!(forall<k: Int, l: Int> 0 <= k && k < d@ && 0 <= l && l < d@ ==> {
            index_in_bounds(d@, k, l); row_cmp(d@, k, l, a@); true
        });
        snapshot!(row_cmp(d@, a@, 0, c@));
        snapshot!(row_cmp(d@, c@, 0, a@));
        let old = snapshot!(*self);
        let (dst, src) = (a * d, c * d);
        let r = relax_range(&mut self.entries, dst, src, d, via);
        proof_assert!(forall<l: Int> 0 <= l && l < d@ ==>
            old.at(a@, l) == old.entries@[dst@ + l] && old.at(c@, l) == old.entries@[src@ + l]);
        proof_assert!(r ==> exists<l: Int> 0 <= l && l < d@
            && relax_needed(old.at(a@, l)@, via@, old.at(c@, l)@)
            && !via@.add_in_range(old.at(c@, l)@));
        proof_assert!(!r ==> forall<l: Int> 0 <= l && l < d@ ==>
            !(relax_needed(old.at(a@, l)@, via@, old.at(c@, l)@)
                && !via@.add_in_range(old.at(c@, l)@)));
        r
    }

    /// Entry `(i, j)`.
    #[check(terminates)]
    #[requires(i@ < self.dim_logic() && j@ < self.dim_logic())]
    #[ensures(result == self.at(i@, j@))]
    pub(crate) fn get(&self, i: usize, j: usize) -> Bound {
        snapshot!(index_in_bounds(self.dim@, i@, j@));
        self.entries[i * self.dim + j]
    }

    /// Overwrites entry `(i, j)`; every other entry is unchanged.
    ///
    /// `WInv` asks for `W[0][j] ≼ Le 0`; [`Matrix::close`] re-imposes it, so
    /// a loosened row 0 is harmless there, but [`Matrix::publish_canonical`]
    /// requires the caller to keep it.
    #[check(terminates)]
    #[requires(i@ < self.dim_logic() && j@ < self.dim_logic())]
    #[ensures((^self).dim_logic() == self.dim_logic())]
    #[ensures(forall<k: Int, l: Int>
        0 <= k && k < self.dim_logic() && 0 <= l && l < self.dim_logic() ==>
        (^self).at(k, l) == if k == i@ && l == j@ { b } else { self.at(k, l) })]
    pub(crate) fn set(&mut self, i: usize, j: usize, b: Bound) {
        let d = snapshot!(self.dim@);
        snapshot!(index_in_bounds(*d, i@, j@));
        proof_assert!(forall<k: Int, l: Int> 0 <= k && k < *d && 0 <= l && l < *d ==> {
            index_injective(*d, i@, j@, k, l); index_in_bounds(*d, k, l); true
        });
        self.entries[i * self.dim + j] = b;
    }

    /// `W[i][j] := min(W[i][j], b)`; every other entry is unchanged. This is
    /// the conjunction with `xᵢ − xⱼ ⋈ b` (before closure).
    #[check(terminates)]
    #[requires(i@ < self.dim_logic() && j@ < self.dim_logic())]
    #[ensures((^self).dim_logic() == self.dim_logic())]
    #[ensures(forall<k: Int, l: Int>
        0 <= k && k < self.dim_logic() && 0 <= l && l < self.dim_logic() ==>
        (^self).at(k, l) == if k == i@ && l == j@ && b.deep_model() < self.at(k, l).deep_model()
            { b } else { self.at(k, l) })]
    pub(crate) fn tighten(&mut self, i: usize, j: usize, b: Bound) {
        if tighter(b, self.get(i, j)) {
            self.set(i, j, b);
        }
    }

    /// Full closure, converting a working matrix into a canonical public zone.
    ///
    /// Returns `Ok(∅_d)` if the matrix denotes the empty zone, the canonical
    /// form otherwise, or `Err(Range)` if a finite intermediate sum is
    /// unrepresentable (never saturated to `∞`). This operation needs no
    /// workspace and takes `O(d³)` time in place.
    ///
    /// Proved: the result denotes exactly the zone of `self` over
    /// nonnegative valuations, it is canonical or `∅_d` by the `Dbm`
    /// invariant (so `∅_d` is returned iff that zone is empty), and
    /// `Err(Range)` only when exact arithmetic leaves the range.
    #[check(terminates)]
    #[ensures(match result {
        Ok(z) => z.variables_logic() == self.dim_logic() - 1
            && forall<u: proof::Val> z.zone(u) == self.zone(u),
        Err(e) => e == Error::Range && self.range_failure_logic()
            && forall<b: Int> 0 <= b && self.bounded_logic(b) ==>
                crate::bounds::MAX_CONSTANT@ < b * proof::pow2(self.dim_logic()),
    })]
    pub(crate) fn close(self) -> Result<Dbm, Error> {
        let d = self.dim;
        let mut entries = self.entries;
        let variables = (d - 1) as u32;
        match close_in_place(&mut entries, d) {
            Ok(true) => Ok(Dbm { variables, entries }),
            Ok(false) => Ok(Dbm {
                variables,
                entries: no_entries(),
            }),
            Err(e) => Err(e),
        }
    }

    /// Publishes a matrix that the caller guarantees to be **canonical and
    /// nonempty** (the public invariant), without closure. For
    /// in-place kernels that preserve canonicity (future, reset, free,
    /// incremental closure).
    ///
    /// The precondition `canonical` (C2–C4) is a proof obligation for each
    /// caller; Creusot rejects a call that does not discharge it.
    /// Debug builds additionally check the invariant by brute force
    /// (`O(d³)`) and panic on a violation.
    #[check(terminates)]
    #[requires(self.canonical_logic())]
    #[ensures(result.variables_logic() == self.dim_logic() - 1 && !result.is_empty_logic())]
    #[ensures(forall<u: proof::Val> result.zone(u) == self.zone(u))]
    #[ensures(result.mmat() == self.mmat())]
    pub(crate) fn publish_canonical(self) -> Dbm {
        #[cfg(all(debug_assertions, not(creusot)))]
        if let Err(msg) = check_canonical(&self.entries, self.dim) {
            panic!("publish_canonical: {msg}");
        }
        Dbm {
            variables: (self.dim - 1) as u32,
            entries: self.entries,
        }
    }
}

// ----- whole-row and whole-column updates (temporal operations) -----
//
// `O(d)` primitives for `ops::temporal`. The contiguous row of
// `add_weak_to_row` goes through a slice (vectorized); columns are strided
// index loops (`x += d`), with the source column addressed relative to the
// target (`x − (a − c)`, `c < a`) so that one bounds check per row remains.
// Each states its exact effect and frame: only the named row or column
// changes. Proved, with termination.

/// `e[dst + l] := via + e[src + l]` for `l < n` (`bounds::add_weak_row` on
/// two disjoint ranges of one slice); every other element is unchanged.
#[check(terminates)]
#[requires(dst@ + n@ <= e@.len() && src@ + n@ <= e@.len())]
#[requires(dst@ + n@ <= src@ || src@ + n@ <= dst@)]
#[requires(exists<c: Int> via@ == BoundModel::Le(c))]
#[requires(forall<l: Int> 0 <= l && l < n@ ==> via@.add_in_range(e@[src@ + l]@))]
#[ensures((^e)@.len() == e@.len())]
#[ensures(forall<x: Int> 0 <= x && x < e@.len() ==>
    if dst@ <= x && x < dst@ + n@ {
        (^e)@[x]@ == via@.add(e@[src@ + (x - dst@)]@)
    } else {
        (^e)@[x] == e@[x]
    })]
#[inline]
fn add_weak_range(e: &mut [Bound], dst: usize, src: usize, n: usize, via: Bound) {
    let old = snapshot!(e@);
    if dst < src {
        let (lo, hi) = e.split_at_mut(src);
        let row = &mut lo[dst..dst + n];
        let from = &hi[..n];
        add_weak_row(row, via, from);
        proof_assert!(forall<l: Int> 0 <= l && l < n@ ==> (^lo)@[dst@ + l] == (^row)@[l]);
        proof_assert!(forall<x: Int> 0 <= x && x < src@ && (x < dst@ || dst@ + n@ <= x) ==>
            (^lo)@[x] == old[x]);
        proof_assert!(forall<x: Int> 0 <= x && x < (^hi)@.len() ==> (^hi)@[x] == old[src@ + x]);
        proof_assert!(forall<x: Int> src@ <= x && x < old.len() ==> (^hi)@[x - src@] == old[x]);
    } else {
        let (lo, hi) = e.split_at_mut(dst);
        let row = &mut hi[..n];
        let from = &lo[src..src + n];
        add_weak_row(row, via, from);
        proof_assert!(forall<l: Int> 0 <= l && l < n@ ==> (^hi)@[l] == (^row)@[l]);
        proof_assert!(forall<x: Int> n@ <= x && x < (^hi)@.len() ==> (^hi)@[x] == old[dst@ + x]);
        proof_assert!(forall<x: Int> 0 <= x && x < dst@ ==> (^lo)@[x] == old[x]);
    }
}

impl Matrix {
    /// Row `a := via + row c` entrywise (`bounds::add_weak`, whose
    /// precondition must hold for every entry; `via` finite and weak,
    /// `a ≠ c`); every other row is unchanged.
    #[check(terminates)]
    #[requires(a@ < self.dim_logic() && c@ < self.dim_logic() && a@ != c@)]
    #[requires(exists<v: Int> via@ == BoundModel::Le(v))]
    #[requires(forall<l: Int> 0 <= l && l < self.dim_logic() ==>
        via@.add_in_range(self.at(c@, l)@))]
    #[ensures((^self).dim_logic() == self.dim_logic())]
    #[ensures(forall<k: Int, l: Int>
        0 <= k && k < self.dim_logic() && 0 <= l && l < self.dim_logic() ==>
        if k == a@ {
            (^self).at(k, l)@ == via@.add(self.at(c@, l)@)
        } else {
            (^self).at(k, l) == self.at(k, l)
        })]
    #[inline]
    pub(crate) fn add_weak_to_row(&mut self, a: usize, c: usize, via: Bound) {
        let d = self.dim;
        assert!(a < d && c < d && a != c);
        snapshot!(square_fits(d@));
        snapshot!(index_in_bounds(d@, a@, 0));
        snapshot!(index_in_bounds(d@, c@, 0));
        proof_assert!(forall<k: Int, l: Int> 0 <= k && k < d@ && 0 <= l && l < d@ ==> {
            index_in_bounds(d@, k, l); row_cmp(d@, k, l, a@); true
        });
        snapshot!(row_cmp(d@, a@, 0, c@));
        snapshot!(row_cmp(d@, c@, 0, a@));
        let old = snapshot!(*self);
        proof_assert!(forall<l: Int> 0 <= l && l < d@ ==> old.at(c@, l) == old.entries@[c@ * d@ + l]);
        add_weak_range(&mut self.entries, a * d, c * d, d, via);
        proof_assert!(forall<l: Int> 0 <= l && l < d@ ==>
            old.at(a@, l) == old.entries@[a@ * d@ + l] && old.at(c@, l) == old.entries@[c@ * d@ + l]);
    }

    /// A working matrix has at least the reference clock.
    #[logic]
    #[requires(inv(self))]
    #[ensures(1 <= self.dim_logic() && self.dim_logic() <= MAX_DIMENSION@)]
    pub(crate) fn dim_pos(self) {}

    /// Every entry is its `cell` (bridges `at` to the loop invariants).
    #[logic]
    #[requires(inv(self))]
    #[ensures(forall<k: Int, l: Int> 0 <= k && k < self.dim_logic() && 0 <= l && l < self.dim_logic() ==>
        self.at(k, l) == cell(self.entries@, self.dim@, k, l))]
    pub(crate) fn at_cell(self) {
        pearlite! { cell_all(self.entries@, self.dim@) }
    }

    /// Entry `(i, j)` read at its precomputed flat index `x = i·d + j`.
    #[check(terminates)]
    #[requires(0 <= *i && *i < self.dim_logic() && j@ < self.dim_logic())]
    #[requires(x@ == *i * self.dim_logic() + j@)]
    #[ensures(result == cell(self.entries@, self.dim@, *i, j@))]
    #[inline(always)]
    fn load(&self, x: usize, i: Snapshot<Int>, j: usize) -> Bound {
        snapshot!(cell_read(self.entries@, self.dim@, *i, j@));
        self.entries[x]
    }

    /// Overwrites entry `(i, j)` at its precomputed flat index `x = i·d + j`;
    /// every other entry is unchanged.
    #[check(terminates)]
    #[requires(0 <= *i && *i < self.dim_logic() && j@ < self.dim_logic())]
    #[requires(x@ == *i * self.dim_logic() + j@)]
    #[ensures((^self).dim_logic() == self.dim_logic())]
    #[ensures(forall<k: Int, l: Int> 0 <= k && k < self.dim_logic() && 0 <= l && l < self.dim_logic() ==>
        cell((^self).entries@, self.dim@, k, l)
            == if k == *i && l == j@ { v } else { cell(self.entries@, self.dim@, k, l) })]
    #[inline(always)]
    fn store(&mut self, x: usize, i: Snapshot<Int>, j: usize, v: Bound) {
        let old = snapshot!(self.entries@);
        snapshot!(cell_set(*old, self.dim@, *i, j@, v));
        self.entries[x] = v;
        proof_assert!(self.entries@.ext_eq(old.set(x@, v)));
    }

    /// Column `a := via + column c` entrywise, in every row (as
    /// [`Matrix::add_weak_to_row`], with `c < a`); every other column is
    /// unchanged.
    #[check(terminates)]
    #[requires(a@ < self.dim_logic() && c@ < a@)]
    #[requires(exists<v: Int> via@ == BoundModel::Le(v))]
    #[requires(forall<k: Int> 0 <= k && k < self.dim_logic() ==>
        via@.add_in_range(self.at(k, c@)@))]
    #[ensures((^self).dim_logic() == self.dim_logic())]
    #[ensures(forall<k: Int, l: Int>
        0 <= k && k < self.dim_logic() && 0 <= l && l < self.dim_logic() ==>
        if l == a@ {
            (^self).at(k, l)@ == via@.add(self.at(k, c@)@)
        } else {
            (^self).at(k, l) == self.at(k, l)
        })]
    #[inline]
    pub(crate) fn add_weak_to_column(&mut self, a: usize, c: usize, via: Bound) {
        let d = self.dim;
        assert!(a < d && c < a);
        snapshot!(square_fits(d@));
        let old = snapshot!(*self);
        snapshot!(old.at_cell());
        let off = a - c;
        let mut x = a;
        let mut i = snapshot!(0);
        #[invariant(0 <= *i && *i <= d@ && x@ == *i * d@ + a@)]
        #[invariant(self.dim == d && self.entries@.len() == d@ * d@)]
        #[invariant(forall<k: Int, l: Int> 0 <= k && k < d@ && 0 <= l && l < d@ ==>
            if l == a@ && k < *i {
                cell(self.entries@, d@, k, l)@ == via@.add(cell(old.entries@, d@, k, c@)@)
            } else {
                cell(self.entries@, d@, k, l) == cell(old.entries@, d@, k, l)
            })]
        #[variant(d@ * d@ - x@)]
        while x < self.entries.len() {
            snapshot!(row_cmp(d@, *i, a@, d@));
            let v = add_weak(self.load(x - off, i, c), via);
            self.store(x, i, a, v);
            x += d;
            i = snapshot!(*i + 1);
        }
        snapshot!(row_cmp(d@, *i, a@, d@));
        snapshot!(self.at_cell());
    }

    /// Column `a := column c` in every row (`c < a`); every other column is
    /// unchanged.
    #[check(terminates)]
    #[requires(a@ < self.dim_logic() && c@ < a@)]
    #[ensures((^self).dim_logic() == self.dim_logic())]
    #[ensures(forall<k: Int, l: Int>
        0 <= k && k < self.dim_logic() && 0 <= l && l < self.dim_logic() ==>
        (^self).at(k, l) == if l == a@ { self.at(k, c@) } else { self.at(k, l) })]
    #[inline]
    pub(crate) fn copy_column(&mut self, a: usize, c: usize) {
        let d = self.dim;
        assert!(a < d && c < a);
        snapshot!(square_fits(d@));
        let old = snapshot!(*self);
        snapshot!(old.at_cell());
        let off = a - c;
        let mut x = a;
        let mut i = snapshot!(0);
        #[invariant(0 <= *i && *i <= d@ && x@ == *i * d@ + a@)]
        #[invariant(self.dim == d && self.entries@.len() == d@ * d@)]
        #[invariant(forall<k: Int, l: Int> 0 <= k && k < d@ && 0 <= l && l < d@ ==>
            cell(self.entries@, d@, k, l) == if l == a@ && k < *i {
                cell(old.entries@, d@, k, c@)
            } else {
                cell(old.entries@, d@, k, l)
            })]
        #[variant(d@ * d@ - x@)]
        while x < self.entries.len() {
            snapshot!(row_cmp(d@, *i, a@, d@));
            let v = self.load(x - off, i, c);
            self.store(x, i, a, v);
            x += d;
            i = snapshot!(*i + 1);
        }
        snapshot!(row_cmp(d@, *i, a@, d@));
        snapshot!(self.at_cell());
    }

    /// Every entry of column `a` becomes `b`; every other column is unchanged.
    #[check(terminates)]
    #[requires(a@ < self.dim_logic())]
    #[ensures((^self).dim_logic() == self.dim_logic())]
    #[ensures(forall<k: Int, l: Int>
        0 <= k && k < self.dim_logic() && 0 <= l && l < self.dim_logic() ==>
        (^self).at(k, l) == if l == a@ { b } else { self.at(k, l) })]
    #[inline]
    pub(crate) fn fill_column(&mut self, a: usize, b: Bound) {
        let d = self.dim;
        assert!(a < d);
        snapshot!(square_fits(d@));
        let old = snapshot!(*self);
        snapshot!(old.at_cell());
        let mut x = a;
        let mut i = snapshot!(0);
        #[invariant(0 <= *i && *i <= d@ && x@ == *i * d@ + a@)]
        #[invariant(self.dim == d && self.entries@.len() == d@ * d@)]
        #[invariant(forall<k: Int, l: Int> 0 <= k && k < d@ && 0 <= l && l < d@ ==>
            cell(self.entries@, d@, k, l) == if l == a@ && k < *i {
                b
            } else {
                cell(old.entries@, d@, k, l)
            })]
        #[variant(d@ * d@ - x@)]
        while x < self.entries.len() {
            snapshot!(row_cmp(d@, *i, a@, d@));
            self.store(x, i, a, b);
            x += d;
            i = snapshot!(*i + 1);
        }
        snapshot!(row_cmp(d@, *i, a@, d@));
        snapshot!(self.at_cell());
    }

    /// Every entry of row `a` becomes `b`; every other row is unchanged.
    #[check(terminates)]
    #[requires(a@ < self.dim_logic())]
    #[ensures((^self).dim_logic() == self.dim_logic())]
    #[ensures(forall<k: Int, l: Int>
        0 <= k && k < self.dim_logic() && 0 <= l && l < self.dim_logic() ==>
        (^self).at(k, l) == if k == a@ { b } else { self.at(k, l) })]
    #[inline]
    pub(crate) fn fill_row(&mut self, a: usize, b: Bound) {
        let d = self.dim;
        assert!(a < d);
        snapshot!(square_fits(d@));
        snapshot!(index_in_bounds(d@, a@, 0));
        let old = snapshot!(*self);
        proof_assert!(forall<k: Int, l: Int> 0 <= k && k < d@ && 0 <= l && l < d@ ==> {
            index_in_bounds(d@, k, l); row_cmp(d@, k, l, a@); true
        });
        let mut x = a * d;
        let end = x + d;
        #[invariant(a@ * d@ <= x@ && x@ <= end@ && end@ == a@ * d@ + d@)]
        #[invariant(self.entries@.len() == d@ * d@ && self.dim == d)]
        #[invariant(forall<y: Int> 0 <= y && y < d@ * d@ ==>
            self.entries@[y] == if a@ * d@ <= y && y < x@ { b } else { old.entries@[y] })]
        #[variant(end@ - x@)]
        while x < end {
            self.entries[x] = b;
            x += 1;
        }
    }
}

/// Full closure in place on a flat row-major `d × d` matrix, using
/// Floyd–Warshall with the diagonal/reference-row preprocessing described
/// by the full-closure algorithm.
///
/// 1. `W[i][i] := min(W[i][i], Le 0)` and `W[0][j] := min(W[0][j], Le 0)`.
/// Both preserve γ over nonnegative clocks. A diagonal that is still
/// below `Le 0` (an input such as `xᵢ − xᵢ < 0`) means γ = ∅. Afterwards
/// every diagonal entry is exactly `Le 0`, and step 3 keeps it so for
/// every row that step 2 changes.
/// 2. Floyd–Warshall: for every pivot `k`, row `i ≠ k` and column `j`,
/// `W[i][j] := min(W[i][j], W[i][k] + W[k][j])`, skipping infinite
/// summands. Row `k` itself is skipped: with `W[k][k] = Le 0` its update
/// is a no-op.
/// 3. After each row, a diagonal below `Le 0` means γ = ∅: return
/// `Ok(false)` immediately (the negative-diagonal test).
///
/// Returns `Ok(true)` if the result is nonempty (then canonical), and
/// `Err(Range)` on an unrepresentable finite sum, leaving the matrix
/// partially updated (the caller drops it).
///
/// Proved using the ghost lemmas in `dbm/proof.rs`:
/// - `Ok(true)`: the result is canonical (`Inv` C2–C4, hence nonempty by
/// `proof::canonical_nonempty`) and denotes the input's zone;
/// - `Ok(false)`: the input's zone is empty;
/// - `Err(Range)`: exact arithmetic left the range (`proof::range_failure`),
/// which cannot happen if every finite input constant has magnitude
/// `≤ B` with `B · 2^d ≤ MAX_CONSTANT` (each pivot at most doubles it).
///
/// The loop invariants justify the optimizations: row `k` is skipped and
/// `W[i][k]` is read once per row because, with `W[k][k] = Le 0`, pivot `k`
/// changes neither; skipped infinite summands give `∞`, which never
/// tightens; and every early exit happens in a state with the input's zone.
#[check(terminates)]
#[requires(1 <= d@ && d@ <= MAX_DIMENSION@)]
#[requires(m@.len() == d@ * d@)]
#[ensures((^m)@.len() == m@.len())]
#[ensures(match result {
    Ok(true) => proof::canonical((^m)@, d@) && proof::same_zone((^m)@, m@, d@),
    Ok(false) => forall<u: proof::Val> !proof::zone(m@, d@, u),
    Err(e) => e == Error::Range && proof::range_failure(m@, d@)
        && forall<b: Int> 0 <= b && proof::bounded(m@, d@, b) ==>
            crate::bounds::MAX_CONSTANT@ < b * proof::pow2(d@),
})]
fn close_in_place(m: &mut [Bound], d: usize) -> Result<bool, Error> {
    let len = snapshot!(m@.len());
    let w = snapshot!(m@);
    snapshot!(square_fits(d@));
    snapshot!(proof::growth_init(m@, d@));

    // Step 1: normalize the diagonal and the reference row.
    let mut i: usize = 0;
    #[invariant(i@ <= d@)]
    #[invariant(m@.len() == *len)]
    #[invariant(inv(m))]
    #[invariant(proof::same_zone(m@, *w, d@))]
    #[invariant(proof::growth(*w, m@, d@, 0))]
    #[invariant(forall<a: Int> 0 <= a && a < i@ ==>
        proof::ent(m@, d@, a, a) == BoundModel::Le(0)
            && proof::ent(m@, d@, 0, a).le(BoundModel::Le(0)))]
    #[variant(d@ - i@)]
    while i < d {
        snapshot!(index_in_bounds(d@, i@, i@));
        snapshot!(index_in_bounds(d@, 0, i@));
        let p = i * d + i;
        snapshot!(proof::ent_read(m@, d@, i@, i@));
        snapshot!(order_refines(Bound::LE_ZERO, m@[p@]));
        snapshot!(order_refines(m@[p@], Bound::LE_ZERO));
        if tighter(Bound::LE_ZERO, m[p]) {
            snapshot!(proof::ent_set(m@, d@, i@, i@, Bound::LE_ZERO));
            snapshot!(proof::zone_diag(m@, d@, i@, Bound::LE_ZERO));
            snapshot!(proof::growth_le0(*w, m@, d@, 0, i@, i@, Bound::LE_ZERO));
            let prev = snapshot!(m@);
            m[p] = Bound::LE_ZERO;
            proof_assert!(m@.ext_eq(prev.set(p@, Bound::LE_ZERO)));
        } else if tighter(m[p], Bound::LE_ZERO) {
            snapshot!(proof::neg_diag_empty(m@, d@, i@));
            return Ok(false);
        } else {
            snapshot!(view_injective(m@[p@], Bound::LE_ZERO));
        }
        snapshot!(proof::ent_read(m@, d@, 0, i@));
        proof_assert!(0 * d@ + i@ == i@);
        snapshot!(order_refines(Bound::LE_ZERO, m@[i@]));
        if tighter(Bound::LE_ZERO, m[i]) {
            snapshot!(proof::zone_ref(m@, d@, i@, Bound::LE_ZERO));
            snapshot!(proof::growth_le0(*w, m@, d@, 0, 0, i@, Bound::LE_ZERO));
            let prev = snapshot!(m@);
            m[i] = Bound::LE_ZERO;
            proof_assert!(m@.ext_eq(prev.set(i@, Bound::LE_ZERO)));
        }
        proof_assert!(proof::ent(m@, d@, i@, i@) == BoundModel::Le(0));
        proof_assert!(proof::ent(m@, d@, 0, i@).le(BoundModel::Le(0)));
        i += 1;
    }
    proof_assert!(proof::diag_le0(m@, d@) && proof::ref_nonneg(m@, d@));

    // Step 2: Floyd–Warshall with early exit on a negative diagonal.
    let mut k: usize = 0;
    #[invariant(k@ <= d@)]
    #[invariant(m@.len() == *len)]
    #[invariant(inv(m))]
    #[invariant(proof::same_zone(m@, *w, d@))]
    #[invariant(proof::diag_le0(m@, d@) && proof::ref_nonneg(m@, d@))]
    #[invariant(proof::tri_upto(m@, d@, k@))]
    #[invariant(proof::growth(*w, m@, d@, k@))]
    #[variant(d@ - k@)]
    while k < d {
        snapshot!(index_in_bounds(d@, k@, 0));
        let old = snapshot!(m@);
        snapshot!(proof::growth_mono(*w, m@, d@, k@, k@ + 1));
        let rk = k * d;
        let mut i: usize = 0;
        #[invariant(i@ <= d@)]
        #[invariant(m@.len() == *len)]
        #[invariant(inv(m))]
        // Rows `< i` other than `k` are relaxed through `k`; the others,
        // including row `k`, are unchanged so far.
        #[invariant(forall<a: Int, b: Int> 0 <= a && a < d@ && 0 <= b && b < d@ ==>
            if a < i@ && a != k@ {
                proof::relax_full(proof::ent(*old, d@, a, b),
                    proof::ent(*old, d@, a, k@).add(proof::ent(*old, d@, k@, b)),
                    proof::ent(m@, d@, a, b))
            } else {
                proof::ent(m@, d@, a, b) == proof::ent(*old, d@, a, b)
            })]
        #[invariant(proof::diag_le0(m@, d@))]
        #[invariant(proof::growth(*w, m@, d@, k@ + 1))]
        #[variant(d@ - i@)]
        while i < d {
            if i != k {
                snapshot!(index_in_bounds(d@, i@, k@));
                snapshot!(index_in_bounds(d@, i@, i@));
                let ri = i * d;
                snapshot!(proof::ent_read(m@, d@, i@, k@));
                let ik = m[ri + k];
                proof_assert!(ik@ == proof::ent(*old, d@, i@, k@));
                if !ik.is_infinite() {
                    let row = snapshot!(m@);
                    let mut j: usize = 0;
                    #[invariant(j@ <= d@)]
                    #[invariant(m@.len() == *len)]
                    #[invariant(inv(m))]
                    #[invariant(forall<b: Int> 0 <= b && b < j@ ==>
                        proof::relax_full(proof::ent(*old, d@, i@, b),
                            ik@.add(proof::ent(*old, d@, k@, b)),
                            proof::ent(m@, d@, i@, b)))]
                    #[invariant(forall<a: Int, b: Int> 0 <= a && a < d@ && 0 <= b && b < d@ ==>
                        a != i@ || j@ <= b ==> proof::ent(m@, d@, a, b) == proof::ent(*row, d@, a, b))]
                    #[invariant(proof::growth(*w, m@, d@, k@ + 1))]
                    #[variant(d@ - j@)]
                    while j < d {
                        snapshot!(index_in_bounds(d@, k@, j@));
                        snapshot!(index_in_bounds(d@, i@, j@));
                        snapshot!(proof::ent_read(m@, d@, k@, j@));
                        snapshot!(proof::ent_read(m@, d@, i@, j@));
                        let kj = m[rk + j];
                        if !kj.is_infinite() {
                            let s = match ik.checked_add(kj) {
                                Ok(s) => s,
                                Err(e) => {
                                    snapshot!(proof::range_failure_intro(*old, *w, d@, i@, k@, j@));
                                    snapshot!(proof::growth_err(*w, *old, d@, k@, i@, j@));
                                    return Err(e);
                                }
                            };
                            snapshot!(order_refines(s, m@[i@ * d@ + j@]));
                            if tighter(s, m[ri + j]) {
                                snapshot!(proof::ent_set(m@, d@, i@, j@, s));
                                proof_assert!(kj@ == proof::ent(*old, d@, k@, j@));
                                snapshot!(proof::growth_sum(*w, *old, m@, d@, k@, i@, j@, s));
                                let prev = snapshot!(m@);
                                m[ri + j] = s;
                                proof_assert!(m@.ext_eq(prev.set(i@ * d@ + j@, s)));
                            }
                        } else {
                            snapshot!(add_comm_unit(ik@, BoundModel::Inf));
                        }
                        proof_assert!(proof::relax_full(proof::ent(*old, d@, i@, j@),
                            ik@.add(proof::ent(*old, d@, k@, j@)),
                            proof::ent(m@, d@, i@, j@)));
                        j += 1;
                    }
                    proof_assert!(forall<a: Int, b: Int> 0 <= a && a < d@ && 0 <= b && b < d@ ==>
                        a != i@ ==> proof::ent(m@, d@, a, b) == proof::ent(*row, d@, a, b));
                    proof_assert!(forall<b: Int> 0 <= b && b < d@ ==>
                        proof::relax_full(proof::ent(*old, d@, i@, b),
                            proof::ent(*old, d@, i@, k@).add(proof::ent(*old, d@, k@, b)),
                            proof::ent(m@, d@, i@, b)));
                    proof_assert!(proof::step_sound(*old, m@, d@, k@));
                    snapshot!(proof::ent_read(m@, d@, i@, i@));
                    snapshot!(order_refines(m@[i@ * d@ + i@], Bound::LE_ZERO));
                    if tighter(m[ri + i], Bound::LE_ZERO) {
                        snapshot!(proof::zone_relax(*old, m@, d@, k@));
                        snapshot!(proof::neg_diag_empty(m@, d@, i@));
                        return Ok(false);
                    }
                    snapshot!(view_injective(m@[i@ * d@ + i@], Bound::LE_ZERO));
                    proof_assert!(proof::ent(m@, d@, i@, i@) == BoundModel::Le(0));
                } else {
                    proof_assert!(forall<b: Int> 0 <= b && b < d@ ==>
                        proof::relax_full(proof::ent(*old, d@, i@, b),
                            ik@.add(proof::ent(*old, d@, k@, b)),
                            proof::ent(m@, d@, i@, b)));
                }
            } else {
                proof_assert!(forall<b: Int> 0 <= b && b < d@ ==> {
                    add_comm_unit(proof::ent(*old, d@, k@, b), BoundModel::Le(0));
                    le_trans(proof::ent(*old, d@, k@, b), proof::ent(*old, d@, k@, b), proof::ent(*old, d@, k@, b));
                    proof::relax_full(proof::ent(*old, d@, k@, b),
                        proof::ent(*old, d@, k@, k@).add(proof::ent(*old, d@, k@, b)),
                        proof::ent(m@, d@, k@, b))
                });
            }
            i += 1;
        }
        proof_assert!(proof::step_full(*old, m@, d@, k@));
        snapshot!(proof::pivot_step(*old, m@, d@, k@));
        snapshot!(proof::zone_relax(*old, m@, d@, k@));
        proof_assert!(forall<b: Int> 0 <= b && b < d@ ==> {
            le_trans(proof::ent(*old, d@, 0, b), proof::ent(*old, d@, 0, b), proof::ent(*old, d@, 0, b));
            le_trans(proof::ent(m@, d@, 0, b), proof::ent(*old, d@, 0, b), BoundModel::Le(0));
            proof::ent(m@, d@, 0, b).le(BoundModel::Le(0))
        });
        k += 1;
    }
    Ok(true)
}

/// Brute-force check of the canonicality conditions C2–C4 for the debug
/// assertion in [`Matrix::publish_canonical`] and for tests. C1 holds by the
/// `Bound` type invariant; C5 follows from C2 and C4.
// Only debug builds and tests call it (`publish_canonical`).
#[cfg(all(not(creusot), any(test, debug_assertions)))]
fn check_canonical(m: &[Bound], d: usize) -> Result<(), String> {
    for i in 0..d {
        if m[i * d + i] != Bound::LE_ZERO {
            return Err(format!(
                "diagonal ({i},{i}) is {:?}, not Le 0",
                m[i * d + i]
            ));
        }
        if m[i] > Bound::LE_ZERO {
            return Err(format!("reference entry (0,{i}) allows a negative clock"));
        }
        for k in 0..d {
            for j in 0..d {
                let (ik, kj, ij) = (m[i * d + k], m[k * d + j], m[i * d + j]);
                let violated = match ik.checked_add(kj) {
                    Ok(via) => via < ij,
                    // Both summands are finite. A sum above MAX_CONSTANT is
                    // looser than every valid bound; one below MIN_CONSTANT
                    // is tighter than every valid bound.
                    Err(_) => {
                        let c = |b: Bound| i64::from(b.constant().unwrap_or(0));
                        c(ik) + c(kj) < 0
                    }
                };
                if violated {
                    return Err(format!("({i},{j}) is looser than ({i},{k}) + ({k},{j})"));
                }
            }
        }
    }
    Ok(())
}

// ----- whole-matrix comparison and meet (relations) -----
//
// Kernels of `ops::relations`, proved.

impl Dbm {
    /// `self[i][j] ≼ other[i][j]` for every `i, j` (`Bound`'s code order is
    /// the tightness order, B2). Both DBMs are nonempty with the same number
    /// of variables. Each row is compared branch-free (the loop vectorizes);
    /// a failing row ends the scan.
    ///
    /// Proved: the result is exactly the entrywise comparison, with
    /// termination and in-bounds row slices.
    #[check(terminates)]
    #[requires(self.variables_logic() == other.variables_logic())]
    #[requires(!self.is_empty_logic() && !other.is_empty_logic())]
    #[ensures(result == forall<i: Int, j: Int>
        0 <= i && i <= self.variables_logic() && 0 <= j && j <= self.variables_logic() ==>
            self.at(i, j).deep_model() <= other.at(i, j).deep_model())]
    // The explicit, non-short-circuiting `&` keeps the loop branch-free.
    #[allow(clippy::assign_op_pattern)]
    pub(crate) fn entries_le(&self, other: &Dbm) -> bool {
        let d = self.variables as usize + 1;
        let (a, b) = (&*self.entries, &*other.entries);
        snapshot!(square_fits(d@));
        proof_assert!(a@.len() == d@ * d@ && b@.len() == d@ * d@);
        let mut i: usize = 0;
        let mut r: usize = 0;
        #[invariant(i@ <= d@ && r@ == i@ * d@)]
        #[invariant(forall<k: Int, l: Int> 0 <= k && k < i@ && 0 <= l && l < d@ ==>
            a@[k * d@ + l].deep_model() <= b@[k * d@ + l].deep_model())]
        #[variant(d@ - i@)]
        while i < d {
            snapshot!(index_in_bounds(d@, i@, d@ - 1));
            proof_assert!(r@ + d@ <= d@ * d@);
            let (ra, rb) = (&a[r..r + d], &b[r..r + d]);
            // `n ≤ ra.len(), rb.len()` lets the compiler drop the bounds checks.
            let n = if ra.len() < rb.len() {
                ra.len()
            } else {
                rb.len()
            };
            let mut le = true;
            let mut l: usize = 0;
            #[invariant(l@ <= n@ && n@ == d@)]
            #[invariant(le == forall<x: Int> 0 <= x && x < l@ ==>
                ra@[x].deep_model() <= rb@[x].deep_model())]
            #[variant(n@ - l@)]
            while l < n {
                le = le & !tighter(rb[l], ra[l]);
                l += 1;
            }
            proof_assert!(forall<x: Int> 0 <= x && x < d@ ==>
                ra@[x] == a@[i@ * d@ + x] && rb@[x] == b@[i@ * d@ + x]);
            if !le {
                return false;
            }
            proof_assert!((i@ + 1) * d@ == i@ * d@ + d@);
            i += 1;
            r += d;
        }
        true
    }
}

impl Matrix {
    /// `W[i][j] := min(W[i][j], E[i][j])` for every `i, j` (the pointwise meet,
    /// before closure), where `W = self` and `E = other` have the same
    /// dimension. Sets `touched[i]` and `touched[j]` for every entry that
    /// `E` strictly tightens, and no other flag.
    ///
    /// Returns `false` as soon as a tightened entry `(i, j)` and the current
    /// opposite entry `(j, i)` close a negative 2-cycle (the exact test
    /// `below_le_zero`, strict-zero cycles included): the intersection is
    /// empty, and the partially updated matrix must be discarded.
    ///
    /// Proved: on `true`, every entry is the pointwise minimum (`E`'s
    /// entry exactly when it is strictly tighter, both endpoints then
    /// touched, otherwise unchanged) and the flags grow exactly by the
    /// endpoints of tightened entries; on `false`, the zones of `W` and `E`
    /// do not intersect. Termination and in-bounds accesses.
    #[check(terminates)]
    #[requires(other.variables_logic() + 1 == self.dim_logic() && !other.is_empty_logic())]
    #[requires(touched@.len() == self.dim_logic())]
    #[ensures((^self).dim_logic() == self.dim_logic())]
    #[ensures((^touched)@.len() == touched@.len())]
    #[ensures(forall<x: Int> 0 <= x && x < self.dim_logic() && touched@[x] ==> (^touched)@[x])]
    #[ensures(result ==> forall<i: Int, j: Int>
        0 <= i && i < self.dim_logic() && 0 <= j && j < self.dim_logic() ==>
        if other.at(i, j).deep_model() < self.at(i, j).deep_model() {
            (^self).at(i, j) == other.at(i, j) && (^touched)@[i] && (^touched)@[j]
        } else {
            (^self).at(i, j) == self.at(i, j)
        })]
    #[ensures(result ==> forall<x: Int> 0 <= x && x < self.dim_logic() && (^touched)@[x] ==>
        touched@[x] || exists<y: Int> 0 <= y && y < self.dim_logic() && (
            other.at(x, y).deep_model() < self.at(x, y).deep_model()
                || other.at(y, x).deep_model() < self.at(y, x).deep_model()))]
    #[ensures(!result ==> forall<u: proof::Val> !(self.zone(u) && other.zone(u)))]
    pub(crate) fn meet(&mut self, other: &Dbm, touched: &mut [bool]) -> bool {
        let d = self.dim;
        let old = snapshot!(*self);
        let t0 = snapshot!(touched@);
        snapshot!(old.model());
        snapshot!(other.model());
        snapshot!(square_fits(d@));
        let mut i: usize = 0;
        let mut r: usize = 0;
        #[invariant(i@ <= d@ && r@ == i@ * d@)]
        #[invariant(self.dim_logic() == d@ && self.entries@.len() == d@ * d@ && touched@.len() == d@)]
        #[invariant(forall<x: Int> 0 <= x && x < d@ && t0[x] ==> touched@[x])]
        #[invariant(forall<a: Int, b: Int> 0 <= a && a < d@ && 0 <= b && b < d@ ==>
            if a < i@ && other.at(a, b).deep_model() < old.at(a, b).deep_model() {
                self.at(a, b) == other.at(a, b) && touched@[a] && touched@[b]
            } else {
                self.at(a, b) == old.at(a, b)
            })]
        #[invariant(forall<x: Int> 0 <= x && x < d@ && touched@[x] ==>
            t0[x] || exists<y: Int> 0 <= y && y < d@ && (
                (x < i@ && other.at(x, y).deep_model() < old.at(x, y).deep_model())
                    || (y < i@ && other.at(y, x).deep_model() < old.at(y, x).deep_model())))]
        #[variant(d@ - i@)]
        while i < d {
            snapshot!(index_in_bounds(d@, i@, d@ - 1));
            // Row `i` of `E`, read through one slice (no per-entry index check).
            let er = &other.entries[r..r + d];
            proof_assert!(d@ == other.variables@ + 1);
            proof_assert!(forall<y: Int> 0 <= y && y < d@ ==>
                er@[y] == other.entries@[r@ + y] && other.at(i@, y) == other.entries@[r@ + y]);
            let mut j: usize = 0;
            #[invariant(j@ <= d@ && self.dim_logic() == d@ && self.entries@.len() == d@ * d@)]
            #[invariant(touched@.len() == d@)]
            #[invariant(forall<y: Int> 0 <= y && y < d@ ==> er@[y] == other.at(i@, y))]
            #[invariant(forall<x: Int> 0 <= x && x < d@ && t0[x] ==> touched@[x])]
            #[invariant(forall<a: Int, b: Int> 0 <= a && a < d@ && 0 <= b && b < d@ ==>
                if (a < i@ || (a == i@ && b < j@))
                    && other.at(a, b).deep_model() < old.at(a, b).deep_model() {
                    self.at(a, b) == other.at(a, b) && touched@[a] && touched@[b]
                } else {
                    self.at(a, b) == old.at(a, b)
                })]
            #[invariant(forall<x: Int> 0 <= x && x < d@ && touched@[x] ==>
                t0[x] || exists<y: Int> 0 <= y && y < d@ && (
                    ((x < i@ || (x == i@ && y < j@))
                        && other.at(x, y).deep_model() < old.at(x, y).deep_model())
                    || ((y < i@ || (y == i@ && x < j@))
                        && other.at(y, x).deep_model() < old.at(y, x).deep_model())))]
            #[variant(d@ - j@)]
            while j < d {
                snapshot!(index_in_bounds(d@, i@, j@));
                let e = er[j];
                proof_assert!(e == other.at(i@, j@));
                let x = r + j;
                proof_assert!(x@ == i@ * d@ + j@ && d@ == self.dim@);
                proof_assert!(self.entries@[x@] == self.at(i@, j@));
                if tighter(e, self.entries[x]) {
                    // Only tightened entries take the proved `set`/`get`.
                    self.set(i, j, e);
                    let back = self.get(j, i);
                    if below_le_zero(e, back) {
                        // `back` is `W[j][i]` or `E[j][i]`: both hold on the
                        // intersection, and so does `e`, so it is empty.
                        proof_assert!(back == old.at(j@, i@) || back == other.at(j@, i@));
                        proof_assert!(forall<u: proof::Val> old.zone(u) && other.zone(u) ==> {
                            add_sound(e@, back@, u[i@] - u[j@], u[j@] - u[i@]);
                            below_le_zero_unsat(e@.add(back@));
                            (u[i@] - u[j@]) + (u[j@] - u[i@]) == Real::from_int(0)
                        });
                        return false;
                    }
                    touched[i] = true;
                    touched[j] = true;
                }
                j += 1;
            }
            proof_assert!((i@ + 1) * d@ == i@ * d@ + d@);
            i += 1;
            r += d;
        }
        true
    }
}

impl Matrix {
    /// The precondition of [`Matrix::close_pivots`]: a `Le 0`
    /// diagonal, a nonnegative reference row, and the triangle inequality
    /// through every pivot that is **not** selected.
    #[logic(open(self))]
    pub(crate) fn pivot_ready(self, pivots: Seq<bool>) -> bool {
        pearlite! {
            pivots.len() == self.dim@
                && proof::diag_le0(self.entries@, self.dim@)
                && proof::ref_nonneg(self.entries@, self.dim@)
                && forall<l: Int> 0 <= l && l < self.dim@ && !pivots[l] ==>
                    proof::tri_through(self.entries@, self.dim@, l)
        }
    }

    /// What [`Matrix::meet`] leaves for [`Matrix::close_pivots`].
    /// Let `w0` be a canonical matrix, `e` a nonempty `Dbm` of the same
    /// dimension, and `w` their pointwise minimum with `t` covering both
    /// endpoints of every tightened entry. Then:
    ///
    /// - `γ(w) = γ(w0) ∩ γ(e)`;
    /// - `w` is ready for the touched-pivot closure. For an untouched `l`,
    /// row and column `l` of `w` are those of `w0`, so
    /// `w[i][j] ≼ w0[i][j] ≼ w0[i][l] + w0[l][j] = w[i][l] + w[l][j]`.
    /// This is the path-free form of "a run of unchanged edges collapses
    /// into one entry of `w0`".
    #[logic]
    #[requires(inv(w0) && inv(w) && inv(e) && !e.is_empty_logic())]
    #[requires(w.dim_logic() == w0.dim_logic() && e.variables_logic() + 1 == w0.dim_logic())]
    #[requires(w0.canonical_logic() && t.len() == w0.dim_logic())]
    #[requires(forall<i: Int, j: Int>
        0 <= i && i < w0.dim_logic() && 0 <= j && j < w0.dim_logic() ==>
        if e.at(i, j).deep_model() < w0.at(i, j).deep_model() {
            w.at(i, j) == e.at(i, j) && t[i] && t[j]
        } else {
            w.at(i, j) == w0.at(i, j)
        })]
    #[ensures(w.pivot_ready(t))]
    #[ensures(forall<u: proof::Val> w.zone(u) == (w0.zone(u) && e.zone(u)))]
    #[ensures(proof::meq(w.mmat(), proof::bmin_mat(w0.mmat(), e.mmat()), w0.dim_logic()))]
    pub(crate) fn meet_ready(w0: Matrix, e: Dbm, w: Matrix, t: Seq<bool>) {
        pearlite! {
            let d = w0.dim@;
            w0.model();
            w.model();
            e.model();
            // The code order of `meet` is the tightness order (B2).
            proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> {
                order_refines(e.at(i, j), w0.at(i, j));
                order_refines(w0.at(i, j), e.at(i, j));
                le_total(w0.mmat()[i][j], e.mmat()[i][j]);
                (w.mmat()[i][j] == w0.mmat()[i][j] && w0.mmat()[i][j].le(e.mmat()[i][j]))
                    || (w.mmat()[i][j] == e.mmat()[i][j] && !w0.mmat()[i][j].le(e.mmat()[i][j])
                        && t[i] && t[j])
            });
            proof::min_closed(w0.mmat(), e.mmat(), w.mmat(), t, d);
        }
    }

    /// With every pivot selected, [`Matrix::pivot_ready`] asks only for a
    /// `Le 0` diagonal and a reference row `≼ Le 0` (ExtraM,: `norm`
    /// keeps both, `extra_m::proof::norm_ready`).
    #[logic]
    #[requires(inv(self))]
    #[requires(pivots.len() == self.dim_logic())]
    #[requires(forall<l: Int> 0 <= l && l < pivots.len() ==> pivots[l])]
    #[requires(forall<i: Int> 0 <= i && i < self.dim_logic() ==>
        self.mmat()[i][i] == BoundModel::Le(0))]
    #[requires(forall<j: Int> 0 <= j && j < self.dim_logic() ==>
        self.mmat()[0][j].le(BoundModel::Le(0)))]
    #[ensures(self.pivot_ready(pivots))]
    pub(crate) fn full_pivot_ready(self, pivots: Seq<bool>) {
        pearlite! { proof::mat_bridge(self.entries@, self.dim@) }
    }

    /// A range failure of this matrix, stated on its model matrix.
    #[logic]
    #[requires(inv(self) && self.range_failure_logic())]
    #[ensures(proof::mrange_failure(self.mmat(), self.dim_logic()))]
    pub(crate) fn range_failure_model(self) {
        pearlite! { proof::mat_bridge(self.entries@, self.dim@) }
    }

    /// Floyd–Warshall restricted to the pivots `k` with `pivots[k]`, each
    /// row relaxed by the proved, vectorized [`Matrix::relax_row`]. Row `k`
    /// is skipped (with `W[k][k] = Le 0` its update is a no-op), and so is a
    /// row with `W[i][k] = ∞`. After each relaxed row, a diagonal entry
    /// below `Le 0` means the zone is empty. `O(p·d²)` for `p` pivots, no
    /// scratch memory.
    ///
    /// The precondition [`Matrix::pivot_ready`] says that every unselected
    /// pivot already satisfies the triangle inequality. For the pointwise
    /// minimum of two canonical matrices with the touched clocks of
    /// [`Matrix::meet`] selected, [`Matrix::meet_ready`] establishes it.
    /// Each full pivot step keeps the triangles that hold and adds its own
    /// (`proof::pivot_keep`), so at the end the matrix is canonical: the
    /// result is the full closure of `self`, computed from the selected
    /// pivots only.
    ///
    /// Proved:
    /// - `Ok(z)`: `z` denotes exactly the zone of `self`. It is `∅_d` iff
    /// that zone is empty (a negative cycle of any length), otherwise
    /// canonical (`publish_canonical`'s precondition is discharged).
    /// - `Err(Range)`: only when an exact needed sum is unrepresentable
    /// (`proof::range_failure`, as for `Matrix::close`). This is never a
    /// way of reporting emptiness.
    /// - Termination and in-bounds accesses.
    #[check(terminates)]
    #[requires(self.pivot_ready(pivots@))]
    #[ensures(match result {
        Ok(z) => z.variables_logic() == self.dim_logic() - 1
            && forall<u: proof::Val> z.zone(u) == self.zone(u),
        Err(e) => e == Error::Range && self.range_failure_logic(),
    })]
    // Without a selected pivot nothing is relaxed, so nothing can fail.
    #[ensures((forall<l: Int> 0 <= l && l < self.dim_logic() ==> !pivots@[l])
        ==> match result { Ok(_) => true, Err(_) => false })]
    pub(crate) fn close_pivots(mut self, pivots: &[bool]) -> Result<Dbm, Error> {
        let d = self.dim;
        let w = snapshot!(self);
        let len = snapshot!(d@ * d@);
        let mut k: usize = 0;
        #[invariant(k@ <= d@ && self.dim@ == d@ && self.entries@.len() == *len)]
        #[invariant(inv(self))]
        #[invariant(proof::same_zone(self.entries@, w.entries@, d@))]
        #[invariant(proof::diag_le0(self.entries@, d@) && proof::ref_nonneg(self.entries@, d@))]
        #[invariant(forall<l: Int> 0 <= l && l < d@ && (!pivots@[l] || l < k@) ==>
            proof::tri_through(self.entries@, d@, l))]
        #[variant(d@ - k@)]
        while k < d {
            if pivots[k] {
                let old = snapshot!(self);
                snapshot!(old.model());
                let mut i: usize = 0;
                #[invariant(i@ <= d@ && self.dim@ == d@ && self.entries@.len() == *len)]
                #[invariant(inv(self))]
                // Rows `< i` other than `k` are relaxed through `k`; the
                // others, including row `k`, are unchanged so far.
                #[invariant(forall<a: Int, b: Int> 0 <= a && a < d@ && 0 <= b && b < d@ ==>
                    if a < i@ && a != k@ {
                        proof::relax_full(proof::ent(old.entries@, d@, a, b),
                            proof::ent(old.entries@, d@, a, k@)
                                .add(proof::ent(old.entries@, d@, k@, b)),
                            proof::ent(self.entries@, d@, a, b))
                    } else {
                        proof::ent(self.entries@, d@, a, b) == proof::ent(old.entries@, d@, a, b)
                    })]
                #[invariant(proof::diag_le0(self.entries@, d@))]
                #[variant(d@ - i@)]
                while i < d {
                    snapshot!(self.model());
                    let ik = self.get(i, k);
                    if i != k && !ik.is_infinite() {
                        let row = snapshot!(self);
                        let failed = self.relax_row(i, k, ik);
                        snapshot!(self.model());
                        proof_assert!(forall<b: Int> 0 <= b && b < d@ ==>
                            row.at(i@, b)@ == proof::ent(old.entries@, d@, i@, b)
                                && row.at(k@, b)@ == proof::ent(old.entries@, d@, k@, b));
                        if failed {
                            proof_assert!(exists<b: Int> 0 <= b && b < d@ &&
                                proof::range_failure_at(old.entries@, w.entries@, d@, i@, k@, b));
                            return Err(Error::Range);
                        }
                        proof_assert!(forall<b: Int> 0 <= b && b < d@ ==> {
                            proof::relax_row_full(row.at(i@, b)@, ik@, row.at(k@, b)@, self.at(i@, b)@);
                            proof::relax_full(proof::ent(old.entries@, d@, i@, b),
                                proof::ent(old.entries@, d@, i@, k@)
                                    .add(proof::ent(old.entries@, d@, k@, b)),
                                proof::ent(self.entries@, d@, i@, b))
                        });
                        proof_assert!(proof::step_sound(old.entries@, self.entries@, d@, k@));
                        snapshot!(order_refines(self.at(i@, i@), Bound::LE_ZERO));
                        if tighter(self.get(i, i), Bound::LE_ZERO) {
                            snapshot!(proof::zone_relax(old.entries@, self.entries@, d@, k@));
                            snapshot!(proof::neg_diag_empty(self.entries@, d@, i@));
                            return Ok(Dbm {
                                variables: (d - 1) as u32,
                                entries: no_entries(),
                            });
                        }
                        snapshot!(view_injective(self.at(i@, i@), Bound::LE_ZERO));
                        proof_assert!(proof::ent(self.entries@, d@, i@, i@) == BoundModel::Le(0));
                    } else if i == k {
                        proof_assert!(forall<b: Int> 0 <= b && b < d@ ==> {
                            add_comm_unit(proof::ent(old.entries@, d@, k@, b), BoundModel::Le(0));
                            le_trans(proof::ent(old.entries@, d@, k@, b),
                                proof::ent(old.entries@, d@, k@, b),
                                proof::ent(old.entries@, d@, k@, b));
                            proof::relax_full(proof::ent(old.entries@, d@, k@, b),
                                proof::ent(old.entries@, d@, k@, k@)
                                    .add(proof::ent(old.entries@, d@, k@, b)),
                                proof::ent(self.entries@, d@, k@, b))
                        });
                    } else {
                        proof_assert!(forall<b: Int> 0 <= b && b < d@ ==> {
                            add_comm_unit(proof::ent(old.entries@, d@, k@, b), BoundModel::Inf);
                            le_trans(proof::ent(old.entries@, d@, i@, b),
                                proof::ent(old.entries@, d@, i@, b),
                                proof::ent(old.entries@, d@, i@, b));
                            proof::relax_full(proof::ent(old.entries@, d@, i@, b),
                                proof::ent(old.entries@, d@, i@, k@)
                                    .add(proof::ent(old.entries@, d@, k@, b)),
                                proof::ent(self.entries@, d@, i@, b))
                        });
                    }
                    i += 1;
                }
                proof_assert!(proof::step_full(old.entries@, self.entries@, d@, k@));
                snapshot!(proof::pivot_keep(old.entries@, self.entries@, d@, k@));
                snapshot!(proof::zone_relax(old.entries@, self.entries@, d@, k@));
                proof_assert!(forall<b: Int> 0 <= b && b < d@ ==> {
                    le_trans(proof::ent(old.entries@, d@, 0, b),
                        proof::ent(old.entries@, d@, 0, b),
                        proof::ent(old.entries@, d@, 0, b));
                    le_trans(proof::ent(self.entries@, d@, 0, b),
                        proof::ent(old.entries@, d@, 0, b), BoundModel::Le(0));
                    proof::ent(self.entries@, d@, 0, b).le(BoundModel::Le(0))
                });
            }
            k += 1;
        }
        proof_assert!(proof::tri_upto(self.entries@, d@, d@));
        Ok(self.publish_canonical())
    }
}

// ----- workspace -----

/// Reusable scratch storage for operations that require temporary buffers.
///
/// Reuse one workspace across successive [`Dbm::try_intersect`] and
/// [`Dbm::try_extrapolate_max`] calls, including calls on different dimensions.
/// It contains no references to zones and does not affect their semantics.
/// A workspace is intended to be borrowed mutably by one operation at a time.
/// It is `Send`, so a caller may use one per thread or exploration loop.
///
/// [`Workspace::with_capacity`] accepts a sizing hint, but callers must
/// not rely on it eliminating allocations.
///
/// # Example
///
/// ```
/// use clock_dbm::{Dbm, Workspace};
/// # fn main() -> Result<(), clock_dbm::Error> {
/// let mut ws = Workspace::new();
/// let a = Dbm::zero(1)?;
/// let b = Dbm::universe(1)?;
/// assert_eq!(a.clone().try_intersect(&b, &mut ws)?, a);
/// assert_eq!(b.try_intersect(&a, &mut ws)?, a);
/// # Ok(())
/// # }
/// ```
#[derive(Default, Debug)]
pub struct Workspace {
    _private: (),
    /// Touched-clock flags of `Dbm::try_intersect`, and
    /// the all-pivot flags of `Dbm::try_extrapolate_max`.
    pub(crate) touched: Vec<bool>,
}

impl Workspace {
    /// A fresh workspace.
    ///
    /// # Complexity
    ///
    /// `O(1)` time; temporary storage is allocated when needed by an operation.
    #[check(terminates)]
    pub fn new() -> Workspace {
        Workspace {
            _private: (),
            touched: Vec::new(),
        }
    }

    /// `d` cleared touched-clock flags (intersection).
    #[check(terminates)]
    #[ensures((^self).touched@.len() == d@)]
    #[ensures(forall<x: Int> 0 <= x && x < d@ ==> !(^self).touched@[x])]
    pub(crate) fn reset_touched(&mut self, d: usize) {
        self.fill_touched(d, false);
    }

    /// `d` set flags: every clock is a pivot (ExtraM's full closure).
    #[check(terminates)]
    #[ensures((^self).touched@.len() == d@)]
    #[ensures(forall<x: Int> 0 <= x && x < d@ ==> (^self).touched@[x])]
    pub(crate) fn select_all(&mut self, d: usize) {
        self.fill_touched(d, true);
    }

    /// `d` flags equal to `flag`. Once the vector has length `d` (every call
    /// after the first for that dimension), the flags are overwritten in
    /// place. Otherwise they are pushed one by one, because `Vec::resize` and
    /// `slice::fill` have no creusot-std specification. Allocates only while
    /// the vector grows.
    #[check(terminates)]
    #[ensures((^self).touched@.len() == d@)]
    #[ensures(forall<x: Int> 0 <= x && x < d@ ==> (^self).touched@[x] == flag)]
    #[inline]
    fn fill_touched(&mut self, d: usize, flag: bool) {
        if self.touched.len() == d {
            let mut x: usize = 0;
            #[invariant(x@ <= d@ && self.touched@.len() == d@)]
            #[invariant(forall<y: Int> 0 <= y && y < x@ ==> self.touched@[y] == flag)]
            #[variant(d@ - x@)]
            while x < d {
                self.touched[x] = flag;
                x += 1;
            }
        } else {
            self.touched.clear();
            let mut x: usize = 0;
            #[invariant(x@ <= d@ && self.touched@.len() == x@)]
            #[invariant(forall<y: Int> 0 <= y && y < x@ ==> self.touched@[y] == flag)]
            #[variant(d@ - x@)]
            while x < d {
                self.touched.push(flag);
                x += 1;
            }
        }
    }

    /// Creates a workspace using `variables` as a capacity hint.
    ///
    /// The current implementation does not preallocate storage, so this
    /// behaves like [`Workspace::new`]. No allocation guarantee is made.
    ///
    /// # Complexity
    ///
    /// `O(1)` time. The argument is currently only a hint; no storage
    /// is allocated eagerly.
    #[check(terminates)]
    pub fn with_capacity(variables: usize) -> Workspace {
        let _ = variables;
        Workspace::new()
    }
}

// Ghost-only proof layer; it has no runtime content.
#[cfg(creusot)]
pub(crate) mod proof;

#[cfg(test)]
mod tests;
