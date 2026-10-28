//! Ghost-only model of ExtraM's normalization. Everything here
//! is logic and exists only for Creusot.
//!
//! `norm_upper`, `norm_lower`, `norm_diag`, `norm_entry` and `norm` are
//! defined entrywise over `BoundModel`, with the strict order `≺` written
//! `lt` (as defined below). The executable
//! helpers of `extra_m.rs` are proved to compute them exactly. The lemmas:
//!
//! - `norm_weakens`: every entry of `norm` is at least as weak as the input
//!   entry; therefore `norm_extensive`:
//!   `γ(f) ⊆ γ(norm(f))` over nonnegative real valuations;
//! - `norm_ready`: `norm` keeps a `Le 0` diagonal and a reference row
//!   `≼ Le 0` when every ceiling is nonnegative. This is `close_pivots`' precondition with every
//!   pivot selected;
//! - `norm_range`: every entry of `norm` is `∞` or has its constant in
//!   `[−k(j), k(i)]`; the diagonal is `Le 0`, `Lt 0` or `∞`. With integer
//!   constants this leaves finitely many matrices for a fixed dimension and
//!   fixed ceilings (the finite-image argument of `PROOF_STATUS.md`).

use crate::bounds::{BoundModel, le_sound, le_total, le_trans};
use crate::dbm::proof::{MMat, Val, mzone};
use creusot_std::{logic::Mapping, prelude::*};

/// `a ≺ b`: `a` is strictly tighter than `b`.
#[logic(open(crate))]
pub(crate) fn lt(a: BoundModel, b: BoundModel) -> bool {
    pearlite! { a.le(b) && a != b }
}

/// `norm_upper e t = (if Le t ≺ e then ∞ else e)`.
#[logic(open(crate))]
pub(crate) fn norm_upper(e: BoundModel, t: Int) -> BoundModel {
    pearlite! { if lt(BoundModel::Le(t), e) { BoundModel::Inf } else { e } }
}

/// `norm_lower e t = (if e ≺ Lt t then Lt t else e)`.
#[logic(open(crate))]
pub(crate) fn norm_lower(e: BoundModel, t: Int) -> BoundModel {
    pearlite! { if lt(e, BoundModel::Lt(t)) { BoundModel::Lt(t) } else { e } }
}

/// `norm_diag e = (if e ≺ Le 0 then Lt 0 else if e = Le 0 then e else ∞)`.
#[logic(open(crate))]
pub(crate) fn norm_diag(e: BoundModel) -> BoundModel {
    pearlite! {
        if lt(e, BoundModel::Le(0)) {
            BoundModel::Lt(0)
        } else if e == BoundModel::Le(0) {
            e
        } else {
            BoundModel::Inf
        }
    }
}

/// Entry `(i, j)` of the `norm` transformation:
/// `ub = (if i > 0 then k i else 0)`, `lb = (if j > 0 then −k j else 0)`,
/// `norm_lower (norm_upper e ub) lb` off the diagonal, `norm_diag e` on it.
#[logic(open(crate))]
pub(crate) fn norm_entry(e: BoundModel, k: Mapping<Int, Int>, i: Int, j: Int) -> BoundModel {
    pearlite! {
        if i != j {
            norm_lower(norm_upper(e, if i > 0 { k[i] } else { 0 }), if j > 0 { -k[j] } else { 0 })
        } else {
            norm_diag(e)
        }
    }
}

/// `norm f k`, entrywise.
#[logic(open(crate))]
pub(crate) fn norm(f: MMat, k: Mapping<Int, Int>) -> MMat {
    pearlite! { |i: Int| |j: Int| norm_entry(f[i][j], k, i, j) }
}

/// Every normalized entry is at least as weak as the input entry
/// (by the weakening property), the diagonal included.
#[logic]
#[ensures(e.le(norm_entry(e, k, i, j)))]
pub(crate) fn norm_weakens(e: BoundModel, k: Mapping<Int, Int>, i: Int, j: Int) {
    pearlite! {
        let ub = if i > 0 { k[i] } else { 0 };
        let lb = if j > 0 { -k[j] } else { 0 };
        le_trans(e, e, e);
        le_trans(e, norm_upper(e, ub), norm_lower(norm_upper(e, ub), lb));
        le_trans(norm_upper(e, ub), norm_upper(e, ub), norm_upper(e, ub));
    }
}

/// Extensiveness of `norm` over nonnegative real valuations:
/// `γ(f) ⊆ γ(norm(f))`.
#[logic]
#[ensures(forall<u: Val> mzone(f, d, u) ==> mzone(norm(f, k), d, u))]
pub(crate) fn norm_extensive(f: MMat, k: Mapping<Int, Int>, d: Int) {
    pearlite! {
        proof_assert!(forall<u: Val> mzone(f, d, u) ==>
            forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> {
                norm_weakens(f[i][j], k, i, j);
                le_sound(f[i][j], norm(f, k)[i][j], u[i] - u[j]);
                true
            });
    }
}

/// `norm` keeps a `Le 0` diagonal and a reference row `≼ Le 0` when the
/// ceilings are nonnegative: the row-0 upper
/// threshold `Le 0` never fires, and the lower rule yields
/// `Lt (−k(j)) ≼ Le 0`.
#[logic]
#[requires(forall<i: Int> 0 <= i && i < d ==> f[i][i] == BoundModel::Le(0))]
#[requires(forall<j: Int> 0 <= j && j < d ==> f[0][j].le(BoundModel::Le(0)))]
#[requires(forall<j: Int> 0 < j && j < d ==> 0 <= k[j])]
#[ensures(forall<i: Int> 0 <= i && i < d ==> norm(f, k)[i][i] == BoundModel::Le(0))]
#[ensures(forall<j: Int> 0 <= j && j < d ==> norm(f, k)[0][j].le(BoundModel::Le(0)))]
pub(crate) fn norm_ready(f: MMat, k: Mapping<Int, Int>, d: Int) {
    pearlite! {
        proof_assert!(forall<j: Int> 0 < j && j < d ==> {
            le_total(f[0][j], BoundModel::Le(0));
            norm_upper(f[0][j], 0) == f[0][j]
        });
    }
}

/// The range of a normalized entry: `∞`, or a constant in `[−k(j), k(i)]`
/// off the diagonal (`k(0) = 0`), and `Le 0`, `Lt 0` or `∞` on it.
// Not used by a program proof: it is the Creusot-checked part of the
// finite-image argument (`verification/PROOF_STATUS.md`).
#[allow(dead_code)]
#[logic]
#[requires(0 <= i && 0 <= j)]
#[requires(i > 0 ==> 0 <= k[i])]
#[requires(j > 0 ==> 0 <= k[j])]
#[ensures(i == j ==> norm_entry(e, k, i, j) == BoundModel::Le(0)
    || norm_entry(e, k, i, j) == BoundModel::Lt(0) || norm_entry(e, k, i, j) == BoundModel::Inf)]
#[ensures(i != j ==> match norm_entry(e, k, i, j) {
    BoundModel::Inf => true,
    BoundModel::Lt(c) | BoundModel::Le(c) =>
        (if j > 0 { -k[j] } else { 0 }) <= c && c <= (if i > 0 { k[i] } else { 0 }),
})]
pub(crate) fn norm_range(e: BoundModel, k: Mapping<Int, Int>, i: Int, j: Int) {
    pearlite! {
        let ub = if i > 0 { k[i] } else { 0 };
        let lb = if j > 0 { -k[j] } else { 0 };
        le_total(e, BoundModel::Le(ub));
        le_total(norm_upper(e, ub), BoundModel::Lt(lb));
    }
}
