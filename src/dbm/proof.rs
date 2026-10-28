//! Ghost-only semantic layer for the closure proof.
//!
//! Everything here is logic: it is erased from ordinary builds and only
//! exists for Creusot. It connects the flat row-major storage of `dbm.rs`
//! with the zone semantics over **nonnegative real**
//! valuations, and proves the facts that the loop invariants of
//! `close_in_place` rely on:
//!
//! - `zone_tighten`, `zone_relax`: tightening an entry with a bound that
//!   every member of the zone satisfies, in particular a Floyd–Warshall
//!   relaxation, preserves the represented zone;
//! - `neg_diag_empty`: a diagonal entry tighter than `Le 0` empties the zone
//!   including strict-zero cycles `Lt 0`;
//! - `pivot_step`: one full pivot extends the triangle inequality to that
//!   pivot (using a path-free invariant);
//! - `canonical_nonempty`: a canonical matrix with a `Le 0` diagonal and a
//!   nonnegative reference row has a valuation, constructed clock by
//!   clock (`wit`).
//!
//! Entry `(i, j)` is `ent(s, d, i, j)`. Its body (the index `i·d + j`) is
//! private to this module, so the program proofs see only the lemmas
//! `ent_read` and `ent_set` and never the nonlinear index arithmetic.

use super::{index_in_bounds, index_injective};
use crate::bounds::{
    Bound, BoundModel, add_assoc, add_comm_unit, add_mono, add_sound, below_le_zero_unsat,
    le_sound, le_total, le_trans, neg_complement, relax_entry, relax_needed, sat,
};
use creusot_std::{
    logic::{Mapping, real::Real},
    prelude::*,
};

/// A clock valuation; index 0 is the reference clock.
pub(crate) type Val = Mapping<Int, Real>;

// ----- entries -----

/// Entry `(i, j)` of a flat row-major `d × d` matrix, as a model value.
#[logic]
pub(crate) fn ent(s: Seq<Bound>, d: Int, i: Int, j: Int) -> BoundModel {
    pearlite! { s[i * d + j]@ }
}

/// Reading an entry: its flat index is in bounds and holds `ent`.
#[logic]
#[requires(s.len() == d * d)]
#[requires(0 <= i && i < d && 0 <= j && j < d)]
#[ensures(0 <= i * d + j && i * d + j < s.len())]
#[ensures(ent(s, d, i, j) == s[i * d + j]@)]
pub(crate) fn ent_read(s: Seq<Bound>, d: Int, i: Int, j: Int) {
    index_in_bounds(d, i, j)
}

/// Writing entry `(i, j)` changes that entry only.
#[logic]
#[requires(s.len() == d * d)]
#[requires(0 <= i && i < d && 0 <= j && j < d)]
#[ensures(0 <= i * d + j && i * d + j < s.len())]
#[ensures(forall<a: Int, b: Int> 0 <= a && a < d && 0 <= b && b < d ==>
    ent(s.set(i * d + j, v), d, a, b) == if a == i && b == j { v@ } else { ent(s, d, a, b) })]
pub(crate) fn ent_set(s: Seq<Bound>, d: Int, i: Int, j: Int, v: Bound) {
    pearlite! {
        index_in_bounds(d, i, j);
        proof_assert!(forall<a: Int, b: Int> 0 <= a && a < d && 0 <= b && b < d ==> {
            index_injective(d, i, j, a, b); index_in_bounds(d, a, b); true
        });
    }
}

/// Entry `(i, j)` as a stored `Bound` (the storage-level counterpart of
/// `ent`). Its body is private to this module, like `ent`'s, so loop
/// invariants over whole rows and columns carry no index arithmetic.
#[logic]
pub(crate) fn cell(s: Seq<Bound>, d: Int, i: Int, j: Int) -> Bound {
    pearlite! { s[i * d + j] }
}

/// Reading a cell: its flat index is in bounds and holds `cell`.
#[logic]
#[requires(s.len() == d * d)]
#[requires(0 <= i && i < d && 0 <= j && j < d)]
#[ensures(0 <= i * d + j && i * d + j < s.len())]
#[ensures(cell(s, d, i, j) == s[i * d + j])]
pub(crate) fn cell_read(s: Seq<Bound>, d: Int, i: Int, j: Int) {
    index_in_bounds(d, i, j)
}

/// Every cell of `s` is its flat entry (for postconditions stated with
/// the open index arithmetic of `Matrix::at`).
#[logic]
#[requires(s.len() == d * d)]
#[ensures(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
    cell(s, d, i, j) == s[i * d + j])]
pub(crate) fn cell_all(s: Seq<Bound>, d: Int) {}

/// Writing cell `(i, j)` changes that cell only.
#[logic]
#[requires(s.len() == d * d)]
#[requires(0 <= i && i < d && 0 <= j && j < d)]
#[ensures(0 <= i * d + j && i * d + j < s.len())]
#[ensures((s.set(i * d + j, v)).len() == d * d)]
#[ensures(forall<a: Int, b: Int> 0 <= a && a < d && 0 <= b && b < d ==>
    cell(s.set(i * d + j, v), d, a, b) == if a == i && b == j { v } else { cell(s, d, a, b) })]
pub(crate) fn cell_set(s: Seq<Bound>, d: Int, i: Int, j: Int, v: Bound) {
    pearlite! {
        index_in_bounds(d, i, j);
        proof_assert!(forall<a: Int, b: Int> 0 <= a && a < d && 0 <= b && b < d ==> {
            index_injective(d, i, j, a, b); index_in_bounds(d, a, b); true
        });
    }
}

// ----- zones -----

/// `u` is a valuation of `d − 1` actual clocks: `u(x₀) = 0`, all clocks `≥ 0`.
#[logic(open(crate))]
pub(crate) fn valuation(d: Int, u: Val) -> bool {
    pearlite! {
        u[0] == Real::from_int(0)
            && forall<i: Int> 0 <= i && i < d ==> Real::from_int(0) <= u[i]
    }
}

/// `u ∈ γ(s)`: a valuation satisfying every entry.
#[logic(open(crate))]
pub(crate) fn zone(s: Seq<Bound>, d: Int, u: Val) -> bool {
    pearlite! {
        valuation(d, u)
            && forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
                sat(ent(s, d, i, j), u[i] - u[j])
    }
}

/// Two matrices denote the same zone.
#[logic(open(crate))]
pub(crate) fn same_zone(s: Seq<Bound>, t: Seq<Bound>, d: Int) -> bool {
    pearlite! { forall<u: Val> zone(s, d, u) == zone(t, d, u) }
}

/// Replacing entry `(a, b)` by a tighter bound that every member of the
/// zone satisfies keeps the zone.
#[logic]
#[requires(s.len() == d * d)]
#[requires(0 <= a && a < d && 0 <= b && b < d)]
#[requires(v@.le(ent(s, d, a, b)))]
#[requires(forall<u: Val> zone(s, d, u) ==> sat(v@, u[a] - u[b]))]
#[ensures(same_zone(s.set(a * d + b, v), s, d))]
pub(crate) fn zone_tighten(s: Seq<Bound>, d: Int, a: Int, b: Int, v: Bound) {
    pearlite! {
        ent_set(s, d, a, b, v);
        proof_assert!(forall<u: Val> sat(v@, u[a] - u[b]) ==> {
            le_sound(v@, ent(s, d, a, b), u[a] - u[b]); sat(ent(s, d, a, b), u[a] - u[b])
        });
    }
}

/// Normalizing the diagonal entry `(a, a)` to `Le 0` keeps the zone
/// (`xₐ − xₐ = 0`).
#[logic]
#[requires(s.len() == d * d)]
#[requires(0 <= a && a < d)]
#[requires(v@ == BoundModel::Le(0) && v@.le(ent(s, d, a, a)))]
#[ensures(same_zone(s.set(a * d + a, v), s, d))]
pub(crate) fn zone_diag(s: Seq<Bound>, d: Int, a: Int, v: Bound) {
    zone_tighten(s, d, a, a, v)
}

/// Writing the reference entry `(0, b)` (flat index `b`) changes that entry
/// only.
#[logic]
#[requires(s.len() == d * d)]
#[requires(0 <= b && b < d)]
#[ensures(0 <= b && b < s.len())]
#[ensures(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
    ent(s.set(b, v), d, i, j) == if i == 0 && j == b { v@ } else { ent(s, d, i, j) })]
pub(crate) fn ent_set_ref(s: Seq<Bound>, d: Int, b: Int, v: Bound) {
    pearlite! {
        proof_assert!(0 * d + b == b);
        ent_set(s, d, 0, b, v)
    }
}

/// Normalizing the reference entry `(0, b)` to `Le 0` keeps the zone over
/// nonnegative valuations (Lemma 2.1: `0 − x_b ≤ 0`).
#[logic]
#[requires(s.len() == d * d)]
#[requires(0 <= b && b < d)]
#[requires(v@ == BoundModel::Le(0) && v@.le(ent(s, d, 0, b)))]
#[ensures(0 <= b && b < s.len())]
#[ensures(same_zone(s.set(b, v), s, d))]
#[ensures(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
    ent(s.set(b, v), d, i, j) == if i == 0 && j == b { v@ } else { ent(s, d, i, j) })]
pub(crate) fn zone_ref(s: Seq<Bound>, d: Int, b: Int, v: Bound) {
    pearlite! {
        proof_assert!(0 * d + b == b);
        ent_set(s, d, 0, b, v);
        zone_tighten(s, d, 0, b, v)
    }
}

/// A diagonal entry strictly tighter than `Le 0` (e.g. a strict-zero cycle
/// `Lt 0`) means the zone is empty (negative-diagonal emptiness criterion).
#[logic]
#[requires(0 <= i && i < d)]
#[requires(!BoundModel::Le(0).le(ent(s, d, i, i)))]
#[ensures(forall<u: Val> !zone(s, d, u))]
pub(crate) fn neg_diag_empty(s: Seq<Bound>, d: Int, i: Int) {
    pearlite! {
        below_le_zero_unsat(ent(s, d, i, i));
        proof_assert!(forall<u: Val> u[i] - u[i] == Real::from_int(0));
    }
}

// ----- Floyd–Warshall relaxation -----

/// `c` is a sound relaxation of `o` through `p = o_ak + o_kb`: either
/// unchanged or the (tighter) sum.
#[logic(open(crate))]
pub(crate) fn relax_sound(o: BoundModel, p: BoundModel, c: BoundModel) -> bool {
    pearlite! { c == o || (c.le(o) && c == p) }
}

/// `c = min(o, p)`.
#[logic(open(crate))]
pub(crate) fn relax_full(o: BoundModel, p: BoundModel, c: BoundModel) -> bool {
    pearlite! { relax_sound(o, p, c) && c.le(p) }
}

/// Every entry of `cur` is a sound relaxation of `old` through pivot `k`.
#[logic(open(crate))]
pub(crate) fn step_sound(old: Seq<Bound>, cur: Seq<Bound>, d: Int, k: Int) -> bool {
    pearlite! {
        forall<a: Int, b: Int> 0 <= a && a < d && 0 <= b && b < d ==>
            relax_sound(ent(old, d, a, b), ent(old, d, a, k).add(ent(old, d, k, b)), ent(cur, d, a, b))
    }
}

/// `cur` is exactly the Floyd–Warshall step of `old` through pivot `k`.
#[logic(open(crate))]
pub(crate) fn step_full(old: Seq<Bound>, cur: Seq<Bound>, d: Int, k: Int) -> bool {
    pearlite! {
        forall<a: Int, b: Int> 0 <= a && a < d && 0 <= b && b < d ==>
            relax_full(ent(old, d, a, b), ent(old, d, a, k).add(ent(old, d, k, b)), ent(cur, d, a, b))
    }
}

/// One entry of a sound relaxation: the zones agree on it.
#[logic]
#[requires(zone(old, d, u))]
#[requires(0 <= a && a < d && 0 <= b && b < d && 0 <= k && k < d)]
#[requires(relax_sound(ent(old, d, a, b), ent(old, d, a, k).add(ent(old, d, k, b)), ent(cur, d, a, b)))]
#[ensures(sat(ent(cur, d, a, b), u[a] - u[b]))]
fn relax_entry_sat(old: Seq<Bound>, cur: Seq<Bound>, d: Int, k: Int, a: Int, b: Int, u: Val) {
    pearlite! {
        add_sound(ent(old, d, a, k), ent(old, d, k, b), u[a] - u[k], u[k] - u[b]);
        proof_assert!((u[a] - u[k]) + (u[k] - u[b]) == u[a] - u[b]);
    }
}

/// A sound relaxation (complete or partial) keeps the zone
/// (zone preservation for one relaxation).
#[logic]
#[requires(0 <= k && k < d)]
#[requires(step_sound(old, cur, d, k))]
#[ensures(same_zone(cur, old, d))]
pub(crate) fn zone_relax(old: Seq<Bound>, cur: Seq<Bound>, d: Int, k: Int) {
    pearlite! {
        proof_assert!(forall<u: Val> zone(old, d, u) ==>
            forall<a: Int, b: Int> 0 <= a && a < d && 0 <= b && b < d ==> {
                relax_entry_sat(old, cur, d, k, a, b, u); sat(ent(cur, d, a, b), u[a] - u[b])
            });
        proof_assert!(forall<u: Val> zone(cur, d, u) ==>
            forall<a: Int, b: Int> 0 <= a && a < d && 0 <= b && b < d ==> {
                le_trans(ent(cur, d, a, b), ent(cur, d, a, b), ent(cur, d, a, b));
                le_sound(ent(cur, d, a, b), ent(old, d, a, b), u[a] - u[b]);
                sat(ent(old, d, a, b), u[a] - u[b])
            });
    }
}

// ----- canonicity -----

/// C2: every diagonal entry is `Le 0`.
#[logic(open(crate))]
pub(crate) fn diag_le0(s: Seq<Bound>, d: Int) -> bool {
    pearlite! { forall<i: Int> 0 <= i && i < d ==> ent(s, d, i, i) == BoundModel::Le(0) }
}

/// C3: the reference row allows no negative clock.
#[logic(open(crate))]
pub(crate) fn ref_nonneg(s: Seq<Bound>, d: Int) -> bool {
    pearlite! { forall<j: Int> 0 <= j && j < d ==> ent(s, d, 0, j).le(BoundModel::Le(0)) }
}

/// The triangle inequality through every pivot `l < k`.
#[logic(open(crate))]
pub(crate) fn tri_upto(s: Seq<Bound>, d: Int, k: Int) -> bool {
    pearlite! {
        forall<i: Int, j: Int, l: Int>
            0 <= i && i < d && 0 <= j && j < d && 0 <= l && l < k ==>
                ent(s, d, i, j).le(ent(s, d, i, l).add(ent(s, d, l, j)))
    }
}

/// The triangle inequality through the single pivot `l`. `tri_upto`
/// is this for every `l < k`; the touched-pivot closure of
/// `Matrix::close_pivots` establishes it pivot by pivot, in any order.
#[logic(open(crate))]
pub(crate) fn tri_through(s: Seq<Bound>, d: Int, l: Int) -> bool {
    pearlite! {
        forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
            ent(s, d, i, j).le(ent(s, d, i, l).add(ent(s, d, l, j)))
    }
}

/// The canonical-matrix invariant for a `d × d` matrix: C2, C3 and C4
/// (C1 is the `Bound` type invariant, C5 is `canonical_nonempty`).
#[logic(open(crate))]
pub(crate) fn canonical(s: Seq<Bound>, d: Int) -> bool {
    pearlite! { s.len() == d * d && diag_le0(s, d) && ref_nonneg(s, d) && tri_upto(s, d, d) }
}

/// The four-case argument for one triangle through an old pivot `l < k`,
/// stated on bare bounds (`o` = before, `c` = after pivot `k`).
#[logic]
#[requires(cij.le(oij) && cij.le(oik.add(okj)))]
#[requires(cil == oil || cil == oik.add(okl))]
#[requires(clj == olj || clj == olk.add(okj))]
#[requires(oij.le(oil.add(olj)))]
#[requires(oik.le(oil.add(olk)))]
#[requires(okj.le(okl.add(olj)))]
#[requires(BoundModel::Le(0).le(okl.add(olk)))]
#[ensures(cij.le(cil.add(clj)))]
#[allow(clippy::too_many_arguments)]
fn pivot_algebra(
    oij: BoundModel,
    oik: BoundModel,
    okj: BoundModel,
    oil: BoundModel,
    olj: BoundModel,
    olk: BoundModel,
    okl: BoundModel,
    cij: BoundModel,
    cil: BoundModel,
    clj: BoundModel,
) {
    pearlite! {
        if cil == oil {
            if clj == olj {
                le_trans(cij, oij, oil.add(olj))
            } else {
                add_assoc(oil, olk, okj);
                add_mono(oik, oil.add(olk), okj);
                le_trans(cij, oik.add(okj), oil.add(olk).add(okj))
            }
        } else if clj == olj {
            add_assoc(oik, okl, olj);
            add_mono(okj, okl.add(olj), oik);
            le_trans(cij, oik.add(okj), oik.add(okl.add(olj)))
        } else {
            add_assoc(oik, okl, olk.add(okj));
            add_assoc(okl, olk, okj);
            add_mono(BoundModel::Le(0), okl.add(olk), okj);
            add_comm_unit(okj, BoundModel::Le(0));
            add_mono(okj, okl.add(olk).add(okj), oik);
            le_trans(cij, oik.add(okj), oik.add(okl.add(olk).add(okj)))
        }
    }
}

/// One triangle `(i, j)` through pivot `l` after a full pivot `k`: either
/// `l = k`, or `old` already satisfied the triangle through `l` (for
/// Floyd–Warshall, every `l < k`; for the touched-pivot closure of,
/// also every untouched `l`).
#[logic]
#[requires(0 <= i && i < d && 0 <= j && j < d && 0 <= l && l < d && 0 <= k && k < d)]
#[requires(l == k || tri_through(old, d, l))]
#[requires(diag_le0(old, d))]
#[requires(step_full(old, cur, d, k))]
#[ensures(ent(cur, d, i, j).le(ent(cur, d, i, l).add(ent(cur, d, l, j))))]
fn pivot_point(old: Seq<Bound>, cur: Seq<Bound>, d: Int, k: Int, i: Int, j: Int, l: Int) {
    pearlite! {
        add_comm_unit(ent(old, d, i, k), BoundModel::Le(0));
        add_comm_unit(ent(old, d, k, j), BoundModel::Le(0));
        proof_assert!(ent(old, d, k, k) == BoundModel::Le(0));
        le_trans(ent(cur, d, i, j), ent(cur, d, i, j), ent(cur, d, i, j));
        proof_assert!(relax_full(ent(old, d, i, j), ent(old, d, i, k).add(ent(old, d, k, j)), ent(cur, d, i, j)));
        if l != k {
            proof_assert!(relax_full(ent(old, d, i, l), ent(old, d, i, k).add(ent(old, d, k, l)), ent(cur, d, i, l)));
            proof_assert!(relax_full(ent(old, d, l, j), ent(old, d, l, k).add(ent(old, d, k, j)), ent(cur, d, l, j)));
            proof_assert!(ent(old, d, i, j).le(ent(old, d, i, l).add(ent(old, d, l, j))));
            proof_assert!(ent(old, d, i, k).le(ent(old, d, i, l).add(ent(old, d, l, k))));
            proof_assert!(ent(old, d, k, j).le(ent(old, d, k, l).add(ent(old, d, l, j))));
            proof_assert!(ent(old, d, k, k).le(ent(old, d, k, l).add(ent(old, d, l, k))));
            pivot_algebra(
                ent(old, d, i, j), ent(old, d, i, k), ent(old, d, k, j),
                ent(old, d, i, l), ent(old, d, l, j), ent(old, d, l, k), ent(old, d, k, l),
                ent(cur, d, i, j), ent(cur, d, i, l), ent(cur, d, l, j),
            )
        } else {
            proof_assert!(relax_full(ent(old, d, i, k), ent(old, d, i, k).add(ent(old, d, k, k)), ent(cur, d, i, k)));
            proof_assert!(relax_full(ent(old, d, k, j), ent(old, d, k, k).add(ent(old, d, k, j)), ent(cur, d, k, j)));
            proof_assert!(ent(cur, d, i, k) == ent(old, d, i, k));
            proof_assert!(ent(cur, d, k, j) == ent(old, d, k, j));
        }
    }
}

/// A full pivot `k` on a matrix with a `Le 0` diagonal that is already
/// closed through every `l < k` is closed through every `l ≤ k`.
/// A path-free Floyd–Warshall invariant for canonicality after each pivot.
#[logic]
#[requires(0 <= k && k < d)]
#[requires(tri_upto(old, d, k) && diag_le0(old, d))]
#[requires(step_full(old, cur, d, k))]
#[ensures(tri_upto(cur, d, k + 1))]
pub(crate) fn pivot_step(old: Seq<Bound>, cur: Seq<Bound>, d: Int, k: Int) {
    pearlite! {
        proof_assert!(forall<l: Int> 0 <= l && l < k ==> tri_through(old, d, l));
        proof_assert!(forall<i: Int, j: Int, l: Int>
            0 <= i && i < d && 0 <= j && j < d && 0 <= l && l < k + 1 ==> {
                pivot_point(old, cur, d, k, i, j, l);
                ent(cur, d, i, j).le(ent(cur, d, i, l).add(ent(cur, d, l, j)))
            });
    }
}

/// A full pivot `k` on a matrix with a `Le 0` diagonal closes it through
/// `k` and keeps every triangle that already held through another pivot
///. This is what lets `Matrix::close_pivots` process only the touched
/// pivots, in increasing order with gaps.
#[logic]
#[requires(0 <= k && k < d)]
#[requires(diag_le0(old, d) && step_full(old, cur, d, k))]
#[ensures(tri_through(cur, d, k))]
#[ensures(forall<l: Int> 0 <= l && l < d && tri_through(old, d, l) ==> tri_through(cur, d, l))]
pub(crate) fn pivot_keep(old: Seq<Bound>, cur: Seq<Bound>, d: Int, k: Int) {
    pearlite! {
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> {
            pivot_point(old, cur, d, k, i, j, k);
            ent(cur, d, i, j).le(ent(cur, d, i, k).add(ent(cur, d, k, j)))
        });
        proof_assert!(forall<l: Int> 0 <= l && l < d && tri_through(old, d, l) ==>
            forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> {
                pivot_point(old, cur, d, k, i, j, l);
                ent(cur, d, i, j).le(ent(cur, d, i, l).add(ent(cur, d, l, j)))
            });
    }
}

/// One entry written by `Matrix::relax_row` without a range flag is the
/// minimum of the old entry and the sum (`∞` summands included), i.e. a
/// full Floyd–Warshall relaxation.
#[logic]
#[requires(relax_entry(cur, v, s, new))]
#[requires(!(relax_needed(cur, v, s) && !v.add_in_range(s)))]
#[ensures(relax_full(cur, v.add(s), new))]
pub(crate) fn relax_row_full(cur: BoundModel, v: BoundModel, s: BoundModel, new: BoundModel) {
    pearlite! {
        le_total(cur, v.add(s));
        le_trans(cur, cur, cur);
        le_trans(new, new, new);
        add_comm_unit(v, s)
    }
}

// ----- model-level matrices -----
//
// A `d × d` matrix of model bounds with unbounded constants. The storage
// level (`Seq<Bound>`) is linked to it by `mat`; results whose constants may
// leave the representable range (such as exact closure of a constrained zone)
// are stated at this level.

/// A matrix of model bounds, entry `(i, j)` at `f[i][j]`.
pub(crate) type MMat = Mapping<Int, Mapping<Int, BoundModel>>;

/// The model matrix of a flat row-major storage.
#[logic(open(crate))]
pub(crate) fn mat(s: Seq<Bound>, d: Int) -> MMat {
    pearlite! { |i: Int| |j: Int| ent(s, d, i, j) }
}

/// `u ∈ γ(f)`.
#[logic(open(crate))]
pub(crate) fn mzone(f: MMat, d: Int, u: Val) -> bool {
    pearlite! {
        valuation(d, u)
            && forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
                sat(f[i][j], u[i] - u[j])
    }
}

/// The triangle inequality through every pivot.
#[logic(open(crate))]
pub(crate) fn mtri(f: MMat, d: Int) -> bool {
    pearlite! {
        forall<i: Int, j: Int, l: Int>
            0 <= i && i < d && 0 <= j && j < d && 0 <= l && l < d ==>
                f[i][j].le(f[i][l].add(f[l][j]))
    }
}

/// `Inv` (C) C2–C4 of a model matrix.
#[logic(open(crate))]
pub(crate) fn mcanonical(f: MMat, d: Int) -> bool {
    pearlite! {
        (forall<i: Int> 0 <= i && i < d ==> f[i][i] == BoundModel::Le(0))
            && (forall<j: Int> 0 <= j && j < d ==> f[0][j].le(BoundModel::Le(0)))
            && mtri(f, d)
    }
}

/// The two model matrices agree on every in-range entry.
#[logic(open(crate))]
pub(crate) fn meq(f: MMat, g: MMat, d: Int) -> bool {
    pearlite! {
        forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> f[i][j] == g[i][j]
    }
}

/// Storage-level zone and canonicity are those of `mat`.
#[logic]
#[ensures(forall<i: Int, j: Int> mat(s, d)[i][j] == ent(s, d, i, j))]
#[ensures(forall<u: Val> zone(s, d, u) == mzone(mat(s, d), d, u))]
#[ensures(s.len() == d * d ==> canonical(s, d) == mcanonical(mat(s, d), d))]
pub(crate) fn mat_bridge(s: Seq<Bound>, d: Int) {}

/// Agreeing matrices have the same zone and canonicity.
#[logic]
#[requires(meq(f, g, d))]
#[ensures(forall<u: Val> mzone(f, d, u) == mzone(g, d, u))]
#[ensures(mcanonical(f, d) == mcanonical(g, d))]
pub(crate) fn meq_transfer(f: MMat, g: MMat, d: Int) {}

// ----- a canonical matrix has a valuation (Inv C5) -----

/// Constant of a finite bound, as a real (0 for `∞`, never used there).
#[logic]
fn cst(b: BoundModel) -> Real {
    match b {
        BoundModel::Lt(c) | BoundModel::Le(c) => Real::from_int(c),
        BoundModel::Inf => Real::from_int(0),
    }
}

/// The partial valuation `u` (clocks `< p`) satisfies the submatrix `< p`.
#[logic(open(crate))]
pub(crate) fn sat_prefix(f: MMat, u: Val, p: Int) -> bool {
    pearlite! {
        forall<i: Int, j: Int> 0 <= i && i < p && 0 <= j && j < p ==>
            sat(f[i][j], u[i] - u[j])
    }
}

/// Lower bound on a new clock `x_p` from entry `(j, p)`: `x_j − x_p ⋈ c`.
#[logic]
fn lo(f: MMat, u: Val, p: Int, j: Int) -> Real {
    pearlite! { u[j] - cst(f[j][p]) }
}

/// Upper bound on a new clock `x_p` from entry `(p, j)`: `x_p − x_j ⋈ c`.
#[logic]
fn hi(f: MMat, u: Val, p: Int, j: Int) -> Real {
    pearlite! { u[j] + cst(f[p][j]) }
}

/// The index `j < n` with the largest finite lower bound on `x_p`
/// (row 0 always gives one).
#[logic]
#[variant(n)]
fn arg_lo(f: MMat, d: Int, u: Val, p: Int, n: Int) -> Int {
    pearlite! {
        if n <= 1 {
            0
        } else {
            let a = arg_lo(f, d, u, p, n - 1);
            if f[n - 1][p] != BoundModel::Inf && lo(f, u, p, a) < lo(f, u, p, n - 1) {
                n - 1
            } else {
                a
            }
        }
    }
}

#[logic]
#[variant(n)]
#[requires(1 <= n)]
#[requires(f[0][p] != BoundModel::Inf)]
#[ensures(0 <= arg_lo(f, d, u, p, n) && arg_lo(f, d, u, p, n) < n)]
#[ensures(f[arg_lo(f, d, u, p, n)][p] != BoundModel::Inf)]
#[ensures(forall<j: Int> 0 <= j && j < n && f[j][p] != BoundModel::Inf ==>
    lo(f, u, p, j) <= lo(f, u, p, arg_lo(f, d, u, p, n)))]
fn arg_lo_spec(f: MMat, d: Int, u: Val, p: Int, n: Int) {
    pearlite! { if n > 1 { arg_lo_spec(f, d, u, p, n - 1) } }
}

/// The index `j < n` with the smallest finite upper bound on `x_p`, or −1.
#[logic]
#[variant(n)]
fn arg_hi(f: MMat, d: Int, u: Val, p: Int, n: Int) -> Int {
    pearlite! {
        if n <= 0 {
            -1
        } else {
            let a = arg_hi(f, d, u, p, n - 1);
            if f[p][n - 1] != BoundModel::Inf
                && (a < 0 || hi(f, u, p, n - 1) < hi(f, u, p, a)) {
                n - 1
            } else {
                a
            }
        }
    }
}

#[logic]
#[variant(n)]
#[requires(0 <= n)]
#[ensures(-1 <= arg_hi(f, d, u, p, n) && arg_hi(f, d, u, p, n) < n)]
#[ensures(0 <= arg_hi(f, d, u, p, n) ==> f[p][arg_hi(f, d, u, p, n)] != BoundModel::Inf)]
#[ensures(forall<j: Int> 0 <= j && j < n && f[p][j] != BoundModel::Inf ==>
    0 <= arg_hi(f, d, u, p, n) && hi(f, u, p, arg_hi(f, d, u, p, n)) <= hi(f, u, p, j))]
fn arg_hi_spec(f: MMat, d: Int, u: Val, p: Int, n: Int) {
    pearlite! { if n > 0 { arg_hi_spec(f, d, u, p, n - 1) } }
}

/// The value chosen for clock `x_p` given `u` on the clocks `< p`.
#[logic]
pub(crate) fn pick(f: MMat, d: Int, u: Val, p: Int) -> Real {
    pearlite! {
        let l = lo(f, u, p, arg_lo(f, d, u, p, p));
        let b = arg_hi(f, d, u, p, p);
        if b < 0 {
            l + Real::from_int(1)
        } else if l < hi(f, u, p, b) {
            (l + hi(f, u, p, b)) / Real::from_int(2)
        } else {
            l
        }
    }
}

/// Every finite lower bound on `x_p` is below every finite upper bound,
/// strictly if either is strict: the triangle `(j, l)` through `p`.
#[logic]
#[requires(0 <= j && j < p && 0 <= l && l < p)]
#[requires(sat(f[j][l], u[j] - u[l]))]
#[requires(f[j][l].le(f[j][p].add(f[p][l])))]
#[requires(f[j][p] != BoundModel::Inf && f[p][l] != BoundModel::Inf)]
#[ensures(lo(f, u, p, j) <= hi(f, u, p, l))]
#[ensures(match f[j][p] { BoundModel::Lt(_) => lo(f, u, p, j) < hi(f, u, p, l), _ => true })]
#[ensures(match f[p][l] { BoundModel::Lt(_) => lo(f, u, p, j) < hi(f, u, p, l), _ => true })]
fn compat(f: MMat, d: Int, u: Val, p: Int, j: Int, l: Int) {
    pearlite! {
        le_sound(f[j][l], f[j][p].add(f[p][l]), u[j] - u[l]);
        match (f[j][p], f[p][l]) {
            (BoundModel::Lt(a) | BoundModel::Le(a), BoundModel::Lt(b) | BoundModel::Le(b)) => {
                proof_assert!(Real::from_int(a + b) == Real::from_int(a) + Real::from_int(b))
            }
            _ => {}
        }
    }
}

/// The hypotheses of one extension step `p → p + 1`: `u` satisfies the
/// submatrix `< p`, `x_p` has a finite lower bound from row 0 and a `Le 0`
/// diagonal, and every pair `j, l < p` satisfies the triangle through `p`.
/// A canonical `f` (`mcanonical`) meets them for every `p`; the temporal
/// proofs also use them for non-canonical auxiliary matrices.
#[logic(open(crate))]
pub(crate) fn step_pre(f: MMat, d: Int, u: Val, p: Int) -> bool {
    pearlite! {
        1 <= p && p < d
            && f[0][p] != BoundModel::Inf
            && f[p][p] == BoundModel::Le(0)
            && (forall<j: Int, l: Int> 0 <= j && j < p && 0 <= l && l < p ==>
                f[j][l].le(f[j][p].add(f[p][l])))
            && sat_prefix(f, u, p)
    }
}

/// The chosen value satisfies the lower bound from `(j, p)`.
#[logic]
#[requires(step_pre(f, d, u, p))]
#[requires(0 <= j && j < p)]
#[ensures(sat(f[j][p], u[j] - pick(f, d, u, p)))]
fn pick_lower(f: MMat, d: Int, u: Val, p: Int, j: Int) {
    pearlite! {
        let a = arg_lo(f, d, u, p, p);
        let b = arg_hi(f, d, u, p, p);
        arg_lo_spec(f, d, u, p, p);
        arg_hi_spec(f, d, u, p, p);
        if f[j][p] != BoundModel::Inf && 0 <= b {
            compat(f, d, u, p, a, b);
            compat(f, d, u, p, j, b);
        }
    }
}

/// The chosen value satisfies the upper bound from `(p, j)`.
#[logic]
#[requires(step_pre(f, d, u, p))]
#[requires(0 <= j && j < p)]
#[ensures(sat(f[p][j], pick(f, d, u, p) - u[j]))]
fn pick_upper(f: MMat, d: Int, u: Val, p: Int, j: Int) {
    pearlite! {
        let a = arg_lo(f, d, u, p, p);
        arg_lo_spec(f, d, u, p, p);
        arg_hi_spec(f, d, u, p, p);
        if f[p][j] != BoundModel::Inf {
            let b = arg_hi(f, d, u, p, p);
            compat(f, d, u, p, a, b);
            compat(f, d, u, p, a, j);
        }
    }
}

/// Extending a valuation of the clocks `< p` by `pick` satisfies the
/// submatrix `≤ p`.
#[logic]
#[requires(step_pre(f, d, u, p))]
#[ensures(sat_prefix(f, u.set(p, pick(f, d, u, p)), p + 1))]
pub(crate) fn extend(f: MMat, d: Int, u: Val, p: Int) {
    pearlite! {
        let v = u.set(p, pick(f, d, u, p));
        proof_assert!(forall<j: Int> 0 <= j && j < p ==> {
            pick_lower(f, d, u, p, j); pick_upper(f, d, u, p, j);
            sat(f[j][p], v[j] - v[p]) && sat(f[p][j], v[p] - v[j])
        });
        proof_assert!(v[p] - v[p] == Real::from_int(0));
    }
}

/// The witness valuation on the clocks `< p`, built clock by clock.
#[logic]
#[variant(p)]
pub(crate) fn wit(f: MMat, d: Int, p: Int) -> Val {
    pearlite! {
        if p <= 1 {
            Mapping::cst(Real::from_int(0))
        } else {
            let u = wit(f, d, p - 1);
            u.set(p - 1, pick(f, d, u, p - 1))
        }
    }
}

#[logic]
#[variant(p)]
#[requires(mcanonical(f, d))]
#[requires(1 <= p && p <= d)]
#[ensures(wit(f, d, p)[0] == Real::from_int(0))]
#[ensures(sat_prefix(f, wit(f, d, p), p))]
fn wit_spec(f: MMat, d: Int, p: Int) {
    pearlite! {
        if p > 1 {
            wit_spec(f, d, p - 1);
            extend(f, d, wit(f, d, p - 1), p - 1)
        }
    }
}

/// A canonical model matrix (C2–C4) admits a witness valuation, so its
/// zone is nonempty (C5).
#[logic]
#[requires(1 <= d && mcanonical(f, d))]
#[ensures(mzone(f, d, wit(f, d, d)))]
#[ensures(exists<u: Val> mzone(f, d, u))]
pub(crate) fn mcanonical_nonempty(f: MMat, d: Int) {
    pearlite! {
        wit_spec(f, d, d);
        proof_assert!(forall<i: Int> 0 <= i && i < d ==> {
            le_sound(f[0][i], BoundModel::Le(0), wit(f, d, d)[0] - wit(f, d, d)[i]);
            Real::from_int(0) <= wit(f, d, d)[i]
        });
    }
}

/// A canonical matrix denotes a nonempty zone (`mcanonical_nonempty` on
/// its entries).
#[logic]
#[requires(1 <= d && canonical(s, d))]
#[ensures(zone(s, d, wit(mat(s, d), d, d)))]
#[ensures(exists<u: Val> zone(s, d, u))]
pub(crate) fn canonical_nonempty(s: Seq<Bound>, d: Int) {
    pearlite! {
        mat_bridge(s, d);
        mcanonical_nonempty(mat(s, d), d)
    }
}

// ----- closing one tightened edge; uniqueness of canonical forms (B7) -----
//
// `edge(f, i, j, b)` is the exact closure of a canonical `f` conjoined with
// `xᵢ − xⱼ ⋈ b`, with unbounded constants:
// `min(f[k][l], f[k][i] + b + f[j][l])`. It is the specification of the
// incremental closure of `ops::constraints`, and it also gives
// the tightness of canonical entries, hence Theorem 3.1 (B7).

/// The tighter of two bounds.
#[logic(open(crate))]
pub(crate) fn bmin(a: BoundModel, b: BoundModel) -> BoundModel {
    if a.le(b) { a } else { b }
}

/// `bmin` is a lower bound, one of its arguments, and the greatest lower
/// bound.
#[logic]
#[ensures(bmin(a, b).le(a) && bmin(a, b).le(b))]
#[ensures(bmin(a, b) == a || bmin(a, b) == b)]
#[ensures(a.le(b) ==> bmin(a, b) == a)]
#[ensures(b.le(a) ==> bmin(a, b) == b)]
#[ensures(forall<c: BoundModel> c.le(a) && c.le(b) ==> c.le(bmin(a, b)))]
pub(crate) fn bmin_spec(a: BoundModel, b: BoundModel) {
    pearlite! { le_total(a, b); le_trans(a, a, a); le_trans(b, b, b) }
}

/// The entrywise minimum of two model matrices.
#[logic(open(crate))]
pub(crate) fn bmin_mat(f: MMat, g: MMat) -> MMat {
    pearlite! { |i: Int| |j: Int| bmin(f[i][j], g[i][j]) }
}

/// The pointwise minimum `w` of a canonical `f` and a matrix `g` with a
/// `Le 0` diagonal, where `t` marks both endpoints of every entry in which
/// `g` is strictly tighter (the model of `Matrix::meet`):
///
/// - `w` is `bmin_mat(f, g)` and denotes `γ(f) ∩ γ(g)`;
/// - `w` has a `Le 0` diagonal and a nonnegative reference row;
/// - `w` satisfies the triangle inequality through every **untouched** `l`.
///   Row and column `l` are those of `f`, so
///   `w[i][j] ≼ f[i][j] ≼ f[i][l] + f[l][j] = w[i][l] + w[l][j]`. This is
///   the path-free form of "a run of unchanged edges collapses into one
///   entry of `f`", which is why closing through the touched clocks only is
///   enough (`Matrix::close_pivots`).
#[logic]
#[requires(1 <= d && mcanonical(f, d))]
#[requires(forall<i: Int> 0 <= i && i < d ==> g[i][i] == BoundModel::Le(0))]
#[requires(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
    (w[i][j] == f[i][j] && f[i][j].le(g[i][j]))
        || (w[i][j] == g[i][j] && !f[i][j].le(g[i][j]) && t[i] && t[j]))]
#[ensures(meq(w, bmin_mat(f, g), d))]
#[ensures(forall<u: Val> mzone(w, d, u) == (mzone(f, d, u) && mzone(g, d, u)))]
#[ensures(forall<i: Int> 0 <= i && i < d ==> w[i][i] == BoundModel::Le(0))]
#[ensures(forall<j: Int> 0 <= j && j < d ==> w[0][j].le(BoundModel::Le(0)))]
#[ensures(forall<l: Int> 0 <= l && l < d && !t[l] ==>
    forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
        w[i][j].le(w[i][l].add(w[l][j])))]
pub(crate) fn min_closed(f: MMat, g: MMat, w: MMat, t: Seq<bool>, d: Int) {
    pearlite! {
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> {
            bmin_spec(f[i][j], g[i][j]);
            le_total(f[i][j], g[i][j]);
            le_trans(f[i][j], f[i][j], f[i][j]);
            w[i][j] == bmin(f[i][j], g[i][j]) && w[i][j].le(f[i][j]) && w[i][j].le(g[i][j])
        });
        proof_assert!(forall<l: Int> 0 <= l && l < d && !t[l] ==>
            forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> {
                le_trans(w[i][j], f[i][j], f[i][l].add(f[l][j]));
                w[i][l] == f[i][l] && w[l][j] == f[l][j]
                    && w[i][j].le(w[i][l].add(w[l][j]))
            });
        proof_assert!(forall<j: Int> 0 <= j && j < d ==> {
            le_trans(w[0][j], f[0][j], BoundModel::Le(0));
            w[0][j].le(BoundModel::Le(0))
        });
        proof_assert!(forall<u: Val> mzone(w, d, u) ==>
            forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> {
                le_sound(w[i][j], f[i][j], u[i] - u[j]);
                le_sound(w[i][j], g[i][j], u[i] - u[j]);
                sat(f[i][j], u[i] - u[j]) && sat(g[i][j], u[i] - u[j])
            });
    }
}

/// The weight of the path `k → i → j → l` through the new edge `(i, j)`.
#[logic(open(crate))]
pub(crate) fn via(f: MMat, i: Int, j: Int, b: BoundModel, k: Int, l: Int) -> BoundModel {
    pearlite! { f[k][i].add(b).add(f[j][l]) }
}

/// The closure of `f ∧ xᵢ − xⱼ ⋈ b`, entry by entry.
#[logic(open(crate))]
pub(crate) fn edge(f: MMat, i: Int, j: Int, b: BoundModel) -> MMat {
    pearlite! { |k: Int| |l: Int| bmin(f[k][l], via(f, i, j, b, k, l)) }
}

/// The new edge closes no negative cycle: `Le 0 ≼ b + f[j][i]`.
#[logic(open(crate))]
pub(crate) fn edge_ok(f: MMat, i: Int, j: Int, b: BoundModel) -> bool {
    pearlite! { BoundModel::Le(0).le(b.add(f[j][i])) }
}

/// The hypotheses of the edge lemmas.
#[logic(open(crate))]
pub(crate) fn edge_pre(f: MMat, d: Int, i: Int, j: Int, b: BoundModel) -> bool {
    pearlite! {
        mcanonical(f, d) && 0 <= i && i < d && 0 <= j && j < d && edge_ok(f, i, j, b)
    }
}

/// `f[k][i] + b + f[j][m] + f[m][l] ≽ f[k][i] + b + f[j][l]`.
#[logic]
#[requires(mtri(f, d) && 0 <= j && j < d && 0 <= m && m < d && 0 <= l && l < d)]
#[ensures(via(f, i, j, b, k, l).le(via(f, i, j, b, k, m).add(f[m][l])))]
fn via_right(f: MMat, d: Int, i: Int, j: Int, b: BoundModel, k: Int, m: Int, l: Int) {
    pearlite! {
        let a = f[k][i].add(b);
        add_assoc(a, f[j][m], f[m][l]);
        add_mono(f[j][l], f[j][m].add(f[m][l]), a)
    }
}

/// `f[k][m] + f[m][i] + b + f[j][l] ≽ f[k][i] + b + f[j][l]`.
#[logic]
#[requires(mtri(f, d) && 0 <= k && k < d && 0 <= m && m < d && 0 <= i && i < d)]
#[ensures(via(f, i, j, b, k, l).le(f[k][m].add(via(f, i, j, b, m, l))))]
fn via_left(f: MMat, d: Int, i: Int, j: Int, b: BoundModel, k: Int, m: Int, l: Int) {
    pearlite! {
        add_assoc(f[k][m], f[m][i].add(b), f[j][l]);
        add_assoc(f[k][m], f[m][i], b);
        add_mono(f[k][i], f[k][m].add(f[m][i]), b);
        add_mono(f[k][i].add(b), f[k][m].add(f[m][i]).add(b), f[j][l])
    }
}

/// Two passes through the new edge are no shorter than one.
#[logic]
#[requires(edge_pre(f, d, i, j, b) && 0 <= m && m < d)]
#[ensures(via(f, i, j, b, k, l).le(via(f, i, j, b, k, m).add(via(f, i, j, b, m, l))))]
fn via_twice(f: MMat, d: Int, i: Int, j: Int, b: BoundModel, k: Int, m: Int, l: Int) {
    pearlite! {
        let a = f[k][i].add(b);
        let c = f[j][m];
        let e = f[m][i].add(b);
        let w = c.add(f[m][i]).add(b);
        // ((a + c) + (e + f[j][l])) == (a + w) + f[j][l]
        add_assoc(a, c, e.add(f[j][l]));
        add_assoc(c, e, f[j][l]);
        add_assoc(c, f[m][i], b);
        add_assoc(a, w, f[j][l]);
        // w ≽ f[j][i] + b ≽ Le 0
        add_mono(f[j][i], c.add(f[m][i]), b);
        add_comm_unit(f[j][i], b);
        le_trans(BoundModel::Le(0), f[j][i].add(b), w);
        add_mono(BoundModel::Le(0), w, a);
        add_comm_unit(a, BoundModel::Le(0));
        add_mono(a, a.add(w), f[j][l])
    }
}

/// The triangle `(k, l)` through `m` of `edge`.
#[logic]
#[requires(edge_pre(f, d, i, j, b))]
#[requires(0 <= k && k < d && 0 <= m && m < d && 0 <= l && l < d)]
#[ensures(edge(f, i, j, b)[k][l].le(edge(f, i, j, b)[k][m].add(edge(f, i, j, b)[m][l])))]
fn edge_tri_point(f: MMat, d: Int, i: Int, j: Int, b: BoundModel, k: Int, m: Int, l: Int) {
    pearlite! {
        let e = edge(f, i, j, b);
        bmin_spec(f[k][l], via(f, i, j, b, k, l));
        bmin_spec(f[k][m], via(f, i, j, b, k, m));
        bmin_spec(f[m][l], via(f, i, j, b, m, l));
        let target = if e[k][m] == f[k][m] {
            if e[m][l] == f[m][l] {
                f[k][l]
            } else {
                via_left(f, d, i, j, b, k, m, l);
                via(f, i, j, b, k, l)
            }
        } else if e[m][l] == f[m][l] {
            via_right(f, d, i, j, b, k, m, l);
            via(f, i, j, b, k, l)
        } else {
            via_twice(f, d, i, j, b, k, m, l);
            via(f, i, j, b, k, l)
        };
        proof_assert!(e[k][l].le(target));
        proof_assert!(target.le(e[k][m].add(e[m][l])));
        le_trans(e[k][l], target, e[k][m].add(e[m][l]))
    }
}

/// `f[k][i] + b + f[j][k] ≽ Le 0`: the diagonal of `edge` stays `Le 0`.
#[logic]
#[requires(edge_pre(f, d, i, j, b) && 0 <= k && k < d)]
#[ensures(BoundModel::Le(0).le(via(f, i, j, b, k, k)))]
#[ensures(edge(f, i, j, b)[k][k] == BoundModel::Le(0))]
fn edge_diag(f: MMat, d: Int, i: Int, j: Int, b: BoundModel, k: Int) {
    pearlite! {
        let a = f[k][i].add(b);
        add_comm_unit(a, f[j][k]);
        add_assoc(f[j][k], f[k][i], b);
        add_mono(f[j][i], f[j][k].add(f[k][i]), b);
        add_comm_unit(f[j][i], b);
        le_trans(BoundModel::Le(0), f[j][i].add(b), via(f, i, j, b, k, k));
        bmin_spec(f[k][k], via(f, i, j, b, k, k))
    }
}

/// The closure of a tightened canonical matrix is canonical.
#[logic]
#[requires(edge_pre(f, d, i, j, b))]
#[ensures(mcanonical(edge(f, i, j, b), d))]
pub(crate) fn edge_canonical(f: MMat, d: Int, i: Int, j: Int, b: BoundModel) {
    pearlite! {
        proof_assert!(forall<k: Int> 0 <= k && k < d ==> {
            edge_diag(f, d, i, j, b, k); edge(f, i, j, b)[k][k] == BoundModel::Le(0)
        });
        proof_assert!(forall<l: Int> 0 <= l && l < d ==> {
            bmin_spec(f[0][l], via(f, i, j, b, 0, l));
            le_trans(edge(f, i, j, b)[0][l], f[0][l], BoundModel::Le(0));
            edge(f, i, j, b)[0][l].le(BoundModel::Le(0))
        });
        proof_assert!(forall<k: Int, l: Int, m: Int>
            0 <= k && k < d && 0 <= l && l < d && 0 <= m && m < d ==> {
                edge_tri_point(f, d, i, j, b, k, m, l);
                edge(f, i, j, b)[k][l].le(edge(f, i, j, b)[k][m].add(edge(f, i, j, b)[m][l]))
            });
    }
}

/// `γ(edge) = γ(f) ∩ ⟦xᵢ − xⱼ ⋈ b⟧`. Needs only `Le 0` on the diagonal.
#[logic]
#[requires(0 <= i && i < d && 0 <= j && j < d)]
#[requires(f[i][i] == BoundModel::Le(0) && f[j][j] == BoundModel::Le(0))]
#[ensures(forall<u: Val> mzone(edge(f, i, j, b), d, u) == (mzone(f, d, u) && sat(b, u[i] - u[j])))]
pub(crate) fn edge_zone(f: MMat, d: Int, i: Int, j: Int, b: BoundModel) {
    pearlite! {
        let e = edge(f, i, j, b);
        add_comm_unit(b, BoundModel::Le(0));
        add_comm_unit(BoundModel::Le(0), b);
        bmin_spec(f[i][j], via(f, i, j, b, i, j));
        proof_assert!(via(f, i, j, b, i, j) == b);
        proof_assert!(forall<u: Val> mzone(e, d, u) ==> sat(b, u[i] - u[j]) && {
            le_sound(e[i][j], b, u[i] - u[j]); true
        });
        proof_assert!(forall<u: Val> mzone(e, d, u) ==>
            forall<k: Int, l: Int> 0 <= k && k < d && 0 <= l && l < d ==> {
                bmin_spec(f[k][l], via(f, i, j, b, k, l));
                le_sound(e[k][l], f[k][l], u[k] - u[l]);
                sat(f[k][l], u[k] - u[l])
            });
        proof_assert!(forall<u: Val> mzone(f, d, u) && sat(b, u[i] - u[j]) ==>
            forall<k: Int, l: Int> 0 <= k && k < d && 0 <= l && l < d ==> {
                add_sound(f[k][i], b, u[k] - u[i], u[i] - u[j]);
                add_sound(f[k][i].add(b), f[j][l], (u[k] - u[i]) + (u[i] - u[j]), u[j] - u[l]);
                proof_assert!((u[k] - u[i]) + (u[i] - u[j]) + (u[j] - u[l]) == u[k] - u[l]);
                bmin_spec(f[k][l], via(f, i, j, b, k, l));
                sat(e[k][l], u[k] - u[l])
            });
    }
}

/// `c ≺ e` leaves room for the opposite constraint: `Le 0 ≼ neg c + e`.
#[logic]
#[requires(!e.le(c))]
#[ensures(c != BoundModel::Inf)]
#[ensures(BoundModel::Le(0).le(c.neg().add(e)))]
fn neg_gap(c: BoundModel, e: BoundModel) {}

/// Every off-diagonal entry of a canonical matrix is tight: a strictly
/// tighter bound is violated by some member of the zone, witnessed by
/// the closure of the opposite constraint.
#[logic]
#[requires(mcanonical(f, d))]
#[requires(0 <= k && k < d && 0 <= l && l < d && k != l)]
#[requires(!f[k][l].le(c))]
#[ensures(exists<u: Val> mzone(f, d, u) && !sat(c, u[k] - u[l]))]
pub(crate) fn tight(f: MMat, d: Int, k: Int, l: Int, c: BoundModel) {
    pearlite! {
        neg_gap(c, f[k][l]);
        edge_canonical(f, d, l, k, c.neg());
        edge_zone(f, d, l, k, c.neg());
        mcanonical_nonempty(edge(f, l, k, c.neg()), d);
        neg_complement(c);
        proof_assert!(forall<u: Val> -(u[k] - u[l]) == u[l] - u[k]);
    }
}

/// Theorem 3.1 (B7): two canonical matrices with the same zone are equal.
#[logic]
#[requires(mcanonical(f, d) && mcanonical(g, d))]
#[requires(forall<u: Val> mzone(f, d, u) == mzone(g, d, u))]
#[ensures(meq(f, g, d))]
pub(crate) fn canonical_unique(f: MMat, g: MMat, d: Int) {
    pearlite! {
        proof_assert!(forall<k: Int, l: Int> 0 <= k && k < d && 0 <= l && l < d && k != l ==> {
            if !f[k][l].le(g[k][l]) { tight(f, d, k, l, g[k][l]) }
            f[k][l].le(g[k][l])
        });
        proof_assert!(forall<k: Int, l: Int> 0 <= k && k < d && 0 <= l && l < d && k != l ==> {
            if !g[k][l].le(f[k][l]) { tight(g, d, k, l, f[k][l]) }
            g[k][l].le(f[k][l])
        });
        proof_assert!(forall<k: Int, l: Int> 0 <= k && k < d && 0 <= l && l < d ==> {
            le_total(f[k][l], g[k][l]); f[k][l] == g[k][l]
        });
    }
}

// ----- constructors -----

/// The matrix of `zero(n)`: every entry `Le 0` is canonical.
#[logic]
#[requires(1 <= d && s.len() == d * d)]
#[requires(forall<x: Int> 0 <= x && x < s.len() ==> s[x]@ == BoundModel::Le(0))]
#[ensures(canonical(s, d))]
pub(crate) fn zero_canonical(s: Seq<Bound>, d: Int) {
    pearlite! {
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> {
            ent_read(s, d, i, j); ent(s, d, i, j) == BoundModel::Le(0)
        });
    }
}

/// Entry `(i, j)` of `universe(n)`: `Le 0` on row 0 and the diagonal, `∞`
/// elsewhere.
#[logic(open(crate))]
pub(crate) fn universe_entry(i: Int, j: Int) -> BoundModel {
    if i == 0 || i == j {
        BoundModel::Le(0)
    } else {
        BoundModel::Inf
    }
}

/// The matrix of `universe(n)` is canonical.
#[logic]
#[requires(1 <= d && s.len() == d * d)]
#[requires(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
    ent(s, d, i, j) == universe_entry(i, j))]
#[ensures(canonical(s, d))]
pub(crate) fn universe_canonical(s: Seq<Bound>, d: Int) {}

/// The zone of `universe(n)` is every nonnegative valuation.
#[logic]
#[requires(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
    ent(s, d, i, j) == universe_entry(i, j))]
#[ensures(forall<u: Val> zone(s, d, u) == valuation(d, u))]
pub(crate) fn universe_zone(s: Seq<Bound>, d: Int) {
    pearlite! {
        proof_assert!(forall<u: Val> valuation(d, u) ==>
            forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> {
                proof_assert!(u[i] - u[i] == Real::from_int(0));
                proof_assert!(u[0] - u[j] == -u[j]);
                sat(ent(s, d, i, j), u[i] - u[j])
            });
    }
}

// ----- range failures -----

/// Exact arithmetic left the representable range: some state `s` reached
/// by closure, which denotes the same zone as the input and has not (yet)
/// exposed a negative diagonal, has finite entries `(i, k)` and `(k, j)`
/// whose exact sum has an unrepresentable constant.
#[logic(open(crate))]
pub(crate) fn range_failure(w: Seq<Bound>, d: Int) -> bool {
    pearlite! {
        exists<s: Seq<Bound>, i: Int, k: Int, j: Int>
            range_failure_at(s, w, d, i, k, j)
    }
}

/// The witness form of `range_failure`.
#[logic(open(crate))]
pub(crate) fn range_failure_at(
    s: Seq<Bound>,
    w: Seq<Bound>,
    d: Int,
    i: Int,
    k: Int,
    j: Int,
) -> bool {
    pearlite! {
        s.len() == d * d && same_zone(s, w, d) && diag_le0(s, d)
            && 0 <= i && i < d && 0 <= k && k < d && 0 <= j && j < d
            && ent(s, d, i, k) != BoundModel::Inf && ent(s, d, k, j) != BoundModel::Inf
            && !ent(s, d, i, k).add_in_range(ent(s, d, k, j))
    }
}

/// `range_failure` of some storage whose model matrix is `f`: the
/// range failures of an intersection are stated on the model of the
/// minimum, which has no storage in the specification.
#[logic(open(crate))]
pub(crate) fn mrange_failure(f: MMat, d: Int) -> bool {
    pearlite! {
        exists<s: Seq<Bound>> s.len() == d * d && meq(mat(s, d), f, d) && range_failure(s, d)
    }
}

/// `mrange_failure` depends only on the entries of the model matrix.
#[logic]
#[requires(meq(f, g, d) && mrange_failure(f, d))]
#[ensures(mrange_failure(g, d))]
pub(crate) fn mrange_failure_meq(f: MMat, g: MMat, d: Int) {}

/// Introduces `range_failure` from a witness.
#[logic]
#[requires(range_failure_at(s, w, d, i, k, j))]
#[ensures(range_failure(w, d))]
pub(crate) fn range_failure_intro(s: Seq<Bound>, w: Seq<Bound>, d: Int, i: Int, k: Int, j: Int) {}

// ----- a sufficient condition for arithmetic success -----
//
// Path-free bound: every pivot at most doubles the magnitude of finite
// constants, so `B · 2^d ≤ MAX_CONSTANT` excludes `Err(Range)`. The linear
// premise `2·d·B ≤ MAX_CONSTANT` of §7.1 needs simple-path weights and is
// not proved here (see `verification/PROOF_STATUS.md`).

/// `2ⁿ` for `n ≥ 0`.
#[logic]
#[variant(n)]
pub(crate) fn pow2(n: Int) -> Int {
    if n <= 0 { 1 } else { 2 * pow2(n - 1) }
}

/// `2ⁿ ≥ 1`.
#[logic]
#[variant(n)]
#[ensures(1 <= pow2(n))]
fn pow2_pos(n: Int) {
    pearlite! { if n > 0 { pow2_pos(n - 1) } }
}

/// `2ⁿ` is positive, doubles per step and is monotone.
#[logic]
#[variant(c)]
#[requires(0 <= a && a <= c)]
#[ensures(1 <= pow2(a) && pow2(a) <= pow2(c))]
#[ensures(pow2(a + 1) == 2 * pow2(a))]
pub(crate) fn pow2_mono(a: Int, c: Int) {
    pearlite! {
        pow2_pos(a);
        if a < c {
            pow2_mono(a, c - 1);
            pow2_pos(c - 1)
        }
    }
}

/// A finite bound has a constant of magnitude at most `m`.
#[logic(open(crate))]
pub(crate) fn fin_bounded(b: BoundModel, m: Int) -> bool {
    match b {
        BoundModel::Lt(c) | BoundModel::Le(c) => -m <= c && c <= m,
        BoundModel::Inf => true,
    }
}

/// Every finite entry has a constant of magnitude at most `m`.
#[logic(open(crate))]
pub(crate) fn bounded(s: Seq<Bound>, d: Int, m: Int) -> bool {
    pearlite! {
        forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
            fin_bounded(ent(s, d, i, j), m)
    }
}

/// Bounds are monotone in `m`; a sum of two `m`-bounded bounds is
/// `2m`-bounded, and representable if `2m ≤ MAX_CONSTANT`.
#[logic]
#[requires(fin_bounded(a, m) && fin_bounded(b, m))]
#[ensures(m <= m2 ==> fin_bounded(a, m2))]
#[ensures(fin_bounded(a.add(b), 2 * m))]
#[ensures(2 * m <= crate::bounds::MAX_CONSTANT@ ==> a.add_in_range(b))]
pub(crate) fn sum_bounded(a: BoundModel, b: BoundModel, m: Int, m2: Int) {}

/// Overwriting one entry with an `m`-bounded value keeps `bounded`.
#[logic]
#[requires(s.len() == d * d && 0 <= i && i < d && 0 <= j && j < d)]
#[requires(bounded(s, d, m) && fin_bounded(v@, m))]
#[ensures(bounded(s.set(i * d + j, v), d, m))]
#[ensures(i == 0 ==> bounded(s.set(j, v), d, m))]
pub(crate) fn bounded_set(s: Seq<Bound>, d: Int, i: Int, j: Int, v: Bound, m: Int) {
    pearlite! {
        ent_set(s, d, i, j, v);
        if i == 0 { ent_set_ref(s, d, j, v) }
    }
}

/// `bounded` is monotone in `m`.
#[logic]
#[requires(bounded(s, d, m) && m <= m2)]
#[ensures(bounded(s, d, m2))]
pub(crate) fn bounded_mono(s: Seq<Bound>, d: Int, m: Int, m2: Int) {}

/// After `e` pivots, every `B`-bounded input is `B·2ᵉ`-bounded.
#[logic(open(crate))]
pub(crate) fn growth(w: Seq<Bound>, s: Seq<Bound>, d: Int, e: Int) -> bool {
    pearlite! { forall<b: Int> 0 <= b && bounded(w, d, b) ==> bounded(s, d, b * pow2(e)) }
}

/// No pivot yet: the input bounds itself.
#[logic]
#[ensures(growth(w, w, d, 0))]
pub(crate) fn growth_init(w: Seq<Bound>, d: Int) {}

/// `growth` is monotone in the number of pivots.
#[logic]
#[requires(0 <= e && e <= e2 && growth(w, s, d, e))]
#[ensures(growth(w, s, d, e2))]
pub(crate) fn growth_mono(w: Seq<Bound>, s: Seq<Bound>, d: Int, e: Int, e2: Int) {
    pearlite! {
        pow2_mono(e, e2);
        proof_assert!(forall<b: Int> 0 <= b && bounded(w, d, b) ==> {
            proof_assert!(b * pow2(e) <= b * pow2(e2));
            bounded_mono(s, d, b * pow2(e), b * pow2(e2));
            bounded(s, d, b * pow2(e2))
        });
    }
}

/// Writing `Le 0` (the normalization of step 1) keeps `growth`.
#[logic]
#[requires(0 <= e && s.len() == d * d && 0 <= i && i < d && 0 <= j && j < d)]
#[requires(growth(w, s, d, e) && v@ == BoundModel::Le(0))]
#[ensures(growth(w, s.set(i * d + j, v), d, e))]
#[ensures(i == 0 ==> growth(w, s.set(j, v), d, e))]
pub(crate) fn growth_le0(w: Seq<Bound>, s: Seq<Bound>, d: Int, e: Int, i: Int, j: Int, v: Bound) {
    pearlite! {
        pow2_mono(e, e);
        proof_assert!(forall<b: Int> 0 <= b && bounded(w, d, b) ==> {
            proof_assert!(0 <= b * pow2(e));
            bounded_set(s, d, i, j, v, b * pow2(e));
            bounded(s.set(i * d + j, v), d, b * pow2(e))
                && (i == 0 ==> bounded(s.set(j, v), d, b * pow2(e)))
        });
    }
}

/// `growth_sum` for one input bound `b`.
#[logic]
#[requires(0 <= k && k < d && s.len() == d * d && old.len() == d * d)]
#[requires(0 <= i && i < d && 0 <= j && j < d && 0 <= b)]
#[requires(bounded(old, d, b * pow2(k)) && bounded(s, d, b * pow2(k + 1)))]
#[requires(v@ == ent(old, d, i, k).add(ent(old, d, k, j)))]
#[ensures(bounded(s.set(i * d + j, v), d, b * pow2(k + 1)))]
#[allow(clippy::too_many_arguments)]
fn growth_sum_at(old: Seq<Bound>, s: Seq<Bound>, d: Int, k: Int, i: Int, j: Int, v: Bound, b: Int) {
    pearlite! {
        pow2_mono(k, k);
        proof_assert!(b * (2 * pow2(k)) == 2 * (b * pow2(k)));
        proof_assert!(b * pow2(k + 1) == 2 * (b * pow2(k)));
        sum_bounded(ent(old, d, i, k), ent(old, d, k, j), b * pow2(k), b * pow2(k));
        bounded_set(s, d, i, j, v, b * pow2(k + 1))
    }
}

/// Writing the sum `old[i][k] + old[k][j]` during pivot `k` keeps the
/// `k + 1` growth bound.
#[logic]
#[requires(0 <= k && k < d && s.len() == d * d && old.len() == d * d)]
#[requires(0 <= i && i < d && 0 <= j && j < d)]
#[requires(growth(w, old, d, k) && growth(w, s, d, k + 1))]
#[requires(v@ == ent(old, d, i, k).add(ent(old, d, k, j)))]
#[ensures(growth(w, s.set(i * d + j, v), d, k + 1))]
#[allow(clippy::too_many_arguments)]
pub(crate) fn growth_sum(
    w: Seq<Bound>,
    old: Seq<Bound>,
    s: Seq<Bound>,
    d: Int,
    k: Int,
    i: Int,
    j: Int,
    v: Bound,
) {
    pearlite! {
        proof_assert!(forall<b: Int> 0 <= b && bounded(w, d, b) ==> {
            growth_sum_at(old, s, d, k, i, j, v, b);
            bounded(s.set(i * d + j, v), d, b * pow2(k + 1))
        });
    }
}

/// An unrepresentable sum during pivot `k` violates `B · 2^d ≤ MAX_CONSTANT`
/// for every bound `B` of the input.
#[logic]
#[requires(0 <= k && k < d && 0 <= i && i < d && 0 <= j && j < d)]
#[requires(growth(w, old, d, k))]
#[requires(!ent(old, d, i, k).add_in_range(ent(old, d, k, j)))]
#[ensures(forall<b: Int> 0 <= b && bounded(w, d, b) ==>
    crate::bounds::MAX_CONSTANT@ < b * pow2(d))]
pub(crate) fn growth_err(w: Seq<Bound>, old: Seq<Bound>, d: Int, k: Int, i: Int, j: Int) {
    pearlite! {
        pow2_mono(k, k);
        pow2_mono(k + 1, d);
        proof_assert!(forall<b: Int> 0 <= b && bounded(w, d, b) ==> {
            let m = b * pow2(k);
            sum_bounded(ent(old, d, i, k), ent(old, d, k, j), m, m);
            proof_assert!(b * pow2(k + 1) == 2 * m);
            proof_assert!(b * pow2(k + 1) <= b * pow2(d));
            crate::bounds::MAX_CONSTANT@ < b * pow2(d)
        });
    }
}
