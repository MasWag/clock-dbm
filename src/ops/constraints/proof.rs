//! Ghost-only lemmas for the incremental closure of `constraints.rs`.
//! Everything here is logic and exists only for Creusot.
//!
//! The specification is `dbm::proof::edge`: for a canonical `f` and a guard
//! `xᵢ − xⱼ ⋈ b`, the closed result is `min(f[k][l], f[k][i] + b + f[j][l])`
//! (`edge_canonical`, `edge_zone`; it is the unique canonical form by
//! `canonical_unique`). The lemmas below justify each step of the shipped
//! algorithm against it: the implied and contradiction tests, the `d = 2`
//! store, phase 1 (row `i`), the selective skip and phase 2 (every other
//! row), and the stability of the entries read in place.

use crate::bounds::{
    BoundModel, Constraint, add_assoc, add_comm_unit, add_mono, add_sound, below_le_zero_unsat,
    le_sound, le_total, le_trans, relax_entry, relax_needed, sat,
};
use crate::dbm::proof::{MMat, Val, bmin, bmin_spec, edge, edge_ok, mcanonical, mzone, via};
use creusot_std::{logic::real::Real, prelude::*};

// ----- constraints and their conjunction -----

/// `u` satisfies the constraint `c`.
#[logic(open(crate))]
pub(crate) fn csat(c: Constraint, u: Val) -> bool {
    pearlite! { sat(c@.2, u[c@.0] - u[c@.1]) }
}

/// `u` satisfies the first `n` constraints of `cs`.
#[logic(open(crate))]
pub(crate) fn conj(cs: Seq<Constraint>, n: Int, u: Val) -> bool {
    pearlite! { forall<t: Int> 0 <= t && t < n ==> csat(cs[t], u) }
}

/// Both clocks of `c` are clocks of a DBM over `n` variables.
#[logic(open(crate))]
pub(crate) fn valid(c: Constraint, n: Int) -> bool {
    pearlite! { c@.0 <= n && c@.1 <= n }
}

/// Every constraint of `cs` is valid.
#[logic(open(crate))]
pub(crate) fn all_valid(cs: Seq<Constraint>, n: Int) -> bool {
    pearlite! { forall<t: Int> 0 <= t && t < cs.len() ==> valid(cs[t], n) }
}

// ----- the single-constraint cases -----

/// Some entry of the exact closure `edge(f, i, j, b)` is unrepresentable.
#[logic(open(crate))]
pub(crate) fn edge_unrepresentable(f: MMat, d: Int, i: Int, j: Int, b: BoundModel) -> bool {
    pearlite! {
        exists<k: Int, l: Int> 0 <= k && k < d && 0 <= l && l < d
            && !edge(f, i, j, b)[k][l].representable()
    }
}

/// The exact range failure of one constraint: it is neither implied nor
/// contradicting, so the result is the nonempty `edge`, and that has an
/// unrepresentable entry.
#[logic(open(crate))]
pub(crate) fn single_range_failure(f: MMat, d: Int, i: Int, j: Int, b: BoundModel) -> bool {
    pearlite! {
        !f[i][j].le(b) && edge_ok(f, i, j, b) && edge_unrepresentable(f, d, i, j, b)
    }
}

/// Introduces `edge_unrepresentable` from a witness.
#[logic]
#[requires(0 <= k && k < d && 0 <= l && l < d)]
#[requires(!edge(f, i, j, b)[k][l].representable())]
#[ensures(edge_unrepresentable(f, d, i, j, b))]
pub(crate) fn edge_unrep_intro(f: MMat, d: Int, i: Int, j: Int, b: BoundModel, k: Int, l: Int) {}

/// Implied (`f[i][j] ≼ b`): the zone already satisfies the constraint and
/// the closure is `f` itself.
#[logic]
#[requires(mcanonical(f, d) && 0 <= i && i < d && 0 <= j && j < d)]
#[requires(f[i][j].le(b))]
#[ensures(forall<u: Val> mzone(f, d, u) ==> sat(b, u[i] - u[j]))]
#[ensures(forall<k: Int, l: Int> 0 <= k && k < d && 0 <= l && l < d ==>
    edge(f, i, j, b)[k][l] == f[k][l])]
pub(crate) fn implied(f: MMat, d: Int, i: Int, j: Int, b: BoundModel) {
    pearlite! {
        proof_assert!(forall<u: Val> mzone(f, d, u) ==> {
            le_sound(f[i][j], b, u[i] - u[j]); sat(b, u[i] - u[j])
        });
        proof_assert!(forall<k: Int, l: Int> 0 <= k && k < d && 0 <= l && l < d ==> {
            add_mono(f[i][j], b, f[k][i]);
            add_mono(f[k][i].add(f[i][j]), f[k][i].add(b), f[j][l]);
            add_mono(f[k][j], f[k][i].add(f[i][j]), f[j][l]);
            le_trans(f[k][j].add(f[j][l]), f[k][i].add(f[i][j]).add(f[j][l]), via(f, i, j, b, k, l));
            le_trans(f[k][l], f[k][j].add(f[j][l]), via(f, i, j, b, k, l));
            bmin_spec(f[k][l], via(f, i, j, b, k, l));
            edge(f, i, j, b)[k][l] == f[k][l]
        });
    }
}

/// Contradiction (`b + f[j][i] ≺ Le 0`): no member of the zone satisfies
/// the constraint. This covers strict-zero cycles (`Lt 0`) and `i = j`.
#[logic]
#[requires(0 <= i && i < d && 0 <= j && j < d)]
#[requires(!edge_ok(f, i, j, b))]
#[ensures(forall<u: Val> !(mzone(f, d, u) && sat(b, u[i] - u[j])))]
pub(crate) fn contradiction(f: MMat, d: Int, i: Int, j: Int, b: BoundModel) {
    pearlite! {
        below_le_zero_unsat(b.add(f[j][i]));
        proof_assert!(forall<u: Val> mzone(f, d, u) && sat(b, u[i] - u[j]) ==> {
            add_sound(b, f[j][i], u[i] - u[j], u[j] - u[i]);
            proof_assert!((u[i] - u[j]) + (u[j] - u[i]) == Real::from_int(0));
            false
        });
    }
}

/// Neither implied nor contradicting: the indices differ and `b` is finite.
#[logic]
#[requires(mcanonical(f, d) && 0 <= i && i < d && 0 <= j && j < d)]
#[requires(!f[i][j].le(b) && edge_ok(f, i, j, b))]
#[ensures(i != j && b != BoundModel::Inf)]
pub(crate) fn tighten_distinct(f: MMat, d: Int, i: Int, j: Int, b: BoundModel) {
    pearlite! { add_comm_unit(b, BoundModel::Le(0)) }
}

/// The path through the new edge to column `j` or from row `i` uses one
/// diagonal entry: `via(k, j) = f[k][i] + b` and `via(i, l) = b + f[j][l]`.
#[logic]
#[requires(f[i][i] == BoundModel::Le(0) && f[j][j] == BoundModel::Le(0))]
#[ensures(via(f, i, j, b, k, j) == f[k][i].add(b))]
#[ensures(via(f, i, j, b, i, l) == b.add(f[j][l]))]
pub(crate) fn via_unit(f: MMat, i: Int, j: Int, b: BoundModel, k: Int, l: Int) {
    pearlite! {
        add_comm_unit(f[k][i].add(b), BoundModel::Le(0));
        add_comm_unit(BoundModel::Le(0), b);
        add_comm_unit(b, BoundModel::Le(0))
    }
}

/// In-place read stability: the closure changes neither column `i` nor
/// row `j`, and puts `b` at `(i, j)`.
#[logic]
#[requires(mcanonical(f, d) && 0 <= i && i < d && 0 <= j && j < d)]
#[requires(!f[i][j].le(b) && edge_ok(f, i, j, b))]
#[ensures(forall<k: Int> edge(f, i, j, b)[k][i] == f[k][i])]
#[ensures(forall<l: Int> edge(f, i, j, b)[j][l] == f[j][l])]
#[ensures(edge(f, i, j, b)[i][j] == b)]
pub(crate) fn stable(f: MMat, d: Int, i: Int, j: Int, b: BoundModel) {
    pearlite! {
        proof_assert!(forall<k: Int> {
            add_assoc(f[k][i], b, f[j][i]);
            add_mono(BoundModel::Le(0), b.add(f[j][i]), f[k][i]);
            add_comm_unit(f[k][i], BoundModel::Le(0));
            bmin_spec(f[k][i], via(f, i, j, b, k, i));
            edge(f, i, j, b)[k][i] == f[k][i]
        });
        proof_assert!(forall<l: Int> {
            add_comm_unit(f[j][i], b);
            add_mono(BoundModel::Le(0), f[j][i].add(b), f[j][l]);
            add_comm_unit(f[j][l], BoundModel::Le(0));
            bmin_spec(f[j][l], via(f, i, j, b, j, l));
            edge(f, i, j, b)[j][l] == f[j][l]
        });
        via_unit(f, i, j, b, i, j);
        add_comm_unit(b, BoundModel::Le(0));
        le_total(f[i][j], b);
        bmin_spec(f[i][j], via(f, i, j, b, i, j));
    }
}

/// One actual clock (`d = 2`): the closure changes `(i, j)` only.
#[logic]
#[requires(d == 2 && mcanonical(f, d) && 0 <= i && i < d && 0 <= j && j < d)]
#[requires(!f[i][j].le(b) && edge_ok(f, i, j, b))]
#[ensures(forall<k: Int, l: Int> 0 <= k && k < d && 0 <= l && l < d ==>
    edge(f, i, j, b)[k][l] == if k == i && l == j { b } else { f[k][l] })]
pub(crate) fn one_clock(f: MMat, d: Int, i: Int, j: Int, b: BoundModel) {
    pearlite! {
        tighten_distinct(f, d, i, j, b);
        stable(f, d, i, j, b)
    }
}

// ----- the rows of the incremental closure -----

/// One entry written by `Matrix::relax_row` when no needed sum is
/// unrepresentable: the minimum.
#[logic]
#[requires(relax_entry(cur, v, s, new))]
#[requires(!(relax_needed(cur, v, s) && !v.add_in_range(s)))]
#[ensures(new == bmin(cur, v.add(s)))]
pub(crate) fn relax_min(cur: BoundModel, v: BoundModel, s: BoundModel, new: BoundModel) {
    pearlite! { le_total(cur, v.add(s)); add_comm_unit(v, s) }
}

/// The sum is representable iff `add_in_range` holds.
#[logic]
#[ensures(a.add_in_range(b) == a.add(b).representable())]
pub(crate) fn add_repr(a: BoundModel, b: BoundModel) {}

/// Phase 1: row `i` of the closure is `min(f[i][l], b + f[j][l])`; a needed
/// but unrepresentable sum there is an unrepresentable entry.
#[logic]
#[requires(mcanonical(f, d) && 0 <= i && i < d && 0 <= j && j < d)]
#[ensures(forall<l: Int> edge(f, i, j, b)[i][l] == bmin(f[i][l], b.add(f[j][l])))]
#[ensures(forall<l: Int> 0 <= l && l < d && relax_needed(f[i][l], b, f[j][l])
    && !b.add_in_range(f[j][l]) ==> edge_unrepresentable(f, d, i, j, b))]
pub(crate) fn phase1(f: MMat, d: Int, i: Int, j: Int, b: BoundModel) {
    pearlite! {
        proof_assert!(forall<l: Int> {
            via_unit(f, i, j, b, i, l);
            edge(f, i, j, b)[i][l] == bmin(f[i][l], b.add(f[j][l]))
        });
        proof_assert!(forall<l: Int> 0 <= l && l < d && relax_needed(f[i][l], b, f[j][l])
            && !b.add_in_range(f[j][l]) ==> {
                add_repr(b, f[j][l]);
                edge_unrep_intro(f, d, i, j, b, i, l);
                true
            });
    }
}

/// The selective skip: if `f[k][j] ≼ f[k][i] + b`, the closure leaves row
/// `k` unchanged (canonicity: `f[k][i] + b + f[j][l] ≽ f[k][j] + f[j][l] ≽
/// f[k][l]`).
#[logic]
#[requires(mcanonical(f, d) && 0 <= k && k < d && 0 <= j && j < d)]
#[requires(f[k][j].le(f[k][i].add(b)))]
#[ensures(forall<l: Int> 0 <= l && l < d ==> edge(f, i, j, b)[k][l] == f[k][l])]
pub(crate) fn skip(f: MMat, d: Int, i: Int, j: Int, b: BoundModel, k: Int) {
    pearlite! {
        proof_assert!(forall<l: Int> 0 <= l && l < d ==> {
            add_mono(f[k][j], f[k][i].add(b), f[j][l]);
            le_trans(f[k][l], f[k][j].add(f[j][l]), via(f, i, j, b, k, l));
            bmin_spec(f[k][l], via(f, i, j, b, k, l));
            edge(f, i, j, b)[k][l] == f[k][l]
        });
    }
}

/// A row with `f[k][i] = ∞` is unchanged.
#[logic]
#[requires(f[k][i] == BoundModel::Inf)]
#[ensures(forall<l: Int> edge(f, i, j, b)[k][l] == f[k][l])]
pub(crate) fn infinite_row(f: MMat, i: Int, j: Int, b: BoundModel, k: Int) {
    pearlite! {
        proof_assert!(forall<l: Int> {
            bmin_spec(f[k][l], via(f, i, j, b, k, l)); edge(f, i, j, b)[k][l] == f[k][l]
        });
    }
}

/// The skip test failed with an unrepresentable sum: entry `(k, j)` of the
/// closure is that sum.
#[logic]
#[requires(mcanonical(f, d) && 0 <= i && i < d && 0 <= j && j < d && 0 <= k && k < d)]
#[requires(!f[k][j].le(f[k][i].add(b)) && !f[k][i].add(b).representable())]
#[ensures(edge_unrepresentable(f, d, i, j, b))]
pub(crate) fn skip_test_unrepresentable(f: MMat, d: Int, i: Int, j: Int, b: BoundModel, k: Int) {
    pearlite! {
        via_unit(f, i, j, b, k, j);
        bmin_spec(f[k][j], via(f, i, j, b, k, j));
        edge_unrep_intro(f, d, i, j, b, k, j)
    }
}

/// Phase 2 for row `k`: relaxing through the **updated** row `i`,
/// `min(f[k][l], f[k][i] + e[i][l])`, is the closure (because `f[k][i] +
/// f[i][l] ≽ f[k][l]`); a needed sum is the closure's entry itself.
#[logic]
#[requires(mcanonical(f, d) && 0 <= i && i < d && 0 <= j && j < d && 0 <= k && k < d)]
#[ensures(forall<l: Int> 0 <= l && l < d ==>
    bmin(f[k][l], f[k][i].add(edge(f, i, j, b)[i][l])) == edge(f, i, j, b)[k][l])]
#[ensures(forall<l: Int> 0 <= l && l < d && relax_needed(f[k][l], f[k][i], edge(f, i, j, b)[i][l]) ==>
    f[k][i].add(edge(f, i, j, b)[i][l]) == edge(f, i, j, b)[k][l])]
pub(crate) fn phase2(f: MMat, d: Int, i: Int, j: Int, b: BoundModel, k: Int) {
    pearlite! {
        proof_assert!(forall<l: Int> 0 <= l && l < d ==> {
            let e = edge(f, i, j, b);
            via_unit(f, i, j, b, i, l);
            add_assoc(f[k][i], b, f[j][l]);
            bmin_spec(f[i][l], via(f, i, j, b, i, l));
            bmin_spec(f[k][l], via(f, i, j, b, k, l));
            bmin_spec(f[k][l], f[k][i].add(e[i][l]));
            if e[i][l] == f[i][l] {
                add_mono(f[i][l], b.add(f[j][l]), f[k][i]);
                le_trans(f[k][l], f[k][i].add(f[i][l]), via(f, i, j, b, k, l));
            }
            bmin(f[k][l], f[k][i].add(e[i][l])) == e[k][l]
                && (relax_needed(f[k][l], f[k][i], e[i][l]) ==> f[k][i].add(e[i][l]) == e[k][l])
        });
    }
}

// ----- tightening one entry before a full closure -----

/// `g` is `f` with `(i, j)` tightened to `min(f[i][j], b)`: its zone is
/// `γ(f) ∩ ⟦xᵢ − xⱼ ⋈ b⟧` (no canonicity needed).
#[logic]
#[requires(0 <= i && i < d && 0 <= j && j < d)]
#[requires(forall<k: Int, l: Int> 0 <= k && k < d && 0 <= l && l < d ==>
    g[k][l] == if k == i && l == j { bmin(f[i][j], b) } else { f[k][l] })]
#[ensures(forall<u: Val> mzone(g, d, u) == (mzone(f, d, u) && sat(b, u[i] - u[j])))]
pub(crate) fn tighten_zone(f: MMat, g: MMat, d: Int, i: Int, j: Int, b: BoundModel) {
    pearlite! {
        bmin_spec(f[i][j], b);
        proof_assert!(forall<u: Val> mzone(g, d, u) ==> {
            le_sound(g[i][j], b, u[i] - u[j]);
            le_sound(g[i][j], f[i][j], u[i] - u[j]);
            sat(b, u[i] - u[j]) && sat(f[i][j], u[i] - u[j])
        });
    }
}
