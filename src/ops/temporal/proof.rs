//! Ghost-only lemmas for the temporal operations of `temporal.rs`.
//! Everything here is logic and exists only for Creusot.
//!
//! The model operations `up`, `reset` and `free` are, entry by entry, what
//! the shipped in-place updates compute. For a canonical `f` this module
//! proves that each result is canonical (`up_canonical`, `reset_canonical`,
//! `free_canonical`) and denotes exactly the image
//! of `γ(f)` over nonnegative real valuations (`up_zone`, `reset_zone`,
//! `free_zone`). The hard directions rest on one-clock extensions built
//! with the witness step of `dbm::proof` (`extend`):
//!
//! - `project`: a valuation that satisfies every entry of a canonical `f`
//!   not involving `x_k` extends to `x_k` (Fourier–Motzkin elimination of a
//!   closed system: the projection is the submatrix). Free and reset use it.
//! - `unshift`: a valuation of `up(f)` is a delayed valuation of `f`.
//! - `rewind`: a valuation of `down(f, d)` (past) delayed by some `t ≥ 0`
//!   lies in `γ(f)`. The delay is the extension of the **negated**
//!   valuation by one clock, so that the reference row of the auxiliary
//!   matrix has the finite entry that `extend` needs.
//!
//! Past (`down`) replaces row 0 by `pmin`, the minimum of `Le 0` and the
//! entries below it in the same column; `pmin_spec` gives its argmin
//! `parg`, and `down_canonical`/`down_zone` are its two theorems.
//!
//! `reset_representable` gives the range facts of the reset kernel from
//! C2–C4 alone (not from an unproved sufficient-range premise).

use crate::bounds::{
    BoundModel, add_assoc, add_comm_unit, add_mono, add_sound, le_sound, le_total, le_trans,
    relax_entry, sat,
};
use crate::dbm::proof::{
    MMat, Val, bmin, bmin_spec, extend, mcanonical, mzone, pick, sat_prefix, step_pre, valuation,
};
use creusot_std::{logic::real::Real, prelude::*};

// ----- the model operations (what the kernels compute) -----

/// Future: column 0 becomes `∞` except the diagonal.
#[logic(open(crate))]
pub(crate) fn up(f: MMat) -> MMat {
    pearlite! { |i: Int| |j: Int| if j == 0 && i != 0 { BoundModel::Inf } else { f[i][j] } }
}

/// Reset of `x_k` to `c`.
#[logic(open(crate))]
pub(crate) fn reset(f: MMat, k: Int, c: Int) -> MMat {
    pearlite! {
        |i: Int| |j: Int|
            if i == k && j == k {
                BoundModel::Le(0)
            } else if i == k {
                BoundModel::Le(c).add(f[0][j])
            } else if j == k {
                BoundModel::Le(-c).add(f[i][0])
            } else {
                f[i][j]
            }
    }
}

/// Free of `x_k`.
#[logic(open(crate))]
pub(crate) fn free(f: MMat, k: Int) -> MMat {
    pearlite! {
        |i: Int| |j: Int|
            if i == k && j == k {
                BoundModel::Le(0)
            } else if i == k {
                BoundModel::Inf
            } else if j == k {
                f[i][0]
            } else {
                f[i][j]
            }
    }
}

// ----- the images of a zone -----

/// `v` is `u` delayed by `t`: `v(x₀) = 0` and every actual clock advanced
/// by the same `t`.
#[logic(open(crate))]
pub(crate) fn shifted(u: Val, t: Real, v: Val, d: Int) -> bool {
    pearlite! {
        v[0] == Real::from_int(0)
            && forall<i: Int> 1 <= i && i < d ==> v[i] == u[i] + t
    }
}

/// `v` agrees with `u` on every clock except `x_k`.
#[logic(open(crate))]
pub(crate) fn agree_except(u: Val, v: Val, d: Int, k: Int) -> bool {
    pearlite! { forall<i: Int> 0 <= i && i < d && i != k ==> v[i] == u[i] }
}

// ----- elementary facts -----

/// Satisfaction is downward closed in the difference.
#[logic]
#[requires(sat(b, x) && y <= x)]
#[ensures(sat(b, y))]
pub(crate) fn sat_down(b: BoundModel, x: Real, y: Real) {}

/// In a canonical matrix, `f[i][0] ≽ Le 0` (`f[i][0]` is `∞` or has a
/// nonnegative constant, strictly positive if strict).
#[logic]
#[requires(mcanonical(f, d))]
#[requires(0 <= i && i < d)]
#[ensures(BoundModel::Le(0).le(f[i][0]))]
pub(crate) fn col0_nonneg(f: MMat, d: Int, i: Int) {
    pearlite! {
        // Le 0 = f[i][i] ≼ f[i][0] + f[0][i] ≼ f[i][0] + Le 0 = f[i][0].
        add_mono(f[0][i], BoundModel::Le(0), f[i][0]);
        add_comm_unit(f[i][0], f[0][i]);
        add_comm_unit(f[i][0], BoundModel::Le(0));
        le_trans(BoundModel::Le(0), f[i][0].add(f[0][i]), f[i][0])
    }
}

// ----- canonicity (C2–C4) -----

/// `up(f)` is canonical.
#[logic]
#[requires(1 <= d && mcanonical(f, d))]
#[ensures(mcanonical(up(f), d))]
pub(crate) fn up_canonical(f: MMat, d: Int) {
    pearlite! {
        proof_assert!(forall<i: Int, j: Int, l: Int>
            0 <= i && i < d && 0 <= j && j < d && 0 <= l && l < d ==> {
                add_comm_unit(up(f)[i][l], up(f)[l][j]);
                // up(f) ≽ f entrywise, so f's triangle carries over.
                le_trans(f[i][l], up(f)[i][l], up(f)[i][l]);
                add_mono(f[i][l], up(f)[i][l], f[l][j]);
                add_mono(f[l][j], up(f)[l][j], up(f)[i][l]);
                add_comm_unit(f[l][j], up(f)[i][l]);
                le_trans(f[i][l].add(f[l][j]), up(f)[i][l].add(f[l][j]), up(f)[i][l].add(up(f)[l][j]));
                le_trans(f[i][j], f[i][l].add(f[l][j]), up(f)[i][l].add(up(f)[l][j]));
                up(f)[i][j].le(up(f)[i][l].add(up(f)[l][j]))
            });
    }
}

/// In a canonical matrix, `f[i][k] ≼ f[i][0]` (via `f[0][k] ≼ Le 0`).
#[logic]
#[requires(mcanonical(f, d))]
#[requires(0 <= i && i < d && 0 <= k && k < d)]
#[ensures(f[i][k].le(f[i][0]))]
pub(crate) fn col_below_col0(f: MMat, d: Int, i: Int, k: Int) {
    pearlite! {
        add_mono(f[0][k], BoundModel::Le(0), f[i][0]);
        add_comm_unit(f[i][0], f[0][k]);
        add_comm_unit(f[i][0], BoundModel::Le(0));
        le_trans(f[i][k], f[i][0].add(f[0][k]), f[i][0])
    }
}

/// One triangle of `free(f, k)`.
#[logic]
#[requires(mcanonical(f, d))]
#[requires(1 <= k && k < d)]
#[requires(0 <= i && i < d && 0 <= j && j < d && 0 <= l && l < d)]
#[ensures(free(f, k)[i][j].le(free(f, k)[i][l].add(free(f, k)[l][j])))]
pub(crate) fn free_tri(f: MMat, d: Int, k: Int, i: Int, j: Int, l: Int) {
    pearlite! {
        let g = free(f, k);
        add_comm_unit(g[i][l], g[l][j]);
        add_comm_unit(g[i][l], BoundModel::Le(0));
        add_comm_unit(BoundModel::Le(0), g[l][j]);
        if i != k && j != k && l != k {
            // g = f on these entries.
            proof_assert!(g[i][j] == f[i][j] && g[i][l] == f[i][l] && g[l][j] == f[l][j]);
        } else if i != k && j == k && l != k {
            // f[i][0] ≼ f[i][l] + f[l][0].
            proof_assert!(g[i][j] == f[i][0] && g[i][l] == f[i][l] && g[l][j] == f[l][0]);
        }
    }
}

/// `free(f, k)` is canonical.
#[logic]
#[requires(mcanonical(f, d))]
#[requires(1 <= k && k < d)]
#[ensures(mcanonical(free(f, k), d))]
pub(crate) fn free_canonical(f: MMat, d: Int, k: Int) {
    pearlite! {
        proof_assert!(forall<i: Int, j: Int, l: Int>
            0 <= i && i < d && 0 <= j && j < d && 0 <= l && l < d ==> {
                free_tri(f, d, k, i, j, l);
                free(f, k)[i][j].le(free(f, k)[i][l].add(free(f, k)[l][j]))
            });
    }
}

/// `Le c + Le(−c) = Le 0`.
#[logic]
#[ensures(BoundModel::Le(c).add(BoundModel::Le(-c)) == BoundModel::Le(0))]
#[ensures(BoundModel::Le(-c).add(BoundModel::Le(c)) == BoundModel::Le(0))]
pub(crate) fn cancel(c: Int) {}

/// `(n + a) + (p + b) = a + b` when `n + p = Le 0`.
#[logic]
#[requires(n.add(p) == BoundModel::Le(0))]
#[ensures(n.add(a).add(p.add(b)) == a.add(b))]
pub(crate) fn cancel_sum(n: BoundModel, a: BoundModel, p: BoundModel, b: BoundModel) {
    pearlite! {
        add_assoc(n, a, p.add(b));
        add_assoc(a, p, b);
        add_comm_unit(a, p);
        add_assoc(p, a, b);
        add_assoc(n, p, a.add(b));
        add_comm_unit(a.add(b), n.add(p));
    }
}

/// One triangle of `reset(f, k, c)`.
#[logic]
#[requires(mcanonical(f, d))]
#[requires(1 <= k && k < d && 0 <= c)]
#[requires(0 <= i && i < d && 0 <= j && j < d && 0 <= l && l < d)]
#[ensures(reset(f, k, c)[i][j].le(reset(f, k, c)[i][l].add(reset(f, k, c)[l][j])))]
pub(crate) fn reset_tri(f: MMat, d: Int, k: Int, c: Int, i: Int, j: Int, l: Int) {
    pearlite! {
        let g = reset(f, k, c);
        let p = BoundModel::Le(c);
        let n = BoundModel::Le(-c);
        cancel(c);
        if i != k && j != k && l == k {
            // (n + f[i][0]) + (p + f[0][j]) = f[i][0] + f[0][j] ≽ f[i][j].
            cancel_sum(n, f[i][0], p, f[0][j]);
        } else if i == k && j != k && l != k {
            // p + f[0][j] ≼ (p + f[0][l]) + f[l][j].
            add_assoc(p, f[0][l], f[l][j]);
            add_mono(f[0][j], f[0][l].add(f[l][j]), p);
        } else if i != k && j == k && l != k {
            // n + f[i][0] ≼ f[i][l] + (n + f[l][0]).
            add_assoc(f[i][l], n, f[l][0]);
            add_comm_unit(f[i][l], n);
            add_assoc(n, f[i][l], f[l][0]);
            add_mono(f[i][0], f[i][l].add(f[l][0]), n);
        } else if i == k && j == k && l != k {
            // Le 0 ≼ (p + f[0][l]) + (n + f[l][0]) = f[0][l] + f[l][0].
            cancel_sum(p, f[0][l], n, f[l][0]);
        } else {
            add_comm_unit(g[i][l], g[l][j]);
            add_comm_unit(g[i][l], BoundModel::Le(0));
            add_comm_unit(BoundModel::Le(0), g[l][j]);
        }
    }
}

/// `reset(f, k, c)` is canonical for `c ≥ 0` (
/// `reset_canonical_canonical`).
#[logic]
#[requires(mcanonical(f, d))]
#[requires(1 <= k && k < d && 0 <= c)]
#[ensures(mcanonical(reset(f, k, c), d))]
pub(crate) fn reset_canonical(f: MMat, d: Int, k: Int, c: Int) {
    pearlite! {
        cancel(c);
        proof_assert!(forall<i: Int, j: Int, l: Int>
            0 <= i && i < d && 0 <= j && j < d && 0 <= l && l < d ==> {
                reset_tri(f, d, k, c, i, j, l);
                reset(f, k, c)[i][j].le(reset(f, k, c)[i][l].add(reset(f, k, c)[l][j]))
            });
    }
}

// ----- one-clock extensions (the witness step of `dbm::proof`) -----

/// Auxiliary matrix over `d + 1` clocks for `project`: clock `d` is a fresh
/// copy of `x_k`, the old `x_k` is unconstrained.
#[logic(open(crate))]
pub(crate) fn proj_aux(f: MMat, d: Int, k: Int) -> MMat {
    pearlite! {
        |i: Int| |j: Int|
            if i == d && j == d {
                BoundModel::Le(0)
            } else if i == d {
                if j == k { BoundModel::Inf } else { f[k][j] }
            } else if j == d {
                if i == k { BoundModel::Inf } else { f[i][k] }
            } else if i == k && j == k {
                BoundModel::Le(0)
            } else if i == k || j == k {
                BoundModel::Inf
            } else {
                f[i][j]
            }
    }
}

/// The value given to `x_k` by `project`.
#[logic]
pub(crate) fn proj_value(f: MMat, d: Int, k: Int, v: Val) -> Real {
    pearlite! { pick(proj_aux(f, d, k), d + 1, v, d) }
}

/// Projection (Fourier–Motzkin over a closed system; new): if `v` is a
/// valuation on the clocks other than `x_k` that satisfies every entry of
/// a canonical `f` not involving `x_k`, then some `r ≥ 0` for `x_k`
/// completes it to a member of `γ(f)`.
#[logic]
#[requires(mcanonical(f, d))]
#[requires(1 <= k && k < d)]
#[requires(v[0] == Real::from_int(0))]
#[requires(forall<i: Int> 0 <= i && i < d && i != k ==> Real::from_int(0) <= v[i])]
#[requires(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d && i != k && j != k ==>
    sat(f[i][j], v[i] - v[j]))]
#[ensures(mzone(f, d, v.set(k, proj_value(f, d, k, v))))]
pub(crate) fn project(f: MMat, d: Int, k: Int, v: Val) {
    pearlite! {
        let h = proj_aux(f, d, k);
        let r = proj_value(f, d, k, v);
        proof_assert!(forall<j: Int, l: Int> 0 <= j && j < d && 0 <= l && l < d ==> {
            add_comm_unit(h[j][d], h[d][l]);
            add_comm_unit(BoundModel::Inf, h[d][l]);
            h[j][l].le(h[j][d].add(h[d][l]))
        });
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
            sat(h[i][j], v[i] - v[j]));
        proof_assert!(sat_prefix(h, v, d));
        proof_assert!(step_pre(h, d + 1, v, d));
        extend(h, d + 1, v, d);
        let w = v.set(d, r);
        let u = v.set(k, r);
        proof_assert!(sat_prefix(h, w, d + 1));
        proof_assert!(forall<i: Int> 0 <= i && i < d && i != k ==> sat(h[i][d], w[i] - w[d]));
        proof_assert!(forall<j: Int> 0 <= j && j < d && j != k ==> sat(h[d][j], w[d] - w[j]));
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
            sat(f[i][j], u[i] - u[j]));
        le_sound(f[0][k], BoundModel::Le(0), u[0] - u[k]);
        proof_assert!(Real::from_int(0) <= r);
    }
}

/// Auxiliary matrix over `d + 1` clocks for `unshift`: clock `d` is the
/// delay `t`.
#[logic(open(crate))]
pub(crate) fn up_aux(f: MMat, d: Int) -> MMat {
    pearlite! {
        |i: Int| |j: Int|
            if i == d && j == d {
                BoundModel::Le(0)
            } else if i == d {
                if j == 0 { BoundModel::Inf } else { f[0][j] }
            } else if j == d {
                f[i][0]
            } else {
                up(f)[i][j]
            }
    }
}

/// The delay found by `unshift`.
#[logic]
pub(crate) fn delay(f: MMat, d: Int, v: Val) -> Real {
    pearlite! { pick(up_aux(f, d), d + 1, v, d) }
}

/// `v` moved back by the delay: `u(x₀) = 0`, `u(xᵢ) = v(xᵢ) − t`.
#[logic]
pub(crate) fn unshifted(v: Val, t: Real) -> Val {
    pearlite! { |i: Int| if i == 0 { Real::from_int(0) } else { v[i] - t } }
}

/// Every valuation of `up(f)` is a valuation of a canonical `f` delayed by
/// some `t ≥ 0`.
#[logic]
#[requires(1 <= d && mcanonical(f, d))]
#[requires(mzone(up(f), d, v))]
#[ensures(Real::from_int(0) <= delay(f, d, v))]
#[ensures(mzone(f, d, unshifted(v, delay(f, d, v))))]
#[ensures(shifted(unshifted(v, delay(f, d, v)), delay(f, d, v), v, d))]
pub(crate) fn unshift(f: MMat, d: Int, v: Val) {
    pearlite! {
        let h = up_aux(f, d);
        let t = delay(f, d, v);
        proof_assert!(forall<j: Int, l: Int> 0 <= j && j < d && 0 <= l && l < d ==> {
            add_comm_unit(h[j][d], h[d][l]);
            h[j][l].le(h[j][d].add(h[d][l]))
        });
        proof_assert!(sat_prefix(h, v, d));
        proof_assert!(step_pre(h, d + 1, v, d));
        extend(h, d + 1, v, d);
        let w = v.set(d, t);
        let u = unshifted(v, t);
        proof_assert!(sat_prefix(h, w, d + 1));
        proof_assert!(sat(h[0][d], w[0] - w[d]));
        proof_assert!(forall<i: Int> 1 <= i && i < d ==> sat(f[i][0], u[i] - u[0]));
        proof_assert!(forall<j: Int> 1 <= j && j < d ==> sat(f[0][j], u[0] - u[j]));
        proof_assert!(forall<i: Int, j: Int> 1 <= i && i < d && 1 <= j && j < d ==>
            sat(f[i][j], u[i] - u[j]));
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
            sat(f[i][j], u[i] - u[j]));
        proof_assert!(forall<j: Int> 0 <= j && j < d ==> {
            le_sound(f[0][j], BoundModel::Le(0), u[0] - u[j]);
            Real::from_int(0) <= u[j]
        });
    }
}

// ----- the zone equations -----

/// Future: `γ(up f)` is the
/// set of valuations of `γ(f)` delayed by a common `t ≥ 0`.
#[logic]
#[requires(1 <= d && mcanonical(f, d))]
#[ensures(forall<v: Val> mzone(up(f), d, v) ==
    exists<u: Val, t: Real> Real::from_int(0) <= t && mzone(f, d, u) && shifted(u, t, v, d))]
pub(crate) fn up_zone(f: MMat, d: Int) {
    pearlite! {
        proof_assert!(forall<v: Val> mzone(up(f), d, v) ==> {
            unshift(f, d, v);
            mzone(f, d, unshifted(v, delay(f, d, v)))
        });
        proof_assert!(forall<v: Val, u: Val, t: Real>
            Real::from_int(0) <= t && mzone(f, d, u) && shifted(u, t, v, d) ==> {
                proof_assert!(forall<i: Int, j: Int> 1 <= i && i < d && 1 <= j && j < d ==>
                    v[i] - v[j] == u[i] - u[j]);
                proof_assert!(forall<j: Int> 1 <= j && j < d ==> {
                    sat_down(f[0][j], u[0] - u[j], v[0] - v[j]);
                    sat(up(f)[0][j], v[0] - v[j])
                });
                mzone(up(f), d, v)
            });
    }
}

/// A valuation of `free(f, k)` comes from `γ(f)` by changing `x_k` only.
#[logic]
#[requires(mcanonical(f, d))]
#[requires(1 <= k && k < d)]
#[requires(mzone(free(f, k), d, v))]
#[ensures(mzone(f, d, v.set(k, proj_value(f, d, k, v))))]
#[ensures(agree_except(v.set(k, proj_value(f, d, k, v)), v, d, k))]
pub(crate) fn free_complete(f: MMat, d: Int, k: Int, v: Val) {
    pearlite! {
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d && i != k && j != k ==>
            free(f, k)[i][j] == f[i][j]);
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d && i != k && j != k ==>
            sat(f[i][j], v[i] - v[j]));
        project(f, d, k, v)
    }
}

/// Free (new): `γ(free(f, k))` is `γ(f)` with `x_k` replaced by any value
/// `≥ 0`; the clock is kept.
#[logic]
#[requires(mcanonical(f, d))]
#[requires(1 <= k && k < d)]
#[ensures(forall<v: Val> mzone(free(f, k), d, v) ==
    exists<u: Val> mzone(f, d, u) && Real::from_int(0) <= v[k] && agree_except(u, v, d, k))]
pub(crate) fn free_zone(f: MMat, d: Int, k: Int) {
    pearlite! {
        proof_assert!(forall<v: Val> mzone(free(f, k), d, v) ==> {
            free_complete(f, d, k, v);
            exists<u: Val> mzone(f, d, u) && Real::from_int(0) <= v[k] && agree_except(u, v, d, k)
        });
        proof_assert!(forall<v: Val, u: Val>
            mzone(f, d, u) && Real::from_int(0) <= v[k] && agree_except(u, v, d, k) ==> {
                proof_assert!(forall<i: Int> 0 <= i && i < d && i != k ==> {
                    sat_down(f[i][0], u[i] - u[0], v[i] - v[k]);
                    sat(free(f, k)[i][k], v[i] - v[k])
                });
                mzone(free(f, k), d, v)
            });
    }
}

/// A valuation of `reset(f, k, c)` pins `x_k` to `c`.
#[logic]
#[requires(mcanonical(f, d))]
#[requires(1 <= k && k < d && 0 <= c)]
#[requires(mzone(reset(f, k, c), d, v))]
#[ensures(v[k] == Real::from_int(c))]
pub(crate) fn reset_pins(f: MMat, d: Int, k: Int, c: Int, v: Val) {
    pearlite! {
        let g = reset(f, k, c);
        add_comm_unit(BoundModel::Le(c), BoundModel::Le(0));
        add_comm_unit(BoundModel::Le(-c), BoundModel::Le(0));
        proof_assert!(g[k][0] == BoundModel::Le(c) && g[0][k] == BoundModel::Le(-c));
        proof_assert!(sat(BoundModel::Le(c), v[k] - v[0]));
        proof_assert!(sat(BoundModel::Le(-c), v[0] - v[k]));
        proof_assert!(v[k] <= Real::from_int(c));
        proof_assert!(Real::from_int(-c) == -Real::from_int(c));
        proof_assert!(-v[k] <= -Real::from_int(c));
    }
}

/// `x_k := c` maps `γ(f)` into `γ(reset(f, k, c))`.
#[logic]
#[requires(mcanonical(f, d))]
#[requires(1 <= k && k < d && 0 <= c)]
#[requires(mzone(f, d, u) && v[k] == Real::from_int(c) && agree_except(u, v, d, k))]
#[ensures(mzone(reset(f, k, c), d, v))]
pub(crate) fn reset_sound(f: MMat, d: Int, k: Int, c: Int, u: Val, v: Val) {
    pearlite! {
        let g = reset(f, k, c);
        proof_assert!(Real::from_int(-c) == -Real::from_int(c));
        proof_assert!(forall<j: Int> 0 <= j && j < d && j != k ==> {
            add_sound(BoundModel::Le(c), f[0][j], Real::from_int(c), u[0] - u[j]);
            proof_assert!(Real::from_int(c) + (u[0] - u[j]) == v[k] - v[j]);
            sat(g[k][j], v[k] - v[j])
        });
        proof_assert!(forall<i: Int> 0 <= i && i < d && i != k ==> {
            add_sound(BoundModel::Le(-c), f[i][0], Real::from_int(-c), u[i] - u[0]);
            proof_assert!(Real::from_int(-c) + (u[i] - u[0]) == v[i] - v[k]);
            sat(g[i][k], v[i] - v[k])
        });
        proof_assert!(sat(g[k][k], v[k] - v[k]));
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
            sat(g[i][j], v[i] - v[j]));
    }
}

/// A valuation of `reset(f, k, c)` comes from `γ(f)` by setting `x_k := c`.
#[logic]
#[requires(mcanonical(f, d))]
#[requires(1 <= k && k < d && 0 <= c)]
#[requires(mzone(reset(f, k, c), d, v))]
#[ensures(mzone(f, d, v.set(k, proj_value(f, d, k, v))))]
#[ensures(v[k] == Real::from_int(c))]
#[ensures(agree_except(v.set(k, proj_value(f, d, k, v)), v, d, k))]
pub(crate) fn reset_complete(f: MMat, d: Int, k: Int, c: Int, v: Val) {
    pearlite! {
        reset_pins(f, d, k, c, v);
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d && i != k && j != k ==>
            reset(f, k, c)[i][j] == f[i][j]);
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d && i != k && j != k ==>
            sat(f[i][j], v[i] - v[j]));
        proof_assert!(v[0] == Real::from_int(0));
        proof_assert!(forall<i: Int> 0 <= i && i < d && i != k ==> Real::from_int(0) <= v[i]);
        project(f, d, k, v)
    }
}

/// Reset: `γ(reset(f,
/// k, c))` is `γ(f)` with `x_k` set to `c ≥ 0`.
#[logic]
#[requires(mcanonical(f, d))]
#[requires(1 <= k && k < d && 0 <= c)]
#[ensures(forall<v: Val> mzone(reset(f, k, c), d, v) ==
    exists<u: Val> mzone(f, d, u) && v[k] == Real::from_int(c) && agree_except(u, v, d, k))]
pub(crate) fn reset_zone(f: MMat, d: Int, k: Int, c: Int) {
    pearlite! {
        proof_assert!(forall<v: Val> mzone(reset(f, k, c), d, v) ==> {
            reset_complete(f, d, k, c, v);
            exists<u: Val> mzone(f, d, u) && v[k] == Real::from_int(c) && agree_except(u, v, d, k)
        });
        proof_assert!(forall<v: Val, u: Val>
            mzone(f, d, u) && v[k] == Real::from_int(c) && agree_except(u, v, d, k) ==> {
                reset_sound(f, d, k, c, u, v);
                mzone(reset(f, k, c), d, v)
            });
    }
}

// ----- reset arithmetic -----

/// The range facts of the reset kernel (C2–C4 only): for `0 ≤ c ≤
/// MAX_CONSTANT`, the row pass's sums `Le c + f[0][j]`, the column pass's
/// sums `Le(−c) + f[i][0]` (`i ≠ k`) and `Le(−c) + Le c` are representable.
#[logic]
#[requires(mcanonical(f, d))]
#[requires(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> f[i][j].representable())]
#[requires(0 <= c && BoundModel::in_range(c))]
#[ensures(forall<j: Int> 0 <= j && j < d ==> BoundModel::Le(c).add_in_range(f[0][j]))]
#[ensures(forall<i: Int> 0 <= i && i < d ==> BoundModel::Le(-c).add_in_range(f[i][0]))]
#[ensures(BoundModel::Le(-c).add_in_range(BoundModel::Le(c)))]
pub(crate) fn reset_representable(f: MMat, d: Int, c: Int) {
    pearlite! {
        proof_assert!(forall<i: Int> 0 <= i && i < d ==> { col0_nonneg(f, d, i); true });
    }
}

// ----- past (time predecessors) -----

/// `min(Le 0, f[1][j], …, f[n−1][j])`: row 0 of `past` after the rows
/// `1..n` have been folded in (`n ≥ 1`).
#[logic(open(crate))]
#[variant(n)]
pub(crate) fn pmin(f: MMat, n: Int, j: Int) -> BoundModel {
    pearlite! {
        if n <= 1 { BoundModel::Le(0) } else { bmin(pmin(f, n - 1, j), f[n - 1][j]) }
    }
}

/// The row attaining `pmin(f, n, j)`; `0` stands for `Le 0`.
#[logic(open(crate))]
#[variant(n)]
pub(crate) fn parg(f: MMat, n: Int, j: Int) -> Int {
    pearlite! {
        if n <= 1 {
            0
        } else if pmin(f, n - 1, j).le(f[n - 1][j]) {
            parg(f, n - 1, j)
        } else {
            n - 1
        }
    }
}

/// `pmin` is below `Le 0` and every folded entry, and it is attained.
#[logic]
#[variant(n)]
#[requires(1 <= n)]
#[ensures(pmin(f, n, j).le(BoundModel::Le(0)))]
#[ensures(forall<k: Int> 1 <= k && k < n ==> pmin(f, n, j).le(f[k][j]))]
#[ensures(0 <= parg(f, n, j) && parg(f, n, j) < n)]
#[ensures(parg(f, n, j) == 0 ==> pmin(f, n, j) == BoundModel::Le(0))]
#[ensures(parg(f, n, j) != 0 ==> pmin(f, n, j) == f[parg(f, n, j)][j])]
pub(crate) fn pmin_spec(f: MMat, n: Int, j: Int) {
    pearlite! {
        if n > 1 {
            pmin_spec(f, n - 1, j);
            let p = pmin(f, n - 1, j);
            bmin_spec(p, f[n - 1][j]);
            le_trans(pmin(f, n, j), p, BoundModel::Le(0));
            proof_assert!(forall<k: Int> 1 <= k && k < n - 1 ==> {
                le_trans(pmin(f, n, j), p, f[k][j]);
                pmin(f, n, j).le(f[k][j])
            });
        } else {
            le_trans(BoundModel::Le(0), BoundModel::Le(0), BoundModel::Le(0));
        }
    }
}

/// One step of the kernel's loop: `relax_row` through `Le 0` with a
/// representable source entry `s` computes `min(cur, s)`.
#[logic]
#[requires(s.representable())]
#[requires(relax_entry(cur, BoundModel::Le(0), s, new))]
#[ensures(new == bmin(cur, s))]
#[ensures(BoundModel::Le(0).add_in_range(s))]
pub(crate) fn relax_le_zero(cur: BoundModel, s: BoundModel, new: BoundModel) {
    pearlite! {
        add_comm_unit(s, BoundModel::Le(0));
        bmin_spec(cur, s);
    }
}

/// Past: row 0 becomes `pmin`, every other entry is unchanged.
#[logic(open(crate))]
pub(crate) fn down(f: MMat, d: Int) -> MMat {
    pearlite! { |i: Int| |j: Int| if i == 0 { pmin(f, d, j) } else { f[i][j] } }
}

/// For a canonical `f`, `pmin(f, d, 0) = Le 0` (column 0 is `≽ Le 0`).
#[logic]
#[requires(1 <= d && mcanonical(f, d))]
#[ensures(pmin(f, d, 0) == BoundModel::Le(0))]
pub(crate) fn pmin_ref_zero(f: MMat, d: Int) {
    pearlite! {
        pmin_spec(f, d, 0);
        let k = parg(f, d, 0);
        if k != 0 {
            col0_nonneg(f, d, k);
            le_total(f[k][0], BoundModel::Le(0));
        }
    }
}

/// One triangle of `down(f, d)`.
#[logic]
#[requires(1 <= d && mcanonical(f, d))]
#[requires(0 <= i && i < d && 0 <= j && j < d && 0 <= l && l < d)]
#[ensures(down(f, d)[i][j].le(down(f, d)[i][l].add(down(f, d)[l][j])))]
pub(crate) fn down_tri(f: MMat, d: Int, i: Int, j: Int, l: Int) {
    pearlite! {
        let g = down(f, d);
        let z = BoundModel::Le(0);
        pmin_spec(f, d, j);
        pmin_spec(f, d, l);
        pmin_ref_zero(f, d);
        if i != 0 && l != 0 {
            proof_assert!(g[i][j] == f[i][j] && g[i][l] == f[i][l] && g[l][j] == f[l][j]);
        } else if i != 0 {
            // l = 0: f[i][j] ≼ f[i][0] + pmin(j).
            let k = parg(f, d, j);
            if k == 0 {
                add_mono(f[0][j], z, f[i][0]);
                add_comm_unit(f[i][0], z);
                le_trans(f[i][j], f[i][0].add(f[0][j]), f[i][0].add(z));
            } else {
                col_below_col0(f, d, i, k);
                add_mono(f[i][k], f[i][0], f[k][j]);
                le_trans(f[i][j], f[i][k].add(f[k][j]), f[i][0].add(f[k][j]));
            }
        } else if l == 0 {
            // i = 0: pmin(j) ≼ Le 0 + pmin(j).
            add_comm_unit(g[0][j], z);
            le_trans(g[0][j], g[0][j], g[0][j]);
        } else {
            // i = 0, l ≥ 1: pmin(j) ≼ pmin(l) + f[l][j].
            let k = parg(f, d, l);
            if k == 0 {
                add_comm_unit(f[l][j], z);
            } else {
                le_trans(g[0][j], f[k][j], f[k][l].add(f[l][j]));
            }
        }
    }
}

/// `down(f, d)` is canonical (Isabelle's `down` served as a guide only).
#[logic]
#[requires(1 <= d && mcanonical(f, d))]
#[ensures(mcanonical(down(f, d), d))]
pub(crate) fn down_canonical(f: MMat, d: Int) {
    pearlite! {
        pmin_ref_zero(f, d);
        proof_assert!(forall<j: Int> 0 <= j && j < d ==> {
            pmin_spec(f, d, j);
            down(f, d)[0][j].le(BoundModel::Le(0))
        });
        proof_assert!(forall<i: Int, j: Int, l: Int>
            0 <= i && i < d && 0 <= j && j < d && 0 <= l && l < d ==> {
                down_tri(f, d, i, j, l);
                down(f, d)[i][j].le(down(f, d)[i][l].add(down(f, d)[l][j]))
            });
    }
}

/// A valuation `v` whose delay `u = v + t` lies in `γ(f)` lies in
/// `γ(down(f, d))`.
#[logic]
#[requires(1 <= d && mcanonical(f, d))]
#[requires(valuation(d, v) && Real::from_int(0) <= t && mzone(f, d, u) && shifted(v, t, u, d))]
#[ensures(mzone(down(f, d), d, v))]
pub(crate) fn down_sound(f: MMat, d: Int, v: Val, t: Real, u: Val) {
    pearlite! {
        let g = down(f, d);
        pmin_ref_zero(f, d);
        proof_assert!(forall<i: Int, j: Int> 1 <= i && i < d && 1 <= j && j < d ==>
            v[i] - v[j] == u[i] - u[j] && sat(g[i][j], v[i] - v[j]));
        proof_assert!(forall<i: Int> 1 <= i && i < d ==> {
            sat_down(f[i][0], u[i] - u[0], v[i] - v[0]);
            sat(g[i][0], v[i] - v[0])
        });
        proof_assert!(sat(g[0][0], v[0] - v[0]));
        proof_assert!(forall<j: Int> 1 <= j && j < d ==> {
            pmin_spec(f, d, j);
            let k = parg(f, d, j);
            if k != 0 {
                proof_assert!(v[k] - v[j] == u[k] - u[j]);
                sat_down(f[k][j], u[k] - u[j], v[0] - v[j]);
            }
            sat(g[0][j], v[0] - v[j])
        });
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
            sat(g[i][j], v[i] - v[j]));
    }
}

/// Auxiliary matrix over `d + 1` clocks for `rewind`. It constrains the
/// negated valuation `w = −v` (`w(x₀) = 0`); clock `d` is the delay `t`:
/// `xᵢ + t` (`i ≥ 1`) is `w_d − w_i`, and `−t − xⱼ` is `w_j − w_d`.
#[logic(open(crate))]
pub(crate) fn down_aux(f: MMat, d: Int) -> MMat {
    pearlite! {
        |i: Int| |j: Int|
            if i == d && j == d {
                BoundModel::Le(0)
            } else if i == d {
                if j == 0 { BoundModel::Inf } else { f[j][0] }
            } else if j == d {
                if i == 0 { BoundModel::Le(0) } else { f[0][i] }
            } else {
                down(f, d)[j][i]
            }
    }
}

/// `v` negated on the actual clocks.
#[logic(open(crate))]
pub(crate) fn negated(v: Val) -> Val {
    pearlite! { |i: Int| if i == 0 { Real::from_int(0) } else { -v[i] } }
}

/// `v` delayed by `t`.
#[logic(open(crate))]
pub(crate) fn delayed(v: Val, t: Real) -> Val {
    pearlite! { |i: Int| if i == 0 { Real::from_int(0) } else { v[i] + t } }
}

/// The delay found by `rewind`.
#[logic]
pub(crate) fn rewind_delay(f: MMat, d: Int, v: Val) -> Real {
    pearlite! { pick(down_aux(f, d), d + 1, negated(v), d) }
}

/// Every valuation of `down(f, d)`, delayed by some `t ≥ 0`, lies in the
/// canonical `γ(f)`.
#[logic]
#[requires(1 <= d && mcanonical(f, d))]
#[requires(mzone(down(f, d), d, v))]
#[ensures(Real::from_int(0) <= rewind_delay(f, d, v))]
#[ensures(mzone(f, d, delayed(v, rewind_delay(f, d, v))))]
#[ensures(shifted(v, rewind_delay(f, d, v), delayed(v, rewind_delay(f, d, v)), d))]
pub(crate) fn rewind(f: MMat, d: Int, v: Val) {
    pearlite! {
        let g = down(f, d);
        let h = down_aux(f, d);
        let w = negated(v);
        let t = rewind_delay(f, d, v);
        pmin_ref_zero(f, d);
        proof_assert!(forall<i: Int> 0 <= i && i < d ==> w[i] == -v[i]);
        proof_assert!(forall<j: Int, l: Int> 0 <= j && j < d && 0 <= l && l < d ==> {
            add_comm_unit(h[j][d], h[d][l]);
            add_comm_unit(h[d][l], BoundModel::Le(0));
            h[j][l].le(h[j][d].add(h[d][l]))
        });
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> {
            proof_assert!(w[i] - w[j] == v[j] - v[i]);
            sat(h[i][j], w[i] - w[j])
        });
        proof_assert!(sat_prefix(h, w, d));
        proof_assert!(step_pre(h, d + 1, w, d));
        extend(h, d + 1, w, d);
        let x = w.set(d, t);
        let u = delayed(v, t);
        proof_assert!(sat_prefix(h, x, d + 1));
        proof_assert!(sat(h[0][d], x[0] - x[d]));
        proof_assert!(Real::from_int(0) <= t);
        proof_assert!(forall<i: Int> 1 <= i && i < d ==> {
            proof_assert!(sat(h[d][i], x[d] - x[i]));
            proof_assert!(x[d] - x[i] == u[i] - u[0]);
            sat(f[i][0], u[i] - u[0])
        });
        proof_assert!(forall<j: Int> 1 <= j && j < d ==> {
            proof_assert!(sat(h[j][d], x[j] - x[d]));
            proof_assert!(x[j] - x[d] == u[0] - u[j]);
            sat(f[0][j], u[0] - u[j])
        });
        proof_assert!(forall<i: Int, j: Int> 1 <= i && i < d && 1 <= j && j < d ==> {
            proof_assert!(u[i] - u[j] == v[i] - v[j]);
            sat(f[i][j], u[i] - u[j])
        });
        proof_assert!(sat(f[0][0], u[0] - u[0]));
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
            sat(f[i][j], u[i] - u[j]));
        proof_assert!(forall<j: Int> 0 <= j && j < d ==> {
            le_sound(f[0][j], BoundModel::Le(0), u[0] - u[j]);
            Real::from_int(0) <= u[j]
        });
        proof_assert!(g[0][0] == BoundModel::Le(0));
    }
}

/// Past: `γ(down(f, d))` is the set of nonnegative valuations that some
/// common delay `t ≥ 0` moves into `γ(f)`.
#[logic]
#[requires(1 <= d && mcanonical(f, d))]
#[ensures(forall<v: Val> mzone(down(f, d), d, v) ==
    (valuation(d, v)
        && exists<u: Val, t: Real> Real::from_int(0) <= t && mzone(f, d, u) && shifted(v, t, u, d)))]
pub(crate) fn down_zone(f: MMat, d: Int) {
    pearlite! {
        proof_assert!(forall<v: Val> mzone(down(f, d), d, v) ==> {
            rewind(f, d, v);
            exists<u: Val, t: Real> Real::from_int(0) <= t && mzone(f, d, u) && shifted(v, t, u, d)
        });
        proof_assert!(forall<v: Val, u: Val, t: Real>
            valuation(d, v) && Real::from_int(0) <= t && mzone(f, d, u) && shifted(v, t, u, d) ==> {
                down_sound(f, d, v, t, u);
                mzone(down(f, d), d, v)
            });
    }
}
