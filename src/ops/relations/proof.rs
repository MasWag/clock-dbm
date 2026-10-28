//! Ghost-only lemmas for the relations of `relations.rs`.
//! Everything here is logic and exists only for Creusot.
//!
//! The read-only queries rely on the tightness of canonical bounds:
//! every entry of a canonical matrix is the tightest bound on its
//! corresponding clock difference over the zone (`dbm::proof::tight`):
//!
//! - `entry_tight`: `f[i][j] ≼ c` iff `c` holds on the whole zone, for
//!   every pair `i, j` including the diagonal. It gives `entails` and the
//!   tightness of `difference_bound`;
//! - `subset_pointwise`: for a canonical `f`, `γ(f) ⊆ γ(g)` iff `f ≤ g`
//!   entrywise;
//! - `meets`: the zone meets `xᵢ − xⱼ ⋈ b` iff `Le 0 ≼ b + f[j][i]`
//!   (`edge_ok`), by the single-edge closure lemmas
//!   `edge_canonical`, `edge_zone`, and `contradiction`.

use crate::bounds::{BoundModel, below_le_zero_unsat, le_sound, sat};
use crate::dbm::proof::{
    MMat, Val, edge, edge_canonical, edge_ok, edge_zone, mcanonical, mcanonical_nonempty, mzone,
    tight,
};
use crate::ops::constraints::proof::contradiction;
use creusot_std::{logic::real::Real, prelude::*};

/// Entry `(i, j)` of a canonical matrix is the tightest bound on
/// `xᵢ − xⱼ` over its zone: a bound `c` holds on the whole zone iff
/// `f[i][j] ≼ c`. Off the diagonal this is `tight`; on it, `f[i][i] = Le 0`
/// and the zone is nonempty.
#[logic]
#[requires(1 <= d && mcanonical(f, d))]
#[requires(0 <= i && i < d && 0 <= j && j < d)]
#[ensures(f[i][j].le(c) == forall<u: Val> mzone(f, d, u) ==> sat(c, u[i] - u[j]))]
pub(crate) fn entry_tight(f: MMat, d: Int, i: Int, j: Int, c: BoundModel) {
    pearlite! {
        proof_assert!(f[i][j].le(c) ==> forall<u: Val> mzone(f, d, u) ==> {
            le_sound(f[i][j], c, u[i] - u[j]);
            sat(c, u[i] - u[j])
        });
        if !f[i][j].le(c) {
            if i != j {
                tight(f, d, i, j, c)
            } else {
                proof_assert!(f[i][i] == BoundModel::Le(0));
                below_le_zero_unsat(c);
                mcanonical_nonempty(f, d);
                proof_assert!(forall<u: Val> u[i] - u[j] == Real::from_int(0));
            }
        }
    }
}

/// Inclusion of zones is the entrywise order on a canonical `f`:
/// `γ(f) ⊆ γ(g)` iff `f[i][j] ≼ g[i][j]` for all
/// `i, j`. Only `f` needs to be canonical.
#[logic]
#[requires(1 <= d && mcanonical(f, d))]
#[ensures((forall<u: Val> mzone(f, d, u) ==> mzone(g, d, u)) ==
    forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> f[i][j].le(g[i][j]))]
pub(crate) fn subset_pointwise(f: MMat, g: MMat, d: Int) {
    pearlite! {
        proof_assert!(forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> {
            entry_tight(f, d, i, j, g[i][j]);
            true
        });
        proof_assert!((forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==>
            f[i][j].le(g[i][j])) ==> forall<u: Val> mzone(f, d, u) ==>
                forall<i: Int, j: Int> 0 <= i && i < d && 0 <= j && j < d ==> {
                    le_sound(f[i][j], g[i][j], u[i] - u[j]);
                    sat(g[i][j], u[i] - u[j])
                });
    }
}

/// The zone of a canonical `f` meets `xᵢ − xⱼ ⋈ b` iff the new edge closes
/// no negative cycle, `Le 0 ≼ b + f[j][i]` (strict-zero cycles included).
/// If it does not, the single-edge closure `edge` is canonical and denotes
/// the intersection, hence is nonempty; otherwise `contradiction`.
#[logic]
#[requires(1 <= d && mcanonical(f, d))]
#[requires(0 <= i && i < d && 0 <= j && j < d)]
#[ensures((exists<u: Val> mzone(f, d, u) && sat(b, u[i] - u[j])) == edge_ok(f, i, j, b))]
pub(crate) fn meets(f: MMat, d: Int, i: Int, j: Int, b: BoundModel) {
    pearlite! {
        if edge_ok(f, i, j, b) {
            edge_canonical(f, d, i, j, b);
            edge_zone(f, d, i, j, b);
            mcanonical_nonempty(edge(f, i, j, b), d);
        } else {
            contradiction(f, d, i, j, b);
        }
    }
}
