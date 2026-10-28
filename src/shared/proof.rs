//! Client-side statements about [`SharedDbm`], proved by
//! Creusot and compiled only under `cfg(creusot)`.
//!
//! creusot-std models an `Rc<T>` as a value of type `T`, so in the proof two
//! handles are two values and an operation on one cannot change the other.
//! What makes that model sound for the executable code is that `update`
//! writes through `Rc::get_mut` only (trusted: `rc_spec.rs`) and that every
//! operation consumes its handle (Rust's ownership). The functions below
//! spell out the resulting guarantees as checked statements.

use super::{SharedDbm, lift, same_outcome};
use crate::bounds::{Constraint, Variable};
use crate::dbm::Workspace;
use crate::ops::extra_m::MaxBounds;
use creusot_std::prelude::*;

/// Snapshot isolation: a clone keeps its zone through every update of the
/// handle it was cloned from, successful or not.
#[allow(clippy::too_many_arguments)]
#[ensures(result@ == z@)]
pub(crate) fn snapshot_isolation(
    z: SharedDbm,
    c: Constraint,
    cs: &[Constraint],
    other: &SharedDbm,
    x: Variable,
    value: i32,
    bounds: &MaxBounds,
    ws: &mut Workspace,
) -> SharedDbm {
    let snapshot = z.clone();
    let z = match z.try_constrain(c) {
        Ok(z) => z,
        Err(_) => snapshot.clone(),
    };
    let z = match z.try_constrain_all(cs, ws) {
        Ok(z) => z,
        Err(_) => snapshot.clone(),
    };
    let z = match z.try_intersect(other, ws) {
        Ok(z) => z,
        Err(_) => snapshot.clone(),
    };
    let z = z.future();
    let z = z.past();
    let z = match z.try_reset_zero(x) {
        Ok(z) => z,
        Err(_) => snapshot.clone(),
    };
    let z = match z.try_reset(x, value) {
        Ok(z) => z,
        Err(_) => snapshot.clone(),
    };
    let z = match z.try_free(x) {
        Ok(z) => z,
        Err(_) => snapshot.clone(),
    };
    let _ = z.try_extrapolate_max(bounds, ws);
    snapshot
}

/// Copy-on-write agreement: the contract of an update does not depend on
/// whether the handle is shared, and for the temporal operations it fixes
/// the outcome. So updating a shared handle (`a`: `z` is still alive) and
/// updating a unique one (the last `b`: the copies of `a` are detached) give
/// the same zone or the same error. (The `update` proof covers both
/// branches of `Rc::get_mut`; this is the consequence for callers.)
pub(crate) fn copy_on_write_agrees(z: SharedDbm, x: Variable, value: i32) {
    proof_assert!({
        super::unique_zones();
        true
    });
    let a = z.clone().future();
    let b = z.clone().future();
    proof_assert!(a.deep_model() == b.deep_model());
    let a = z.clone().past();
    let b = z.clone().past();
    proof_assert!(a.deep_model() == b.deep_model());
    let a = z.clone().try_reset_zero(x);
    let b = z.clone().try_reset_zero(x);
    proof_assert!(same_outcome(lift(a), lift(b)));
    let a = z.clone().try_reset(x, value);
    let b = z.clone().try_reset(x, value);
    proof_assert!(same_outcome(lift(a), lift(b)));
    let a = z.clone().try_free(x);
    let b = z.try_free(x);
    proof_assert!(same_outcome(lift(a), lift(b)));
}
