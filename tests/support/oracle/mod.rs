//! An independent, exact reference oracle for DBM zones.
//!
//! This is test support, not the production implementation. It is written for
//! clarity, not speed, and never uses the production crate:
//!
//! - Bounds are unpacked: `Lt c` / `Le c` with an arbitrary-precision
//!   [`num_bigint::BigInt`] constant and an explicit [`Strictness`], or `∞`
//!   ([`ExactBound`]). There is no range limit and no overflow.
//! - Clocks are nonnegative **reals**; index 0 is the reference clock `x₀`.
//!   Test points are exact rationals ([`Valuation`]).
//! - Every zone ([`OracleDbm`]) is canonical or the dimension-aware empty zone
//!   `∅_d`. Every operation builds the raw matrix given by the spec formula
//!   and then runs exact full closure: impose
//!   `x₀ − xᵢ ≤ 0`, tighten the diagonal to `Le 0`, run full Floyd–Warshall,
//!   and report `∅_d` if any diagonal entry is below `Le 0`.
//! - [`valuation`] contains closure-free checks (direct membership and an
//!   exact `∃t` solver for the set equations of future, reset and free) that
//!   the randomized tests use to cross-check the closure-based operations.
//!
//! # Operations
//!
//! | Independent oracle | Public API |
//! |---|---|
//! | `zero`, `universe`, `empty` | `Dbm::zero`, `Dbm::universe`, `Dbm::empty` |
//! | `from_constraints` | `Dbm::try_from_constraints` |
//! | `constrain`, `constrain_all` | `Dbm::try_constrain`, `Dbm::try_constrain_all` |
//! | `intersect` | `Dbm::try_intersect` |
//! | `future` | `Dbm::future` |
//! | `reset`, `reset_zero` | `Dbm::try_reset`, `Dbm::try_reset_zero` |
//! | `free` | `Dbm::try_free` |
//! | `is_subset_of`, `==` | `Dbm::is_subset_of`, `PartialEq` |
//! | `entails`, `intersects_constraint`, `difference_bound` | same names |
//! | `extrapolate_max` | `Dbm::try_extrapolate_max` |
//! | `from_matrix`, `parse`, `contains`, `witness`, `subset_counterexample` | test aids only |
//!
//! //! Argument errors are checked before emptiness. Not
//! modelled: `Error::Range` (the oracle is exact; use
//! [`compare::classify_range`]), `TooManyVariables`, the `MAX_CONSTANT` upper
//! limit of `MaxBounds`, `Workspace` (no semantic effect) and `SharedDbm`.
//!
//! # Writing a differential test
//!
//! ```text
//! mod support;
//! use support::oracle::{compare::*, fixtures, scenario::*};
//!
//! for f in fixtures::all() {
//!     let trace = f.scenario.run_oracle().unwrap();
//!     // replay f.scenario on clock_dbm::Dbm, translate every step into an
//!     // ObservedZone via ExactBound::from_parts, then:
//!     // check_outcome(&observed, &Ok(trace[k].clone()), range, PRODUCTION_MAX_CONSTANT)
//! }
//! ```
//!
//! For random cases use [`random::check_scenarios`]; failures report a seed
//! (`ORACLE_SEED=<seed>` replays it) and a shrunk scenario printed as Rust.

// Index loops are the clearest way to write matrix algorithms.
#![allow(clippy::needless_range_loop)]

pub mod bound;
pub mod compare;
pub mod fixtures;
pub mod random;
pub mod scenario;
pub mod valuation;
pub mod zone;

pub use bound::{ExactBound, Matrix, Strictness, parse_matrix};
pub use valuation::Valuation;
pub use zone::{OracleConstraint, OracleDbm, OracleError};
