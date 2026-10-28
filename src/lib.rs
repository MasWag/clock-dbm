//! # clock-dbm
//!
//! Difference-bound matrices (DBMs) for representing zones of timed automata.
//! Clocks range over the **nonnegative real numbers**; constraints have integer
//! bounds, including strict inequalities.
//!
//! A [`Dbm`] stores a zone in canonical form (or represents the empty zone).
//! Its operations include guard insertion, time elapse ([`Dbm::future`]) and
//! its backward counterpart ([`Dbm::past`]), resets, intersection,
//! inclusion, and maximal-constant extrapolation. [`SharedDbm`] provides cheap
//! immutable snapshots and copy-on-write updates for single-threaded exploration.
//!
//! ## Quick start
//!
//! This example describes two clocks, `x` and `y`, and then branches from the
//! original zone without changing the saved snapshot.
//!
//! ```rust
//! use clock_dbm::{constraint, Clock, Dbm, SharedDbm, Variable, Workspace};
//!
//! # fn main() -> Result<(), clock_dbm::Error> {
//! let x = Clock::new(1).unwrap();
//! let y = Clock::new(2).unwrap();
//! let mut ws = Workspace::new();
//!
//! // 2 <= x <= 10 and y - x < 3.
//! let zone = Dbm::try_from_constraints(2, &[
//!     constraint!(x >= 2)?,
//!     constraint!(x <= 10)?,
//!     constraint!(y - x < 3)?,
//! ], &mut ws)?;
//! assert!(!zone.is_empty());
//! assert!(zone.entails(&constraint!(x <= 10)?)?);
//!
//! // All clocks elapse together; then y is reset to zero.
//! let reset = zone.clone().future().try_reset_zero(Variable::new(2).unwrap())?;
//! assert!(reset.entails(&constraint!(y <= 0)?)?);
//!
//! // Time predecessors: every valuation that can reach the zone by waiting.
//! let before = zone.clone().past();
//! assert!(zone.is_subset_of(&before)?);
//! assert!(before.entails(&constraint!(x <= 10)?)?);
//!
//! // A shared branch leaves the original zone unchanged.
//! let snapshot = SharedDbm::from(zone);
//! let branch = snapshot.clone().try_constrain(constraint!(x < 5)?)?;
//! assert!(!branch.is_empty());
//! assert!(branch.is_subset_of(&snapshot)?);
//! # Ok(())
//! # }
//! ```
//!
//! ## Mathematical model
//!
//! A zone is a set of valuations of `n` clocks `x₁, …, xₙ` over the
//! **nonnegative real numbers**. A DBM adds a reference clock `x₀ = 0`,
//! represented by [`Clock::ZERO`], so its matrix dimension is `d = n + 1`.
//! The case `n = 0` is supported.
//!
//! Each matrix entry `D[i][j]` bounds the difference `xᵢ - xⱼ` by one
//! of `< c`, `<= c`, or infinity (no restriction). The integers `c` are
//! represented as [`Bound`] values. A valuation belongs to the zone
//! precisely when it satisfies **every** entry:
//!
//! ```text
//! Z(D) = { v ∈ (ℝ≥0)ⁿ | for all i,j ∈ {0,…,n},
//!                      v(xᵢ) - v(xⱼ) satisfies D[i][j] },
//! with v(x₀) = 0.
//! ```
//!
//! [`Constraint::le`] and [`Constraint::lt`] construct difference guards.
//! For example, `x >= 2` is `Constraint::le(Clock::ZERO, x, -2)`, while
//! `x - y < 3` is `Constraint::lt(x, y, 3)`. The [`constraint!`] macro
//! provides the shorter notations `constraint!(x >= 2)` and
//! `constraint!(x - y < 3)` for clock identifiers; single-clock forms with
//! `<`, `<=`, `>` and `>=` use the reference clock implicitly.
//! Use [`Clock`] for constraints and [`Variable`] for reset/free operations,
//! which cannot target the reference clock.
//!
//! ## Canonical zones
//!
//! Every nonempty public [`Dbm`] satisfies the canonicality conditions:
//!
//! - **C1 — Representability:** every stored bound is finite and within
//!   [`MIN_CONSTANT`]–[`MAX_CONSTANT`], or infinity.
//! - **C2 — Diagonal:** `D[i][i] = Le(0)` for every clock.
//! - **C3 — Nonnegativity:** `D[0][i]` is at least as tight as `Le(0)`,
//!   ensuring that all actual clocks are nonnegative.
//! - **C4 — Closure:** `D[i][j]` is at least as tight as
//!   `D[i][k] + D[k][j]` for all `i, j, k`.
//! - **C5 — Nonemptiness:** the represented zone is nonempty.
//!
//! Conditions C2–C4 imply C5. Thus each entry is the tightest implied
//! difference bound. Two canonical DBMs with the same clock count denote
//! the same zone exactly when their entries coincide; [`Dbm`] equality
//! and hashing follow this semantic equality.
//!
//! The empty zone is represented separately and **remembers its clock count**:
//! `Dbm::empty(1)? != Dbm::empty(2)?`. Every successful update returns
//! a canonical or empty zone; no partially updated matrix becomes public.
//!
//! ## Results and errors
//!
//! Operations taking ownership of a zone return a new canonical [`Dbm`] or
//! [`SharedDbm`]. Mathematically inconsistent constraints return **`Ok` with
//! an empty zone**, detectable with [`Dbm::is_empty`]. They do not return an
//! error. [`Error::Range`] instead means an exact finite bound needed by the
//! computation lies outside the range from [`MIN_CONSTANT`] to
//! [`MAX_CONSTANT`]; it must not be interpreted as emptiness. Bad clock indices and incompatible dimensions
//! are also errors. [`Workspace`] reuses scratch buffers but never changes
//! the result.
//!
//! ```rust
//! use clock_dbm::{Bound, Clock, Constraint, Dbm, Error, MAX_CONSTANT};
//!
//! # fn main() -> Result<(), Error> {
//! let x = Clock::new(1).unwrap();
//! let impossible = Dbm::universe(1)?
//!     .try_constrain(Constraint::lt(x, Clock::ZERO, 0)?)?;
//! assert!(impossible.is_empty()); // x >= 0 and x < 0
//! assert_eq!(Bound::le(MAX_CONSTANT + 1), Err(Error::Range));
//! # Ok(())
//! # }
//! ```
//!
//! ## Supported abstractions
//!
//! This release provides maximal-constant extrapolation (ExtraM). More
//! advanced abstractions, including separate lower/upper (LU) bounds and
//! related variants, are left for future development.
//!
//! ## Developer references
//!
//! The public API pages describe each operation's behavior, errors, and
//! complexity without requiring other documents. For implementation and
//! verification work, the [developer reference index](guide) provides the
//! algorithm guide, proof-status report, and pinned toolchain information.
//!
//! The executable DBM operations have been checked with Creusot against
//! their stated zone semantics. The shared layer relies on trusted `Rc`
//! specifications; hashing is outside the machine-checked subset.

// Ghost-only bindings (logic imports) are unused once contracts are erased.
#![cfg_attr(not(creusot), allow(unused_imports, unused_variables))]
// `#[derive(DeepModel)]` generates undocumented model types under Creusot.
#![cfg_attr(creusot, allow(missing_docs))]
// The trusted `Rc` specifications of `shared` name `Rc<T, A>`'s allocator.
#![cfg_attr(creusot, feature(allocator_api))]

pub mod bounds;
pub mod dbm;
pub mod error;
pub mod guide;
mod macros;
pub mod ops;
pub mod shared;

// The exact reference oracle, shared by the differential integration tests and
// the differential unit tests of `dbm` and `ops::constraints`.
#[cfg(test)]
#[allow(dead_code, unused_imports)]
#[path = "../tests/support/oracle/mod.rs"]
mod oracle;

pub use bounds::{Bound, Clock, Constraint, MAX_CONSTANT, MIN_CONSTANT, Variable};
pub use dbm::{Dbm, MAX_VARIABLES, Workspace};
pub use error::Error;
pub use ops::extra_m::MaxBounds;
pub use shared::SharedDbm;
