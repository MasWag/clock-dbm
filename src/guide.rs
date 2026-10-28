//! Algorithms and verification references.
//!
//! Start with the public [`Dbm`](crate::Dbm) and
//! [`SharedDbm`](crate::SharedDbm) API documentation for semantics, errors,
//! and complexity. The [algorithm guide](algorithms) then explains the
//! implementation; the [proof status](proof_status) builds on both to
//! document machine-checked properties and trusted assumptions.
//!
//! The proof-status report also records the pinned verification toolchain.
//! Both developer references are included from Markdown files in the repository.

/// Algorithms, implementation strategies, and complexity.
#[doc = include_str!("../docs/algorithms.md")]
pub mod algorithms {}

/// Scope of the machine-checked proofs, trusted base, and known limitations.
#[doc = include_str!("../verification/PROOF_STATUS.md")]
pub mod proof_status {}
