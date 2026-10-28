//! Operations on canonical DBMs.
//!
//! Methods on [`Dbm`](crate::Dbm) define each operation's behavior,
//! error cases, and complexity. These submodules group related operations
//! for convenient browsing.

pub mod constraints;
pub mod extra_m;
pub mod relations;
pub mod temporal;

#[cfg(test)]
pub(crate) mod test_support;
