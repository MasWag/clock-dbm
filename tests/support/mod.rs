//! Helpers shared by integration tests.
//!
//! Each feature gets its own integration test file `tests/<feature>.rs`,
//! which opts in with `mod support;`. Keep helpers here small and generic so
//! independent changes do not conflict.

// Not every test file uses every helper.
#[allow(dead_code, unused_imports)]
pub mod oracle;
