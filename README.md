# clock-dbm

[![License: Apache-2.0 OR MIT](https://img.shields.io/badge/License-Apache--2.0%20OR%20MIT-blue.svg)](#license)

`clock-dbm` is a Rust library for representing **zones of timed automata**
using canonical difference-bound matrices (DBMs). Clock values are nonnegative
real numbers; constraints use strict or non-strict integer bounds stored in
packed `i32` entries.

The library provides canonical zone construction, constraints and batch
constraints, time elapse, reset, free, intersection, inclusion, maximal-constant
extrapolation (ExtraM), and copy-on-write shared zones.

The core DBM operations are **formally verified using
[Creusot](https://github.com/creusot-rs/creusot)** against their specified
zone semantics. See [verification status](verification/PROOF_STATUS.md)
for the exact coverage and trusted assumptions.

## Quick start

The `constraint!` macro writes clock guards in the usual notation: single-clock
bounds such as `x >= 2` and clock differences such as `y - x < 3`.

```rust
use clock_dbm::{constraint, Clock, Dbm, SharedDbm, Workspace};

fn main() -> Result<(), clock_dbm::Error> {
    let x = Clock::new(1).unwrap();
    let y = Clock::new(2).unwrap();
    let mut ws = Workspace::new();

    // 2 <= x <= 10 and y - x < 3
    let zone = Dbm::try_from_constraints(2, &[
        constraint!(x >= 2)?,
        constraint!(x <= 10)?,
        constraint!(y - x < 3)?,
    ], &mut ws)?;

    let saved = SharedDbm::from(zone);
    let smaller = saved.clone().try_constrain(constraint!(x < 4)?)?;
    assert!(smaller.is_subset_of(&saved)?);
    Ok(())
}
```

A successful operation always returns a canonical or empty zone. Inconsistent
constraints return **`Ok` with an empty zone**, not an error.
`Error::Range` means exact finite arithmetic encountered an unrepresentable
bound; it must not be treated as emptiness.

## Documentation

The generated **Rustdoc** contains the complete public API reference,
including mathematical meaning, errors, complexity, and usage examples:

```sh
cargo doc --no-deps --open
```

For developers and verification researchers, further technical documents
are included in Rustdoc and maintained as Markdown in the repository:

- [Algorithms and implementation](docs/algorithms.md): representation, closure,
  optimizations, complexity, ExtraM, and sharing.
- [Proof status and toolchain](verification/PROOF_STATUS.md): machine-checked
  properties, trusted assumptions, pinned verification tools, and reproduction.

The copy-on-write layer is checked relative to documented trusted
specifications of selected `Rc` operations; hashing is not machine-checked.
See the proof-status reference for the precise verified subset.

## Build and test

```sh
cargo fmt --check
cargo clippy --all-targets -- -D warnings
cargo test --all-targets
cargo test --doc
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
```

The Rust toolchain configuration is in `rust-toolchain.toml`, and the minimum
supported Rust version is declared in `Cargo.toml`. Verification uses the
separately pinned environment documented under `verification/`.

## Development

This project has been developed with assistance from AI coding agents,
including Claude Code and OpenAI Codex. The project maintainer remains
responsible for the design, implementation, and maintenance of the software.

The implementation builds on established DBM algorithms described by, for
example, [Bengtsson and Yi (2004)](https://doi.org/10.1007/978-3-540-27755-2_3).
Its mathematical specifications are informed by the [Isabelle AFP formalization
of difference-bound matrices](https://www.isa-afp.org/entries/Difference_Bound_Matrices.html),
associated with [Wimmer and Lammich (2018)](https://doi.org/10.1007/978-3-319-89960-2_4).
[UDBM](https://github.com/UPPAALModelChecker/UDBM) was consulted as a design
and performance reference, particularly for packed-bound representations and
efficient incremental closure.

Another Creusot-based verification of DBM operations is
[VerifiedDBM](https://github.com/ruth561/VerifiedDBM), which focuses on
a simplified DBM representation and selected operations.

## License

Licensed under either the [Apache License, Version 2.0](LICENSE-APACHE) or
the [MIT license](LICENSE-MIT), at your option.
