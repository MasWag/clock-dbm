# Contributing

Thank you for contributing to `clock-dbm`. Keep changes focused, and make
sure tests, documentation, and verification claims match the code being shipped.

## Documentation guidelines

Documentation has three levels, ordered from general to specialized:

1. **Public API Rustdoc** (crate, type, module, and method pages) is the
   complete reference for library users. A reader should be able to use the
   crate without opening another document. Explain mathematical behavior,
   parameters, return values, errors, empty-zone cases, and relevant
   performance characteristics (including complexity and copy-on-write
   costs). Define any necessary notation locally. Use runnable examples
   when they clarify usage. Module-level pages may briefly compare related
   operations to help users choose the right one.
2. **[Algorithm guide](docs/algorithms.md)** is for developers who want to
   understand the implementation. It may assume familiarity with the public
   API and focuses on data representation, algorithms, optimizations, and
   explanations of complexity bounds. Do not repeat complete API contracts
   or user-facing error descriptions here.
3. **[Proof status](verification/PROOF_STATUS.md)** is for developers and
   verification researchers. It may assume both the public API and the
   algorithm guide. Record precise machine-checked properties, proof
   evidence, trusted assumptions, and remaining obligations. Do not
   duplicate the API specification or the algorithm guide.

**Dependencies go in one direction:** advanced documents may rely on more
basic ones, but public API pages must not require the algorithm guide or
proof-status report to be understood, and the algorithm guide must not
require the proof-status report.

Give each explanation one primary home. A complexity bound may appear on
both a method page (so users can estimate cost) and in the algorithm guide
(where its implementation and derivation are explained), but avoid repeating
the derivation. Keep internal proof names and implementation-only details
out of user-facing method documentation.

## Checks

When changing code or documentation, run the applicable checks from the
[README](README.md), especially:

```sh
cargo fmt --check
cargo clippy --all-targets -- -D warnings
cargo test --all-targets
cargo test --doc
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
```

Documentation examples and intra-doc links must compile without warnings.
For changes to verified executable code or its contracts, run the pinned
proof procedure described in [proof status](verification/PROOF_STATUS.md)
and update verification claims only when the corresponding obligations have
actually been discharged.
