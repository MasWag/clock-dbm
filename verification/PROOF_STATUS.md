# Verification status and toolchain

This document records the machine-checked guarantees, trusted assumptions,
verification environment, and reproducibility evidence for the production
`clock-dbm` crate. It assumes familiarity with the public
[`Dbm`](crate::Dbm) and [`SharedDbm`](crate::SharedDbm) API documentation
and the [algorithm guide](crate::guide::algorithms). Those references
define the operations' semantics and describe their implementations; this
report does not restate them.

**Verification evidence is revision-specific.** The recorded proof run
covers a development revision that precedes this source snapshot; its log
records that revision's identifier. Verification of a different source
revision, including a release, requires a corresponding proof run.

## Reproducing the verification

From the repository root:

```sh
verification/scripts/install-creusot.sh  # install the pinned environment
verification/scripts/prove-crate.sh              # full gate, including negative controls
verification/scripts/prove-crate.sh --proof-only # PR/push proof and erasure checks
```

The proof gate, `verification/scripts/prove-crate.sh`, records tool versions,
builds and tests the executable crate, clears the Creusot build and
`why3find` proof cache, and then runs:

```sh
cargo creusot --erasure-check=error -- --locked
verification/scripts/check-proofs.sh verif
verification/scripts/negative-control-crate.sh
```

The proof-summary step checks that all generated proof goals have prover
certificates; the negative controls check that deliberately incorrect
variants are rejected. A successful translation alone is not counted as verification. The
`--proof-only` mode runs every step except the 21 negative controls; a
proof-only pass does not certify that deliberately defective code is rejected.
Prover outcomes near the time limit can vary between runs on
the same machine: an earlier clean run of the recorded revision left one
goal of the unchanged `ops/temporal/proof/rewind` lemma open and could not
calibrate z3 for two negative controls; the recorded rerun passed every
step. Run logs are saved to
`verification/results/crate-<os>-<arch>.log`.

### Recorded evidence

| Property | Recorded result |
|---|---|
| Source revision | pre-release development revision (the log's `commit:` line) |
| Run | `verification/results/crate-darwin-arm64.log` (2026-11-11) |
| Platform | macOS (Darwin) arm64 (64-bit `usize`) |
| Creusot | v0.14.0 |
| Proof obligations | 342 Coma files, 843 goals, all discharged |
| Negative controls | 21 injected defects, all rejected |
| Overall | PASS |

This table is a recorded **local** verification run, not a GitHub Actions run.
The separate [Creusot Actions workflow](../.github/workflows/creusot.yml)
checks the pinned proof obligations and erasure on PRs targeting `public`
and on pushes to `public`, and uploads source-revision-specific logs.
Full verification, including the 21 negative controls, runs on version-tag
pushes or an explicitly requested full manual dispatch (when available on
the repository's default branch; see [verification README](README.md#github-actions)).
The ordinary CI workflow remains separate. Consult the actual Actions run
and its artifact for evidence of CI success; this historical table does not
make that claim.

## Pinned toolchain

The installation script pins **Creusot v0.14.0** at commit
`65349025c67e69fcd7479f1f420fa5904f69bc27` and uses the dependencies
associated with that release.

| Component | Version / source |
|---|---|
| `cargo-creusot`, `creusot-rustc`, prelude | Creusot `v0.14.0`, commit above |
| `creusot-std` | `=0.14.0` |
| Rust | `nightly-2026-08-03` with `rustc-dev`, `llvm-tools`, `rust-src` and `rustfmt` |
| OCaml | 5.3.0 (dedicated opam switch) |
| Why3 | git `05bf4ddf55cb3042f34c3bc0ed3aff56a226978a` (1.8.2) |
| why3find | git `0f054b93c86ac7ba20bca7df5d1563a9a4434a30` (1.3.0) |
| Alt-Ergo | 2.6.4 |
| Z3 | 5.1.0 |
| CVC5 | 1.4.1 |
| CVC4 | 1.8 (unavailable on aarch64 Linux) |

The Creusot tag and upstream dependency definitions are the source of the
pins; `verification/scripts/install-creusot.sh` checks the exact Creusot
commit. The repository also retains the pinned `why3find.json` configuration.
Some opam build dependencies are resolved at installation time rather than
pinned individually. The run log records the actual installed versions.

### Isolated installation

The installer uses `~/.local/share/creusot-v0.14.0` by default; override
this with `CREUSOT_PREFIX`. Within the prefix, `data/` contains the
verification tools and prover configuration, `opam/` holds the dedicated
Why3/why3find switch, and `cargo/bin/` contains `cargo-creusot`.
`verification/scripts/env.sh` selects this environment for the proof gate,
allowing it to coexist with a separate development Creusot installation.
The rustup toolchains, download cache and generic Why3 prover configuration
remain shared.

A global `[patch.crates-io] creusot-std = { path = ... }` in
`~/.cargo/config.toml` can override the pinned dependency even for
`--locked` builds. Keep such patches in the project that needs them.
`env.sh` detects and refuses this global override; the installer does not
write one.

## Machine-checked coverage

The claims below concern the executable Rust bodies and their Creusot
contracts on the recorded revision. Ghost definitions, contracts, and
proof statements erase in ordinary builds. Unless otherwise qualified,
the verified postconditions establish the corresponding public operation's
meaning over **nonnegative real-valued clocks with integer bounds**.

The proof uses logical models `BoundModel` (strict/weak/infinite bounds)
and `Val` (real-valued clock valuations). The production types carry
invariants constraining finite bounds, clock indices and canonical-or-empty
DBM storage.

| Production code | Machine-checked properties |
|---|---|
| `Bound`, `Clock`, `Variable`, `Constraint` (`src/bounds.rs`) | Representation invariants, ordering, finite-range validation, exact strict and non-strict constructors, clock indices, and checked bound addition. Required arithmetic and indexing are proved overflow-free under their contracts. |
| `Dbm` constructors, queries and equality (`src/dbm.rs`) | The canonical-or-empty invariant, correct clock counts and constructors, preservation by cloning, and semantic equality of canonical zones. `Dbm::eq_semantic` proves equality independent of how a zone was constructed. |
| Full closure (`src/dbm.rs`) | Exact zone preservation when closure succeeds, correct detection of empty zones (including strict-zero cycles), canonical nonempty results, range-error provenance, memory safety and termination of checked loops. |
| `try_constrain` (`src/ops/constraints.rs`) | Exact restriction by one difference guard. The implied, contradictory, single-store, incremental-closure and selective-row-skip paths are covered; invalid indices and unrepresentable resulting bounds follow the contract. `close_edge`, independently reimplemented from the algorithm guide, is proved to produce exactly the one-edge closure on success, and an unrepresentable closure entry on `Err(Range)`. |
| `try_constrain_all`, `try_from_constraints` (`src/ops/constraints.rs`) | Correct successful conjunction, including the early contradiction check and both batch strategies, validated clock indices and range-error provenance. Successful results are order-independent as zones; range errors can depend on intermediate calculations. |
| `future`, `try_reset_zero`, `try_reset`, `try_free` (`src/ops/temporal.rs`) | Exact common-delay, reset and free semantics; clock-count and empty-zone preservation; validated arguments; canonicality of in-place updates. Reset has an exact range-error condition. |
| `past` (`src/ops/temporal.rs`) | Exact time-predecessor semantics, both inclusions: `v ∈ past(Z)` iff `v` is a nonnegative valuation and `v + t ∈ Z` for some real `t ≥ 0` (a common delay). Clock-count and empty-zone preservation, a canonical result, an overflow-free and panic-free row-minimum loop (the overflow flag of `relax_row` is proved unset), and termination. |
| `is_subset_of`, `entails`, `intersects_constraint`, `difference_bound` (`src/ops/relations.rs`) | Inclusion, universal and existential satisfaction, and tight difference bounds, including the empty-zone cases and exact argument errors. These queries do not return arithmetic range errors. |
| `try_intersect` (`src/ops/relations.rs`) | Exact intersection, canonical-or-empty result, dimension errors and range-error provenance. The touched-pivot closure, no-change behavior and negative-cycle detection are covered. |
| `MaxBounds`, `try_extrapolate_max` (`src/ops/extra_m.rs`) | Validated ceilings, correct entrywise ExtraM normalization, the unchanged and full-closure paths, canonical-or-empty results, semantic overapproximation and range-error provenance. |
| `Workspace` (`src/dbm.rs`) | Invariants and exact effects of the touched-pivot and all-pivot flag operations used by the verified kernels. |
| `SharedDbm` (`src/shared.rs`) | Refinement to the corresponding `Dbm` operation contracts, including unique/shared update paths, copy-on-write shortcuts, conversions, equality, and snapshot-isolation harnesses (which also cover `past`), **relative to the trusted `Rc` model and specifications below**. |

### Key proof connections

These are the main proof components for tracing an operation to its
machine-checked justification. The algorithm guide covers the underlying
transformations.

- **Representation and closure** (`src/dbm/proof.rs`):
  `canonical_nonempty` constructs a valuation for canonical matrices;
  `zone_relax` preserves zone semantics during relaxation;
  `pivot_step` establishes the closure invariant;
  `canonical_unique` and `Dbm::eq_semantic` establish semantic equality.
  `range_failure` records the provenance of arithmetic failures.
- **Constraint insertion** (`src/ops/constraints/proof.rs`):
  `edge_zone` and `edge_canonical` justify single-edge closure,
  including the fast paths. For `close_edge`, `phase1`, `skip`,
  `infinite_row`, `skip_test_unrepresentable` and `phase2` justify the
  updated row `i`, the row skip and the other rows; its loop invariant
  (unprocessed rows are still the input's) gives in-place read stability.
  `single_range_failure` and
  `batch_range_failure` specify when range errors may occur.
- **Temporal operations** (`src/ops/temporal/proof.rs`):
  `up_zone`, `reset_zone`, `free_zone` and `down_zone` establish the exact
  valuation transformations. `project`, `unshift` and `rewind` provide the
  required witnesses for the reverse inclusions. `rewind` finds the delay
  by extending the negated valuation by one clock. `reset_representable`
  justifies arithmetic range safety after reset arguments are validated.
  For `past`, `pmin_spec` characterizes the folded row minimum and its
  argmin, and `down_canonical` proves the result canonical.
- **Intersection and queries** (`src/ops/relations/proof.rs`,
  `src/dbm/proof.rs`): `subset_pointwise`, `entry_tight`, `meets`,
  `min_closed` and `pivot_keep` justify direct queries and restricted
  closure through only changed endpoints.
- **ExtraM** (`src/ops/extra_m/proof.rs`): `norm_extensive`,
  `norm_ready` and `norm_range` connect normalization to the zone
  overapproximation and canonical closure.
- **Shared zones** (`src/shared/proof.rs`): `unique_zones`,
  `snapshot_isolation` and `copy_on_write_agrees` connect the wrapper
  contracts to the verified owned-zone operations.

The checked in-place kernels use contracts on the actual row/column
mutations and the canonicality precondition of `publish_canonical`.
A working matrix is never published on an error. The relevant kernel
loops carry `#[check(terminates)]`; this is **not** a claim that every
derived trait method has a termination proof.

### Negative controls

`verification/scripts/negative-control-crate.sh` creates scratch copies
with deliberate semantic, arithmetic, indexing or shortcut defects, then
requires the verifier to reject them. Controls cover bound strictness,
finite range, out-of-bounds access, closure and contradiction tests,
row skipping, temporal operations, touched-pivot intersection, ExtraM
normalization, shared-zone shortcuts and the naive `past` that sets every
lower bound to `Le 0`. The recorded run rejected all 21 controls; the script is the source for the individual injected defects
and expected failing proof goals.

## Trusted base

- **Compiler and verification tools:** the pinned Rust compiler,
  `creusot-rustc` translation, Creusot's Coma prelude, Why3, why3find
  and the SMT solvers. A goal counts as discharged when a configured
  prover proves it.
- **`creusot-std` v0.14.0 specifications:** arithmetic, comparisons,
  casts and bit operations; collection and slice access; `Option`,
  `Result`, cloning and comparison traits; and the `Vec`, `Box` and
  `Rc` operations used in the kernels.
- **`Rc` for `SharedDbm`:** Creusot's existing trusted value model for
  `Rc<T>` and its specifications of `new`, `Clone`, `Deref`, `AsRef`
  and `ptr_eq`, together with three local extern specifications in
  `src/shared/rc_spec.rs`:
  - `Rc::get_mut`: on `Some`, permits mutation of the value of a unique
    handle; on `None`, the handle is unchanged.
  - `Rc::strong_count`: only termination is specified; the count is
    used to choose between independently correct paths.
  - `Rc::unwrap_or_clone`: returns the original value or a value
    satisfying the element's `Clone` postcondition.

These `Rc` specifications are **trusted**, not proved from the Rust
standard-library implementation. They do not assert snapshot isolation
directly; the shared-zone verification derives it relative to this model.
There are no trusted assertions or admitted lemmas in the production
DBM algorithms.

## Scope and limitations

- **Proof provenance:** the recorded evidence covers only the
  revision and target recorded in its log. Ordinary build/test CI is not a replacement
  for rerunning the full pinned proof gate on a release revision.
- **Platforms and resources:** the recorded proof run targets macOS
  arm64. Verification of this revision on other targets, including the
  Linux x86_64 target of earlier revisions, is not recorded.
  Allocation failure, out-of-memory behavior and allocator capacity
  failures are not proved safe; proofs rely on the available collection
  specifications.
- **Hashing and formatting:** `Hash` implementations are outside the
  machine-checked subset, although they are derived from fields used
  for equality and tested for consistency. `Display` and
  `std::error::Error` formatting are also outside that subset.
- **Termination boundaries:** not every trait implementation is marked
  `#[check(terminates)]`; for example, `Dbm::PartialEq` and
  `MaxBounds::Clone` have functional contracts without that annotation.
- **Arithmetic range:** for full closure, a proved sufficient condition
  for avoiding `Error::Range` is `B * 2^d <= MAX_CONSTANT`, for
  `d = n + 1` and finite input constants of magnitude at most `B`.
  The stronger linear condition `2 * d * B <= MAX_CONSTANT` is
  **not** machine-checked. The incremental, batch, intersection and
  ExtraM contracts have the provenance and exactness guarantees stated
  above, not a general sufficient no-range-error premise.
- **ExtraM:** idempotence is not proved; applicability to timed-automata
  reachability requires automaton-level assumptions and is not established
  by the crate-level proof. `norm_range` constrains each normalized entry,
  but the complete finite-image counting argument is not machine-checked.
- **Shared updates:** snapshot isolation and contract refinement are
  proved relative to the trusted `Rc` specifications. For some updates
  that reach the kernel, their contracts do not uniquely determine
  whether `Ok` or `Err(Error::Range)` occurs; equivalence beyond
  those contracts is not itself a separate universal theorem.
- **Macro expansion:** the `constraint!` syntax macro delegates to
  the verified `Constraint` constructors; its expansion does not
  have an independent machine-checked theorem.
