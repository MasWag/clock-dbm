# Verification

The production `clock-dbm` crate is verified with **Creusot v0.14.0**.
[`PROOF_STATUS.md`](PROOF_STATUS.md) states the machine-checked properties,
the trusted base, the pinned toolchain and the recorded evidence. This page
covers the layout of this directory and practical notes for running the proofs.

- `scripts/install-creusot.sh`: installs the pinned Creusot, Why3, why3find and
  solver environment in an isolated prefix.
- `scripts/env.sh`: selects that environment and the pinned nightly Rust.
- `scripts/prove-crate.sh`: the proof gate for the crate at the repository root.
- `scripts/check-proofs.sh`, `scripts/check-proofs.py`: independently check
  that every generated goal has a prover certificate.
- `scripts/negative-control-crate.sh`: injects deliberate defects into scratch
  copies and requires the verifier to reject each one.
- `results/`: recorded proof-gate logs.

## Quick start

Requirements: `git`, `rustup`, `opam` (≥ 2.1), `curl`, `python3`, a C toolchain, and gmp/zlib/pkg-config/autoconf.

```sh
verification/scripts/install-creusot.sh      # install the pinned toolchain
verification/scripts/prove-crate.sh --proof-only  # prove all goals and check erasure
verification/scripts/prove-crate.sh              # full gate, including 21 negative controls
```

The steps of the gate are listed in
[`PROOF_STATUS.md`](PROOF_STATUS.md#reproducing-the-verification). The log goes
to `results/crate-<os>-<arch>.log` by default; set `PROVE_LOG` to write it
elsewhere.

To look at a single function, run `cargo creusot <module>/<function>` with the
pinned environment (`. verification/scripts/env.sh && use_pinned_rust`). Add
`--why3session` and inspect `verif/**/why3session.xml` to find an unproved
sub-goal.

## GitHub Actions

The [Creusot workflow](../.github/workflows/creusot.yml) runs `--proof-only`
for PRs targeting `master` and pushes to `master`. This mode still builds
and tests the crate, clears the proof cache, checks erasure, proves every
obligation, and checks the generated proof certificates. It omits only the
21 negative controls, which are more expensive and can encounter solver
calibration instability.

The **full gate** runs on version-tag pushes (`v*`) and on manual
`workflow_dispatch` runs with the `full_gate` input enabled (the default).
Each run uploads its verification log as an Actions artifact. A successful
proof-only run is **not** evidence that the negative controls passed.

## Pitfalls

1. **Cached builds skip checks.** `cargo creusot` relies on cargo's fingerprinting, and changing only Creusot flags (`--erasure-check`, `--only`) does not trigger a rebuild. So a second invocation can "pass" without re-running the erasure check. The gate always deletes `target/creusot` first.
2. **Rust toolchain resolution.** If another `cargo` precedes rustup's proxies in `PATH`, `rust-toolchain.toml` is ignored and `creusot-rustc` fails to build or run. The scripts put the pinned toolchain's `bin/` first and set `DYLD_FALLBACK_LIBRARY_PATH` / `LD_LIBRARY_PATH` to its sysroot (`scripts/env.sh`).
3. **The erasure checker does not support builtin slice indexing** (`slice[i]`, "unsupported expression `Index`"). `Vec` indexing, which goes through `Index::index`, works.
4. **A public `ensures` that names a private field** is mistranslated when the function is called from another module (Coma `ERROR_UNBOUND_f0`; Why3 rejects the file, so it fails closed). State such contracts through `View`/`DeepModel` instead.
5. **`cargo creusot version` prints "bad CVC5 version"** for the pinned CVC5 1.4.1, because its parser expects the older `This is cvc5 version …` banner. This is cosmetic: Why3 is configured with CVC5 (`creusot_why3.conf`), and CVC5 discharges goals in the recorded run.
6. **`#[derive(PartialEq)]`** in verified code needs a `DeepModel`. A derived `DeepModel` on a type with private fields hits a visibility error, so a manual `impl DeepModel` with `#[logic(open(self))]` is used.
