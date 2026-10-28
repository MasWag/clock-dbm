#!/usr/bin/env bash
# Install the pinned Creusot toolchain used by verification/scripts/prove-crate.sh.
#
# Pins (see verification/PROOF_STATUS.md):
#   Creusot v0.14.0 = commit 65349025c67e69fcd7479f1f420fa5904f69bc27
#   Rust nightly-2026-08-03; Why3/why3find/provers as pinned by that commit.
#
# Side effects outside the repository, all under the pinned prefix of env.sh
# (default ~/.local/share/creusot-v0.14.0) unless noted:
#   - rustup toolchain nightly-2026-08-03 (+ rustc-dev, llvm-tools, rust-src),
#     in the shared rustup home
#   - <prefix>/opam: an opam switch of its own (OCaml 5.3.0, the pinned Why3
#     and why3find), created here rather than by Creusot's installer, which
#     on macOS always uses ~/.creusot
#   - <prefix>/cargo/bin/cargo-creusot (CARGO_INSTALL_ROOT)
#   - <prefix>/data (CREUSOT_DATA_HOME): creusot-rustc, prelude,
#     SHA-256-checked prover binaries, links to Why3/why3find in <prefix>/opam
#   - Creusot's user why3.conf (generic prover limits) and download cache,
#     which Creusot keeps outside CREUSOT_DATA_HOME and shares
# Creusot's `cargo-creusot-config` component is skipped: it rewrites
# $HOME/.cargo/config.toml (for a release, it removes a development build's
# creusot-std patch). Nothing of another Creusot installation is touched.
#
# The Why3 GUI (why3-ide, GTK) is not needed for the gate and is skipped the
# way Creusot's own CI does it, unless CREUSOT_WITH_IDE=1. Without the GUI the
# remaining system dependencies are gmp, zlib, pkg-config and autoconf; opam's
# depext check is skipped (OPAMASSUMEDEPEXTS) because it insists on Homebrew
# zlib although the system zlib is found via pkg-config. If a C library is
# genuinely missing, the opam build fails loudly.
#
# Extra INSTALL options may be passed through, e.g. `--external z3`.
set -euo pipefail

CREUSOT_TAG=v0.14.0
CREUSOT_COMMIT=65349025c67e69fcd7479f1f420fa5904f69bc27

here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
tools="$here/../.tools"
src="$tools/creusot"

for cmd in git rustup opam curl python3; do
    command -v "$cmd" >/dev/null || { echo "error: '$cmd' is required" >&2; exit 1; }
done

mkdir -p "$tools"
if [ ! -d "$src/.git" ]; then
    git clone --depth 1 --branch "$CREUSOT_TAG" https://github.com/creusot-rs/creusot "$src"
fi
actual="$(git -C "$src" rev-parse HEAD)"
if [ "$actual" != "$CREUSOT_COMMIT" ]; then
    echo "error: $src is at $actual, expected $CREUSOT_COMMIT ($CREUSOT_TAG)" >&2
    exit 1
fi
if [ -n "$(git -C "$src" status --porcelain --untracked-files=no)" ]; then
    echo "error: $src has local modifications" >&2
    exit 1
fi

rustup toolchain install "$CREUSOT_NIGHTLY" --profile minimal \
    --component rustfmt,rustc-dev,llvm-tools,rust-src
use_pinned_rust
cargo --version

if [ "${CREUSOT_WITH_IDE:-0}" != 1 ]; then
    export OPAMVAR_in_creusot_ci=true
    export OPAMASSUMEDEPEXTS=1
fi

# The pinned Why3/why3find, in a switch of our own (the same commands as
# Creusot's installer, at a different location).
mkdir -p "$CREUSOT_SWITCH" "$CREUSOT_DATA_HOME/bin"
cp "$src/creusot-deps.opam" "$CREUSOT_SWITCH/creusot-deps.opam"
if [ -d "$CREUSOT_SWITCH/_opam" ]; then
    opam install --yes --update-invariant --switch "$CREUSOT_SWITCH" "$CREUSOT_SWITCH"
else
    opam switch create -y "$CREUSOT_SWITCH"
fi
ln -sf "$CREUSOT_SWITCH/_opam/bin/why3" "$CREUSOT_DATA_HOME/bin/why3"
ln -sf "$CREUSOT_SWITCH/_opam/bin/why3find" "$CREUSOT_DATA_HOME/bin/why3find"

# Everything else, except `why3` (done above) and `cargo-creusot-config`.
cd "$src"
./INSTALL prelude cargo-creusot creusot-rustc provers why3-conf "$@"

cargo creusot version
