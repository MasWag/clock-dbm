# Sourced by the scripts in this directory.
CREUSOT_NIGHTLY=nightly-2026-08-03

# The pinned Creusot is installed under its own prefix, so that it coexists
# with any other Creusot on the machine (e.g. a development build in
# ~/.cargo/bin, the default data directory and the opam switch ~/.creusot).
# Under the prefix (override with CREUSOT_PREFIX):
#   data/       CREUSOT_DATA_HOME: creusot-rustc, prelude, provers,
#               why3find.json, and links to Why3/why3find in opam/
#   opam/       an opam switch of its own with the pinned Why3 and why3find
#   cargo/bin/  cargo-creusot (CARGO_INSTALL_ROOT)
# CREUSOT_DATA_HOME is set unconditionally, so an inherited value of another
# installation is never used. See verification/PROOF_STATUS.md for what stays shared.
CREUSOT_PREFIX="${CREUSOT_PREFIX:-$HOME/.local/share/creusot-v0.14.0}"
export CREUSOT_DATA_HOME="$CREUSOT_PREFIX/data"
export CARGO_INSTALL_ROOT="$CREUSOT_PREFIX/cargo"
CREUSOT_SWITCH="$CREUSOT_PREFIX/opam"

# A development Creusot's installer writes [patch.crates-io] creusot-std into
# $HOME/.cargo/config.toml. Cargo reads that file for every build under
# $HOME, so it breaks the --locked builds of the gate (Cargo.lock would gain
# a [[patch.unused]] entry). Fail early with an explanation.
check_no_creusot_patch() {
    local cfg="$HOME/.cargo/config.toml"
    if [ -f "$cfg" ] && grep -q 'creusot-std' "$cfg"; then
        echo "error: $cfg patches creusot-std (written by a development Creusot's" >&2
        echo "  installer); it applies to this repository too. Move the [patch] into a" >&2
        echo "  .cargo/config.toml of the projects that use that build (PROOF_STATUS.md)." >&2
        return 1
    fi
}

# Put the pinned toolchain's own bin directory first in PATH, so that the
# right cargo/rustc are used even when rustup proxies are absent or another
# cargo (e.g. Homebrew's) comes first. cargo-creusot is installed by
# `cargo install`, i.e. into $CARGO_INSTALL_ROOT/bin. creusot-rustc links
# against the toolchain's librustc_driver, which rustup proxies would normally
# put on the dynamic library path; do that explicitly.
use_pinned_rust() {
    check_no_creusot_patch || return 1
    local cargo_bin
    cargo_bin="$(rustup which --toolchain "$CREUSOT_NIGHTLY" cargo)" || {
        echo "error: toolchain $CREUSOT_NIGHTLY missing; run scripts/install-creusot.sh" >&2
        return 1
    }
    export PATH="$(dirname "$cargo_bin"):$CARGO_INSTALL_ROOT/bin:$PATH"
    local lib
    lib="$(rustc --print sysroot)/lib"
    export DYLD_FALLBACK_LIBRARY_PATH="$lib${DYLD_FALLBACK_LIBRARY_PATH:+:$DYLD_FALLBACK_LIBRARY_PATH}"
    export LD_LIBRARY_PATH="$lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
}
