#!/usr/bin/env bash
# Verification gate for the production crate `clock-dbm` (repository root).
#
# Every step runs from the repository root, its command and exit status are
# appended to the log (default: verification/results/crate-<os>-<arch>.log),
# and the script exits non-zero if any step fails. --proof-only omits the
# expensive negative controls but still checks erasure and every proof goal.
set -uo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
use_pinned_rust || exit 1
root="$(cd "$here/../.." && pwd)"
results="$here/../results"
proof_only=0
case "${1:-}" in
    "") [ $# -eq 0 ] || { echo "usage: $0 [--proof-only]" >&2; exit 2; } ;;
    --proof-only) [ $# -eq 1 ] || { echo "usage: $0 [--proof-only]" >&2; exit 2; }; proof_only=1 ;;
    *) echo "usage: $0 [--proof-only]" >&2; exit 2 ;;
esac
os="$(uname -s | tr '[:upper:]' '[:lower:]')"
log="${PROVE_LOG:-$results/crate-$os-$(uname -m).log}"
mkdir -p "$(dirname "$log")"
: > "$log"
cd "$root"

failed=0
step() {
    local name="$1"; shift
    echo "=== [$name] \$ $*" | tee -a "$log"
    "$@" 2>&1 | tee -a "$log"
    local status="${PIPESTATUS[0]}"
    echo "=== [$name] exit status: $status" | tee -a "$log"
    [ "$status" -eq 0 ] || failed=1
}

{
    echo "# clock-dbm production crate verification run"
    echo "date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "host: $(uname -srm)"
    echo "mode: $([ "$proof_only" -eq 1 ] && echo proof-only || echo full)"
    echo "commit: $(git rev-parse HEAD 2>/dev/null)$([ -z "$(git status --porcelain -- . ':!verification/results' 2>/dev/null)" ] || echo ' (uncommitted changes)')"
} | tee -a "$log"

step versions      cargo creusot version
step rustc         rustc --version --verbose
# Ordinary build and tests of the same sources (contracts erase here).
step build         cargo build --locked
step test          cargo test --locked
# Start from a clean Creusot build and an empty prover cache, so that every
# goal is proved by a fresh prover call (verification/README.md, pitfall 1).
step clean         rm -rf target/creusot verif .why3find
# Translate, check #[erasure] (failures are errors) and prove every goal.
step prove         cargo creusot --erasure-check=error -- --locked
# Independently re-check: every goal in every proof.json is proved.
step proof-summary "$here/check-proofs.sh" verif
if [ "$proof_only" -eq 0 ]; then
    step negative "$here/negative-control-crate.sh"
else
    echo "=== [negative] skipped (--proof-only)" | tee -a "$log"
fi

echo "=== overall: $([ $failed -eq 0 ] && echo PASS || echo FAIL)" | tee -a "$log"
exit $failed
