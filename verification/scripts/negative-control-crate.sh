#!/usr/bin/env bash
# Shows that the production gate (prove-crate.sh) can fail. In scratch copies
# of the crate, inject one defect each and require that proving fails with
# open goals only where the defect is:
#   1. a false postcondition: `Lt(a) + Le(b)` is weak;
#   2. an off-by-one range: MAX_CONSTANT = 2^29 (no longer −MIN_CONSTANT, and
#      its codes exceed the largest valid code). The constructors must break
#      `Bound`'s type invariant, `checked_add` its range equivalence, and
#      `neg_in_range`, `dbm/proof/sum_bounded` and
#      `ops/temporal/proof/reset_representable` and
#      `ops/extra_m/thresholds` (`Lt(−MAX_CONSTANT)`) the symmetry of the range,
#      and `enc_range` the code range of representable bounds;
#   3. an out-of-bounds index in the closure kernel: the diagonal test reads
#      `m[i·d + d]` instead of `m[i·d + i]`, which overruns the last row;
#   4. a missed strict-zero cycle: the closure's emptiness test compares the
#      diagonal against `Lt 0` instead of `Le 0`, so `Lt 0` on the diagonal
#      is published as nonempty. The semantic contract of closure
#      must break, and nothing else;
#   5. an unmasked infinite summand in the row primitive of incremental
#      closure: `relax_row` relaxes through `∞` entries (replaced
#      by 0) as if they were finite. Only `bounds/relax_row` must break;
#   6. an unjustified row skip in the incremental closure: phase 2
#      never updates row 0. Only `ops/constraints/close_edge` must break;
#   7. a missed strict-zero contradiction: the O(1)
#      contradiction test compares `b + D[j][i]` against `Lt 0` instead of
#      `Le 0`. Only `ops/constraints/below_le_zero` must break;
#   8. the one-clock shortcut (a single store) taken for
#      `d = 3`. Only `ops/constraints/constrain_one` must break;
#   9. future without restoring `D[0][0] := Le 0` after filling
#      column 0 with `∞`. Only `ops/temporal/impl_Dbm/future` must break;
#  10. reset whose column pass adds `Le c` instead of `Le(−c)`
#      (a sign error in `R[i][k] = Le(−c) + D[i][0]`). Only
#      `ops/temporal/impl_Dbm/try_reset` must break;
#  11. `add_weak` without its `∞` mask, so `∞ + Le c` becomes
#      finite. Only `bounds/add_weak` must break;
#  12. a missing touched flag: `meet` marks only the row clock
#      `i` of a tightened entry, not `j`, so the touched-pivot closure could
#      skip a needed pivot. Only `dbm/impl_Matrix_*/meet` must break;
#  13. no emptiness check in the touched-pivot closure:
#      `close_pivots` never tests the diagonal, so an intersection that is
#      empty only through a longer negative cycle would be published as
#      nonempty. Only `dbm/impl_Matrix_*/close_pivots` must break;
#  14. inclusion with the comparison reversed: `entries_le`
#      tests `other ≼ self` instead of `self ≼ other`. Only
#      `dbm/impl_Dbm_*/entries_le` must break;
#  15. a weak lower threshold in ExtraM: `thresholds` returns
#      `Le(−k)` instead of `Lt(−k)`, so `norm_lower` would keep `Le(−k)`
#      entries that Isabelle's `norm` relaxes. Only `ops/extra_m/thresholds`
#      must break;
#  16. an inexact change flag: `normalize` reports a change only
#      when an entry became `∞`, missing `norm_lower` changes, so the
#      no-closure path could publish a weakened, noncanonical matrix. Only
#      `ops/extra_m/normalize` must break;
#  17. skipped closure: `try_extrapolate_max` always takes the
#      unchanged fast path and publishes the normalized matrix without
#      closing it. Only `ops/extra_m/impl_Dbm/try_extrapolate_max` must
#      break;
#  18. a nonzero reference ceiling: `MaxBounds::k(0)` returns
#      `MAX_CONSTANT` (UDBM's "no ceiling" reading) instead of Isabelle's
#      `k(0) = 0`. Only `ops/extra_m/impl_MaxBounds/k` must break;
#  19. a reversed implied-constraint shortcut in `SharedDbm`:
#      `try_constrain` returns the shared handle unchanged when `D[i][j]` is
#      tighter than the guard instead of the converse. Only
#      `shared/impl_SharedDbm/try_constrain` must break;
#  20. an unconditional no-copy intersection in `SharedDbm`:
#      a shared handle is returned unchanged without the `self ⊆ other`
#      test. Only `shared/impl_SharedDbm/try_intersect` must break;
#  21. the naive past: every lower bound is set to `Le 0` and the
#      row-minimum pass is skipped, so lower bounds implied by differences
#      (`x − y ≥ 5 ∧ y ≥ 0 ⇒ x ≥ 5`) are lost and the published matrix is
#      not canonical. Only `ops/temporal/impl_Dbm/past` must break.
# Exits 0 only if all twenty-one defects are rejected for the expected reason.
set -uo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
use_pinned_rust || exit 1
root="$(cd "$here/../.." && pwd)"
work="$(mktemp -d "${TMPDIR:-/tmp}/creusot-negative-crate.XXXXXX")"
trap 'rm -rf "$work"' EXIT
ok=1

# copy <dir>: a fresh copy of the crate sources in <dir>.
copy() {
    mkdir -p "$1"
    cp -R "$root/Cargo.toml" "$root/Cargo.lock" "$root/why3find.json" "$root/src" "$1/"
    # `src/guide.rs` embeds these pages with `include_str!`.
    mkdir -p "$1/verification"
    cp -R "$root/docs" "$1/"
    cp "$root/verification/PROOF_STATUS.md" "$1/verification/"
}

# expect <name> <dir> <pattern>: proving in <dir> fails, and every open goal
# matches <pattern>.
expect() {
    local name="$1" dir="$2" pattern="$3"
    echo "--- negative $name"
    (cd "$dir" && rm -rf target/creusot verif && cargo creusot --erasure-check=error -- --locked) \
        > "$dir.out" 2>&1
    local status=$?
    tail -n 20 "$dir.out"
    local summary open
    summary="$("$here/check-proofs.sh" "$dir/verif")"
    echo "$summary"
    open="$(echo "$summary" | grep -E '^(OPEN|MISSING)' || true)"
    if [ "$status" -eq 0 ]; then
        echo "FAIL: cargo creusot succeeded on a defective crate"; ok=0
    elif [ -z "$open" ] || echo "$open" | grep -qvE "$pattern"; then
        echo "FAIL: expected open goals only matching '$pattern'"; ok=0
    else
        echo "ok: rejected (exit $status), open goals only in $pattern"
    fi
}

copy "$work/strictness"
cat >> "$work/strictness/src/bounds.rs" <<'RS'

/// Negative control: falsely claims that `Lt(a) + Le(b)` is weak.
#[check(terminates)]
#[requires(BoundModel::in_range(a@) && BoundModel::in_range(b@))]
#[ensures(match result { Ok(r) => r@ == BoundModel::Le(a@ + b@), Err(_) => true })]
pub fn wrong_strictness(a: i32, b: i32) -> Result<Bound, Error> {
    match (Bound::lt(a), Bound::le(b)) {
        (Ok(x), Ok(y)) => x.checked_add(y),
        _ => Err(Error::Range),
    }
}
RS
expect strictness "$work/strictness" 'bounds/wrong_strictness'

copy "$work/range"
sed -i.bak 's/^pub const MAX_CONSTANT: i32 = 0x1FFF_FFFF;$/pub const MAX_CONSTANT: i32 = 0x2000_0000;/' \
    "$work/range/src/bounds.rs"
grep -q '^pub const MAX_CONSTANT: i32 = 0x2000_0000;$' "$work/range/src/bounds.rs" ||
    { echo "FAIL: could not inject the range defect"; ok=0; }
expect range "$work/range" '(bounds/(impl_Bound/(le|lt|checked_add)|neg_in_range|enc_range)|dbm/proof/sum_bounded|ops/temporal/proof/reset_representable|ops/extra_m/thresholds)\.coma'

copy "$work/index"
sed -i.bak 's/if tighter(m\[ri + i\], Bound::LE_ZERO) {/if tighter(m[ri + d], Bound::LE_ZERO) {/' \
    "$work/index/src/dbm.rs"
grep -q 'if tighter(m\[ri + d\], Bound::LE_ZERO) {' "$work/index/src/dbm.rs" ||
    { echo "FAIL: could not inject the index defect"; ok=0; }
expect index "$work/index" 'dbm/close_in_place\.coma'

copy "$work/strictzero"
sed -i.bak 's/if tighter(m\[ri + i\], Bound::LE_ZERO) {/if tighter(m[ri + i], Bound::LT_ZERO) {/' \
    "$work/strictzero/src/dbm.rs"
grep -q 'if tighter(m\[ri + i\], Bound::LT_ZERO) {' "$work/strictzero/src/dbm.rs" ||
    { echo "FAIL: could not inject the strict-zero defect"; ok=0; }
expect strictzero "$work/strictzero" 'dbm/close_in_place\.coma'

copy "$work/rowmask"
sed -i.bak 's/        let tighter = fin \& (sum < cur);/        let tighter = sum < cur;/' \
    "$work/rowmask/src/bounds.rs"
grep -q '        let tighter = sum < cur;' "$work/rowmask/src/bounds.rs" ||
    { echo "FAIL: could not inject the row-mask defect"; ok=0; }
expect rowmask "$work/rowmask" 'bounds/relax_row\.coma'

copy "$work/skiprow"
sed -i.bak 's/        if k != i \&\& !ki.is_infinite() {/        if k != i \&\& k != 0 \&\& !ki.is_infinite() {/' \
    "$work/skiprow/src/ops/constraints.rs"
grep -q '        if k != i && k != 0 && !ki.is_infinite() {' "$work/skiprow/src/ops/constraints.rs" ||
    { echo "FAIL: could not inject the row-skip defect"; ok=0; }
expect skiprow "$work/skiprow" 'ops/constraints/close_edge\.coma'

copy "$work/contra"
sed -i.bak 's/            tighter(s, Bound::LE_ZERO)$/            tighter(s, Bound::LT_ZERO)/' \
    "$work/contra/src/ops/constraints.rs"
grep -q '            tighter(s, Bound::LT_ZERO)$' "$work/contra/src/ops/constraints.rs" ||
    { echo "FAIL: could not inject the contradiction defect"; ok=0; }
expect contra "$work/contra" 'ops/constraints/below_le_zero\.coma'

copy "$work/oneclock"
sed -i.bak 's/    if m.dimension() == 2 {/    if m.dimension() <= 3 {/' \
    "$work/oneclock/src/ops/constraints.rs"
grep -q '    if m.dimension() <= 3 {' "$work/oneclock/src/ops/constraints.rs" ||
    { echo "FAIL: could not inject the one-clock defect"; ok=0; }
expect oneclock "$work/oneclock" 'ops/constraints/constrain_one\.coma'

copy "$work/updiag"
sed -i.bak '/^        m.set(0, 0, Bound::LE_ZERO);$/d' "$work/updiag/src/ops/temporal.rs"
grep -q '^        m.set(0, 0, Bound::LE_ZERO);$' "$work/updiag/src/ops/temporal.rs" &&
    { echo "FAIL: could not inject the future-diagonal defect"; ok=0; }
expect updiag "$work/updiag" 'ops/temporal/impl_Dbm/future\.coma'

copy "$work/resetsign"
sed -i.bak 's/^        m.add_weak_to_column(k, 0, down);$/        m.add_weak_to_column(k, 0, up);/' \
    "$work/resetsign/src/ops/temporal.rs"
grep -q '^        m.add_weak_to_column(k, 0, up);$' "$work/resetsign/src/ops/temporal.rs" ||
    { echo "FAIL: could not inject the reset-sign defect"; ok=0; }
expect resetsign "$work/resetsign" 'ops/temporal/impl_Dbm/try_reset\.coma'

copy "$work/weakmask"
sed -i.bak 's/^    Bound(if fin { sum } else { INF })$/    Bound(sum)/' "$work/weakmask/src/bounds.rs"
grep -q '^    Bound(sum)$' "$work/weakmask/src/bounds.rs" ||
    { echo "FAIL: could not inject the weak-mask defect"; ok=0; }
expect weakmask "$work/weakmask" 'bounds/add_weak\.coma'

copy "$work/touchedj"
sed -i.bak '/^                    touched\[j\] = true;$/d' "$work/touchedj/src/dbm.rs"
grep -q '^                    touched\[j\] = true;$' "$work/touchedj/src/dbm.rs" &&
    { echo "FAIL: could not inject the touched-flag defect"; ok=0; }
expect touchedj "$work/touchedj" 'dbm/impl_Matrix_[0-9]+/meet\.coma'

copy "$work/longcycle"
sed -i.bak 's/^                        if tighter(self.get(i, i), Bound::LE_ZERO) {$/                        if false \&\& tighter(self.get(i, i), Bound::LE_ZERO) {/' \
    "$work/longcycle/src/dbm.rs"
grep -q 'if false && tighter(self.get(i, i), Bound::LE_ZERO) {$' "$work/longcycle/src/dbm.rs" ||
    { echo "FAIL: could not inject the long-cycle defect"; ok=0; }
expect longcycle "$work/longcycle" 'dbm/impl_Matrix_[0-9]+/close_pivots\.coma'

copy "$work/subset"
sed -i.bak 's/^                le = le \& !tighter(rb\[l\], ra\[l\]);$/                le = le \& !tighter(ra[l], rb[l]);/' \
    "$work/subset/src/dbm.rs"
grep -q '^                le = le & !tighter(ra\[l\], rb\[l\]);$' "$work/subset/src/dbm.rs" ||
    { echo "FAIL: could not inject the inclusion defect"; ok=0; }
expect subset "$work/subset" 'dbm/impl_Dbm_[0-9]+/entries_le\.coma'

copy "$work/lowthr"
sed -i.bak 's/^    match (Bound::le(k), Bound::lt(-k)) {$/    match (Bound::le(k), Bound::le(-k)) {/' \
    "$work/lowthr/src/ops/extra_m.rs"
grep -q '^    match (Bound::le(k), Bound::le(-k)) {$' "$work/lowthr/src/ops/extra_m.rs" ||
    { echo "FAIL: could not inject the threshold defect"; ok=0; }
expect lowthr "$work/lowthr" 'ops/extra_m/thresholds\.coma'

copy "$work/changeflag"
sed -i.bak 's/^                changed = true;$/                changed = normed.is_infinite();/' \
    "$work/changeflag/src/ops/extra_m.rs"
grep -q '^                changed = normed.is_infinite();$' "$work/changeflag/src/ops/extra_m.rs" ||
    { echo "FAIL: could not inject the change-flag defect"; ok=0; }
expect changeflag "$work/changeflag" 'ops/extra_m/normalize\.coma'

copy "$work/skipclose"
sed -i.bak 's/^        let r = if changed {$/        let r = if false \&\& changed {/' \
    "$work/skipclose/src/ops/extra_m.rs"
grep -q '^        let r = if false && changed {$' "$work/skipclose/src/ops/extra_m.rs" ||
    { echo "FAIL: could not inject the skipped-closure defect"; ok=0; }
expect skipclose "$work/skipclose" 'ops/extra_m/impl_Dbm/try_extrapolate_max\.coma'

copy "$work/refceil"
sed -i.bak 's/^        if i == 0 { 0 } else { self.ceilings\[i - 1\] }$/        if i == 0 { MAX_CONSTANT } else { self.ceilings[i - 1] }/' \
    "$work/refceil/src/ops/extra_m.rs"
grep -q '^        if i == 0 { MAX_CONSTANT } else' "$work/refceil/src/ops/extra_m.rs" ||
    { echo "FAIL: could not inject the reference-ceiling defect"; ok=0; }
expect refceil "$work/refceil" 'ops/extra_m/impl_MaxBounds/k\.coma'

copy "$work/sharedimplied"
sed -i.bak 's/^        if z.is_empty() || !tighter(b, z.entry(i, j)) {$/        if z.is_empty() || !tighter(z.entry(i, j), b) {/' \
    "$work/sharedimplied/src/shared.rs"
grep -q '^        if z.is_empty() || !tighter(z.entry(i, j), b) {$' "$work/sharedimplied/src/shared.rs" ||
    { echo "FAIL: could not inject the shared implied-shortcut defect"; ok=0; }
expect sharedimplied "$work/sharedimplied" 'shared/impl_SharedDbm/try_constrain\.coma'

copy "$work/sharedsubset"
sed -i.bak 's/^        if Rc::strong_count(&self.0) > 1 && (Rc::ptr_eq(&self.0, &other.0) || z.entries_le(o)) {$/        if Rc::strong_count(\&self.0) > 1 {/' \
    "$work/sharedsubset/src/shared.rs"
grep -q '^        if Rc::strong_count(&self.0) > 1 {$' "$work/sharedsubset/src/shared.rs" ||
    { echo "FAIL: could not inject the shared subset-shortcut defect"; ok=0; }
expect sharedsubset "$work/sharedsubset" 'shared/impl_SharedDbm/try_intersect\.coma'

copy "$work/naivepast"
sed -i.bak 's/^        while i < dim {$/        while false \&\& i < dim {/' "$work/naivepast/src/ops/temporal.rs"
grep -q '^        while false && i < dim {$' "$work/naivepast/src/ops/temporal.rs" ||
    { echo "FAIL: could not inject the naive-past defect"; ok=0; }
expect naivepast "$work/naivepast" 'ops/temporal/impl_Dbm/past\.coma'

[ "$ok" -eq 1 ] && echo "negative controls: PASS" || echo "negative controls: FAIL"
[ "$ok" -eq 1 ]
