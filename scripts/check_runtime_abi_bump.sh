#!/bin/sh
# A change to slop_runtime.h either bumps SLOP_RUNTIME_ABI or declares that
# it does not need to (#360). The generated-code check is equality, so a
# bump orphans every previously generated C file until it is regenerated,
# and a missed bump compiles old generated C against a runtime it was not
# generated for. Neither mistake is visible in the diff, so this check
# makes the author say which it is.
#
#   scripts/check_runtime_abi_bump.sh [base-ref]      (default origin/main)
#
# Passes when, against the base ref, the header is unchanged; or the ABI
# number went up (YYYYNN, six digits, NN in 01..99, never backwards); or the
# header changed at the same number and $ABI_NOTE (CI passes the pull
# request body) has a line starting `ABI: unchanged`, ideally followed by
# why. $SLOP_RUNTIME_HEADER points the check at another copy of the header
# (the test suite uses it).

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
HEADER_PATH="src/slop/runtime/slop_runtime.h"
HEADER="${SLOP_RUNTIME_HEADER:-$ROOT/$HEADER_PATH}"
BASE="${1:-origin/main}"

fail() {
    echo "check_runtime_abi_bump: $1" >&2
    exit 1
}

abi_of() {
    sed -n 's/^#define SLOP_RUNTIME_ABI \([0-9][0-9]*\).*/\1/p' "$1"
}

[ -f "$HEADER" ] || fail "no header at $HEADER"

base_header="$(mktemp)"
trap 'rm -f "$base_header"' EXIT
if ! git -C "$ROOT" show "$BASE:$HEADER_PATH" > "$base_header" 2>/dev/null; then
    fail "cannot read $HEADER_PATH at $BASE (fetch it, or pass the base ref)"
fi

if cmp -s "$base_header" "$HEADER"; then
    echo "slop_runtime.h unchanged from $BASE"
    exit 0
fi

base_abi=$(abi_of "$base_header")
new_abi=$(abi_of "$HEADER")
[ -n "$base_abi" ] || fail "no '#define SLOP_RUNTIME_ABI <n>' in $HEADER_PATH at $BASE"
[ -n "$new_abi" ] || fail "slop_runtime.h changed and lost its '#define SLOP_RUNTIME_ABI <n>'"

declared_unchanged=false
if printf '%s\n' "${ABI_NOTE:-}" | grep -iqE '^[[:space:]]*ABI:[[:space:]]*unchanged'; then
    declared_unchanged=true
fi

if [ "$new_abi" = "$base_abi" ]; then
    if $declared_unchanged; then
        echo "slop_runtime.h changed; ABI stays $((base_abi / 100))-$((base_abi % 100)) ($base_abi), declared unchanged"
        exit 0
    fi
    fail "slop_runtime.h changed but SLOP_RUNTIME_ABI is still $base_abi.
  If generated code can observe the change (a runtime struct's layout, the
  signature or semantics of a function or macro it calls, what a
  SLOP_*_DEFINE macro expands to), bump SLOP_RUNTIME_ABI and RUNTIME_ABI in
  lib/compiler/transpiler/transpiler.slop; the procedure is in the comment
  above the define.
  If it cannot (a new function or macro, a comment, an attribute, a
  portability shim), add a line to the pull request body:
    ABI: unchanged, <why generated code cannot tell>"
fi

if $declared_unchanged; then
    fail "SLOP_RUNTIME_ABI went from $base_abi to $new_abi but the pull request says 'ABI: unchanged'; one of them is wrong"
fi
case "$new_abi" in
    [0-9][0-9][0-9][0-9][0-9][0-9]) ;;
    *) fail "SLOP_RUNTIME_ABI $new_abi is not YYYYNN (six digits, 202601 is ABI 2026-1)" ;;
esac
new_nn=$((new_abi % 100))
[ "$new_nn" -ge 1 ] || fail "SLOP_RUNTIME_ABI $new_abi: the counter NN runs from 01 (202601 is ABI 2026-1)"
[ "$new_abi" -gt "$base_abi" ] || fail "SLOP_RUNTIME_ABI went from $base_abi to $new_abi; the ABI number never goes backwards"

echo "slop_runtime.h changed; ABI $((base_abi / 100))-$((base_abi % 100)) ($base_abi) -> $((new_abi / 100))-$((new_abi % 100)) ($new_abi)"
