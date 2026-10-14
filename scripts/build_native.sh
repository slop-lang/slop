#!/bin/sh

## Build the native slop toolchain from SLOP source.
##
## This is a self-hosting rebuild: it uses the SLOP compiler that is already
## installed in bin/ to recompile the toolchain from lib/compiler/*.slop and
## writes the fresh binaries back into bin/.
##
## On a clean checkout there is no compiler to self-host with yet. Run
## `make install` first (builds the C-bootstrap snapshot into bin/), then
## `make build-native` to rebuild from current SLOP source.
##
## Runtime ABI (#360): a compiler's output is checked, at C compile time,
## against the SLOP_RUNTIME_ABI of the slop_runtime.h it is compiled with.
## The compiler in bin/ generates for the ABI of the source it was built
## from, which across an ABI bump is the previous one, so its output is
## compiled against the runtime header of that ABI (bootstrap/runtime, the
## snapshot it was itself built with). The compiler that comes out of that
## pass generates for the current ABI, and a second pass rebuilds everything
## against the current runtime. With no bump in flight the two headers agree
## and one pass is made.

set -e

# Resolve the repository root from this script's location so the build works
# regardless of the directory it is invoked from.
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="$ROOT/bin"
CURRENT_RUNTIME="$ROOT/src/slop/runtime"
BOOTSTRAP_RUNTIME="$ROOT/bootstrap/runtime"

if [ ! -x "$BIN/slop-compiler" ]; then
    echo "Error: native compiler not found at $BIN/slop-compiler" >&2
    echo "Run 'make install' first to install the bootstrap toolchain." >&2
    exit 1
fi

mkdir -p "$BIN"

# Optional optimization level for the C backend. Release builds set SLOP_OPT=3;
# the default leaves `slop build` on its own default (-O2).
OPT_FLAG=""
if [ -n "${SLOP_OPT:-}" ]; then
    OPT_FLAG="-O ${SLOP_OPT}"
fi

# The ABI number in a runtime header; empty when the header predates ABI
# versioning
header_abi() {
    sed -n 's/^#define SLOP_RUNTIME_ABI \([0-9][0-9]*\).*/\1/p' "$1/slop_runtime.h"
}

# The ABI the compiler in bin/ generates code for: what it reports, or, for a
# compiler from before it could report it, the number it writes into the
# check in every header it emits; empty when it predates ABI versioning
compiler_abi() {
    abi=$("$BIN/slop-compiler" --runtime-abi 2>/dev/null || true)
    case "$abi" in
        *[!0-9]*|"") ;;
        *) echo "$abi"; return ;;
    esac
    probe=$(mktemp -d)
    printf '(module probe\n  (fn probe-one ()\n    (@intent "A module to read the ABI check from")\n    (@spec (() -> Int))\n    1))\n' > "$probe/probe.slop"
    "$BIN/slop-compiler" transpile "$probe/probe.slop" 2>/dev/null \
        | sed -n 's/.*#elif SLOP_RUNTIME_ABI != \([0-9][0-9]*\).*/\1/p' | head -1
    rm -rf "$probe"
}

# build_pass <runtime dir>: build each tool from SLOP source with the compiler
# in bin/, compiling its output against that runtime, and move the result
# into bin/. Only the merged slop-compiler is built (it subsumes the
# transpiler modules).
build_pass() {
    for tool in parser checker tester compiler; do
        echo "Building slop-$tool..."
        cd "$ROOT/lib/compiler/$tool"
        SLOP_RUNTIME_DIR="$1" uv run slop build $OPT_FLAG
        mv "./slop-$tool" "$BIN/slop-$tool"
    done
}

compiler=$(compiler_abi)
current=$(header_abi "$CURRENT_RUNTIME")
bootstrap=$(header_abi "$BOOTSTRAP_RUNTIME")

if [ "$compiler" = "$current" ]; then
    build_pass "$CURRENT_RUNTIME"
elif [ "$compiler" = "$bootstrap" ]; then
    echo "The compiler in bin/ generates for runtime ABI ${compiler:-(unversioned)}; the current runtime is ABI $current."
    echo "Pass 1: building against bootstrap/runtime (ABI ${bootstrap:-(unversioned)})..."
    build_pass "$BOOTSTRAP_RUNTIME"
    echo ""
    echo "Pass 2: rebuilding with that compiler against the current runtime (ABI $current)..."
    build_pass "$CURRENT_RUNTIME"
else
    echo "Error: the compiler in bin/ generates for runtime ABI ${compiler:-(unversioned)}, but neither" >&2
    echo "src/slop/runtime (ABI ${current:-(unversioned)}) nor bootstrap/runtime (ABI ${bootstrap:-(unversioned)}) is that ABI." >&2
    echo "Run 'make install' to start again from the bootstrap snapshot." >&2
    exit 1
fi

echo "Native toolchain built in $BIN/"
