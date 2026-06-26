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

set -e

# Resolve the repository root from this script's location so the build works
# regardless of the directory it is invoked from.
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="$ROOT/bin"

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

# Build each tool from SLOP source and move the result into bin/.
# Only the merged slop-compiler is built (it subsumes the transpiler modules).
for tool in parser checker tester compiler; do
    echo "Building slop-$tool..."
    cd "$ROOT/lib/compiler/$tool"
    uv run slop build $OPT_FLAG
    mv "./slop-$tool" "$BIN/slop-$tool"
done

echo "Native toolchain built in $BIN/"
