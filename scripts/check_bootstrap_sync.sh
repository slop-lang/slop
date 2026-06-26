#!/bin/sh

## Verify the committed bootstrap C is in sync with current SLOP source.
##
## Regenerates the bootstrap C from lib/compiler/*.slop using the *native*
## compiler (bin/slop-compiler) and fails if the result differs from what is
## committed under bootstrap/. This guards against editing SLOP source without
## running `make bootstrap-update`, which would silently ship a stale toolchain.
##
## When the toolchain in bin/ is the self-hosted one, a clean diff here also
## proves the compiler is a fixed point: it regenerates the very C that builds
## it. Requires a working bin/slop-compiler (run scripts/selfhost.sh first).

set -e

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

echo "Regenerating bootstrap C from SLOP source..."
make -C "$ROOT" bootstrap-update

echo ""
echo "Checking for drift against committed bootstrap/ ..."
if ! git -C "$ROOT" diff --exit-code -- bootstrap/; then
    echo ""
    echo "ERROR: bootstrap C is out of sync with SLOP source." >&2
    echo "Run 'make bootstrap-update' and commit the result." >&2
    exit 1
fi

echo "Bootstrap C is in sync with SLOP source."
