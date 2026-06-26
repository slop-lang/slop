#!/bin/sh

## Two-stage self-hosting build of the SLOP toolchain.
##
## The Python transpiler is no longer maintained; the committed bootstrap C
## files under bootstrap/ are the cold-start recovery snapshot. This script
## rebuilds the toolchain entirely from current SLOP source:
##
##   1. make install      cold-start: compile bootstrap C -> bin/ (bootstrap compiler)
##   2. build_native.sh   pass 1: bootstrap compiler recompiles latest lib/compiler/*.slop
##   3. build_native.sh   pass 2: the just-built compiler rebuilds latest -> fixed point
##
## Set SLOP_OPT to pass an optimization level to the C backend (release uses 3).

set -e

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

echo "== Stage 0: cold-start from bootstrap C =="
make -C "$ROOT" install

echo ""
echo "== Stage 1: rebuild from SLOP source with the bootstrap compiler =="
"$ROOT/scripts/build_native.sh"

echo ""
echo "== Stage 2: self-host rebuild with the freshly built compiler =="
"$ROOT/scripts/build_native.sh"

echo ""
echo "Self-hosted toolchain built in $ROOT/bin/"
ls -la "$ROOT/bin/"
