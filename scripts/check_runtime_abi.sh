#!/bin/sh
# The runtime ABI number lives in two places (#360): SLOP_RUNTIME_ABI in
# src/slop/runtime/slop_runtime.h, which generated code is checked against,
# and RUNTIME_ABI in lib/compiler/transpiler/transpiler.slop, which the
# transpiler writes into that check. They must be the same number, YYYYNN
# (202601 is ABI 2026-1).

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
HEADER="$ROOT/src/slop/runtime/slop_runtime.h"
TRANSPILER="$ROOT/lib/compiler/transpiler/transpiler.slop"

header_abi=$(sed -n 's/^#define SLOP_RUNTIME_ABI \([0-9][0-9]*\).*/\1/p' "$HEADER")
transpiler_abi=$(sed -n 's/^  (const RUNTIME_ABI Int \([0-9][0-9]*\)).*/\1/p' "$TRANSPILER")

if [ -z "$header_abi" ]; then
    echo "check_runtime_abi: no '#define SLOP_RUNTIME_ABI <n>' in $HEADER" >&2
    exit 1
fi
if [ -z "$transpiler_abi" ]; then
    echo "check_runtime_abi: no '(const RUNTIME_ABI Int <n>)' in $TRANSPILER" >&2
    exit 1
fi
if [ "$header_abi" != "$transpiler_abi" ]; then
    echo "check_runtime_abi: slop_runtime.h is ABI $header_abi but the transpiler generates for ABI $transpiler_abi" >&2
    exit 1
fi
echo "runtime ABI $((header_abi / 100))-$((header_abi % 100)) ($header_abi)"
