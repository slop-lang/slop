#!/bin/bash
# update_bootstrap.sh - Regenerate bootstrap C files from SLOP source
#
# This script uses slop's module resolution to determine the correct build
# order, then calls the native transpiler to generate C files.
#
# Structure:
#   bootstrap/
#     runtime/     - Shared runtime header
#     parser/      - All parser .h and .c files
#     checker/     - All checker .h and .c files
#     transpiler/  - All transpiler .h and .c files
#     tester/      - All tester .h and .c files
#
# Prerequisites:
#   - Working native SLOP toolchain (bin/slop-transpiler)
#   - Python 3 with slop package available

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Check that transpiler exists
if [ ! -x "$PROJECT_ROOT/bin/slop-transpiler" ]; then
    echo "Error: Native transpiler not found at $PROJECT_ROOT/bin/slop-transpiler"
    echo "Build the native toolchain first with: ./build_native.sh"
    exit 1
fi

# Create directories
mkdir -p "$SCRIPT_DIR/runtime"
mkdir -p "$SCRIPT_DIR/parser"
mkdir -p "$SCRIPT_DIR/checker"
mkdir -p "$SCRIPT_DIR/transpiler"
mkdir -p "$SCRIPT_DIR/tester"

echo "Updating bootstrap C files..."
echo ""

# Generate C files for each tool using slop's module resolution
echo "Transpiling parser..."
uv run python "$SCRIPT_DIR/generate_c.py" "$PROJECT_ROOT/lib/compiler/parser" "$SCRIPT_DIR/parser"

echo "Transpiling checker..."
uv run python "$SCRIPT_DIR/generate_c.py" "$PROJECT_ROOT/lib/compiler/checker" "$SCRIPT_DIR/checker"

echo "Transpiling transpiler..."
uv run python "$SCRIPT_DIR/generate_c.py" "$PROJECT_ROOT/lib/compiler/transpiler" "$SCRIPT_DIR/transpiler"

echo "Transpiling tester..."
uv run python "$SCRIPT_DIR/generate_c.py" "$PROJECT_ROOT/lib/compiler/tester" "$SCRIPT_DIR/tester"

# Copy runtime header
echo ""
echo "Copying runtime header..."
cp "$PROJECT_ROOT/src/slop/runtime/slop_runtime.h" "$SCRIPT_DIR/runtime/"

echo ""
echo "Bootstrap files updated successfully!"
echo "To build from bootstrap: cd bootstrap && make"
