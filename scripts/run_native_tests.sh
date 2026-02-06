#!/bin/bash
# Native SLOP Compiler Test Runner
# Runs @example unit tests and integration tests using native toolchain

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BUILD_DIR="$REPO_ROOT/build/test"
RUNTIME_DIR="$REPO_ROOT/src/slop/runtime"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

PASS_COUNT=0
FAIL_COUNT=0
SKIP_COUNT=0

mkdir -p "$BUILD_DIR"

echo "=== SLOP Native Test Runner ==="
echo ""

# ============================================================
# Part 1: Unit Tests (@example annotations)
# ============================================================
echo "=== Running @example Unit Tests ==="
echo ""

run_unit_tests() {
    local dir="$1"
    local name="$2"

    if [ -d "$REPO_ROOT/$dir" ]; then
        echo -n "Testing $name... "
        local output
        output=$(uv run slop test "$REPO_ROOT/$dir" 2>&1)
        local exit_code=$?

        if [ $exit_code -eq 0 ]; then
            echo -e "${GREEN}PASS${NC}"
            PASS_COUNT=$((PASS_COUNT + 1))
        else
            # Check if it's a "no tests found" situation (single file with no @example)
            if echo "$output" | grep -q "No @example annotations found"; then
                echo -e "${YELLOW}SKIP (no @example)${NC}"
                SKIP_COUNT=$((SKIP_COUNT + 1))
            else
                echo -e "${RED}FAIL${NC}"
                FAIL_COUNT=$((FAIL_COUNT + 1))
            fi
        fi
    fi
}

# Run unit tests on lib directories
run_unit_tests "lib/std/strlib" "strlib"
run_unit_tests "lib/std/math" "mathlib"
run_unit_tests "lib/std/io" "io"
run_unit_tests "lib/std/os" "os"
run_unit_tests "lib/std/path" "path"

echo ""

# ============================================================
# Part 2: Integration Tests (tests/*.slop)
# ============================================================
echo "=== Running Integration Tests ==="
echo ""

run_integration_test() {
    local test_file="$1"
    local test_name=$(basename "$test_file" .slop)
    local exe_path="$BUILD_DIR/$test_name"

    echo -n "Testing $test_name... "

    # Build the test
    if ! uv run slop build "$test_file" -o "$exe_path" 2>/dev/null; then
        echo -e "${RED}FAIL (build)${NC}"
        FAIL_COUNT=$((FAIL_COUNT + 1))
        return
    fi

    # Run the test
    if "$exe_path" >/dev/null 2>&1; then
        echo -e "${GREEN}PASS${NC}"
        PASS_COUNT=$((PASS_COUNT + 1))
    else
        echo -e "${RED}FAIL (exit $?)${NC}"
        FAIL_COUNT=$((FAIL_COUNT + 1))
    fi
}

# Run each integration test
for test_file in "$REPO_ROOT"/tests/*.slop; do
    if [ -f "$test_file" ]; then
        run_integration_test "$test_file"
    fi
done

# ============================================================
# Cleanup and Summary
# ============================================================
echo ""
rm -rf "$BUILD_DIR"

echo "=== Results ==="
echo "Passed:  $PASS_COUNT"
echo "Failed:  $FAIL_COUNT"
echo "Skipped: $SKIP_COUNT"

if [ $FAIL_COUNT -gt 0 ]; then
    echo ""
    echo -e "${RED}$FAIL_COUNT test(s) failed${NC}"
    exit 1
else
    echo ""
    echo -e "${GREEN}All tests passed${NC}"
    exit 0
fi
