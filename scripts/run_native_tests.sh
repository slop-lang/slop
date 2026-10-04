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
run_unit_tests "lib/std/json" "json"
run_unit_tests "lib/std/xml" "xml"
run_unit_tests "tests/example-harness" "example-harness"
# The harness prescans each module again per @example: pick's Pt is beta's
# and its 'red is tint's (#174)
run_unit_tests "tests/type-resolution" "type-resolution-examples"
# The test-harness generator, covered by the mechanism it implements. Meaningful only
# alongside the negative fixture below, which independently proves the harness still
# tells a pass from a skip from a failure.
run_unit_tests "lib/compiler/tester" "tester"
# Shared C-type/identifier helpers. These @example blocks predate this entry and were
# never run by anything; the naming rules they pin (type-to-identifier, and the
# Ptr-container unwrapping) are what issues #72 and #82 turned on.
run_unit_tests "lib/compiler/common" "ctype"
# Transpiler-side pure predicates. The directory had no @example blocks at all
# until #89/#66, so nothing here was ever run; the classification rules these
# pin -- which C types are containers, which payload types need a widening cast
# before hashing -- are what those two issues turned on.
run_unit_tests "lib/compiler/transpiler" "transpiler"

# A run whose @examples fail or cannot be compiled must exit non-zero and account
# for each outcome separately. Before issue #71 was fixed an un-runnable @example
# incremented tests_passed, so a suite could read "N passed, 0 failed" having
# asserted nothing at all - which a fixture that merely passes cannot detect.
run_negative_unit_tests() {
    local dir="$1"
    local name="$2"

    if [ -d "$REPO_ROOT/$dir" ]; then
        echo -n "Testing $name (expected to fail)... "
        local output
        output=$(uv run slop test "$REPO_ROOT/$dir" 2>&1)
        local exit_code=$?
        local problem=""

        if [ $exit_code -eq 0 ]; then
            problem="expected a non-zero exit"
        elif ! echo "$output" | grep -q "0 passed, 3 failed, 2 unrunnable"; then
            problem="expected '0 passed, 3 failed, 2 unrunnable' in the summary"
        elif ! echo "$output" | grep -q "undefined function 'no-such-fixture'"; then
            problem="expected the unresolved fixture to be named"
        elif ! echo "$output" | grep -q "precondition violated: (> n 0)"; then
            problem="expected the violated @pre to be named"
        elif ! echo "$output" | grep -q "diagonal(2) -> FAIL (got <record>, expected <expected>)"; then
            problem="expected the wrong record-new field to fail (#252)"
        elif ! echo "$output" | grep -q "cannot compare the Pt result with this expected value"; then
            problem="expected the uncomparable record result to be reported (#252)"
        fi

        if [ -z "$problem" ]; then
            echo -e "${GREEN}PASS${NC}"
            PASS_COUNT=$((PASS_COUNT + 1))
        else
            echo -e "${RED}FAIL${NC} ($problem)"
            echo "$output"
            FAIL_COUNT=$((FAIL_COUNT + 1))
        fi
    fi
}

run_negative_unit_tests "tests/example-harness-negative" "example-harness-negative"

echo ""

# ============================================================
# Part 1b: Runtime C tests (tests/runtime/*.c)
# ============================================================
# The runtime header is exercised directly, under ASan and UBSan, where a
# SLOP program cannot reach: forced hash collisions, removal across the
# table's wrap-around, what a grow allocates. *_tsan.c tests run under TSan.
echo "=== Running Runtime Tests ==="
echo ""

run_runtime_test() {
    local test_file="$1"
    local test_name=$(basename "$test_file" .c)
    local exe_path="$BUILD_DIR/$test_name"

    # *_tsan.c tests are about threads, and run under ThreadSanitizer, which
    # cannot be combined with ASan
    local sanitize="-fsanitize=address,undefined -fno-sanitize-recover=undefined"
    local run_prefix=()
    case "$test_name" in
        *_tsan)
            sanitize="-fsanitize=thread -pthread"
            # TSan's shadow memory cannot cope with the high-entropy ASLR of
            # recent Linux kernels ("unexpected memory mapping"): run it
            # with randomization off
            if [ "$(uname -s)" = "Linux" ] && command -v setarch >/dev/null 2>&1; then
                run_prefix=(setarch "$(uname -m)" -R)
            fi
            ;;
        *_ubsan)
            # Under ASan the runtime keeps every arena block in malloc, and
            # ASan's allocator and shadow distort resident size: tests of
            # blocks mapped from the OS run under UBSan alone
            sanitize="-fsanitize=undefined -fno-sanitize-recover=undefined"
            ;;
    esac

    echo -n "Testing $test_name... "
    local output
    if ! output=$(cc -g -O1 $sanitize \
            -I "$RUNTIME_DIR" -o "$exe_path" "$test_file" 2>&1); then
        echo -e "${RED}FAIL (build)${NC}"
        echo "$output"
        FAIL_COUNT=$((FAIL_COUNT + 1))
        return
    fi
    if output=$("${run_prefix[@]}" "$exe_path" 2>&1); then
        echo -e "${GREEN}PASS${NC}"
        PASS_COUNT=$((PASS_COUNT + 1))
    else
        echo -e "${RED}FAIL${NC}"
        echo "$output"
        FAIL_COUNT=$((FAIL_COUNT + 1))
    fi
}

for test_file in "$REPO_ROOT"/tests/runtime/*.c; do
    if [ -f "$test_file" ]; then
        run_runtime_test "$test_file"
    fi
done
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
# Part 3: Library Tests (tests with -I flags)
# ============================================================
echo "=== Running Library Tests ==="
echo ""

run_lib_test() {
    local test_file="$1"
    local test_name="$2"
    shift 2
    local exe_path="$BUILD_DIR/$test_name"

    echo -n "Testing $test_name... "

    # Build the test with extra flags
    if ! uv run slop build "$test_file" "$@" -o "$exe_path" 2>/dev/null; then
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

run_lib_test "$REPO_ROOT/lib/std/json/tests/json_test.slop" "json" \
    -I "$REPO_ROOT/lib/std/json" -I "$REPO_ROOT/lib/std/strlib"

run_lib_test "$REPO_ROOT/lib/std/xml/tests/xml_test.slop" "xml" \
    -I "$REPO_ROOT/lib/std/xml" -I "$REPO_ROOT/lib/std/strlib"

# The same suite with contracts compiled in. xml's @post matches on $result and
# reads a field of the (Ptr Document) it binds, which is the shape that made
# --debug unbuildable for anything importing xml (#80). Contracts are no-ops in
# an ordinary build, so only this invocation covers the postcondition path.
run_lib_test "$REPO_ROOT/lib/std/xml/tests/xml_test.slop" "xml-contracts" \
    -I "$REPO_ROOT/lib/std/xml" -I "$REPO_ROOT/lib/std/strlib" --debug

# A multi-module build. Two header passes emit SLOP_LIST_DEFINE for the same type
# -- the struct-key pass and the ordinary list pass -- and ctx-is-type-emitted
# only interlocks them within one module. Across modules the #ifndef guard is all
# that is left, so the guard names have to agree. Nothing in tests/*.slop can
# reach this: it needs one module to register the type and another to import it.
run_lib_test "$REPO_ROOT/tests/struct-key-list-guard/main.slop" "struct-key-list-guard" \
    -I "$REPO_ROOT/tests/struct-key-list-guard"

# A call resolves within the calling module: its own definitions, then what it
# imports. Several modules export f and join here; before, the one registered
# last in the build won, whatever the caller imported, so each import order
# broke a different call. Both orders are built.
run_lib_test "$REPO_ROOT/tests/import-resolution/main.slop" "import-resolution" \
    -I "$REPO_ROOT/tests/import-resolution"
run_lib_test "$REPO_ROOT/tests/import-resolution/main_swapped.slop" "import-resolution-swapped" \
    -I "$REPO_ROOT/tests/import-resolution"

# A type name resolves the same way (#174): alpha and beta each define Pt,
# delta and epsilon each define Scores. Before, the transpiler used the Pt
# registered last in the build, and looked fields up by bare name, so
# (. p y) on beta's Pt could be emitted against alpha's struct and cc
# rejected it. Both import orders are built.
run_lib_test "$REPO_ROOT/tests/type-resolution/main.slop" "type-resolution-build" \
    -I "$REPO_ROOT/tests/type-resolution"
run_lib_test "$REPO_ROOT/tests/type-resolution/main_swapped.slop" "type-resolution-build-swapped" \
    -I "$REPO_ROOT/tests/type-resolution"
# Variants and aliases too: hue and tint each have a red and a dot variant,
# an Ids alias and a Res Result alias. The first registration in the build
# used to win, so one module's code named the other's enum constants and
# Result type, and a variant could take the name of a module's own function.
run_lib_test "$REPO_ROOT/tests/type-resolution/variants.slop" "type-resolution-variants" \
    -I "$REPO_ROOT/tests/type-resolution"
run_lib_test "$REPO_ROOT/tests/type-resolution/variants_swapped.slop" "type-resolution-variants-swapped" \
    -I "$REPO_ROOT/tests/type-resolution"

# A build that must fail with exactly one error: the expected message at the
# expected file:line:col. Exactly one, because a module's errors used to be
# reported again under the file name of every module transpiled after it.
run_negative_build_test() {
    local test_file="$1"
    local test_name="$2"
    local expected="$3"
    shift 3

    echo -n "Testing $test_name (expected to fail)... "
    local output
    output=$(uv run slop build "$test_file" "$@" -o "$BUILD_DIR/$test_name" 2>&1)
    local exit_code=$?
    local problem=""

    if [ $exit_code -eq 0 ]; then
        problem="expected the build to fail"
    elif ! echo "$output" | grep -qF "$expected"; then
        problem="expected: $expected"
    elif [ "$(echo "$output" | grep -c ': error:')" -ne 1 ]; then
        problem="expected exactly one error"
    fi

    if [ -z "$problem" ]; then
        echo -e "${GREEN}PASS${NC}"
        PASS_COUNT=$((PASS_COUNT + 1))
    else
        echo -e "${RED}FAIL${NC} ($problem)"
        echo "$output"
        FAIL_COUNT=$((FAIL_COUNT + 1))
    fi
}

NEG="$REPO_ROOT/tests/import-resolution-negative"
run_negative_build_test "$NEG/ambiguous.slop" "import-ambiguous" \
    "amb-mid.slop:8:17: error: 'f' is imported from both 'alpha' and 'beta'" \
    -I "$NEG" -I "$REPO_ROOT/tests/import-resolution"
run_negative_build_test "$NEG/local-and-import.slop" "import-local-and-import" \
    "local-and-import.slop:6:7: error: 'f' is defined in module 'main' and also imported from 'beta'" \
    -I "$NEG" -I "$REPO_ROOT/tests/import-resolution"
run_negative_build_test "$NEG/unimported.slop" "import-unimported" \
    "unimported.slop:9:15: error: undefined function 'f' - check imports" \
    -I "$NEG" -I "$REPO_ROOT/tests/import-resolution"

TNEG="$REPO_ROOT/tests/type-resolution-negative"
run_negative_build_test "$TNEG/both.slop" "type-import-ambiguous" \
    "both.slop:4:17: error: 'Pt' is imported from both 'alpha' and 'beta'" \
    -I "$TNEG" -I "$REPO_ROOT/tests/type-resolution"
run_negative_build_test "$TNEG/shadow.slop" "type-local-and-import" \
    "shadow.slop:3:17: error: 'Pt' is defined in module 'main' and also imported from 'beta'" \
    -I "$TNEG" -I "$REPO_ROOT/tests/type-resolution"
run_negative_build_test "$TNEG/unimported.slop" "type-unimported-ambiguous" \
    "unimported.slop:10:32: error: type 'Scores' is defined in modules 'epsilon' and 'delta' - import it from the one you mean" \
    -I "$TNEG" -I "$REPO_ROOT/tests/type-resolution"
run_negative_build_test "$TNEG/variant-both.slop" "variant-import-ambiguous" \
    "variant-both.slop:9:17: error: variant 'red' is ambiguous: imported from both 'tint' (Paint) and 'hue' (Color)" \
    -I "$TNEG" -I "$REPO_ROOT/tests/type-resolution"
run_negative_build_test "$TNEG/variant-unimported.slop" "variant-unimported-ambiguous" \
    "variant-unimported.slop:10:14: error: variant 'red' belongs to types in modules 'tint' (Paint) and 'hue' (Color) - import the type you mean" \
    -I "$TNEG" -I "$REPO_ROOT/tests/type-resolution"

# A list literal with no arena in scope was a compound literal in the
# function's own frame, so returning it dangled (#245).
run_negative_build_test "$REPO_ROOT/tests/arena-negative/list_literal_no_arena.slop" "list-literal-no-arena" \
    "list_literal_no_arena.slop:10:6: error: list: no arena in scope"
run_negative_build_test "$REPO_ROOT/tests/arena-negative/list_const_non_literal.slop" "list-const-non-literal" \
    "list_const_non_literal.slop:8:31: error: list: a module-level list literal needs literal elements"
# With two arenas in scope and none named arena, the innermost one used to
# take a literal or a closure env, so a let-bound scratch arena could take
# what the function returned (#277). It is an error; :arena names one.
run_negative_build_test "$REPO_ROOT/tests/arena-negative/list_literal_ambiguous.slop" "list-literal-ambiguous" \
    "list_literal_ambiguous.slop:9:8: error: list: 2 arenas in scope (scratch, a) and none is named arena"
run_negative_build_test "$REPO_ROOT/tests/arena-negative/closure_env_ambiguous.slop" "closure-env-ambiguous" \
    "closure_env_ambiguous.slop:13:15: error: closure env: 2 arenas in scope (scratch, a) and none is named arena"

# A closure passed to spawn captures a mut local by reference, so the thread
# read a stack slot its scope had moved on from (#193). It is an error; the
# copy the message suggests is tests/test_spawn_capture_copy.slop.
run_negative_build_test "$REPO_ROOT/tests/thread-capture-negative/spawn_mut.slop" "spawn-captures-mut" \
    "spawn_mut.slop:22:53: error: closure passed to spawn captures mutable 'part' by reference"

# A key type with no structural hash is a transpiler error. Every compound key
# but (Ptr T) used to be hashed as a String, whatever its size.
run_negative_build_test "$REPO_ROOT/tests/key-type-negative/list_key.slop" "list-key" \
    "list_key.slop:8:31: error: '(List Int)' cannot be a Map key or Set element - it has no structural hash"

# A break or continue outside any loop is a transpiler error, not one for cc.
# Inside a lambda that is the case even in a loop: its body is a C function of
# its own, so it cannot leave the loop around it (#214).
run_negative_build_test "$REPO_ROOT/tests/loop-negative/break_in_lambda.slop" "break-in-lambda" \
    "break_in_lambda.slop:14:48: error: break outside a loop"

# The checker's half of the same rule, for types, variants and re-exports.
# `slop build` drops checker diagnostics (#93), so these run `slop check`.
run_check_clean_test() {
    local test_file="$1"
    local test_name="$2"
    shift 2

    echo -n "Testing $test_name (check)... "
    local output
    output=$(uv run slop check "$test_file" "$@" 2>&1)
    local exit_code=$?

    if [ $exit_code -eq 0 ] && ! echo "$output" | grep -q ': error:'; then
        echo -e "${GREEN}PASS${NC}"
        PASS_COUNT=$((PASS_COUNT + 1))
    else
        echo -e "${RED}FAIL${NC} (expected no errors)"
        echo "$output"
        FAIL_COUNT=$((FAIL_COUNT + 1))
    fi
}

# A check that must fail with exactly one error: the expected message at the
# expected file:line:col.
run_negative_check_test() {
    local test_file="$1"
    local test_name="$2"
    local expected="$3"
    shift 3

    echo -n "Testing $test_name (check, expected to fail)... "
    local output
    output=$(uv run slop check "$test_file" "$@" 2>&1)
    local exit_code=$?
    local problem=""

    if [ $exit_code -eq 0 ]; then
        problem="expected the check to fail"
    elif ! echo "$output" | grep -qF "$expected"; then
        problem="expected: $expected"
    elif [ "$(echo "$output" | grep -c ': error:')" -ne 1 ]; then
        problem="expected exactly one error"
    fi

    if [ -z "$problem" ]; then
        echo -e "${GREEN}PASS${NC}"
        PASS_COUNT=$((PASS_COUNT + 1))
    else
        echo -e "${RED}FAIL${NC} ($problem)"
        echo "$output"
        FAIL_COUNT=$((FAIL_COUNT + 1))
    fi
}

# A check that must pass with no errors and report the expected warning.
run_check_warning_test() {
    local test_file="$1"
    local test_name="$2"
    local expected="$3"
    shift 3

    echo -n "Testing $test_name (check, expected warning)... "
    local output
    output=$(uv run slop check "$test_file" "$@" 2>&1)
    local exit_code=$?
    local problem=""

    if [ $exit_code -ne 0 ] || echo "$output" | grep -q ': error:'; then
        problem="expected no errors"
    elif ! echo "$output" | grep -qF "$expected"; then
        problem="expected: $expected"
    fi

    if [ -z "$problem" ]; then
        echo -e "${GREEN}PASS${NC}"
        PASS_COUNT=$((PASS_COUNT + 1))
    else
        echo -e "${RED}FAIL${NC} ($problem)"
        echo "$output"
        FAIL_COUNT=$((FAIL_COUNT + 1))
    fi
}

# alpha and beta each define Pt, Color and Shape. Before, the checker took
# whichever module registered a name first: beta's own Pt could be "Unknown
# type", its fields were appended to alpha's Pt, and an import could bind
# the wrong module's type. Both import orders are checked.
TRC="$REPO_ROOT/tests/type-resolution-check"
run_check_clean_test "$TRC/main.slop" "type-resolution" -I "$TRC"
run_check_clean_test "$TRC/main_swapped.slop" "type-resolution-swapped" -I "$TRC"

# An enum arm is 'red: (red) used to lower as a union variant and fail in cc (#196)
run_negative_check_test "$REPO_ROOT/tests/enum-pattern-negative/paren_arm.slop" "enum-paren-arm" \
    "paren_arm.slop:11:8: error: a match on enum 'Paint' names a variant as 'red, not (red)"
run_negative_build_test "$REPO_ROOT/tests/enum-pattern-negative/paren_arm.slop" "enum-paren-arm" \
    "paren_arm.slop:11:8: error: a match on enum 'Paint' names a variant as 'red, not (red)"

# map-len / set-len count the collection they name; the checker rejects the
# other one, and a well-typed use checks clean.
run_negative_check_test "$REPO_ROOT/tests/collection-len-negative/map_len_of_set.slop" "map-len-of-set" \
    "map_len_of_set.slop:9:9: error: map-len: expected Map, got Set"
run_check_clean_test "$REPO_ROOT/tests/test_collection_len.slop" "collection-len"
# A (Map K (Set T)) parameter's map-get payload, and a (for-each ((k v) m)) body,
# are typed by the checker; before, the one was untyped and the other unchecked.
run_check_clean_test "$REPO_ROOT/tests/test_map_get_values.slop" "map-get-values"

TRN="$REPO_ROOT/tests/type-resolution-check-negative"
run_negative_check_test "$TRN/both.slop" "type-imported-from-both" \
    "both.slop:4:17: error: 'Pt' is imported from both 'alpha' and 'beta'" \
    -I "$TRN" -I "$TRC"
run_negative_check_test "$TRN/shadow.slop" "type-defined-and-imported" \
    "shadow.slop:3:17: error: 'Pt' is defined in module 'main' and also imported from 'beta'" \
    -I "$TRN" -I "$TRC"
run_negative_check_test "$TRN/noexport.slop" "type-not-exported" \
    "noexport.slop:4:18: error: module 'alpha' does not export 'Qt'" \
    -I "$TRN" -I "$TRC"
run_negative_check_test "$TRN/notimported.slop" "type-not-imported" \
    "notimported.slop:7:14: error: type 'Pt' is defined in module 'alpha' but not imported" \
    -I "$TRN" -I "$TRC"
run_negative_check_test "$TRN/mismatch.slop" "type-module-mismatch" \
    "mismatch.slop:8:5: error: argument 1 to 'beta:show-b': expected beta:Pt, got alpha:Pt" \
    -I "$TRN" -I "$TRC"
run_negative_check_test "$TRN/nofield.slop" "type-fields-not-merged" \
    "nofield.slop:9:14: error: Record 'Pt' has no field 'y'" \
    -I "$TRN" -I "$TRC"
run_negative_check_test "$TRN/variant.slop" "variant-imported-from-both" \
    "variant.slop:8:14: error: variant 'red' is ambiguous: imported from both" \
    -I "$TRN" -I "$TRC"

echo ""

# A @generic call's return type is specialised from its arguments. The
# bindings used to be pushed onto List parameters (copies) and lost, so T was
# never replaced and anything passed through a generic call type-checked (#180).
run_negative_check_test "$REPO_ROOT/tests/generic-negative/first_or.slop" "generic-return-specialised" \
    "first_or.slop:21:9: error: argument 1 to 'string-len': expected String, got Int"

# Arithmetic operands (#264). They were inferred and thrown away, and the
# result was always Int, so (+ n "x") reached cc. A build drops checker
# diagnostics (#93), so these run `slop check` only.
ARN="$REPO_ROOT/tests/arith-negative"
while IFS='|' read -r ar_name ar_expected <&3; do
    run_negative_check_test "$ARN/$ar_name.slop" "arith-$ar_name" "$ar_expected"
done 3<<'AR_CASES'
string_operand|string_operand.slop:8:10: error: '+' needs a numeric operand: expected Int or Float, got String
bool_operand|bool_operand.slop:7:10: error: '-' needs a numeric operand: expected Int or Float, got Bool
record_operand|record_operand.slop:9:10: error: '*' needs a numeric operand: expected Int or Float, got Pt
enum_operand|enum_operand.slop:9:8: error: '+' needs a numeric operand: expected Int or Float, got Color
float_mod|float_mod.slop:7:17: error: '%' needs an integer operand: expected Int, got Float
ptr_operand|ptr_operand.slop:8:17: error: '+' does not do pointer arithmetic: got Ptr_U8; cast the pointer to Int first
AR_CASES
run_check_clean_test "$REPO_ROOT/tests/test_arith_operands.slop" "arith-operands"

# Range types (#265). A value known at compile time -- a literal, a constant,
# arithmetic on them -- is checked at every narrowing point into a range type.
# A value whose interval can never fit is a warning. A build drops checker
# diagnostics (#93), so these run `slop check` only.
RGN="$REPO_ROOT/tests/range-negative"
while IFS='|' read -r rg_name rg_expected <&3; do
    run_negative_check_test "$RGN/$rg_name.slop" "range-$rg_name" "$rg_expected"
done 3<<'RG_CASES'
arg_literal|arg_literal.slop:14:11: error: argument 1 to 'main:bump': 130 is outside Pct (Int 0 .. 100)
arg_constant|arg_constant.slop:15:11: error: argument 1 to 'main:bump': 130 is outside Pct (Int 0 .. 100)
arg_folded|arg_folded.slop:14:11: error: argument 1 to 'main:bump': 101 is outside Pct (Int 0 .. 100)
return_tail|return_tail.slop:7:5: error: return value of 'ascii': 200 is outside (Int 0 .. 127)
return_early|return_early.slop:9:29: error: return value: 101 is outside Pct (Int 0 .. 100)
typed_let|typed_let.slop:9:18: error: 'p': 150 is outside Pct (Int 0 .. 100)
set_var|set_var.slop:10:15: error: assignment: 300 is outside Pct (Int 0 .. 100)
set_field|set_field.slop:10:23: error: assignment: 0 is outside (Int 1 .. 64)
record_field|record_field.slop:9:39: error: field 'workers' of Cfg: 65 is outside (Int 1 .. 64)
positional_field|positional_field.slop:10:23: error: field 'workers' of Cfg: 0 is outside (Int 1 .. 64)
list_push|list_push.slop:10:21: error: 'list-push' element: 101 is outside Pct (Int 0 .. 100)
map_put|map_put.slop:10:22: error: 'map-put' value: 101 is outside Pct (Int 0 .. 100)
cast|cast.slop:9:24: error: cast: 101 is outside Pct (Int 0 .. 100)
constant_decl|constant_decl.slop:5:20: error: constant 'LIMIT': 130 is outside Pct (Int 0 .. 100)
symbolic_bound|symbolic_bound.slop:6:13: error: range bounds must be integer literals
empty_range|empty_range.slop:4:15: error: this range admits no value: its lower bound is above its upper bound
two_dots|two_dots.slop:4:13: error: a range type is written (Int lo .. hi), with a single ..
RG_CASES
run_check_warning_test "$RGN/always_out.slop" "range-always-out" \
    "always_out.slop:10:5: warning: return value of 'always-out': value is always outside Pct (Int 0 .. 100) (it is in [200 .. 300]); this aborts at run time"
run_check_warning_test "$RGN/unchecked_base.slop" "range-unchecked-base" \
    "unchecked_base.slop:4:13: warning: a U8 range is not enforced yet: only (Int lo .. hi) is checked"
run_check_clean_test "$REPO_ROOT/tests/test_range_static.slop" "range-static"
run_check_clean_test "$REPO_ROOT/tests/range-clean/generic_default.slop" "range-generic-default"
run_check_clean_test "$REPO_ROOT/tests/range-clean/width_into_range.slop" "range-width-into-range"
# strlib checks clean on its own: a U8 byte read passed for its Byte range was
# an error in every module importing it, and nothing checked the library itself
run_check_clean_test "$REPO_ROOT/lib/std/strlib/strlib.slop" "strlib-clean"
# Likewise common/types.slop, which every compiler module imports: #267's
# interval helpers returned Int literals as I64, an error in all of them
run_check_clean_test "$REPO_ROOT/lib/compiler/common/types.slop" "common-types-clean"

# Range checks at run time (#265 phase 2). A value only known at run time that
# is outside its range type aborts at the narrowing point, tested at int64_t
# width so it cannot wrap first. They are on in every build;
# --no-range-checks removes them.
run_runtime_abort_test() {
    local test_file="$1"
    local test_name="$2"
    local expected="$3"
    local exe_path="$BUILD_DIR/$test_name"

    echo -n "Testing $test_name (expected to abort)... "
    if ! uv run slop build "$test_file" -o "$exe_path" >/dev/null 2>&1; then
        echo -e "${RED}FAIL (build)${NC}"
        FAIL_COUNT=$((FAIL_COUNT + 1))
        return
    fi
    local output
    output=$("$exe_path" 2>&1)
    local exit_code=$?
    if [ $exit_code -ne 0 ] && echo "$output" | grep -qF "$expected"; then
        echo -e "${GREEN}PASS${NC}"
        PASS_COUNT=$((PASS_COUNT + 1))
    else
        echo -e "${RED}FAIL${NC} (exit $exit_code; expected: $expected)"
        echo "$output"
        FAIL_COUNT=$((FAIL_COUNT + 1))
    fi
}

run_range_unchecked_test() {
    local test_file="$1"
    local test_name="$2"
    local exe_path="$BUILD_DIR/$test_name"

    echo -n "Testing $test_name (--no-range-checks)... "
    if ! uv run slop build --no-range-checks "$test_file" -o "$exe_path" >/dev/null 2>&1; then
        echo -e "${RED}FAIL (build)${NC}"
        FAIL_COUNT=$((FAIL_COUNT + 1))
        return
    fi
    local output
    output=$("$exe_path" 2>&1)
    local exit_code=$?
    if [ $exit_code -eq 0 ] && ! echo "$output" | grep -q "range check failed"; then
        echo -e "${GREEN}PASS${NC}"
        PASS_COUNT=$((PASS_COUNT + 1))
    else
        echo -e "${RED}FAIL${NC} (exit $exit_code; expected the check to be compiled out)"
        echo "$output"
        FAIL_COUNT=$((FAIL_COUNT + 1))
    fi
}

# Transpile and count a pattern in the generated C.
run_codegen_count_test() {
    local test_file="$1"
    local test_name="$2"
    local pattern="$3"
    local expected="$4"
    local c_path="$BUILD_DIR/$test_name.c"

    echo -n "Testing $test_name (codegen)... "
    if ! uv run slop transpile "$test_file" -o "$c_path" >/dev/null 2>&1; then
        echo -e "${RED}FAIL (transpile)${NC}"
        FAIL_COUNT=$((FAIL_COUNT + 1))
        return
    fi
    local count
    count=$(grep -c "$pattern" "$c_path")
    if [ "$count" -eq "$expected" ]; then
        echo -e "${GREEN}PASS${NC}"
        PASS_COUNT=$((PASS_COUNT + 1))
    else
        echo -e "${RED}FAIL${NC} (expected $expected '$pattern', found $count)"
        grep -n "$pattern" "$c_path"
        FAIL_COUNT=$((FAIL_COUNT + 1))
    fi
}

RGR="$REPO_ROOT/tests/range-runtime"
while IFS='|' read -r rr_name rr_expected <&3; do
    run_runtime_abort_test "$RGR/$rr_name.slop" "range-runtime-$rr_name" "$rr_expected"
done 3<<'RR_CASES'
arg|SLOP range check failed: 300 is not in Pct (Int 0 .. 100) at arg.slop:17:11
ret|SLOP range check failed: 130 is not in Pct (Int 0 .. 100) at ret.slop:10:5
wrap|SLOP range check failed: 300 is not in Byte (Int 0 .. 255) at wrap.slop:12:19
set_var|SLOP range check failed: 150 is not in Pct (Int 0 .. 100) at set_var.slop:13:15
set_field|SLOP range check failed: 0 is not in (Int 1 .. 64) at set_field.slop:13:23
record|SLOP range check failed: 65 is not in (Int 1 .. 64) at record.slop:12:39
list_push|SLOP range check failed: 101 is not in Pct (Int 0 .. 100) at list_push.slop:14:23
map_put|SLOP range check failed: 101 is not in (Int 0 .. 100) at map_put.slop:14:24
cast|SLOP range check failed: -1 is not in Pct (Int 0 .. 100) at cast.slop:12:24
early_return|SLOP range check failed: 500 is not in Pct (Int 0 .. 100) at early_return.slop:12:29
lower_only|SLOP range check failed: 0 is not in (Int 1 ..) at lower_only.slop:15:15
RR_CASES
run_range_unchecked_test "$RGR/wrap.slop" "range-unchecked-wrap"
# A multi-module build drops checker diagnostics (#93), so the transpiler
# reports an out-of-range literal itself.
run_negative_build_test "$REPO_ROOT/tests/range-build-negative/main.slop" "range-build-literal" \
    "main.slop:11:11: error: argument 1 to 'bump': 130 is outside Pct (Int 0 .. 100)" \
    -I "$REPO_ROOT/tests/range-build-negative"
# Checks the checker proves unnecessary are not emitted
run_codegen_count_test "$REPO_ROOT/tests/range-codegen/proved.slop" "range-proved" "SLOP_RANGE" 1

echo ""

# A collection grows in the arena it was made in, and a spawned closure's env
# goes in spawn's arena (#276). Each program frees the arena that used to be
# chosen before reading what was put there, so these build under ASan, where
# the old placement is a use after free.
run_asan_integration_test() {
    local test_file="$1"
    local test_name="$2"
    local exe_path="$BUILD_DIR/$test_name"

    echo -n "Testing $test_name (ASan)... "
    if ! SLOP_CFLAGS="-fsanitize=address,undefined -fno-sanitize-recover=undefined -g" \
            uv run slop build "$test_file" -o "$exe_path" >/dev/null 2>&1; then
        echo -e "${RED}FAIL (build)${NC}"
        FAIL_COUNT=$((FAIL_COUNT + 1))
        return
    fi
    local output
    if output=$("$exe_path" 2>&1); then
        echo -e "${GREEN}PASS${NC}"
        PASS_COUNT=$((PASS_COUNT + 1))
    else
        echo -e "${RED}FAIL${NC}"
        echo "$output"
        FAIL_COUNT=$((FAIL_COUNT + 1))
    fi
}

AOWN="$REPO_ROOT/tests/arena-own"
run_asan_integration_test "$AOWN/collections.slop" "arena-own-collections"
run_asan_integration_test "$AOWN/spawn_env.slop" "arena-own-spawn-env"
run_asan_integration_test "$AOWN/push_no_arena_in_scope.slop" "arena-own-push-no-arena-in-scope"
run_runtime_abort_test "$AOWN/const_push.slop" "arena-own-const-push" \
    "SLOP: list-push on a list with no arena (zero-initialized, or a copy of a module constant)"
AONEG="$REPO_ROOT/tests/arena-own-negative"
while IFS='|' read -r ao_name ao_expected <&3; do
    run_negative_check_test "$AONEG/$ao_name.slop" "arena-option-$ao_name" "$ao_expected"
    run_negative_build_test "$AONEG/$ao_name.slop" "arena-option-$ao_name" "$ao_expected"
done 3<<'AO_CASES'
not_arena|not_arena.slop:9:32: error: 'list-push' :arena: expected Arena, got Int
missing_arena|missing_arena.slop:9:9: error: 'map-put' :arena needs exactly one arena after it
unknown_option|unknown_option.slop:9:9: error: 'set-put' has no option :in; the only one is :arena
AO_CASES

echo ""


# Parameter modes (#180). An unmarked parameter's own value is read-only, a
# mut parameter is a local copy of a value type, and out is gone. The checker
# and the transpiler both enforce it, with the same message, since a build
# drops checker diagnostics (#93): each case runs through both.
PMN="$REPO_ROOT/tests/param-modes-negative"
while IFS='|' read -r pm_name pm_expected <&3; do
    run_negative_check_test "$PMN/$pm_name.slop" "param-mode-$pm_name" "$pm_expected"
    run_negative_build_test "$PMN/$pm_name.slop" "param-mode-$pm_name" "$pm_expected"
done 3<<'PM_CASES'
assign_param|assign_param.slop:11:11: error: cannot assign to parameter 'n' - it is read-only; declare it (mut n T) to modify a local copy, or pass a (Ptr T) to change the caller's value
assign_ptr_param|assign_ptr_param.slop:11:11: error: cannot assign to parameter 'p' - it is read-only; declare it (mut p T) to modify a local copy, or pass a (Ptr T) to change the caller's value
field_set|field_set.slop:11:11: error: cannot change a field of parameter 'b' - it is read-only; declare it (mut b T) to modify a local copy, or pass a (Ptr T) to change the caller's value
field_set_dot|field_set_dot.slop:11:11: error: cannot change a field of parameter 'b' - it is read-only; declare it (mut b T) to modify a local copy, or pass a (Ptr T) to change the caller's value
field_set_dotted|field_set_dotted.slop:11:11: error: cannot change a field of parameter 'b' - it is read-only; declare it (mut b T) to modify a local copy, or pass a (Ptr T) to change the caller's value
field_set_typed|field_set_typed.slop:11:11: error: cannot change a field of parameter 'b' - it is read-only; declare it (mut b T) to modify a local copy, or pass a (Ptr T) to change the caller's value
mut_list|mut_list.slop:8:15: error: 'mut' is not allowed on parameter 'xs' - a copy of a List, Map or Set shares the caller's storage; use (Ptr (List T)) to change the caller's list
mut_map_alias|mut_map_alias.slop:8:15: error: 'mut' is not allowed on parameter 'm' - a copy of a List, Map or Set shares the caller's storage; use (Ptr (List T)) to change the caller's list
mut_set|mut_set.slop:8:15: error: 'mut' is not allowed on parameter 's' - a copy of a List, Map or Set shares the caller's storage; use (Ptr (List T)) to change the caller's list
out_param|out_param.slop:8:15: error: 'out' parameter 'r' is not supported - use a (Ptr T) parameter and pass (addr x)
pop_param|pop_param.slop:11:15: error: cannot pop from parameter 'xs' - it is read-only, and a change to a copy is lost to the caller; pass a (Ptr (List T)) and use (deref xs), or return the new list
push_field|push_field.slop:11:16: error: cannot push to a field of parameter 'b' - it is read-only, and a change to a copy is lost to the caller; declare it (mut b T) and return it, or pass a (Ptr T)
push_param|push_param.slop:11:16: error: cannot push to parameter 'xs' - it is read-only, and a change to a copy is lost to the caller; pass a (Ptr (List T)) and use (deref xs), or return the new list
ref_param|ref_param.slop:8:15: error: unknown parameter mode 'ref' - write (name Type) or (mut name Type)
set_expr|set_expr.slop:11:24: error: cannot assign to parameter 'n' - it is read-only; declare it (mut n T) to modify a local copy, or pass a (Ptr T) to change the caller's value
PM_CASES
run_check_clean_test "$REPO_ROOT/tests/test_param_modes.slop" "param-modes"
# A Map or Set alias is the type it names: an inferred (Map String Int) passes
# where Ids is expected (#197). The build ignores that checker error, so only
# the check catches it.
run_check_clean_test "$REPO_ROOT/tests/test_map_alias_param.slop" "map-alias-param"
run_check_clean_test "$REPO_ROOT/tests/test_mutation_allowed.slop" "mutation-allowed"

# Immutable bindings (#180): a let without mut, a for / for-each / match /
# with-arena name, and a constant cannot be set!, in check and build alike.
# Pushing onto a local's own list stays allowed (tests/test_mutation_allowed).
LMN="$REPO_ROOT/tests/let-mutability-negative"
while IFS='|' read -r lm_name lm_expected <&3; do
    run_negative_check_test "$LMN/$lm_name.slop" "binding-$lm_name" "$lm_expected"
    run_negative_build_test "$LMN/$lm_name.slop" "binding-$lm_name" "$lm_expected"
done 3<<'LM_CASES'
const_reassign|const_reassign.slop:10:15: error: cannot assign to constant 'LIMIT'
for_each_field_set|for_each_field_set.slop:10:104: error: cannot change a field of 'p' - names bound by for, for-each, match and with-arena are immutable; copy it into (let ((mut p ...)))
for_reassign|for_reassign.slop:10:45: error: cannot assign to 'i' - names bound by for, for-each, match and with-arena are immutable; copy it into (let ((mut i ...)))
let_field_set|let_field_set.slop:10:31: error: cannot change a field of 'p' - it is immutable; declare it (let ((mut p ...)))
let_reassign|let_reassign.slop:10:24: error: cannot assign to 'x' - it is immutable; declare it (let ((mut x ...)))
match_reassign|match_reassign.slop:10:37: error: cannot assign to 'v' - names bound by for, for-each, match and with-arena are immutable; copy it into (let ((mut v ...)))
LM_CASES

# A program that must abort with the expected message on stderr, built with
# extra cc flags. Its exit code alone would not do: a run that carried on
# past the failure can exit non-zero too.
run_abort_test() {
    local test_file="$1"
    local test_name="$2"
    local cflags="$3"
    local expected="$4"

    echo -n "Testing $test_name (expected to abort)... "
    if ! SLOP_CFLAGS="$cflags" uv run slop build "$test_file" -o "$BUILD_DIR/$test_name" >/dev/null 2>&1; then
        echo -e "${RED}FAIL (build)${NC}"
        FAIL_COUNT=$((FAIL_COUNT + 1))
        return
    fi
    local output
    output=$("$BUILD_DIR/$test_name" 2>&1)
    local exit_code=$?

    if [ $exit_code -ne 0 ] && echo "$output" | grep -qF "$expected" \
            && ! echo "$output" | grep -qF "spawn returned"; then
        echo -e "${GREEN}PASS${NC}"
        PASS_COUNT=$((PASS_COUNT + 1))
    else
        echo -e "${RED}FAIL${NC} (exit $exit_code; expected: $expected)"
        echo "$output"
        FAIL_COUNT=$((FAIL_COUNT + 1))
    fi
}

# spawn when the thread cannot start (#192): failing_create.h makes every
# pthread_create fail. Before, spawn ignored the error and join waited on an
# unset thread id and returned an unwritten result. Both spawn lowerings are
# covered: the inline one for a capturing closure, and the thread library's.
SPF="$REPO_ROOT/tests/spawn-failure"
for spf in closure function; do
    run_abort_test "$SPF/$spf.slop" "spawn-failure-$spf" "-include $SPF/failing_create.h" \
        "SLOP: spawn: cannot start a thread"
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
