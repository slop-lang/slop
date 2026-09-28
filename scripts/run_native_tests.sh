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
        elif ! echo "$output" | grep -q "0 passed, 2 failed, 1 unrunnable"; then
            problem="expected '0 passed, 2 failed, 1 unrunnable' in the summary"
        elif ! echo "$output" | grep -q "undefined function 'no-such-fixture'"; then
            problem="expected the unresolved fixture to be named"
        elif ! echo "$output" | grep -q "precondition violated: (> n 0)"; then
            problem="expected the violated @pre to be named"
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

# list-push grows its list in an arena; with none in scope it used to emit the
# bare identifier `arena`, which only the C compiler caught (#179).
run_negative_build_test "$REPO_ROOT/tests/arena-negative/list_push_no_arena.slop" "list-push-no-arena" \
    "list_push_no_arena.slop:9:6: error: list-push: no arena in scope"

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
