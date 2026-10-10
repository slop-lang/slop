#!/usr/bin/env bash
# Windows test run, for the windows CI job (MSYS2 bash). It covers what
# make test-native covers that needs no sanitizers, no POSIX-only header and
# no self-hosted rebuild:
#   - the std modules' @example tests
#   - every integration test (tests/*.slop), built and run through the CLI
#   - the runtime C tests that are portable
#   - with --clang-cl, the C of the std modules a Rust -sys crate vendors,
#     compiled by clang-cl the way cc-rs compiles it for the MSVC target
#
# CC picks the C compiler, as it does for the CLI. The native tools must
# already be in bin/ and the CLI installed (uv sync).

set -u

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# A Windows path (D:/a/...) where MSYS2 has one, so native programs get the
# same paths bash uses
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && (pwd -W 2>/dev/null || pwd))"
BUILD_DIR="$REPO_ROOT/build/windows-test"
RUNTIME_DIR="$REPO_ROOT/src/slop/runtime"
CC="${CC:-gcc}"

PASS_COUNT=0
FAIL_COUNT=0
SKIP_COUNT=0

mkdir -p "$BUILD_DIR"

pass() {
    echo "PASS"
    PASS_COUNT=$((PASS_COUNT + 1))
}

# fail <reason> [output]
fail() {
    echo "FAIL $1"
    if [ -n "${2:-}" ]; then echo "$2"; fi
    FAIL_COUNT=$((FAIL_COUNT + 1))
}

echo "=== SLOP Windows Test Runner (CC=$CC) ==="
echo ""

echo "=== std @example tests ==="
for m in strlib math io os path json xml; do
    echo -n "slop test lib/std/$m... "
    if out=$(uv run slop test "$REPO_ROOT/lib/std/$m" 2>&1); then
        pass
    elif echo "$out" | grep -q "No @example annotations found"; then
        echo "SKIP (no @example)"
        SKIP_COUNT=$((SKIP_COUNT + 1))
    else
        fail "" "$out"
    fi
done
echo ""

# test_map needs fork, the *_tsan arena/map tests use pthreads directly and
# test_arena_release_ubsan reads resident size through Mach or /proc
echo "=== Runtime C tests ==="
for t in test_list test_shared_global test_intern_threads_tsan; do
    src="$REPO_ROOT/tests/runtime/$t.c"
    srcs=("$src")
    if [ -d "${src%.c}" ]; then
        srcs+=("${src%.c}"/*.c)
    fi
    echo -n "$t... "
    if ! out=$("$CC" -O1 -I "$RUNTIME_DIR" -o "$BUILD_DIR/$t.exe" "${srcs[@]}" 2>&1); then
        fail "(build)" "$out"
        continue
    fi
    if out=$("$BUILD_DIR/$t.exe" 2>&1); then
        pass
    else
        fail "(exit $?)" "$out"
    fi
done
echo ""

echo "=== Integration tests ==="
for test_file in "$REPO_ROOT"/tests/*.slop; do
    name=$(basename "$test_file" .slop)
    echo -n "$name... "
    if ! out=$(uv run slop build "$test_file" -o "$BUILD_DIR/$name" 2>&1); then
        fail "(build)" "$out"
        continue
    fi
    if out=$("$BUILD_DIR/$name.exe" 2>&1); then
        pass
    else
        fail "(exit $?)" "$out"
    fi
done
echo ""

if [ "${1:-}" = "--clang-cl" ]; then
    # The modules slop-std-sys vendors, each its own translation unit, with
    # the defines the -sys crates build with
    echo "=== std module C under clang-cl ==="
    CL_DIR="$BUILD_DIR/clang-cl"
    mkdir -p "$CL_DIR"
    for m in strlib/strlib io/file thread/thread os/env; do
        name=$(basename "$m")
        echo -n "clang-cl $name... "
        if ! out=$(uv run slop transpile "$REPO_ROOT/lib/std/$m.slop" -o "$CL_DIR/$name.c" 2>&1); then
            fail "(transpile)" "$out"
            continue
        fi
        if out=$(clang-cl -nologo -c -W3 -DSLOP_ARENA_NO_CAP -DSLOP_INTERN_THREADSAFE \
                -I "$RUNTIME_DIR" -Fo"$CL_DIR/$name.obj" "$CL_DIR/$name.c" 2>&1); then
            pass
        else
            fail "" "$out"
        fi
    done
    echo ""
fi

echo "=== Results ==="
echo "Passed:  $PASS_COUNT"
echo "Failed:  $FAIL_COUNT"
echo "Skipped: $SKIP_COUNT"
[ "$FAIL_COUNT" -eq 0 ]
