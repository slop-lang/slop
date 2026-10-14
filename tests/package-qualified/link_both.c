/*
 * Two SLOP libraries, each with a module named engine that defines run and
 * Rule, linked into one program (#360). The package qualifier keeps their
 * C names apart; the :c-name functions come out exactly as written.
 *
 * Built by scripts/run_native_tests.sh against the two static libraries and
 * their generated headers.
 */
#include "slop_runtime.h"
#include <stdio.h>

/* Declared by hand rather than through the two slop_engine.h headers, which
 * have the same file name and include guard: a program that uses both
 * libraries' module headers would rename one of them. */
typedef struct { int64_t weight; } pkg_a_engine_Rule;
typedef struct { int64_t weight; int64_t bonus; } pkg_b_engine_Rule;
int64_t pkg_a_engine_run(pkg_a_engine_Rule r);
int64_t pkg_b_engine_run(pkg_b_engine_Rule r);
int64_t engine_entry_a(int64_t x);
int64_t engine_entry_b(int64_t x);

int main(void) {
    int failures = 0;
    pkg_a_engine_Rule a = { 21 };
    pkg_b_engine_Rule b = { 40, 2 };
    if (pkg_a_engine_run(a) != 42) { fprintf(stderr, "FAIL: pkg_a_engine_run\n"); failures++; }
    if (pkg_b_engine_run(b) != 42) { fprintf(stderr, "FAIL: pkg_b_engine_run\n"); failures++; }
    if (engine_entry_a(1) != 2) { fprintf(stderr, "FAIL: engine_entry_a\n"); failures++; }
    if (engine_entry_b(1) != 3) { fprintf(stderr, "FAIL: engine_entry_b\n"); failures++; }
    printf("%s (%d failures)\n", failures == 0 ? "ALL TESTS PASSED" : "SOME TESTS FAILED", failures);
    return failures;
}
