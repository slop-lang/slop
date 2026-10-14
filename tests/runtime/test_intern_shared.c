/*
 * Test: the intern pool is one object across translation units (#360)
 *
 * slop_global_intern_pool and slop_intern_once were static, so every TU
 * that included the runtime interned into a pool of its own, and the same
 * literal interned from two libraries' generated code came back as two
 * different strings. Now they are SLOP_SHARED_GLOBAL, like
 * slop_global_allocated: one pool per program.
 *
 * Built together with test_intern_shared/second_tu.c, as the plain build
 * and (by the test runner's naming) under ASan.
 */

#include "slop_runtime.h"
#include <stdio.h>

/* From test_intern_shared/second_tu.c, which includes the runtime too */
slop_intern_pool** second_tu_pool(void);
slop_string second_tu_intern(const char* s);

int main(void) {
    int failures = 0;

    slop_string here = slop_intern_cstring("shared-across-tus");
    slop_string there = second_tu_intern("shared-across-tus");

    if (second_tu_pool() != &slop_global_intern_pool) {
        fprintf(stderr, "FAIL: each TU has its own slop_global_intern_pool\n");
        failures++;
    }
    if (here.data != there.data) {
        fprintf(stderr, "FAIL: the same literal interned in two TUs is two strings\n");
        failures++;
    }
    if (slop_global_intern_pool == NULL || slop_global_intern_pool->entry_count != 1) {
        fprintf(stderr, "FAIL: expected one entry in the shared pool, have %zu\n",
                slop_global_intern_pool ? slop_global_intern_pool->entry_count : (size_t)0);
        failures++;
    }

    /* A string interned only in the other TU is found from this one */
    slop_string only_there = second_tu_intern("only-there");
    slop_string found_here = slop_intern_cstring("only-there");
    if (only_there.data != found_here.data) {
        fprintf(stderr, "FAIL: a string interned in the other TU is not found here\n");
        failures++;
    }

    printf("%s (%d failures)\n", failures == 0 ? "ALL TESTS PASSED" : "SOME TESTS FAILED", failures);
    return failures;
}
