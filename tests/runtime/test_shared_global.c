/*
 * Test: slop_global_allocated is one object across translation units
 *
 * Every translation unit that includes slop_runtime.h defines
 * slop_global_allocated, and the link must still end up with one object:
 * weak definitions on ELF and Mach-O, a selectany COMDAT on Windows, where
 * a weak symbol does not merge definitions. With a copy per TU, the arena
 * cap would count each TU's arenas separately.
 *
 * Built together with test_shared_global/second_tu.c.
 */

#include "slop_runtime.h"
#include <stdio.h>

/* From test_shared_global/second_tu.c, which includes the runtime too */
_Atomic size_t* second_tu_counter(void);
slop_arena second_tu_arena_new(size_t capacity);

int main(void) {
    int failures = 0;

    if (second_tu_counter() != &slop_global_allocated) {
        fprintf(stderr, "FAIL: each TU has its own slop_global_allocated\n");
        failures++;
    }

    /* An arena made in the other TU is counted where this TU reads... */
    size_t before = atomic_load(&slop_global_allocated);
    slop_arena a = second_tu_arena_new(4096);
    size_t during = atomic_load(&slop_global_allocated);
    if (during - before != 4096) {
        fprintf(stderr, "FAIL: an arena made in the other TU moved this TU's count by %zu, not 4096\n",
                during - before);
        failures++;
    }

    /* ...and freeing it here takes it off the same count */
    slop_arena_free(&a);
    size_t after = atomic_load(&slop_global_allocated);
    if (after != before) {
        fprintf(stderr, "FAIL: count is %zu after the free, was %zu before the arena\n",
                after, before);
        failures++;
    }

    printf("%s (%d failures)\n", failures == 0 ? "ALL TESTS PASSED" : "SOME TESTS FAILED", failures);
    return failures;
}
