/*
 * Test: the runtime's list type on a list with no storage yet
 *
 * Run by scripts/run_native_tests.sh under ASan and UBSan.
 *
 * list-new creates {len 0, cap 0, data NULL} and the first push allocates.
 * The inline push the transpiler emits already grew from cap 0; the
 * SLOP_LIST_DEFINE functions every generated List type carries doubled the
 * capacity (0 -> 0, then wrote into a 0-byte block) and memcpy'd from the
 * NULL data.
 */

#include "slop_runtime.h"
#include <stdio.h>

static int failures = 0;

#define CHECK(cond) do { \
    if (!(cond)) { \
        fprintf(stderr, "%s:%d: CHECK failed: %s\n", __FILE__, __LINE__, #cond); \
        failures++; \
    } \
} while (0)

SLOP_LIST_DEFINE(double, test_list_double)

int main(void) {
    slop_arena arena = slop_arena_new(1 << 16);

    /* Empty, with no storage: reads are bounded and allocate nothing */
    test_list_double empty = {0, 0, NULL};
    size_t before = arena.offset;
    CHECK(empty.len == 0);
    CHECK(!test_list_double_set(&empty, 0, 1.0));
    CHECK(arena.offset == before);

    /* A copy of the empty list: pushing to it leaves the original empty */
    test_list_double copy = empty;
    test_list_double_push(&arena, &copy, 2.5);
    CHECK(copy.len == 1 && copy.cap == 16 && copy.data != NULL);
    CHECK(*test_list_double_get(&copy, 0) == 2.5);
    CHECK(empty.len == 0 && empty.cap == 0 && empty.data == NULL);

    /* Growth from there doubles, keeping every element */
    for (int i = 1; i < 40; i++) test_list_double_push(&arena, &copy, (double)i);
    CHECK(copy.len == 40 && copy.cap == 64);
    CHECK(*test_list_double_get(&copy, 0) == 2.5);
    for (int i = 1; i < 40; i++) CHECK(*test_list_double_get(&copy, (size_t)i) == (double)i);
    CHECK(test_list_double_set(&copy, 39, -1.0) && *test_list_double_get(&copy, 39) == -1.0);
    CHECK(!test_list_double_set(&copy, 40, 0.0));

    /* An explicit capacity is still allocated up front */
    test_list_double sized = test_list_double_new(&arena, 4);
    CHECK(sized.cap == 4 && sized.data != NULL && sized.len == 0);

    slop_arena_free(&arena);
    if (failures) {
        fprintf(stderr, "test_list: %d check(s) failed\n", failures);
        return 1;
    }
    printf("test_list: all checks passed\n");
    return 0;
}
