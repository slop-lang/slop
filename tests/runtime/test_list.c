/*
 * Test: the runtime's list type: a list with no storage yet, and growth
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
    CHECK(copy.len == 1 && copy.cap == SLOP_LIST_FIRST_CAPACITY && copy.data != NULL);
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

    /* Growth always moves to a new buffer, even when the old one is the
     * last allocation in its block and could be extended, and leaves the old
     * one as it was: a copy of the old header still reads its elements */
    test_list_double last = {0, 0, NULL};
    for (int i = 0; i < 4; i++) test_list_double_push(&arena, &last, (double)i);
    double* where = last.data;
    test_list_double before_grow = last;
    test_list_double_push(&arena, &last, 4.0);
    CHECK(last.data != where && last.cap == 8 && last.len == 5);
    for (int i = 0; i < 5; i++) CHECK(*test_list_double_get(&last, (size_t)i) == (double)i);
    CHECK(before_grow.data == where && before_grow.len == 4);
    for (int i = 0; i < 4; i++) CHECK(before_grow.data[i] == (double)i);

    /* Why it must: a List header is a value, and copies share its buffer.
     * Here orig has spare room (len 2, cap 4) and a copy of it -- a `mut`
     * parameter, say -- grows past cap. Had the copy extended the shared
     * buffer in place, orig's next push would land on the copy's element 2;
     * moving cuts the copy loose, so the caller's push never reaches it. */
    test_list_double orig = {0, 0, NULL};
    test_list_double_push(&arena, &orig, 10.0);
    test_list_double_push(&arena, &orig, 11.0);
    test_list_double copy2 = orig;
    test_list_double_push(&arena, &copy2, 20.0);
    test_list_double_push(&arena, &copy2, 21.0);
    test_list_double_push(&arena, &copy2, 22.0);     /* grows */
    test_list_double_push(&arena, &orig, 99.0);
    CHECK(copy2.len == 5 && copy2.data[2] == 20.0 && copy2.data[4] == 22.0);
    CHECK(orig.len == 3 && orig.data[2] == 99.0);

    /* Storage outside the arena (a stack buffer, as a list literal with no
     * arena in scope gets) grows by copying like any other */
    double stack_buf[2] = {1.0, 2.0};
    test_list_double lit = {2, 2, stack_buf};
    test_list_double_push(&arena, &lit, 3.0);
    CHECK(lit.data != stack_buf && lit.len == 3 && lit.cap == 4);
    CHECK(lit.data[0] == 1.0 && lit.data[1] == 2.0 && lit.data[2] == 3.0);

    /* A list grows in its own arena when the push names none (NULL, as a
     * plain list-push does), and in the named one when it names one (#276) */
    slop_arena own = slop_arena_new(1 << 12);
    slop_arena named = slop_arena_new(1 << 12);
    test_list_double r = { .len = 0, .cap = 0, .data = NULL, .arena = &own };
    for (int i = 0; i < 10; i++) test_list_double_push(NULL, &r, (double)i);
    CHECK((uint8_t*)r.data >= own.base && (uint8_t*)r.data < own.base + own.capacity);
    size_t named_used = named.offset;
    CHECK(named_used == 0);
    for (int i = 10; i < 40; i++) test_list_double_push(&named, &r, (double)i);
    CHECK((uint8_t*)r.data >= named.base && (uint8_t*)r.data < named.base + named.capacity);
    CHECK(r.arena == &own);
    for (int i = 0; i < 40; i++) CHECK(r.data[i] == (double)i);
    test_list_double made = test_list_double_new(&own, 2);
    CHECK(made.arena == &own);
    slop_arena_free(&own);
    slop_arena_free(&named);

    /* Growth across chained blocks keeps every element */
    slop_arena small = slop_arena_new(64);
    test_list_double c = {0, 0, NULL};
    for (int i = 0; i < 100; i++) test_list_double_push(&small, &c, (double)i);
    for (int i = 0; i < 100; i++) CHECK(c.data[i] == (double)i);
    slop_arena_free(&small);

    slop_arena_free(&arena);
    if (failures) {
        fprintf(stderr, "test_list: %d check(s) failed\n", failures);
        return 1;
    }
    printf("test_list: all checks passed\n");
    return 0;
}
