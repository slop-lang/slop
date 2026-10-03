/*
 * Test: freeing an arena gives its memory back to the OS
 *
 * Run by scripts/run_native_tests.sh under UBSan only (files named
 * *_ubsan.c): under ASan every arena block comes from malloc, and ASan's own
 * allocator and shadow memory would make resident size meaningless anyway.
 *
 * Blocks of SLOP_ARENA_MAP_THRESHOLD bytes or more are mapped from the OS and
 * unmapped by slop_arena_free and slop_arena_reset. Through malloc, macOS kept
 * big freed blocks dirty in its large-allocation cache, so resident memory
 * never fell after an arena-free. The resident-size checks here fail against
 * a runtime that mallocs its blocks, on macOS; glibc maps blocks this big
 * itself, so there they pass either way.
 */

#define SLOP_ARENA_NO_CAP
#include "slop_runtime.h"
#include <stdio.h>

#ifdef __APPLE__
#include <mach/mach.h>
#endif

static int failures = 0;

#define CHECK(cond) do { \
    if (!(cond)) { \
        fprintf(stderr, "%s:%d: CHECK failed: %s\n", __FILE__, __LINE__, #cond); \
        failures++; \
    } \
} while (0)

#define MIB ((size_t)1 << 20)

/* Resident bytes of this process */
static size_t resident(void) {
#ifdef __APPLE__
    mach_task_basic_info_data_t info;
    mach_msg_type_number_t count = MACH_TASK_BASIC_INFO_COUNT;
    if (task_info(mach_task_self(), MACH_TASK_BASIC_INFO,
                  (task_info_t)&info, &count) != KERN_SUCCESS) {
        fprintf(stderr, "task_info failed\n");
        exit(1);
    }
    return (size_t)info.resident_size;
#else
    FILE* f = fopen("/proc/self/statm", "r");
    unsigned long size = 0, pages = 0;
    if (f == NULL || fscanf(f, "%lu %lu", &size, &pages) != 2) {
        fprintf(stderr, "cannot read /proc/self/statm\n");
        exit(1);
    }
    fclose(f);
    return (size_t)pages * (size_t)sysconf(_SC_PAGESIZE);
#endif
}

/* How much of a fill must show up as resident before the release check means
 * anything. The point of these tests is the drop: after freeing, resident size
 * is back within 64 MiB of where it started, which a runtime that keeps freed
 * blocks dirty fails however much it reclaimed on the way up. The rise only has
 * to show the fill was really mapped and touched, and half of it does; asking
 * for 900 of 1024 MiB failed on CI runners that reclaim pages from a process
 * under memory pressure. */
#define RISE_FLOOR(n) ((n) * MIB / 2)

/* Bump n MiB out of the arena a MiB at a time, writing every page.
 *
 * The bytes are pseudo-random, so that memory compression cannot take pages
 * out of the resident count. That alone did not make the count reliable: on a
 * memory-constrained CI runner the full GiB still read as low as 852 MiB above
 * the start, with random data. The rise checks below therefore ask only for
 * half of what was written; see RISE_FLOOR. */
static uint64_t fill_state = 0x9E3779B97F4A7C15ull;

static void fill(slop_arena* arena, size_t n) {
    for (size_t i = 0; i < n; i++) {
        uint64_t* p = (uint64_t*)slop_arena_alloc(arena, MIB);
        CHECK(p != NULL && ((uintptr_t)p & 7) == 0);
        if (p == NULL || ((uintptr_t)p & 7) != 0) return;
        for (size_t w = 0; w < MIB / sizeof(uint64_t); w++) {
            /* xorshift64, carried across calls so no two pages match */
            fill_state ^= fill_state << 13;
            fill_state ^= fill_state >> 7;
            fill_state ^= fill_state << 17;
            p[w] = fill_state;
        }
    }
}

/* ~1 GiB bumped into a chain of blocks, then arena-free: resident size must
 * rise by about that much and fall back */
static void test_free_releases(void) {
    size_t before = resident();
    size_t accounted = atomic_load(&slop_global_allocated);

    slop_arena arena = slop_arena_new(MIB);
    fill(&arena, 1024);
    size_t full = resident();
    CHECK(full >= before + RISE_FLOOR(1024));

    slop_arena_free(&arena);
    size_t after = resident();
    CHECK(after <= before + 64 * MIB);
    CHECK(atomic_load(&slop_global_allocated) == accounted);
    printf("free:  resident %zu MB -> %zu MB -> %zu MB\n",
           before / MIB, full / MIB, after / MIB);
}

/* slop_arena_reset keeps the head block and gives back the overflow */
static void test_reset_releases(void) {
    size_t before = resident();
    size_t accounted = atomic_load(&slop_global_allocated);

    slop_arena arena = slop_arena_new(MIB);
    fill(&arena, 512);
    size_t full = resident();
    CHECK(full >= before + RISE_FLOOR(512));

    slop_arena_reset(&arena);
    size_t after = resident();
    CHECK(arena.next == NULL && arena.offset == 0 && arena.capacity == MIB);
    CHECK(after <= before + 64 * MIB);
    CHECK(atomic_load(&slop_global_allocated) == accounted + MIB);

    /* The arena still works after the reset, and frees cleanly */
    fill(&arena, 4);
    slop_arena_free(&arena);
    CHECK(atomic_load(&slop_global_allocated) == accounted);
    printf("reset: resident %zu MB -> %zu MB -> %zu MB\n",
           before / MIB, full / MIB, after / MIB);
}

#ifdef SLOP_ARENA_MAP_THRESHOLD
/* Which blocks are mapped: the head and each overflow block by its own size */
static void test_mapped_by_size(void) {
    size_t accounted = atomic_load(&slop_global_allocated);

    slop_arena small = slop_arena_new(4096);
    CHECK(small.base != NULL && !small.mapped);
    /* Each allocation fills the next doubled block exactly: 4 KB .. 512 KB
     * malloc'd, then 1 MiB .. 8 MiB mapped */
    for (int i = 0; i < 12; i++) slop_arena_alloc(&small, (size_t)4096 << i);
    int blocks = 0, mapped = 0;
    for (slop_arena* a = &small; a != NULL; a = a->next, blocks++) {
        CHECK(a->mapped == (SLOP_ARENA_USE_MAP && a->capacity >= SLOP_ARENA_MAP_THRESHOLD));
        CHECK(((uintptr_t)a->base & 7) == 0);
        mapped += a->mapped;
    }
    CHECK(blocks == 12);
    CHECK(mapped == (SLOP_ARENA_USE_MAP ? 4 : 0));
    slop_arena_free(&small);
    CHECK(small.base == NULL && !small.mapped);

    slop_arena big = slop_arena_new(SLOP_ARENA_MAP_THRESHOLD);
    CHECK(big.mapped == SLOP_ARENA_USE_MAP);
    slop_arena_free(&big);

    CHECK(atomic_load(&slop_global_allocated) == accounted);
}
#endif

/* A sole allocation grown in place of its block: malloc'd below the
 * threshold, moved to a mapping when it crosses it, then mapping to mapping.
 * The contents survive every move and the accounting balances. */
static void test_realloc_sole_across_threshold(void) {
    size_t accounted = atomic_load(&slop_global_allocated);
    size_t sizes[] = {512 * 1024, 2 * MIB, 8 * MIB, 64 * MIB};

    slop_arena arena = slop_arena_new(sizes[0]);
    uint8_t* p = (uint8_t*)slop_arena_alloc(&arena, sizes[0]);
    CHECK(p == arena.base);
    for (size_t i = 0; i < sizes[0]; i++) p[i] = (uint8_t)(i * 31 + 7);

    for (int step = 1; step < 4; step++) {
        size_t old = sizes[step - 1];
        uint8_t* q = (uint8_t*)slop_arena_realloc_sole(&arena, p, old, sizes[step]);
        CHECK(q != NULL);
        if (q == NULL) break;
        p = q;
        CHECK(arena.base == p && arena.capacity == sizes[step] && arena.offset == sizes[step]);
#ifdef SLOP_ARENA_MAP_THRESHOLD
        CHECK(arena.mapped == SLOP_ARENA_USE_MAP);
#endif
        CHECK(atomic_load(&slop_global_allocated) == accounted + sizes[step]);
        bool same = true;
        for (size_t i = 0; i < sizes[0]; i++) same &= p[i] == (uint8_t)(i * 31 + 7);
        CHECK(same);
        /* Everything past the first 512 KB is now this step's to write */
        memset(p + sizes[0], step, sizes[step] - sizes[0]);
    }
    CHECK(p[sizes[3] - 1] == 3);

    slop_arena_free(&arena);
    CHECK(atomic_load(&slop_global_allocated) == accounted);
}

/* A map whose table outgrows the threshold: #234's realloc_sole path, now
 * moving from malloc to a mapping and on to bigger mappings */
static const slop_map_desc int_map = SLOP_MAP_DESC(int64_t, slop_hash_int, slop_eq_int, SLOP_KEY_BITS, int64_t);

static void test_map_table_past_threshold(void) {
    size_t accounted = atomic_load(&slop_global_allocated);
    slop_arena arena = slop_arena_new(4096);
    slop_map* m = slop_map_new_ptr(&arena, 0, &int_map);
    enum { N = 400000 };
    for (int64_t k = 0; k < N; k++) {
        int64_t v = k * 5;
        slop_map_put(&arena, m, &k, &v, sizeof(v));
    }
    CHECK(m->len == N);
    bool ok = true;
    for (int64_t k = 0; k < N; k++) {
        int64_t* v = (int64_t*)slop_map_get(m, &k);
        ok &= v != NULL && *v == k * 5;
    }
    CHECK(ok);
#ifdef SLOP_ARENA_MAP_THRESHOLD
    /* The table sits alone in a block past the threshold, mapped */
    bool table_mapped = false;
    for (slop_arena* a = &arena; a != NULL; a = a->next) {
        if (a->base == m->table) table_mapped = a->mapped;
    }
    CHECK(table_mapped == SLOP_ARENA_USE_MAP);
#endif
    slop_arena_free(&arena);
    CHECK(atomic_load(&slop_global_allocated) == accounted);
}

int main(void) {
    test_free_releases();
    test_reset_releases();
#ifdef SLOP_ARENA_MAP_THRESHOLD
    test_mapped_by_size();
#endif
    test_realloc_sole_across_threshold();
    test_map_table_past_threshold();

    if (failures) {
        fprintf(stderr, "%d check(s) failed\n", failures);
        return 1;
    }
    printf("all arena release tests passed\n");
    return 0;
}
