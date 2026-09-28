/*
 * Test: slop_map (the runtime behind Map and Set)
 *
 * Run by scripts/run_native_tests.sh, which builds it with
 *   cc -g -O1 -fsanitize=address,undefined -I src/slop/runtime \
 *      -o test_map tests/runtime/test_map.c
 *
 * Keys are int64_t and each test key's hash comes from a table, so a test can
 * put a key's home slot exactly where it wants: a collision chain, a chain
 * that wraps past the end of the table, a removal that has to shift entries
 * back across the wrap.
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

/* ------------------------------------------------------------
 * Controlled hashing
 * ------------------------------------------------------------ */

#define MAX_KEYS 64
static uint64_t key_hash[MAX_KEYS];     /* hash returned for key k */
static int hash_calls = 0;
static int eq_calls = 0;

static uint64_t table_hash(const void* key) {
    hash_calls++;
    return key_hash[*(const int64_t*)key];
}

static bool counting_eq(const void* a, const void* b) {
    eq_calls++;
    return *(const int64_t*)a == *(const int64_t*)b;
}

/* A raw hash whose mixed value has home slot `slot` in a table of `cap`.
 * `nth` picks among the candidates, so two keys can share a home slot yet
 * have different full hashes. */
static uint64_t hash_for_slot(size_t slot, size_t cap, int nth) {
    for (uint64_t c = 1;; c++) {
        if ((slop_map_mix(c) & (cap - 1)) == slot && nth-- == 0) return c;
    }
}

static int64_t val_storage[1024];

static void put(slop_arena* arena, slop_map* m, int64_t k, int64_t v) {
    val_storage[k] = v;
    slop_map_put(arena, m, &k, &val_storage[k]);
}

static int64_t get(slop_map* m, int64_t k) {
    int64_t* v = (int64_t*)slop_map_get(m, &k);
    return v ? *v : -1;
}

/* Slot index holding key k, or -1 */
static long slot_of(slop_map* m, int64_t k) {
    for (size_t i = 0; i < m->cap; i++) {
        if (m->entries[i].occupied && *(int64_t*)m->entries[i].key == k) return (long)i;
    }
    return -1;
}

/* Every occupied entry is reachable from its home slot without crossing an
 * empty slot, stores the hash of its own key, and len agrees with the table. */
static void check_invariants(slop_map* m) {
    size_t mask = m->cap - 1;
    size_t count = 0;
    for (size_t i = 0; i < m->cap; i++) {
        const slop_map_entry* e = &m->entries[i];
        if (!e->occupied) continue;
        count++;
        int saved = hash_calls;
        CHECK(e->hash == slop_map_mix(m->hash(e->key)));
        hash_calls = saved;
        for (size_t p = e->hash & mask; p != i; p = (p + 1) & mask) {
            CHECK(m->entries[p].occupied);
        }
    }
    CHECK(count == m->len);
}

/* ------------------------------------------------------------
 * Tests
 * ------------------------------------------------------------ */

static void test_capacity_rounding(slop_arena* arena) {
    CHECK(slop_map_new(arena, 0, 8, slop_hash_int, slop_eq_int).cap == 8);
    CHECK(slop_map_new(arena, 5, 8, slop_hash_int, slop_eq_int).cap == 8);
    CHECK(slop_map_new(arena, 16, 8, slop_hash_int, slop_eq_int).cap == 16);
    CHECK(slop_map_new(arena, 17, 8, slop_hash_int, slop_eq_int).cap == 32);
    /* A zero-capacity map is usable (it used to divide by zero). */
    slop_map m = slop_map_new(arena, 0, sizeof(int64_t), slop_hash_int, slop_eq_int);
    CHECK(!slop_map_has(&m, &(int64_t){1}));
    CHECK(!slop_map_remove(&m, &(int64_t){1}));
}

static void test_basic(slop_arena* arena) {
    slop_map* m = slop_map_new_ptr(arena, 16, sizeof(int64_t), slop_hash_int, slop_eq_int);
    static int64_t vals[1000];
    for (int64_t k = 0; k < 1000; k++) {
        vals[k] = k * 3;
        slop_map_put(arena, m, &k, &vals[k]);
    }
    CHECK(m->len == 1000);
    CHECK((m->cap & (m->cap - 1)) == 0);
    for (int64_t k = 0; k < 1000; k++) {
        int64_t* v = (int64_t*)slop_map_get(m, &k);
        CHECK(v && *v == k * 3);
    }
    CHECK(!slop_map_has(m, &(int64_t){1000}));
    CHECK(!slop_map_has(m, &(int64_t){-1}));

    /* Overwrite keeps len and replaces the value */
    static int64_t other = 77;
    slop_map_put(arena, m, &(int64_t){5}, &other);
    CHECK(m->len == 1000);
    CHECK(*(int64_t*)slop_map_get(m, &(int64_t){5}) == 77);

    /* Iteration visits each key exactly once */
    static bool seen[1000];
    size_t visited = 0;
    for (size_t i = 0; i < m->cap; i++) {
        if (m->entries[i].occupied) {
            int64_t k = *(int64_t*)m->entries[i].key;
            CHECK(k >= 0 && k < 1000 && !seen[k]);
            if (k >= 0 && k < 1000) seen[k] = true;
            visited++;
        }
    }
    CHECK(visited == 1000);

    for (int64_t k = 0; k < 1000; k += 2) CHECK(slop_map_remove(m, &k));
    CHECK(m->len == 500);
    for (int64_t k = 0; k < 1000; k++) CHECK(slop_map_has(m, &k) == (k % 2 == 1));
    check_invariants(m);
}

/* Keys that share a home slot but differ in full hash never reach eq; keys
 * with the same full hash (a true collision) are told apart by eq. */
static void test_stored_hash_filters_eq(slop_arena* arena) {
    slop_map m = slop_map_new(arena, 8, sizeof(int64_t), table_hash, counting_eq);
    for (int i = 0; i < 4; i++) key_hash[i] = hash_for_slot(3, 8, i);
    for (int64_t k = 0; k < 4; k++) put(arena, &m, k, k + 100);
    CHECK(slot_of(&m, 0) == 3 && slot_of(&m, 3) == 6);

    eq_calls = 0;
    CHECK(get(&m, 3) == 103);
    CHECK(eq_calls == 1);                   /* only the matching entry */

    /* Full collisions: identical hashes, so every probe compares */
    slop_map c = slop_map_new(arena, 8, sizeof(int64_t), table_hash, counting_eq);
    for (int i = 10; i < 14; i++) key_hash[i] = key_hash[0];
    for (int64_t k = 10; k < 14; k++) put(arena, &c, k, k);
    eq_calls = 0;
    CHECK(get(&c, 13) == 13);
    CHECK(eq_calls == 4);
    CHECK(get(&c, 10) == 10 && get(&c, 11) == 11 && get(&c, 12) == 12);
    CHECK(slop_map_remove(&c, &(int64_t){11}));
    CHECK(get(&c, 10) == 10 && get(&c, 11) == -1 && get(&c, 12) == 12 && get(&c, 13) == 13);
    check_invariants(&c);
}

/* cap 8: A(home 6)@6  B(home 6)@7  C(home 7)@0  D(home 0)@1 */
static void setup_wrap(slop_arena* arena, slop_map* m) {
    *m = slop_map_new(arena, 8, sizeof(int64_t), table_hash, counting_eq);
    key_hash[20] = hash_for_slot(6, 8, 0);   /* A */
    key_hash[21] = hash_for_slot(6, 8, 1);   /* B */
    key_hash[22] = hash_for_slot(7, 8, 0);   /* C */
    key_hash[23] = hash_for_slot(0, 8, 0);   /* D */
    for (int64_t k = 20; k < 24; k++) put(arena, m, k, k);
}

static void test_remove_across_wrap(slop_arena* arena) {
    slop_map m;

    setup_wrap(arena, &m);
    CHECK(slot_of(&m, 20) == 6 && slot_of(&m, 21) == 7);
    CHECK(slot_of(&m, 22) == 0 && slot_of(&m, 23) == 1);

    /* Removing A shifts B, C and D back one slot each, C and D across the wrap */
    CHECK(slop_map_remove(&m, &(int64_t){20}));
    CHECK(slot_of(&m, 21) == 6 && slot_of(&m, 22) == 7 && slot_of(&m, 23) == 0);
    CHECK(!m.entries[1].occupied);
    CHECK(get(&m, 20) == -1 && get(&m, 21) == 21 && get(&m, 22) == 22 && get(&m, 23) == 23);
    CHECK(m.len == 3);
    check_invariants(&m);

    /* Removing C (at slot 0, past the wrap) pulls D back into slot 0 */
    setup_wrap(arena, &m);
    CHECK(slop_map_remove(&m, &(int64_t){22}));
    CHECK(slot_of(&m, 23) == 0 && !m.entries[1].occupied);
    CHECK(get(&m, 20) == 20 && get(&m, 21) == 21 && get(&m, 23) == 23);
    check_invariants(&m);

    /* Removing B: C (home 7) moves into the hole at 7, and D follows into 0 */
    setup_wrap(arena, &m);
    CHECK(slop_map_remove(&m, &(int64_t){21}));
    CHECK(slot_of(&m, 20) == 6 && slot_of(&m, 22) == 7 && slot_of(&m, 23) == 0);
    check_invariants(&m);

    /* Removing D, the last in the chain, moves nothing */
    setup_wrap(arena, &m);
    CHECK(slop_map_remove(&m, &(int64_t){23}));
    CHECK(slot_of(&m, 20) == 6 && slot_of(&m, 21) == 7 && slot_of(&m, 22) == 0);
    check_invariants(&m);

    /* Missing keys, including one whose home is inside the chain */
    setup_wrap(arena, &m);
    key_hash[24] = hash_for_slot(7, 8, 1);
    CHECK(!slop_map_remove(&m, &(int64_t){24}));
    CHECK(m.len == 4);

    /* Re-insert after removal lands back in the chain and is found */
    CHECK(slop_map_remove(&m, &(int64_t){20}));
    put(arena, &m, 20, 200);
    CHECK(get(&m, 20) == 200 && m.len == 4);
    check_invariants(&m);
}

/* Growing moves each entry -- same key copy, same value pointer, same stored
 * hash -- without calling hash or eq and without copying a key. */
static void test_grow(void) {
    /* Its own arena, big enough that no allocation here spills into a
     * chained block, so the head's offset measures every byte allocated */
    slop_arena own = slop_arena_new(1 << 16);
    slop_arena* arena = &own;
    slop_map m = slop_map_new(arena, 8, sizeof(int64_t), table_hash, counting_eq);
    for (int i = 30; i < 36; i++) key_hash[i] = hash_for_slot(5, 8, i - 30);
    for (int64_t k = 30; k < 36; k++) put(arena, &m, k, k);
    CHECK(m.cap == 8 && m.len == 6);

    void* key_ptr[6];
    void* val_ptr[6];
    for (int64_t k = 30; k < 36; k++) {
        long s = slot_of(&m, k);
        key_ptr[k - 30] = m.entries[s].key;
        val_ptr[k - 30] = m.entries[s].value;
    }

    hash_calls = 0;
    eq_calls = 0;
    size_t arena_before = arena->offset;
    slop_map_grow(arena, &m);
    CHECK(hash_calls == 0 && eq_calls == 0);
    /* Exactly one allocation: the new entry array */
    CHECK(arena->offset - arena_before == 16 * sizeof(slop_map_entry));
    CHECK(m.cap == 16 && m.len == 6);

    for (int64_t k = 30; k < 36; k++) {
        long s = slot_of(&m, k);
        CHECK(s >= 0);
        if (s < 0) continue;
        CHECK(m.entries[s].key == key_ptr[k - 30]);
        CHECK(m.entries[s].value == val_ptr[k - 30]);
        CHECK(get(&m, k) == k);
    }
    check_invariants(&m);

    /* The 7th put triggers the grow itself; one hash call, for the new key */
    slop_map g = slop_map_new(arena, 8, sizeof(int64_t), table_hash, counting_eq);
    for (int64_t k = 30; k < 36; k++) put(arena, &g, k, k);
    key_hash[36] = hash_for_slot(5, 8, 6);
    hash_calls = 0;
    put(arena, &g, 36, 36);
    CHECK(hash_calls == 1);
    CHECK(g.cap == 16 && g.len == 7);
    for (int64_t k = 30; k < 37; k++) CHECK(get(&g, k) == k);
    check_invariants(&g);
    slop_arena_free(&own);
}

/* A weak hash (all low bits zero) still spreads, and a long random sequence
 * of puts and removes agrees with a reference array. */
static uint64_t weak_hash(const void* key) {
    return (uint64_t)(*(const int64_t*)key) << 20;
}

static void test_random_against_reference(slop_arena* arena) {
    enum { SPACE = 512, OPS = 200000 };
    slop_map m = slop_map_new(arena, 16, sizeof(int64_t), weak_hash, slop_eq_int);
    static bool present[SPACE];
    static int64_t vals[SPACE];
    uint64_t rng = 12345;
    size_t len = 0;
    for (int op = 0; op < OPS; op++) {
        rng = rng * 6364136223846793005ULL + 1442695040888963407ULL;
        int64_t k = (int64_t)((rng >> 33) % SPACE);
        if ((rng >> 20) & 1) {
            if (!present[k]) len++;
            present[k] = true;
            vals[k] = op;
            slop_map_put(arena, &m, &k, &vals[k]);
        } else {
            bool removed = slop_map_remove(&m, &k);
            CHECK(removed == present[k]);
            if (present[k]) len--;
            present[k] = false;
        }
        if (op % 10000 == 0) check_invariants(&m);
    }
    CHECK(m.len == len);
    for (int64_t k = 0; k < SPACE; k++) {
        int64_t* v = (int64_t*)slop_map_get(&m, &k);
        CHECK((v != NULL) == present[k]);
        if (v && present[k]) CHECK(*v == vals[k]);
    }
    check_invariants(&m);

    /* The mixer, not the raw hash, decides the slot: with the raw hash every
     * key would have home slot 0. */
    size_t distinct_homes = 0;
    static bool home_used[4096];
    for (size_t i = 0; i < m.cap; i++) {
        if (m.entries[i].occupied) {
            size_t h = m.entries[i].hash & (m.cap - 1);
            if (h < 4096 && !home_used[h]) { home_used[h] = true; distinct_homes++; }
        }
    }
    CHECK(distinct_homes > m.len / 2);
}

/* ------------------------------------------------------------
 * Strings
 * ------------------------------------------------------------ */

/* Known answers pin slop_hash_bytes across platforms and releases: Map/Set
 * iteration order follows it. The values were cross-checked against an
 * independent reimplementation of the algorithm. */
static void test_hash_bytes_known_answers(void) {
    static const struct { const char* s; uint64_t h; } kat[] = {
        {"", 0xd8a310150df90781ULL},
        {"a", 0x4973669e9bd25ff8ULL},
        {"abcdefg", 0x5be8620504751cecULL},
        {"abcdefgh", 0x1acde643a7141eddULL},
        {"abcdefghi", 0x6b1378a6bbf4d827ULL},
        {"http://www.co-ode.org/ontologies/galen#Concept_42", 0x677db83406563527ULL},
    };
    for (size_t i = 0; i < sizeof(kat) / sizeof(kat[0]); i++) {
        uint64_t h = slop_hash_bytes(kat[i].s, strlen(kat[i].s));
        if (h != kat[i].h) {
            fprintf(stderr, "slop_hash_bytes(\"%s\") = 0x%016llxULL, expected 0x%016llxULL\n",
                    kat[i].s, (unsigned long long)h, (unsigned long long)kat[i].h);
            failures++;
        }
    }

    /* Every length up to 3 words hashes differently from its neighbours,
     * and the string and raw-data entry points agree */
    const char* text = "the quick brown fox jumps over";
    for (size_t n = 0; n + 1 < 25; n++) {
        CHECK(slop_hash_bytes(text, n) != slop_hash_bytes(text, n + 1));
        slop_string s = {n, text};
        CHECK(slop_hash_string(&s) == slop_hash_string_data(text, n));
    }
}

static void test_strings(slop_arena* arena) {
    /* Interning still dedupes with the new hash */
    slop_string a = slop_intern_cstring("http://example.org/a");
    slop_string b = slop_intern_string("http://example.org/a", 20);
    slop_string c = slop_intern_cstring("http://example.org/b");
    CHECK(a.data == b.data);
    CHECK(a.data != c.data);

    /* Equality: identical storage, equal content in separate storage,
     * unequal content, unequal length */
    char buf[] = "http://example.org/a";
    slop_string copy = {20, buf};
    CHECK(slop_string_eq(a, a));
    CHECK(slop_string_eq(a, copy));
    CHECK(!slop_string_eq(a, c));
    CHECK(!slop_string_eq(a, (slop_string){19, a.data}));

    /* A String-keyed map finds a key through separately stored equal content */
    slop_map* m = slop_map_new_string(arena, 16);
    static int64_t one = 1;
    slop_map_put(arena, m, &a, &one);
    CHECK(slop_map_get(m, &copy) == &one);
    CHECK(slop_map_get(m, &c) == NULL);
}

int main(void) {
    slop_arena arena = slop_arena_new(1 << 20);

    test_capacity_rounding(&arena);
    test_basic(&arena);
    test_stored_hash_filters_eq(&arena);
    test_remove_across_wrap(&arena);
    test_grow();
    test_random_against_reference(&arena);
    test_hash_bytes_known_answers();
    test_strings(&arena);

    slop_arena_free(&arena);
    if (failures) {
        fprintf(stderr, "test_map: %d check(s) failed\n", failures);
        return 1;
    }
    printf("test_map: all checks passed\n");
    return 0;
}
