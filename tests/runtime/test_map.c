/*
 * Test: slop_map (the runtime behind Map and Set)
 *
 * Run by scripts/run_native_tests.sh, which builds it with
 *   cc -g -O1 -fsanitize=address,undefined -I src/slop/runtime \
 *      -o test_map tests/runtime/test_map.c
 *
 * Keys are int64_t and, where a test needs to place keys exactly, each test
 * key's hash comes from a table, so a test can put a key's home index slot
 * where it wants: a collision chain, a chain that wraps past the end of the
 * index, a removal that has to shift slots back across the wrap.
 */

#include "slop_runtime.h"
#include <stdio.h>
#include <sys/wait.h>
#include <unistd.h>

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

static uint64_t counting_hash(const void* key) {
    hash_calls++;
    return slop_hash_int(key);
}

/* A raw hash whose mixed value has home slot `slot` in an index of `slots`.
 * `nth` picks among the candidates, so two keys can share a home slot yet
 * have different full hashes. */
static uint64_t hash_for_slot(size_t slot, size_t slots, int nth) {
    for (uint64_t c = 1;; c++) {
        if ((slop_map_mix(c) & (slots - 1)) == slot && nth-- == 0) return c;
    }
}

static const slop_map_desc int_bits = SLOP_MAP_DESC(int64_t, slop_hash_int, slop_eq_int, SLOP_KEY_BITS, int64_t);
static const slop_map_desc int_counted = SLOP_MAP_DESC(int64_t, counting_hash, counting_eq, SLOP_KEY_BITS, int64_t);
static const slop_map_desc tab_hashed = SLOP_MAP_DESC(int64_t, table_hash, counting_eq, SLOP_KEY_HASHED, int64_t);
static const slop_map_desc tab_call = SLOP_MAP_DESC(int64_t, table_hash, counting_eq, SLOP_KEY_CALL, int64_t);
static const slop_map_desc tab_bits = SLOP_MAP_DESC(int64_t, table_hash, counting_eq, SLOP_KEY_BITS, int64_t);
static const slop_map_desc int_set = SLOP_SET_DESC(int64_t, slop_hash_int, slop_eq_int, SLOP_KEY_BITS);

static void put(slop_arena* arena, slop_map* m, int64_t k, int64_t v) {
    slop_map_put(arena, m, &k, &v, sizeof(v));
}

static int64_t get(slop_map* m, int64_t k) {
    int64_t* v = (int64_t*)slop_map_get(m, &k);
    return v ? *v : -1;
}

static uint8_t* index_of(const slop_map* m) {
    return m->table + slop_map_index_off(m->desc, m->cap);
}

/* Index slot pointing at key k's entry, or -1 */
static long slot_of(slop_map* m, int64_t k) {
    size_t w = slop_map_index_width(m->cap);
    for (size_t s = 0; s < 2 * m->cap; s++) {
        size_t v = slop_map_slot_load(index_of(m), w, s);
        if (v != 0 && *(int64_t*)slop_map_key_at(m, slop_map_slot_entry(m->cap, v)) == k) return (long)s;
    }
    return -1;
}

/* Entry number holding key k, or -1 */
static long entry_of(slop_map* m, int64_t k) {
    for (size_t i = 0; i < m->len; i++) {
        if (*(int64_t*)slop_map_key_at(m, i) == k) return (long)i;
    }
    return -1;
}

/* Every live entry is pointed at by exactly one index slot, which carries
 * the entry's hash tag, no slot points past len, every entry's slot is
 * reachable from its home slot without crossing an empty one, and a stored
 * hash is the hash of its own key. */
static void check_invariants(slop_map* m) {
    if (m->cap == 0) { CHECK(m->len == 0 && m->table == NULL); return; }
    CHECK((m->cap & (m->cap - 1)) == 0);
    CHECK(m->len <= m->cap);
    size_t slots = 2 * m->cap, mask = slots - 1;
    size_t w = slop_map_index_width(m->cap);
    static unsigned char pointed[1 << 18];
    CHECK(m->len <= sizeof(pointed));
    memset(pointed, 0, m->len);
    size_t used = 0;
    int saved = hash_calls;
    for (size_t s = 0; s < slots; s++) {
        size_t v = slop_map_slot_load(index_of(m), w, s);
        if (v == 0) continue;
        used++;
        size_t e = slop_map_slot_entry(m->cap, v);
        CHECK(e < m->len);
        if (e >= m->len) continue;
        CHECK(!pointed[e]);
        pointed[e] = 1;
        uint64_t h = slop_map_mix(m->desc->hash(slop_map_key_at(m, e)));
        if (m->desc->mode == SLOP_KEY_HASHED) CHECK(slop_map_entry_hash(m, e) == h);
        /* The slot carries its entry's hash tag */
        CHECK(v == slop_map_slot_value(m->cap, e, h));
        for (size_t p = h & mask; p != s; p = (p + 1) & mask) {
            CHECK(slop_map_slot_load(index_of(m), w, p) != 0);
        }
    }
    hash_calls = saved;
    CHECK(used == m->len);
}

/* ------------------------------------------------------------
 * Layout
 * ------------------------------------------------------------ */

static void test_desc_layout(void) {
    /* Int -> Int, no stored hash: 16-byte entries */
    CHECK(int_bits.key_size == 8 && int_bits.value_size == 8);
    CHECK(int_bits.value_off == 8 && int_bits.entry_size == 16);
    /* A Set of Int stores nothing but the key */
    CHECK(int_set.value_size == 0 && int_set.entry_size == 8);
    /* Stored hash after the value */
    CHECK(tab_hashed.hash_off == 16 && tab_hashed.entry_size == 24);

    /* Mixed alignment: a 1-byte key before an 8-aligned value */
    static const slop_map_desc i8_double = SLOP_MAP_DESC(int8_t, slop_hash_i8, slop_eq_i8, SLOP_KEY_BITS, double);
    CHECK(i8_double.value_off == 8 && i8_double.entry_size == 16);
    /* String key, Bool value, stored hash: 16 + 1, padded to 24, + 8 */
    static const slop_map_desc str_bool = SLOP_MAP_DESC(slop_string, slop_hash_string, slop_eq_string, SLOP_KEY_HASHED, bool);
    CHECK(str_bool.value_off == 16 && str_bool.hash_off == 24 && str_bool.entry_size == 32);
    /* Byte-sized sets pack: 1-byte entries, or 16 with a stored hash */
    static const slop_map_desc u8_set = SLOP_SET_DESC(uint8_t, slop_hash_u8, slop_eq_u8, SLOP_KEY_BITS);
    static const slop_map_desc u8_set_h = SLOP_SET_DESC(uint8_t, slop_hash_u8, slop_eq_u8, SLOP_KEY_HASHED);
    CHECK(u8_set.entry_size == 1 && u8_set_h.hash_off == 8 && u8_set_h.entry_size == 16);
    /* A 4-byte key with a 4-byte value stays 4-aligned: 8-byte entries */
    static const slop_map_desc f32_i32 = SLOP_MAP_DESC(float, slop_hash_float, slop_eq_float, SLOP_KEY_CALL, int32_t);
    CHECK(f32_i32.value_off == 4 && f32_i32.entry_size == 8);

    /* Index width follows capacity, leaving room for a hash tag */
    CHECK(slop_map_index_width(4) == 1 && slop_map_index_width(64) == 1);
    CHECK(slop_map_index_width(128) == 2 && slop_map_index_width(2048) == 2);
    CHECK(slop_map_index_width(4096) == 4 && slop_map_index_width((size_t)1 << 23) == 4);
    CHECK(slop_map_index_width((size_t)1 << 24) == 8);
    for (size_t cap = 4; cap <= ((size_t)1 << 30); cap <<= 1) {
        size_t bits = 8 * slop_map_index_width(cap);
        CHECK(slop_map_idx_bits(cap) < bits);                     /* a tag fits */
        size_t v = slop_map_slot_value(cap, cap - 1, ~(uint64_t)0);
        CHECK(slop_map_slot_entry(cap, v) == cap - 1);            /* the entry survives the tag */
        CHECK(bits == 64 || (v >> bits) == 0);                    /* and it fits the slot */
    }
}

/* Values of every alignment come back intact, through puts, overwrites,
 * growth and removal */
static void test_mixed_alignment(slop_arena* arena) {
    static const slop_map_desc d = SLOP_MAP_DESC(int8_t, slop_hash_i8, slop_eq_i8, SLOP_KEY_BITS, double);
    slop_map m = slop_map_new(arena, 0, &d);
    for (int k = -100; k < 100; k++) {
        int8_t key = (int8_t)k;
        double v = k * 0.5;
        slop_map_put(arena, &m, &key, &v, sizeof(v));
    }
    CHECK(m.len == 200);
    for (int k = -100; k < 100; k++) {
        int8_t key = (int8_t)k;
        double* v = (double*)slop_map_get(&m, &key);
        CHECK(v != NULL && *v == k * 0.5);
        CHECK(((uintptr_t)v & 7) == 0);
    }
    for (int k = -100; k < 100; k += 3) {
        int8_t key = (int8_t)k;
        CHECK(slop_map_remove(&m, &key));
    }
    for (int k = -100; k < 100; k++) {
        int8_t key = (int8_t)k;
        double* v = (double*)slop_map_get(&m, &key);
        CHECK((v != NULL) == ((k + 100) % 3 != 0));
        if (v) CHECK(*v == k * 0.5);
    }

    static const slop_map_desc sb = SLOP_MAP_DESC(slop_string, slop_hash_string, slop_eq_string, SLOP_KEY_HASHED, bool);
    slop_map s = slop_map_new(arena, 0, &sb);
    const char* words[] = {"alpha", "beta", "gamma", "delta", "epsilon", "zeta"};
    for (int i = 0; i < 6; i++) {
        slop_string k = {strlen(words[i]), words[i]};
        bool v = (i % 2) == 0;
        slop_map_put(arena, &s, &k, &v, sizeof(v));
    }
    for (int i = 0; i < 6; i++) {
        char buf[16];
        strcpy(buf, words[i]);
        slop_string k = {strlen(buf), buf};
        bool* v = (bool*)slop_map_get(&s, &k);
        CHECK(v != NULL && *v == ((i % 2) == 0));
    }
}

/* ------------------------------------------------------------
 * Construction and the lazy table
 * ------------------------------------------------------------ */

static void test_capacity_rounding(slop_arena* arena) {
    CHECK(slop_map_new(arena, 1, &int_bits).cap == 4);
    CHECK(slop_map_new(arena, 5, &int_bits).cap == 8);
    CHECK(slop_map_new(arena, 16, &int_bits).cap == 16);
    CHECK(slop_map_new(arena, 17, &int_bits).cap == 32);
}

/* Capacity 0 -- what map-new and set-new ask for -- makes no table at all.
 * Reads of it neither allocate nor write, so concurrent readers of a map
 * nobody mutates stay safe; the first put makes a SLOP_MAP_FIRST_CAPACITY
 * table, and a lazy and an eager map end up byte-identical. */
static void test_lazy_table(void) {
    slop_arena own = slop_arena_new(1 << 16);
    slop_arena* arena = &own;

    size_t before = arena->offset;
    slop_map m = slop_map_new(arena, 0, &int_counted);
    CHECK(m.cap == 0 && m.len == 0 && m.table == NULL);
    CHECK(arena->offset == before);

    /* Reads: absent, no hashing, no allocation, not a byte of the map changed */
    slop_map snapshot = m;
    hash_calls = 0;
    CHECK(slop_map_get(&m, &(int64_t){1}) == NULL);
    CHECK(!slop_map_has(&m, &(int64_t){1}));
    CHECK(!slop_map_remove(&m, &(int64_t){1}));
    CHECK(hash_calls == 0);
    CHECK(arena->offset == before);
    CHECK(memcmp(&snapshot, &m, sizeof(m)) == 0);

    /* Iteration, the way generated for-each loops read the table */
    size_t visited = 0;
    for (size_t i = 0; i < m.len; i++) visited++;
    CHECK(visited == 0);
    slop_set_elements_result els = slop_set_elements_raw(arena, &m);
    CHECK(els.data == NULL && els.len == 0 && els.cap == 0);
    slop_map_string_int sm = slop_map_string_int_new(arena, 0);
    CHECK(slop_map_keys(arena, &sm).len == 0);

    /* The first put makes the first table and nothing else: no key copy,
     * no value copy */
    before = arena->offset;
    put(arena, &m, 7, 1);
    CHECK(m.cap == SLOP_MAP_FIRST_CAPACITY && m.len == 1);
    CHECK(arena->offset - before == ((slop_map_table_bytes(&int_counted, 4) + 7) & ~(size_t)7));
    CHECK(get(&m, 7) == 1);

    /* Removing back to empty keeps the table; lookups still answer absent */
    CHECK(slop_map_remove(&m, &(int64_t){7}));
    CHECK(m.len == 0 && m.cap == 4);
    CHECK(get(&m, 7) == -1);
    put(arena, &m, 8, 2);
    CHECK(get(&m, 8) == 2 && m.len == 1);

    /* The same insertions into a lazy and an eager map leave identical tables */
    slop_map lazy = slop_map_new(arena, 0, &int_bits);
    slop_map eager = slop_map_new(arena, 16, &int_bits);
    for (int64_t k = 0; k < 200; k++) {
        put(arena, &lazy, k * 7919, k);
        put(arena, &eager, k * 7919, k);
    }
    CHECK(lazy.cap == eager.cap && lazy.len == eager.len);
    if (lazy.cap == eager.cap) {
        CHECK(memcmp(lazy.table, eager.table, lazy.len * int_bits.entry_size) == 0);
        CHECK(memcmp(index_of(&lazy), index_of(&eager),
                     2 * lazy.cap * slop_map_index_width(lazy.cap)) == 0);
    }
    slop_arena_free(&own);
}

/* ------------------------------------------------------------
 * Basic behaviour
 * ------------------------------------------------------------ */

static void test_basic(slop_arena* arena) {
    slop_map* m = slop_map_new_ptr(arena, 0, &int_bits);
    for (int64_t k = 0; k < 1000; k++) put(arena, m, k, k * 3);
    CHECK(m->len == 1000);
    CHECK((m->cap & (m->cap - 1)) == 0);
    for (int64_t k = 0; k < 1000; k++) CHECK(get(m, k) == k * 3);
    CHECK(!slop_map_has(m, &(int64_t){1000}));
    CHECK(!slop_map_has(m, &(int64_t){-1}));
    check_invariants(m);

    /* Iteration is insertion order */
    for (size_t i = 0; i < m->len; i++) CHECK(*(int64_t*)slop_map_key_at(m, i) == (int64_t)i);

    /* Overwrite keeps len and position and replaces the value in place,
     * allocating nothing */
    size_t before = arena->offset;
    void* where = slop_map_get(m, &(int64_t){5});
    put(arena, m, 5, 77);
    CHECK(m->len == 1000);
    CHECK(get(m, 5) == 77);
    CHECK(slop_map_get(m, &(int64_t){5}) == where);
    CHECK(arena->offset == before);

    for (int64_t k = 0; k < 1000; k += 2) CHECK(slop_map_remove(m, &k));
    CHECK(m->len == 500);
    for (int64_t k = 0; k < 1000; k++) CHECK(slop_map_has(m, &k) == (k % 2 == 1));
    check_invariants(m);
}

/* A remove moves the last entry into the hole, so order stays a function of
 * the operations */
static void test_remove_order(slop_arena* arena) {
    slop_map m = slop_map_new(arena, 0, &int_bits);
    for (int64_t k = 1; k <= 5; k++) put(arena, &m, k, k * 10);
    CHECK(slop_map_remove(&m, &(int64_t){2}));
    int64_t want[] = {1, 5, 3, 4};
    CHECK(m.len == 4);
    for (size_t i = 0; i < 4; i++) {
        CHECK(*(int64_t*)slop_map_key_at(&m, i) == want[i]);
        CHECK(*(int64_t*)slop_map_value_at(&m, i) == want[i] * 10);
    }
    /* Removing the last entry moves nothing */
    CHECK(slop_map_remove(&m, &(int64_t){4}));
    CHECK(m.len == 3 && *(int64_t*)slop_map_key_at(&m, 2) == 3);
    check_invariants(&m);
    /* Re-putting a removed key appends it */
    put(arena, &m, 2, 99);
    CHECK(*(int64_t*)slop_map_key_at(&m, 3) == 2 && get(&m, 2) == 99);
    check_invariants(&m);
}

/* ------------------------------------------------------------
 * How a probe matches a key, per mode
 * ------------------------------------------------------------ */

/* HASHED: keys that share a home slot but differ in full hash never reach
 * eq; keys with the same full hash (a true collision) are told apart by eq. */
static void test_hashed_filters_eq(slop_arena* arena) {
    slop_map m = slop_map_new(arena, 4, &tab_hashed);   /* 8 index slots */
    for (int i = 0; i < 4; i++) key_hash[i] = hash_for_slot(3, 8, i);
    for (int64_t k = 0; k < 4; k++) put(arena, &m, k, k + 100);
    CHECK(slot_of(&m, 0) == 3 && slot_of(&m, 3) == 6);

    eq_calls = 0;
    CHECK(get(&m, 3) == 103);
    CHECK(eq_calls == 1);                   /* only the matching entry */

    /* Full collisions: identical hashes, so every probe compares */
    slop_map c = slop_map_new(arena, 4, &tab_hashed);
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

/* The tag a raw hash gets in a table of cap entries */
static size_t tag_of(size_t cap, uint64_t raw) {
    return slop_map_slot_value(cap, 0, slop_map_mix(raw)) >> slop_map_idx_bits(cap);
}

/* CALL: eq only on an entry whose slot tag matches. BITS: eq never called. */
static void test_call_and_bits_modes(slop_arena* arena) {
    /* Keys 0-2 share key 3's home slot (3 of 8) but not its tag: the probe
     * passes their slots without reading their entries */
    key_hash[3] = hash_for_slot(3, 8, 0);
    uint64_t c = 1;
    for (int i = 0; i < 3; i++) {
        while ((slop_map_mix(c) & 7) != 3 || c == key_hash[3] ||
               tag_of(4, c) == tag_of(4, key_hash[3])) c++;
        key_hash[i] = c++;
    }
    slop_map t = slop_map_new(arena, 4, &tab_call);
    for (int64_t k = 0; k < 4; k++) put(arena, &t, k, k + 100);
    CHECK(slot_of(&t, 3) == 6);                         /* behind the other three */
    eq_calls = 0;
    CHECK(get(&t, 3) == 103);
    CHECK(eq_calls == 1);
    check_invariants(&t);

    /* Identical hashes share slot and tag, so each entry probed reaches eq */
    for (int i = 10; i < 14; i++) key_hash[i] = hash_for_slot(5, 8, 0);
    slop_map cc = slop_map_new(arena, 4, &tab_call);
    for (int64_t k = 10; k < 14; k++) put(arena, &cc, k, k);
    eq_calls = 0;
    CHECK(get(&cc, 13) == 13);
    CHECK(eq_calls == 4);
    check_invariants(&cc);

    for (int i = 0; i < 4; i++) key_hash[i] = hash_for_slot(3, 8, i);

    slop_map b = slop_map_new(arena, 4, &tab_bits);
    for (int64_t k = 0; k < 4; k++) put(arena, &b, k, k + 100);
    eq_calls = 0;
    CHECK(get(&b, 3) == 103 && get(&b, 0) == 100);
    CHECK(!slop_map_has(&b, &(int64_t){5}));
    CHECK(slop_map_remove(&b, &(int64_t){1}));
    CHECK(get(&b, 1) == -1 && get(&b, 2) == 102);
    CHECK(eq_calls == 0);
    check_invariants(&b);
}

/* ------------------------------------------------------------
 * Removal across the index's wrap-around
 * ------------------------------------------------------------ */

/* cap 4, 8 slots: A(home 6)@6  B(home 6)@7  C(home 7)@0  D(home 0)@1 */
static void setup_wrap(slop_arena* arena, slop_map* m) {
    *m = slop_map_new(arena, 4, &tab_hashed);
    key_hash[20] = hash_for_slot(6, 8, 0);   /* A */
    key_hash[21] = hash_for_slot(6, 8, 1);   /* B */
    key_hash[22] = hash_for_slot(7, 8, 0);   /* C */
    key_hash[23] = hash_for_slot(0, 8, 0);   /* D */
    for (int64_t k = 20; k < 24; k++) put(arena, m, k, k);
}

static bool slot_empty(slop_map* m, size_t s) {
    return slop_map_slot_load(index_of(m), slop_map_index_width(m->cap), s) == 0;
}

static void test_remove_across_wrap(slop_arena* arena) {
    slop_map m;

    setup_wrap(arena, &m);
    CHECK(m.cap == 4);
    CHECK(slot_of(&m, 20) == 6 && slot_of(&m, 21) == 7);
    CHECK(slot_of(&m, 22) == 0 && slot_of(&m, 23) == 1);

    /* Removing A shifts B, C and D back one slot each, C and D across the
     * wrap; D, the last entry, moves into A's entry */
    CHECK(slop_map_remove(&m, &(int64_t){20}));
    CHECK(slot_of(&m, 21) == 6 && slot_of(&m, 22) == 7 && slot_of(&m, 23) == 0);
    CHECK(slot_empty(&m, 1));
    CHECK(entry_of(&m, 23) == 0);
    CHECK(get(&m, 20) == -1 && get(&m, 21) == 21 && get(&m, 22) == 22 && get(&m, 23) == 23);
    CHECK(m.len == 3);
    check_invariants(&m);

    /* Removing C (at slot 0, past the wrap) pulls D back into slot 0 */
    setup_wrap(arena, &m);
    CHECK(slop_map_remove(&m, &(int64_t){22}));
    CHECK(slot_of(&m, 23) == 0 && slot_empty(&m, 1));
    CHECK(get(&m, 20) == 20 && get(&m, 21) == 21 && get(&m, 23) == 23);
    check_invariants(&m);

    /* Removing B: C (home 7) moves into the hole at 7, and D follows into 0 */
    setup_wrap(arena, &m);
    CHECK(slop_map_remove(&m, &(int64_t){21}));
    CHECK(slot_of(&m, 20) == 6 && slot_of(&m, 22) == 7 && slot_of(&m, 23) == 0);
    check_invariants(&m);

    /* Removing D, the last in the chain and the last entry, moves nothing */
    setup_wrap(arena, &m);
    CHECK(slop_map_remove(&m, &(int64_t){23}));
    CHECK(slot_of(&m, 20) == 6 && slot_of(&m, 21) == 7 && slot_of(&m, 22) == 0);
    CHECK(entry_of(&m, 20) == 0 && entry_of(&m, 22) == 2);
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

/* ------------------------------------------------------------
 * Growth
 * ------------------------------------------------------------ */

/* A table that is the last allocation in its block grows where it stands;
 * one that is not is moved, leaving the old block as it was. Both end in the
 * same bytes. A stored hash is never recomputed. */
static void test_grow_in_place_and_moved(void) {
    slop_arena own = slop_arena_new(1 << 16);
    slop_arena* arena = &own;
    for (int i = 30; i < 38; i++) key_hash[i] = hash_for_slot(5, 8, i - 30);

    slop_map a = slop_map_new(arena, 0, &tab_hashed);
    for (int64_t k = 30; k < 34; k++) put(arena, &a, k, k);
    CHECK(a.cap == 4);
    uint8_t* at = a.table;
    size_t before = arena->offset;
    hash_calls = 0;
    eq_calls = 0;
    slop_map_grow(arena, &a);
    CHECK(hash_calls == 0 && eq_calls == 0);
    CHECK(a.table == at);                            /* in place */
    CHECK(arena->offset - before ==
          slop_map_table_bytes(&tab_hashed, 8) - slop_map_table_bytes(&tab_hashed, 4));
    check_invariants(&a);

    /* Same puts, but something else is allocated after the table */
    slop_map b = slop_map_new(arena, 0, &tab_hashed);
    for (int64_t k = 30; k < 34; k++) put(arena, &b, k, k);
    uint8_t* bt = b.table;
    unsigned char old_bytes[256];
    size_t old_size = slop_map_table_bytes(&tab_hashed, 4);
    memcpy(old_bytes, bt, old_size);
    (void)slop_arena_alloc(arena, 8);
    before = arena->offset;
    slop_map_grow(arena, &b);
    CHECK(b.table != bt);                            /* moved */
    CHECK(memcmp(old_bytes, bt, old_size) == 0);     /* old block untouched */
    CHECK(arena->offset - before == ((slop_map_table_bytes(&tab_hashed, 8) + 7) & ~(size_t)7));
    check_invariants(&b);

    /* Identical entries and index either way */
    CHECK(a.cap == b.cap && a.len == b.len);
    CHECK(memcmp(a.table, b.table, a.len * tab_hashed.entry_size) == 0);
    CHECK(memcmp(index_of(&a), index_of(&b), 2 * a.cap * slop_map_index_width(a.cap)) == 0);

    /* The 5th put triggers the grow; one hash call, for the new key */
    slop_map g = slop_map_new(arena, 0, &tab_hashed);
    for (int64_t k = 30; k < 34; k++) put(arena, &g, k, k);
    hash_calls = 0;
    put(arena, &g, 34, 34);
    CHECK(hash_calls == 1);
    CHECK(g.cap == 8 && g.len == 5);
    for (int64_t k = 30; k < 35; k++) CHECK(get(&g, k) == k);
    check_invariants(&g);
    slop_arena_free(&own);
}

/* Two maps growing alternately in one arena never extend over each other,
 * and end with the same contents and order as maps grown alone */
static void test_interleaved_growth(void) {
    slop_arena shared = slop_arena_new(1 << 12);
    slop_arena alone1 = slop_arena_new(1 << 12);
    slop_arena alone2 = slop_arena_new(1 << 12);
    slop_map x = slop_map_new(&shared, 0, &int_bits);
    slop_map y = slop_map_new(&shared, 0, &int_bits);
    slop_map x1 = slop_map_new(&alone1, 0, &int_bits);
    slop_map y1 = slop_map_new(&alone2, 0, &int_bits);
    for (int64_t k = 0; k < 5000; k++) {
        put(&shared, &x, k * 3, k);
        put(&shared, &y, k * 5, -k);
        put(&alone1, &x1, k * 3, k);
        put(&alone2, &y1, k * 5, -k);
    }
    for (int64_t k = 0; k < 5000; k++) {
        CHECK(get(&x, k * 3) == k && get(&y, k * 5) == -k);
    }
    CHECK(x.cap == x1.cap && y.cap == y1.cap);
    CHECK(memcmp(x.table, x1.table, x.len * int_bits.entry_size) == 0);
    CHECK(memcmp(y.table, y1.table, y.len * int_bits.entry_size) == 0);
    CHECK(memcmp(index_of(&x), index_of(&x1), 2 * x.cap * slop_map_index_width(x.cap)) == 0);
    check_invariants(&x);
    check_invariants(&y);
    slop_arena_free(&shared);
    slop_arena_free(&alone1);
    slop_arena_free(&alone2);
}

/* Growth goes to the arena named at the put: a map made in one arena and
 * put to through another has its table moved into the second, and the first
 * is never extended */
static void test_growth_goes_to_put_arena(void) {
    slop_arena home = slop_arena_new(1 << 12);
    slop_arena other = slop_arena_new(1 << 16);
    slop_map* m = slop_map_new_ptr(&home, 4, &int_bits);
    put(&home, m, 1, 1);
    size_t home_used = home.offset;
    for (int64_t k = 2; k < 100; k++) put(&other, m, k, k);
    CHECK(home.offset == home_used && home.next == NULL);
    CHECK(m->table >= other.base && m->table < other.base + other.capacity);
    for (int64_t k = 1; k < 100; k++) CHECK(get(m, k) == k);
    check_invariants(m);

    /* An extend never reaches a pointer outside the arena named */
    void* p = slop_arena_alloc(&home, 64);
    CHECK(!slop_arena_try_extend(&other, p, 64, 128));
    CHECK(slop_arena_try_extend(&home, p, 64, 128));
    slop_arena_free(&home);
    slop_arena_free(&other);
}

/* A table alone in its block grows by realloc'ing the block, so a big map
 * leaves nothing abandoned behind it */
static void test_sole_block_realloc(void) {
    slop_arena own = slop_arena_new(64);
    slop_map* m = slop_map_new_ptr(&own, 0, &int_bits);   /* struct in the head */
    for (int64_t k = 0; k < 100000; k++) put(&own, m, k, k);
    size_t used = 0, blocks = 0;
    for (slop_arena* a = &own; a != NULL; a = a->next) { used += a->offset; blocks++; }
    size_t table = (slop_map_table_bytes(&int_bits, m->cap) + 7) & ~(size_t)7;
    CHECK(used <= table + 64);
    CHECK(blocks <= 3);
    for (int64_t k = 0; k < 100000; k++) CHECK(get(m, k) == k);
    check_invariants(m);
    slop_arena_free(&own);
}

/* A put whose value (or key) is read out of the very table it grows must
 * not free that table first: it is moved from instead. Under ASan a freed
 * read is an error. */
static void test_put_from_own_table(void) {
    slop_arena own = slop_arena_new(64);
    slop_map* m = slop_map_new_ptr(&own, 0, &int_bits);
    for (int64_t k = 1; k <= 4; k++) put(&own, m, k, k * 10);
    CHECK(m->cap == 4 && m->len == 4 && m->table == own.next->base);   /* alone in block 1 */
    int64_t k100 = 100;
    slop_map_put(&own, m, &k100, slop_map_value_at(m, 0), sizeof(int64_t));
    CHECK(get(m, 100) == 10 && m->cap == 8);
    for (int64_t k = 5; k <= 8; k++) put(&own, m, k, k * 10);
    /* Key aliasing too: key 1's entry copied as a new key into a new map */
    slop_map* n = slop_map_new_ptr(&own, 0, &int_bits);
    for (int64_t k = 1; k <= 4; k++) put(&own, n, k * 1000, k);
    slop_map_put(&own, n, slop_map_key_at(n, 0), &(int64_t){7}, sizeof(int64_t));  /* overwrite */
    CHECK(get(n, 1000) == 7 && n->len == 4);
    check_invariants(m);
    check_invariants(n);
    slop_arena_free(&own);
}

/* The index widens as cap passes 128 and 32768 entries */
static void test_index_widths(void) {
    slop_arena own = slop_arena_new(1 << 20);
    slop_map m = slop_map_new(&own, 0, &int_bits);
    size_t widths_seen = 0, last_w = 0;
    for (int64_t k = 0; k < 70000; k++) {
        put(&own, &m, k * 2654435761LL, k);
        size_t w = slop_map_index_width(m.cap);
        if (w != last_w) { widths_seen++; last_w = w; }
    }
    CHECK(widths_seen == 3 && last_w == 4);
    for (int64_t k = 0; k < 70000; k++) CHECK(get(&m, k * 2654435761LL) == k);
    check_invariants(&m);
    for (int64_t k = 0; k < 70000; k += 7) CHECK(slop_map_remove(&m, &(int64_t){k * 2654435761LL}));
    for (int64_t k = 0; k < 70000; k++) CHECK((get(&m, k * 2654435761LL) == k) == (k % 7 != 0));
    check_invariants(&m);
    slop_arena_free(&own);
}

/* ------------------------------------------------------------
 * Workloads HOWL doesn't have
 * ------------------------------------------------------------ */

/* Overwrites allocate nothing, however many */
static void test_overwrite_allocates_nothing(void) {
    slop_arena own = slop_arena_new(1 << 16);
    slop_map m = slop_map_new(&own, 0, &int_bits);
    for (int64_t k = 0; k < 10; k++) put(&own, &m, k, k);
    size_t used = own.offset;
    for (int64_t i = 0; i < 1000000; i++) put(&own, &m, i % 10, i);
    CHECK(own.offset == used && own.next == NULL);
    for (int64_t k = 0; k < 10; k++) CHECK(get(&m, k) == 999990 + k);
    slop_arena_free(&own);
}

/* Put/remove churn holds the table at its size */
static void test_churn_is_bounded(void) {
    slop_arena own = slop_arena_new(1 << 16);
    slop_map m = slop_map_new(&own, 0, &int_bits);
    for (int64_t i = 0; i < 1000000; i++) {
        put(&own, &m, i, i);
        if (i >= 8) CHECK(slop_map_remove(&m, &(int64_t){i - 8}));
    }
    CHECK(m.len == 8 && m.cap <= 16);
    CHECK(own.offset < 1024 && own.next == NULL);
    for (int64_t i = 1000000 - 8; i < 1000000; i++) CHECK(get(&m, i) == i);
    check_invariants(&m);
    slop_arena_free(&own);
}

/* A put that grows the table or a remove inside a loop over it, the way
 * generated for-each loops read it, stays in bounds (the result is
 * unspecified, but every key read is one that was put) */
static void test_mutation_during_iteration(slop_arena* arena) {
    slop_map* m = slop_map_new_ptr(arena, 0, &int_bits);
    for (int64_t k = 0; k < 6; k++) put(arena, m, k, k);
    size_t steps = 0;
    for (size_t i = 0; i < m->len && steps < 1000; i++, steps++) {
        int64_t k = *(int64_t*)slop_map_key_at(m, i);
        int64_t v = *(int64_t*)slop_map_value_at(m, i);
        CHECK(k >= 0 && k < 1006 && v == k);
        if (k < 1000) put(arena, m, k + 1000, k + 1000);   /* grows */
    }
    check_invariants(m);
    for (size_t i = 0; i < m->len; i++) {
        int64_t k = *(int64_t*)slop_map_key_at(m, i);
        CHECK(k >= 0 && k < 1006);
        slop_map_remove(m, &k);                            /* removes current */
    }
    check_invariants(m);
}

/* A put whose value size is not the map's aborts rather than overrun */
static void test_value_size_mismatch_aborts(slop_arena* arena) {
    fflush(stdout);
    fflush(stderr);
    pid_t pid = fork();
    if (pid == 0) {
        freopen("/dev/null", "w", stderr);
        slop_map m = slop_map_new(arena, 0, &int_bits);
        int32_t small = 1;
        slop_map_put(arena, &m, &(int64_t){1}, &small, sizeof(small));
        _exit(0);
    }
    int status = 0;
    waitpid(pid, &status, 0);
    CHECK(WIFSIGNALED(status) && WTERMSIG(status) == SIGABRT);
}

/* ------------------------------------------------------------
 * Sets
 * ------------------------------------------------------------ */

static void test_sets(slop_arena* arena) {
    slop_map s = slop_map_new(arena, 0, &int_set);
    for (int64_t k = 0; k < 300; k++) slop_map_put(arena, &s, &(int64_t){k * 11}, NULL, 0);
    for (int64_t k = 0; k < 300; k++) slop_map_put(arena, &s, &(int64_t){k * 11}, NULL, 0);
    CHECK(s.len == 300);
    CHECK(slop_map_has(&s, &(int64_t){33}) && !slop_map_has(&s, &(int64_t){34}));
    /* No stored value or hash: a set of Int is its keys, contiguously */
    slop_set_elements_result els = slop_set_elements_raw(arena, &s);
    CHECK(els.len == 300);
    for (size_t i = 0; i < els.len; i++) CHECK(((int64_t*)els.data)[i] == (int64_t)i * 11);
    check_invariants(&s);

    /* A set that stores hashes is copied key by key */
    static const slop_map_desc hs = SLOP_SET_DESC(int64_t, slop_hash_int, slop_eq_int, SLOP_KEY_HASHED);
    slop_map h = slop_map_new(arena, 0, &hs);
    for (int64_t k = 0; k < 50; k++) slop_map_put(arena, &h, &k, NULL, 0);
    els = slop_set_elements_raw(arena, &h);
    CHECK(els.len == 50);
    for (size_t i = 0; i < els.len; i++) CHECK(((int64_t*)els.data)[i] == (int64_t)i);
}

/* ------------------------------------------------------------
 * A long random sequence against a reference, in every mode
 * ------------------------------------------------------------ */

/* A weak hash (all low bits zero) still spreads */
static uint64_t weak_hash(const void* key) {
    return (uint64_t)(*(const int64_t*)key) << 20;
}

static void random_against_reference(slop_arena* arena, const slop_map_desc* d) {
    enum { SPACE = 512, OPS = 200000 };
    slop_map m = slop_map_new(arena, 0, d);
    static bool present[SPACE];
    static int64_t vals[SPACE];
    memset(present, 0, sizeof(present));
    uint64_t rng = 12345;
    size_t len = 0;
    for (int op = 0; op < OPS; op++) {
        rng = rng * 6364136223846793005ULL + 1442695040888963407ULL;
        int64_t k = (int64_t)((rng >> 33) % SPACE);
        if ((rng >> 20) & 1) {
            if (!present[k]) len++;
            present[k] = true;
            vals[k] = op;
            put(arena, &m, k, op);
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
    memset(home_used, 0, sizeof(home_used));
    for (size_t i = 0; i < m.len; i++) {
        size_t h = slop_map_mix(d->hash(slop_map_key_at(&m, i))) & (2 * m.cap - 1);
        if (h < 4096 && !home_used[h]) { home_used[h] = true; distinct_homes++; }
    }
    CHECK(distinct_homes > m.len / 2);
}

static void test_random_against_reference(slop_arena* arena) {
    static const slop_map_desc weak_bits = SLOP_MAP_DESC(int64_t, weak_hash, slop_eq_int, SLOP_KEY_BITS, int64_t);
    static const slop_map_desc weak_call = SLOP_MAP_DESC(int64_t, weak_hash, slop_eq_int, SLOP_KEY_CALL, int64_t);
    static const slop_map_desc weak_hashed = SLOP_MAP_DESC(int64_t, weak_hash, slop_eq_int, SLOP_KEY_HASHED, int64_t);
    random_against_reference(arena, &weak_bits);
    random_against_reference(arena, &weak_call);
    random_against_reference(arena, &weak_hashed);
}

/* ------------------------------------------------------------
 * Strings
 * ------------------------------------------------------------ */

/* Known answers pin slop_hash_bytes across platforms and releases. The
 * values were cross-checked against an independent reimplementation of the
 * algorithm. */
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

    /* A String-keyed map finds a key through separately stored equal
     * content, and lists its keys in order */
    slop_map_string_int m = slop_map_string_int_new(arena, 0);
    slop_map_string_int_put(arena, &m, a, 1);
    slop_map_string_int_put(arena, &m, c, 2);
    slop_map_string_int_put(arena, &m, copy, 3);             /* overwrites a */
    slop_option_int got = slop_map_string_int_get(&m, copy);
    CHECK(got.has_value && got.value == 3);
    CHECK(!slop_map_string_int_has(&m, (slop_string){19, a.data}));
    slop_list_string keys = slop_map_keys(arena, &m);
    CHECK(keys.len == 2 && slop_string_eq(keys.data[0], a) && slop_string_eq(keys.data[1], c));
}

int main(void) {
    slop_arena arena = slop_arena_new(1 << 20);

    test_desc_layout();
    test_mixed_alignment(&arena);
    test_capacity_rounding(&arena);
    test_lazy_table();
    test_basic(&arena);
    test_remove_order(&arena);
    test_hashed_filters_eq(&arena);
    test_call_and_bits_modes(&arena);
    test_remove_across_wrap(&arena);
    test_grow_in_place_and_moved();
    test_interleaved_growth();
    test_growth_goes_to_put_arena();
    test_sole_block_realloc();
    test_put_from_own_table();
    test_index_widths();
    test_overwrite_allocates_nothing();
    test_churn_is_bounded();
    test_mutation_during_iteration(&arena);
    test_value_size_mismatch_aborts(&arena);
    test_sets(&arena);
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
