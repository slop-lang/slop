/*
 * Test: many threads reading maps that nobody is changing
 *
 * Run by scripts/run_native_tests.sh under ThreadSanitizer (files named
 * *_tsan.c are built with -fsanitize=thread). HOWL builds its maps on one
 * thread and then reads them from several; the runtime promises that get,
 * has and iteration never write, so this must be free of races with no
 * locking. A read path that wrote -- a lazily built table, a cached probe,
 * a move-to-front -- would be reported here.
 */

#include "slop_runtime.h"
#include <pthread.h>
#include <stdio.h>

enum { KEYS = 20000, THREADS = 4 };

static const slop_map_desc int_map = SLOP_MAP_DESC(int64_t, slop_hash_int, slop_eq_int, SLOP_KEY_BITS, int64_t);
static const slop_map_desc str_set = SLOP_SET_DESC(slop_string, slop_hash_string, slop_eq_string, SLOP_KEY_HASHED);

static slop_map* ints;
static slop_map* strs;
static slop_map* empty;
static char names[KEYS][24];

static void* reader(void* arg) {
    int64_t sum = 0;
    int64_t seed = (int64_t)(intptr_t)arg;
    for (int round = 0; round < 3; round++) {
        for (int64_t k = 0; k < KEYS; k++) {
            int64_t key = (k * 7 + seed) % (2 * KEYS);
            int64_t* v = (int64_t*)slop_map_get(ints, &key);
            if (v) sum += *v;
            if (slop_map_has(ints, &key)) sum++;
            slop_string s = {strlen(names[k]), names[k]};
            if (slop_map_has(strs, &s)) sum++;
            if (slop_map_has(empty, &key)) sum--;
        }
        for (size_t i = 0; i < ints->len; i++) {
            sum += *(int64_t*)slop_map_key_at(ints, i) + *(int64_t*)slop_map_value_at(ints, i);
        }
        for (size_t i = 0; i < strs->len; i++) {
            sum += (int64_t)((slop_string*)slop_map_key_at(strs, i))->len;
        }
    }
    return (void*)(intptr_t)(sum != 0);
}

int main(void) {
    slop_arena arena = slop_arena_new(1 << 16);
    ints = slop_map_new_ptr(&arena, 0, &int_map);
    strs = slop_map_new_ptr(&arena, 0, &str_set);
    empty = slop_map_new_ptr(&arena, 0, &int_map);
    for (int64_t k = 0; k < KEYS; k++) {
        int64_t v = k * 3;
        slop_map_put(&arena, ints, &k, &v, sizeof(v));
        snprintf(names[k], sizeof(names[k]), "name-%lld", (long long)k);
        slop_string s = {strlen(names[k]), names[k]};
        slop_map_put(&arena, strs, &s, NULL, 0);
    }

    pthread_t t[THREADS];
    for (intptr_t i = 0; i < THREADS; i++) pthread_create(&t[i], NULL, reader, (void*)i);
    int ok = 1;
    for (int i = 0; i < THREADS; i++) {
        void* r;
        pthread_join(t[i], &r);
        ok &= (int)(intptr_t)r;
    }
    slop_arena_free(&arena);
    if (!ok) {
        fprintf(stderr, "test_map_readers_tsan: a reader saw nothing\n");
        return 1;
    }
    printf("test_map_readers_tsan: all checks passed\n");
    return 0;
}
