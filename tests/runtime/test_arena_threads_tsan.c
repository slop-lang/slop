/*
 * Test: threads creating and freeing arenas at once
 *
 * Run by scripts/run_native_tests.sh under ThreadSanitizer (files named
 * *_tsan.c are built with -fsanitize=thread). HOWL creates and frees arenas
 * around its worker threads every saturation round: a 16 MB scratch arena
 * and 1 MB worker and queue arenas, all big enough to be mapped from the OS.
 * Mapping, unmapping, growing a sole table and the global byte count must
 * all be free of races, and the count must balance when every thread is done.
 */

#define SLOP_ARENA_NO_CAP  /* four threads at once come near the 256 MB cap */
#include "slop_runtime.h"
#include <pthread.h>
#include <stdio.h>

enum { THREADS = 4, ROUNDS = 6 };

#define MIB ((size_t)1 << 20)

static void* worker(void* arg) {
    uint8_t seed = (uint8_t)(intptr_t)arg;
    int bad = 0;
    for (int round = 0; round < ROUNDS; round++) {
        slop_arena scratch = slop_arena_new(16 * MIB);
        slop_arena queue = slop_arena_new(MIB);

        /* Fill past the scratch head, so it chains a mapped overflow block */
        for (int i = 0; i < 20; i++) {
            uint8_t* p = (uint8_t*)slop_arena_alloc(&scratch, MIB);
            memset(p, seed + i, MIB);
            bad |= p[MIB - 1] != (uint8_t)(seed + i);
        }

        /* A sole allocation grown across the threshold and beyond */
        size_t size = 256 * 1024;
        uint8_t* q = (uint8_t*)slop_arena_alloc(&queue, size);
        memset(q, seed, size);
        slop_arena_reset(&queue);
        q = (uint8_t*)slop_arena_alloc(&queue, MIB);
        memset(q, seed, MIB);
        for (size_t next = 2 * MIB; next <= 8 * MIB; next *= 2) {
            q = (uint8_t*)slop_arena_realloc_sole(&queue, q, next / 2, next);
            bad |= q == NULL || q[0] != seed;
            if (q != NULL) memset(q + next / 2, seed, next / 2);
        }

        slop_arena_free(&queue);
        slop_arena_free(&scratch);
    }
    return (void*)(intptr_t)bad;
}

int main(void) {
    size_t accounted = atomic_load(&slop_global_allocated);
    pthread_t threads[THREADS];
    for (intptr_t t = 0; t < THREADS; t++) {
        pthread_create(&threads[t], NULL, worker, (void*)(t * 16));
    }
    int bad = 0;
    for (int t = 0; t < THREADS; t++) {
        void* r;
        pthread_join(threads[t], &r);
        bad |= (int)(intptr_t)r;
    }
    if (bad) {
        fprintf(stderr, "a worker read back the wrong bytes\n");
        return 1;
    }
    if (atomic_load(&slop_global_allocated) != accounted) {
        fprintf(stderr, "global allocation count unbalanced: %zu, expected %zu\n",
                atomic_load(&slop_global_allocated), accounted);
        return 1;
    }
    printf("arena threads test passed\n");
    return 0;
}
