/*
 * Test: Thread-safe string intern pool
 *
 * Compile:
 *   cc -DSLOP_INTERN_THREADSAFE -DSLOP_ARENA_NO_CAP -O2 \
 *      -I src/slop/runtime -o test_intern_threadsafe \
 *      tests/test_intern_threadsafe.c -lpthread
 *
 * Run:
 *   ./test_intern_threadsafe
 *
 * Tests:
 *   1. Concurrent interning from N threads doesn't crash/corrupt
 *   2. Identical strings interned from different threads get same pointer (dedup)
 *   3. Distinct strings remain distinct
 */

/* SLOP_INTERN_THREADSAFE must be defined via -D flag at compile time */
#ifndef SLOP_INTERN_THREADSAFE
#define SLOP_INTERN_THREADSAFE
#endif
#include "slop_runtime.h"
#include <pthread.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>

#define NUM_THREADS 8
#define STRINGS_PER_THREAD 1000
#define NUM_SHARED_STRINGS 50

/* Shared strings that all threads will intern (to test dedup under contention) */
static char shared_strings[NUM_SHARED_STRINGS][32];

/* Per-thread results: interned pointers for shared strings */
typedef struct {
    int thread_id;
    slop_string results[NUM_SHARED_STRINGS];
} thread_data;

static void* intern_worker(void* arg) {
    thread_data* td = (thread_data*)arg;

    /* Phase 1: Intern shared strings (tests cross-thread dedup) */
    for (int i = 0; i < NUM_SHARED_STRINGS; i++) {
        td->results[i] = slop_intern_cstring(shared_strings[i]);
    }

    /* Phase 2: Intern unique strings (tests concurrent insert) */
    for (int i = 0; i < STRINGS_PER_THREAD; i++) {
        char buf[64];
        snprintf(buf, sizeof(buf), "thread_%d_str_%d", td->thread_id, i);
        slop_string s = slop_intern_cstring(buf);
        /* Verify content is correct */
        assert(s.len == strlen(buf));
        assert(memcmp(s.data, buf, s.len) == 0);
    }

    /* Phase 3: Re-intern shared strings (tests lookup under contention) */
    for (int i = 0; i < NUM_SHARED_STRINGS; i++) {
        slop_string s = slop_intern_cstring(shared_strings[i]);
        /* Must get same pointer as before (dedup guarantee) */
        assert(s.data == td->results[i].data);
    }

    return NULL;
}

int main(void) {
    int failures = 0;

    /* Initialize shared strings */
    for (int i = 0; i < NUM_SHARED_STRINGS; i++) {
        snprintf(shared_strings[i], sizeof(shared_strings[i]), "shared_str_%d", i);
    }

    /* === Test 1: Concurrent interning === */
    printf("Test 1: Concurrent interning with %d threads, %d strings each...\n",
           NUM_THREADS, STRINGS_PER_THREAD);

    pthread_t threads[NUM_THREADS];
    thread_data tdata[NUM_THREADS];

    for (int i = 0; i < NUM_THREADS; i++) {
        tdata[i].thread_id = i;
        pthread_create(&threads[i], NULL, intern_worker, &tdata[i]);
    }

    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], NULL);
    }

    printf("  PASS: No crashes or corruption\n");

    /* === Test 2: Cross-thread deduplication === */
    printf("Test 2: Cross-thread deduplication...\n");
    int dedup_ok = 1;
    for (int s = 0; s < NUM_SHARED_STRINGS; s++) {
        const char* first_ptr = tdata[0].results[s].data;
        for (int t = 1; t < NUM_THREADS; t++) {
            if (tdata[t].results[s].data != first_ptr) {
                fprintf(stderr, "  FAIL: shared_str_%d has different pointers "
                        "in thread 0 (%p) vs thread %d (%p)\n",
                        s, (void*)first_ptr, t, (void*)tdata[t].results[s].data);
                dedup_ok = 0;
                failures++;
                break;
            }
        }
    }
    if (dedup_ok) {
        printf("  PASS: All %d shared strings deduplicated across %d threads\n",
               NUM_SHARED_STRINGS, NUM_THREADS);
    }

    /* === Test 3: Distinct strings remain distinct === */
    printf("Test 3: Distinct strings remain distinct...\n");
    slop_string a = slop_intern_cstring("alpha");
    slop_string b = slop_intern_cstring("beta");
    if (a.data == b.data) {
        fprintf(stderr, "  FAIL: 'alpha' and 'beta' have same pointer\n");
        failures++;
    } else {
        printf("  PASS: Distinct strings have distinct storage\n");
    }

    /* === Test 4: Post-concurrency single-thread correctness === */
    printf("Test 4: Post-concurrency correctness...\n");
    int post_ok = 1;
    for (int i = 0; i < NUM_SHARED_STRINGS; i++) {
        slop_string s = slop_intern_cstring(shared_strings[i]);
        if (s.data != tdata[0].results[i].data) {
            fprintf(stderr, "  FAIL: post-concurrency lookup for shared_str_%d "
                    "returned different pointer\n", i);
            post_ok = 0;
            failures++;
        }
    }
    if (post_ok) {
        printf("  PASS: Post-concurrency lookups consistent\n");
    }

    printf("\n%s (%d failures)\n", failures == 0 ? "ALL TESTS PASSED" : "SOME TESTS FAILED", failures);
    return failures;
}
