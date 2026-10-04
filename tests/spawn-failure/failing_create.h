/* Included ahead of a test build (SLOP_CFLAGS="-include ..."): every thread
 * creation fails, as it does when a process is out of threads. spawn must
 * then abort, not hand back a thread that join treats as finished (#192). */
#include <errno.h>
#include <pthread.h>

__attribute__((unused))
static int slop_test_failing_create(pthread_t* id, const pthread_attr_t* attr,
                                    void* (*entry)(void*), void* arg) {
    (void)id; (void)attr; (void)entry; (void)arg;
    return EAGAIN;
}

#define SLOP_PTHREAD_CREATE slop_test_failing_create
