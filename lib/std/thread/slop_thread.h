/*
 * SLOP Thread Runtime - Concurrency primitives for SLOP
 *
 * Provides:
 * - Typed channels: (Chan T) -> SLOP_CHAN_DEFINE(T, Name)
 * - Typed threads: (Thread T) -> SLOP_THREAD_DEFINE(T, Name)
 *
 * Built on pthreads. Link with -lpthread.
 *
 * Usage:
 *   SLOP_CHAN_DEFINE(int64_t, slop_chan_int64_t)
 *   SLOP_THREAD_DEFINE(int64_t, slop_thread_int64_t)
 */

#ifndef SLOP_THREAD_H
#define SLOP_THREAD_H

#include <pthread.h>
#include <stdbool.h>
#include <string.h>
#include "slop_runtime.h"

/* ============================================================
 * Channel Type (typed, thread-safe queue)
 *
 * Layout:
 *   - mutex: protects all channel state
 *   - not_empty: signaled when data becomes available
 *   - not_full: signaled when space becomes available
 *   - buffer: ring buffer of T
 *   - capacity: buffer size (0 = unbuffered/synchronous)
 *   - count: number of items in buffer
 *   - head/tail: ring buffer indices
 *   - closed: channel closed flag
 * ============================================================ */

#define SLOP_CHAN_DEFINE(T, Name) \
    typedef struct Name##_state { \
        pthread_mutex_t mutex; \
        pthread_cond_t not_empty; \
        pthread_cond_t not_full; \
        T* buffer; \
        size_t capacity; \
        size_t count; \
        size_t head; \
        size_t tail; \
        bool closed; \
    } Name##_state; \
    \
    typedef struct { Name##_state* state; } Name; \
    \
    /* Create unbuffered channel (capacity=0, synchronous send/recv) */ \
    static inline Name Name##_new(slop_arena* arena) { \
        Name##_state* state = (Name##_state*)slop_arena_alloc(arena, sizeof(Name##_state)); \
        pthread_mutex_init(&state->mutex, NULL); \
        pthread_cond_init(&state->not_empty, NULL); \
        pthread_cond_init(&state->not_full, NULL); \
        state->buffer = NULL; \
        state->capacity = 0; \
        state->count = 0; \
        state->head = 0; \
        state->tail = 0; \
        state->closed = false; \
        return (Name){ .state = state }; \
    } \
    \
    /* Create buffered channel with given capacity */ \
    static inline Name Name##_new_buffered(slop_arena* arena, size_t capacity) { \
        SLOP_PRE(capacity > 0, "buffered channel capacity must be > 0"); \
        Name##_state* state = (Name##_state*)slop_arena_alloc(arena, sizeof(Name##_state)); \
        pthread_mutex_init(&state->mutex, NULL); \
        pthread_cond_init(&state->not_empty, NULL); \
        pthread_cond_init(&state->not_full, NULL); \
        state->buffer = (T*)slop_arena_alloc(arena, capacity * sizeof(T)); \
        state->capacity = capacity; \
        state->count = 0; \
        state->head = 0; \
        state->tail = 0; \
        state->closed = false; \
        return (Name){ .state = state }; \
    } \
    \
    /* Close channel - wakes all waiters */ \
    static inline void Name##_close(Name* ch) { \
        pthread_mutex_lock(&ch->state->mutex); \
        ch->state->closed = true; \
        pthread_cond_broadcast(&ch->state->not_empty); \
        pthread_cond_broadcast(&ch->state->not_full); \
        pthread_mutex_unlock(&ch->state->mutex); \
    } \
    \
    /* Send value to channel. Returns true on success, false if closed. */ \
    static inline bool Name##_send(Name* ch, T value) { \
        pthread_mutex_lock(&ch->state->mutex); \
        \
        /* For unbuffered channel, wait for receiver */ \
        if (ch->state->capacity == 0) { \
            /* Wait until there's a receiver or channel closes */ \
            while (ch->state->count > 0 && !ch->state->closed) { \
                pthread_cond_wait(&ch->state->not_full, &ch->state->mutex); \
            } \
            if (ch->state->closed) { \
                pthread_mutex_unlock(&ch->state->mutex); \
                return false; \
            } \
            /* Store value directly and signal */ \
            ch->state->count = 1; \
            /* For unbuffered, allocate single-element buffer on first send */ \
            if (ch->state->buffer == NULL) { \
                /* Use static storage for single value - not ideal but works */ \
                static __thread T unbuf_value; \
                ch->state->buffer = &unbuf_value; \
            } \
            ch->state->buffer[0] = value; \
            pthread_cond_signal(&ch->state->not_empty); \
            /* Wait for receiver to take it (synchronous) */ \
            while (ch->state->count > 0 && !ch->state->closed) { \
                pthread_cond_wait(&ch->state->not_full, &ch->state->mutex); \
            } \
            pthread_mutex_unlock(&ch->state->mutex); \
            return !ch->state->closed; \
        } \
        \
        /* Buffered channel: wait for space */ \
        while (ch->state->count >= ch->state->capacity && !ch->state->closed) { \
            pthread_cond_wait(&ch->state->not_full, &ch->state->mutex); \
        } \
        if (ch->state->closed) { \
            pthread_mutex_unlock(&ch->state->mutex); \
            return false; \
        } \
        /* Enqueue value */ \
        ch->state->buffer[ch->state->tail] = value; \
        ch->state->tail = (ch->state->tail + 1) % ch->state->capacity; \
        ch->state->count++; \
        pthread_cond_signal(&ch->state->not_empty); \
        pthread_mutex_unlock(&ch->state->mutex); \
        return true; \
    } \
    \
    /* Receive from channel. Returns {true, value} on success, {false, ?} if closed and empty. */ \
    typedef struct { bool ok; T value; } Name##_recv_result; \
    static inline Name##_recv_result Name##_recv(Name* ch) { \
        pthread_mutex_lock(&ch->state->mutex); \
        \
        /* Wait for data or close */ \
        while (ch->state->count == 0 && !ch->state->closed) { \
            pthread_cond_wait(&ch->state->not_empty, &ch->state->mutex); \
        } \
        if (ch->state->count == 0 && ch->state->closed) { \
            pthread_mutex_unlock(&ch->state->mutex); \
            return (Name##_recv_result){ .ok = false }; \
        } \
        \
        /* Dequeue value */ \
        T value; \
        if (ch->state->capacity == 0) { \
            /* Unbuffered: value is in buffer[0] */ \
            value = ch->state->buffer[0]; \
            ch->state->count = 0; \
        } else { \
            /* Buffered: dequeue from ring buffer */ \
            value = ch->state->buffer[ch->state->head]; \
            ch->state->head = (ch->state->head + 1) % ch->state->capacity; \
            ch->state->count--; \
        } \
        pthread_cond_signal(&ch->state->not_full); \
        pthread_mutex_unlock(&ch->state->mutex); \
        return (Name##_recv_result){ .ok = true, .value = value }; \
    } \
    \
    /* Non-blocking receive. Returns {true, value} if data available, {false, ?} otherwise. */ \
    static inline Name##_recv_result Name##_try_recv(Name* ch) { \
        pthread_mutex_lock(&ch->state->mutex); \
        \
        if (ch->state->count == 0) { \
            pthread_mutex_unlock(&ch->state->mutex); \
            return (Name##_recv_result){ .ok = false }; \
        } \
        \
        T value; \
        if (ch->state->capacity == 0) { \
            value = ch->state->buffer[0]; \
            ch->state->count = 0; \
        } else { \
            value = ch->state->buffer[ch->state->head]; \
            ch->state->head = (ch->state->head + 1) % ch->state->capacity; \
            ch->state->count--; \
        } \
        pthread_cond_signal(&ch->state->not_full); \
        pthread_mutex_unlock(&ch->state->mutex); \
        return (Name##_recv_result){ .ok = true, .value = value }; \
    }

/* ============================================================
 * Thread Type (typed thread handle with result)
 *
 * Layout:
 *   - id: pthread handle
 *   - result: storage for thread return value
 *   - func: the function to run
 *   - arg: argument to pass to function
 *   - done: flag indicating completion
 * ============================================================ */

#define SLOP_THREAD_DEFINE(T, Name) \
    typedef struct Name##_state { \
        pthread_t id; \
        T result; \
        T (*func)(void* arg); \
        void* arg; \
        bool done; \
    } Name##_state; \
    \
    typedef struct { Name##_state* state; } Name; \
    \
    /* Internal thread entry point */ \
    static void* Name##_entry(void* arg) { \
        Name##_state* state = (Name##_state*)arg; \
        state->result = state->func(state->arg); \
        state->done = true; \
        return NULL; \
    } \
    \
    /* Spawn a new thread running func(arg) */ \
    static inline Name Name##_spawn(slop_arena* arena, T (*func)(void* arg), void* arg) { \
        Name##_state* state = (Name##_state*)slop_arena_alloc(arena, sizeof(Name##_state)); \
        state->func = func; \
        state->arg = arg; \
        state->done = false; \
        int err = pthread_create(&state->id, NULL, Name##_entry, state); \
        SLOP_PRE(err == 0, "pthread_create failed"); \
        return (Name){ .state = state }; \
    } \
    \
    /* Wait for thread to complete and return its result */ \
    static inline T Name##_join(Name* thread) { \
        pthread_join(thread->state->id, NULL); \
        return thread->state->result; \
    } \
    \
    /* Check if thread is done (non-blocking) */ \
    static inline bool Name##_is_done(Name* thread) { \
        return thread->state->done; \
    }

/* ============================================================
 * Pre-defined common channel/thread types
 * ============================================================ */

SLOP_CHAN_DEFINE(int64_t, slop_chan_int64_t)
SLOP_CHAN_DEFINE(double, slop_chan_double)
SLOP_CHAN_DEFINE(void*, slop_chan_ptr)

SLOP_THREAD_DEFINE(int64_t, slop_thread_int64_t)
SLOP_THREAD_DEFINE(double, slop_thread_double)
SLOP_THREAD_DEFINE(void*, slop_thread_ptr)

#endif /* SLOP_THREAD_H */
