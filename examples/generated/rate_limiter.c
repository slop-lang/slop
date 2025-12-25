/*
 * Generated from: rate-limiter.slop
 * Generator: SLOP transpiler v0.2.0
 * 
 * DO NOT EDIT - regenerate from .slop source
 */

#include "slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>

/* ============================================================
 * Types
 * ============================================================ */

/* (type Tokens (Int 0 .. 10000)) */
typedef struct { int64_t value; } Tokens;

static inline Tokens Tokens_new(int64_t v) {
    SLOP_PRE(v >= 0 && v <= 10000, "Tokens in range 0..10000");
    return (Tokens){v};
}

/* (type MaxTokens (Int 1 .. 10000)) */
typedef struct { int64_t value; } MaxTokens;

static inline MaxTokens MaxTokens_new(int64_t v) {
    SLOP_PRE(v >= 1 && v <= 10000, "MaxTokens in range 1..10000");
    return (MaxTokens){v};
}

/* (type RefillRate (Int 1 .. 1000)) */
typedef struct { int64_t value; } RefillRate;

static inline RefillRate RefillRate_new(int64_t v) {
    SLOP_PRE(v >= 1 && v <= 1000, "RefillRate in range 1..1000");
    return (RefillRate){v};
}

/* (type Milliseconds (Int 0 ..)) */
typedef int64_t Milliseconds;

/* (type Limiter (record ...)) */
typedef struct {
    MaxTokens max_tokens;
    RefillRate refill_rate;
    Tokens tokens;
    Milliseconds last_refill;
} Limiter;

/* (type Status (record ...)) */
typedef struct {
    Tokens available;
    MaxTokens max;
    RefillRate refill_rate;
} Status;

/* (type AcquireResult (enum acquired rate-limited)) */
typedef enum {
    AcquireResult_acquired,
    AcquireResult_rate_limited
} AcquireResult;

/* ============================================================
 * Forward Declarations
 * ============================================================ */

static void refill_tokens(Limiter* limiter);

/* ============================================================
 * Public API
 * ============================================================ */

/*
 * @intent: Create a new rate limiter with specified capacity and refill rate
 * @spec: (Arena MaxTokens RefillRate) -> (Ptr Limiter)
 */
Limiter* limiter_new(slop_arena* arena, int64_t max_tokens_val, int64_t refill_rate_val) {
    /* Preconditions */
    SLOP_PRE(max_tokens_val >= 1, "max_tokens >= 1");
    SLOP_PRE(refill_rate_val >= 1, "refill_rate >= 1");
    
    /* Construct range-checked values */
    MaxTokens max_tokens = MaxTokens_new(max_tokens_val);
    RefillRate refill_rate = RefillRate_new(refill_rate_val);
    
    /* Allocate in arena */
    Limiter* limiter = (Limiter*)slop_arena_alloc(arena, sizeof(Limiter));
    
    /* Initialize fields */
    limiter->max_tokens = max_tokens;
    limiter->refill_rate = refill_rate;
    limiter->tokens = Tokens_new(max_tokens.value);
    limiter->last_refill = slop_now_ms();
    
    /* Postcondition */
    SLOP_POST(limiter != NULL, "result != nil");
    
    return limiter;
}

/*
 * @intent: Try to acquire one token, returns result
 * @spec: (Ptr Limiter) -> AcquireResult
 */
AcquireResult acquire(Limiter* limiter) {
    /* Preconditions */
    SLOP_PRE(limiter != NULL, "limiter != nil");
    
    /* Refill based on elapsed time */
    refill_tokens(limiter);
    
    /* Try to acquire */
    if (limiter->tokens.value > 0) {
        limiter->tokens = Tokens_new(limiter->tokens.value - 1);
        return AcquireResult_acquired;
    } else {
        return AcquireResult_rate_limited;
    }
}

/*
 * @intent: Non-blocking acquire attempt
 * @spec: (Ptr Limiter) -> AcquireResult
 */
AcquireResult try_acquire(Limiter* limiter) {
    /* Preconditions */
    SLOP_PRE(limiter != NULL, "limiter != nil");
    
    /* Same as acquire */
    return acquire(limiter);
}

/*
 * @intent: Get current rate limiter status
 * @spec: (Arena (Ptr Limiter)) -> (Ptr Status)
 */
Status* status(slop_arena* arena, Limiter* limiter) {
    /* Preconditions */
    SLOP_PRE(limiter != NULL, "limiter != nil");
    
    /* Refill first */
    refill_tokens(limiter);
    
    /* Allocate status in arena */
    Status* s = (Status*)slop_arena_alloc(arena, sizeof(Status));
    s->available = limiter->tokens;
    s->max = limiter->max_tokens;
    s->refill_rate = limiter->refill_rate;
    
    return s;
}

/* ============================================================
 * Internal Functions
 * ============================================================ */

/*
 * @intent: Add tokens based on elapsed time
 * @spec: (Ptr Limiter) -> Unit
 */
static void refill_tokens(Limiter* limiter) {
    /* Preconditions */
    SLOP_PRE(limiter != NULL, "limiter != nil");
    
    Milliseconds now = slop_now_ms();
    Milliseconds elapsed_ms = now - limiter->last_refill;
    int64_t elapsed_sec = elapsed_ms / 1000;
    int64_t to_add = elapsed_sec * limiter->refill_rate.value;
    
    if (to_add > 0) {
        int64_t new_tokens = limiter->tokens.value + to_add;
        if (new_tokens > limiter->max_tokens.value) {
            new_tokens = limiter->max_tokens.value;
        }
        limiter->tokens = Tokens_new(new_tokens);
        limiter->last_refill = now;
    }
}

/* ============================================================
 * Example main() for testing
 * ============================================================ */

#ifdef RATE_LIMITER_TEST

#include <stdio.h>

int main(void) {
    /* Create arena for this request */
    slop_arena arena = slop_arena_new(4096);
    
    /* Create limiter: 10 tokens, 2 per second refill */
    Limiter* limiter = limiter_new(&arena, 10, 2);
    printf("Created limiter: max=%ld, rate=%ld/sec\n", 
           limiter->max_tokens.value, limiter->refill_rate.value);
    
    /* Acquire until rate limited */
    int acquired_count = 0;
    for (int i = 0; i < 15; i++) {
        AcquireResult result = acquire(limiter);
        if (result == AcquireResult_acquired) {
            acquired_count++;
            printf("Request %d: acquired\n", i);
        } else {
            printf("Request %d: rate limited\n", i);
        }
    }
    
    printf("Total acquired: %d\n", acquired_count);
    
    /* Check status */
    Status* s = status(&arena, limiter);
    printf("Status: available=%ld, max=%ld\n", s->available.value, s->max.value);
    
    /* Wait for refill */
    printf("Waiting 2 seconds for refill...\n");
    slop_sleep_ms(2000);
    
    /* Try again */
    AcquireResult result = acquire(limiter);
    printf("After wait: %s\n", 
           result == AcquireResult_acquired ? "acquired" : "rate limited");
    
    /* Cleanup */
    slop_arena_free(&arena);
    
    return 0;
}

#endif /* RATE_LIMITER_TEST */
