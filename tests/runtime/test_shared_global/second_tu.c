/* The second translation unit of test_shared_global.c */

#include "slop_runtime.h"

_Atomic size_t* second_tu_counter(void) {
    return &slop_global_allocated;
}

slop_arena second_tu_arena_new(size_t capacity) {
    return slop_arena_new(capacity);
}
