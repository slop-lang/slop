#include "slop_runtime.h"

#ifndef SLOP_test_set_map_foreach_H
#define SLOP_test_set_map_foreach_H

#include "slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>

typedef struct test_set_map_foreach_Point test_set_map_foreach_Point;

struct test_set_map_foreach_Point {
    int64_t x;
    int64_t y;
};
typedef struct test_set_map_foreach_Point test_set_map_foreach_Point;

#ifndef SLOP_OPTION_TEST_SET_MAP_FOREACH_POINT_DEFINED
#define SLOP_OPTION_TEST_SET_MAP_FOREACH_POINT_DEFINED
SLOP_OPTION_DEFINE(test_set_map_foreach_Point, slop_option_test_set_map_foreach_Point)
#endif


/* Hash/eq functions and list types for struct map/set keys */
#ifndef TEST_SET_MAP_FOREACH_POINT_HASH_EQ_DEFINED
#define TEST_SET_MAP_FOREACH_POINT_HASH_EQ_DEFINED
static inline uint64_t slop_hash_test_set_map_foreach_Point(const void* key) {
    const test_set_map_foreach_Point* _k = (const test_set_map_foreach_Point*)key;
    uint64_t hash = 14695981039346656037ULL;
    hash ^= slop_hash_int(&_k->x); hash *= 1099511628211ULL;
    hash ^= slop_hash_int(&_k->y); hash *= 1099511628211ULL;
    return hash;
}
static inline bool slop_eq_test_set_map_foreach_Point(const void* a, const void* b) {
    const test_set_map_foreach_Point* _a = (const test_set_map_foreach_Point*)a;
    const test_set_map_foreach_Point* _b = (const test_set_map_foreach_Point*)b;
    return true
        && _a->x == _b->x
        && _a->y == _b->y
    ;
}
SLOP_LIST_DEFINE(test_set_map_foreach_Point, slop_list_test_set_map_foreach_Point)
#endif

uint8_t test_set_map_foreach_test_for_each_set_int(void);
uint8_t test_set_map_foreach_test_for_each_set_empty(void);
uint8_t test_set_map_foreach_test_for_each_set_string(void);
uint8_t test_set_map_foreach_test_for_each_set_struct(void);
uint8_t test_set_map_foreach_test_for_each_map_kv_int(void);
uint8_t test_set_map_foreach_test_for_each_map_kv_empty(void);
uint8_t test_set_map_foreach_test_for_each_map_kv_string_values(void);
uint8_t test_set_map_foreach_test_for_each_map_kv_struct_values(void);
uint8_t test_set_map_foreach_test_for_each_map_keys_only(void);
int main(void);

#ifndef SLOP_OPTION_TEST_SET_MAP_FOREACH_POINT_DEFINED
#define SLOP_OPTION_TEST_SET_MAP_FOREACH_POINT_DEFINED
SLOP_OPTION_DEFINE(test_set_map_foreach_Point, slop_option_test_set_map_foreach_Point)
#endif


#endif

uint8_t test_set_map_foreach_test_for_each_set_int(void);
uint8_t test_set_map_foreach_test_for_each_set_empty(void);
uint8_t test_set_map_foreach_test_for_each_set_string(void);
uint8_t test_set_map_foreach_test_for_each_set_struct(void);
uint8_t test_set_map_foreach_test_for_each_map_kv_int(void);
uint8_t test_set_map_foreach_test_for_each_map_kv_empty(void);
uint8_t test_set_map_foreach_test_for_each_map_kv_string_values(void);
uint8_t test_set_map_foreach_test_for_each_map_kv_struct_values(void);
uint8_t test_set_map_foreach_test_for_each_map_keys_only(void);
int test_set_map_foreach_main(void);

uint8_t test_set_map_foreach_test_for_each_set_int(void) {
    {
        #ifdef SLOP_DEBUG
        SLOP_PRE((4096) > 0, "with-arena size must be positive");
        #endif
        slop_arena _arena = slop_arena_new(4096);
        #ifdef SLOP_DEBUG
        SLOP_PRE(_arena.base != NULL, "arena allocation failed");
        #endif
        slop_arena* arena = &_arena;
        {
            __auto_type s = slop_map_new_ptr(arena, 16, sizeof(int64_t), slop_hash_int, slop_eq_int);
            int64_t sum = 0;
            ({ uint8_t _dummy = 1; slop_map_put(arena, s, &(int64_t){10}, &_dummy); });
            ({ uint8_t _dummy = 1; slop_map_put(arena, s, &(int64_t){20}, &_dummy); });
            ({ uint8_t _dummy = 1; slop_map_put(arena, s, &(int64_t){30}, &_dummy); });
            for (size_t _i = 0; _i < s->cap; _i++) {
                if (s->entries[_i].occupied) {
                    int64_t item = *(int64_t*)s->entries[_i].key;
                    sum = (sum + item);
                }
            }
            return (sum == 60);
        }
        slop_arena_free(arena);
    }
}

uint8_t test_set_map_foreach_test_for_each_set_empty(void) {
    {
        #ifdef SLOP_DEBUG
        SLOP_PRE((4096) > 0, "with-arena size must be positive");
        #endif
        slop_arena _arena = slop_arena_new(4096);
        #ifdef SLOP_DEBUG
        SLOP_PRE(_arena.base != NULL, "arena allocation failed");
        #endif
        slop_arena* arena = &_arena;
        {
            __auto_type s = slop_map_new_ptr(arena, 16, sizeof(int64_t), slop_hash_int, slop_eq_int);
            int64_t count = 0;
            for (size_t _i = 0; _i < s->cap; _i++) {
                if (s->entries[_i].occupied) {
                    int64_t item = *(int64_t*)s->entries[_i].key;
                    count = (count + 1);
                }
            }
            return (count == 0);
        }
        slop_arena_free(arena);
    }
}

uint8_t test_set_map_foreach_test_for_each_set_string(void) {
    {
        #ifdef SLOP_DEBUG
        SLOP_PRE((4096) > 0, "with-arena size must be positive");
        #endif
        slop_arena _arena = slop_arena_new(4096);
        #ifdef SLOP_DEBUG
        SLOP_PRE(_arena.base != NULL, "arena allocation failed");
        #endif
        slop_arena* arena = &_arena;
        {
            __auto_type s = slop_map_new_ptr(arena, 16, sizeof(slop_string), slop_hash_string, slop_eq_string);
            int64_t count = 0;
            ({ uint8_t _dummy = 1; slop_map_put(arena, s, &(SLOP_STR("hello")), &_dummy); });
            ({ uint8_t _dummy = 1; slop_map_put(arena, s, &(SLOP_STR("world")), &_dummy); });
            for (size_t _i = 0; _i < s->cap; _i++) {
                if (s->entries[_i].occupied) {
                    slop_string item = *(slop_string*)s->entries[_i].key;
                    count = (count + 1);
                }
            }
            return (count == 2);
        }
        slop_arena_free(arena);
    }
}

uint8_t test_set_map_foreach_test_for_each_set_struct(void) {
    {
        #ifdef SLOP_DEBUG
        SLOP_PRE((4096) > 0, "with-arena size must be positive");
        #endif
        slop_arena _arena = slop_arena_new(4096);
        #ifdef SLOP_DEBUG
        SLOP_PRE(_arena.base != NULL, "arena allocation failed");
        #endif
        slop_arena* arena = &_arena;
        {
            __auto_type s = slop_map_new_ptr(arena, 16, sizeof(test_set_map_foreach_Point), slop_hash_test_set_map_foreach_Point, slop_eq_test_set_map_foreach_Point);
            int64_t sum = 0;
            ({ uint8_t _dummy = 1; slop_map_put(arena, s, &((test_set_map_foreach_Point){1, 2}), &_dummy); });
            ({ uint8_t _dummy = 1; slop_map_put(arena, s, &((test_set_map_foreach_Point){3, 4}), &_dummy); });
            for (size_t _i = 0; _i < s->cap; _i++) {
                if (s->entries[_i].occupied) {
                    test_set_map_foreach_Point p = *(test_set_map_foreach_Point*)s->entries[_i].key;
                    sum = (sum + (p.x + p.y));
                }
            }
            return (sum == 10);
        }
        slop_arena_free(arena);
    }
}

uint8_t test_set_map_foreach_test_for_each_map_kv_int(void) {
    {
        #ifdef SLOP_DEBUG
        SLOP_PRE((4096) > 0, "with-arena size must be positive");
        #endif
        slop_arena _arena = slop_arena_new(4096);
        #ifdef SLOP_DEBUG
        SLOP_PRE(_arena.base != NULL, "arena allocation failed");
        #endif
        slop_arena* arena = &_arena;
        {
            __auto_type m = slop_map_new_ptr(arena, 16, sizeof(slop_string), slop_hash_string, slop_eq_string);
            int64_t sum = 0;
            ({ __auto_type _val = 10; void* _vptr = slop_arena_alloc(arena, sizeof(_val)); memcpy(_vptr, &_val, sizeof(_val)); slop_map_put(arena, m, &(SLOP_STR("a")), _vptr); });
            ({ __auto_type _val = 20; void* _vptr = slop_arena_alloc(arena, sizeof(_val)); memcpy(_vptr, &_val, sizeof(_val)); slop_map_put(arena, m, &(SLOP_STR("b")), _vptr); });
            ({ __auto_type _val = 30; void* _vptr = slop_arena_alloc(arena, sizeof(_val)); memcpy(_vptr, &_val, sizeof(_val)); slop_map_put(arena, m, &(SLOP_STR("c")), _vptr); });
            for (size_t _i = 0; _i < m->cap; _i++) {
                if (m->entries[_i].occupied) {
                    slop_string k = *(slop_string*)m->entries[_i].key;
                    int64_t v = *(int64_t*)m->entries[_i].value;
                    sum = (sum + v);
                }
            }
            return (sum == 60);
        }
        slop_arena_free(arena);
    }
}

uint8_t test_set_map_foreach_test_for_each_map_kv_empty(void) {
    {
        #ifdef SLOP_DEBUG
        SLOP_PRE((4096) > 0, "with-arena size must be positive");
        #endif
        slop_arena _arena = slop_arena_new(4096);
        #ifdef SLOP_DEBUG
        SLOP_PRE(_arena.base != NULL, "arena allocation failed");
        #endif
        slop_arena* arena = &_arena;
        {
            __auto_type m = slop_map_new_ptr(arena, 16, sizeof(slop_string), slop_hash_string, slop_eq_string);
            int64_t count = 0;
            for (size_t _i = 0; _i < m->cap; _i++) {
                if (m->entries[_i].occupied) {
                    slop_string k = *(slop_string*)m->entries[_i].key;
                    int64_t v = *(int64_t*)m->entries[_i].value;
                    count = (count + 1);
                }
            }
            return (count == 0);
        }
        slop_arena_free(arena);
    }
}

uint8_t test_set_map_foreach_test_for_each_map_kv_string_values(void) {
    {
        #ifdef SLOP_DEBUG
        SLOP_PRE((4096) > 0, "with-arena size must be positive");
        #endif
        slop_arena _arena = slop_arena_new(4096);
        #ifdef SLOP_DEBUG
        SLOP_PRE(_arena.base != NULL, "arena allocation failed");
        #endif
        slop_arena* arena = &_arena;
        {
            __auto_type m = slop_map_new_ptr(arena, 16, sizeof(int64_t), slop_hash_int, slop_eq_int);
            int64_t count = 0;
            ({ __auto_type _val = SLOP_STR("one"); void* _vptr = slop_arena_alloc(arena, sizeof(_val)); memcpy(_vptr, &_val, sizeof(_val)); slop_map_put(arena, m, &(int64_t){1}, _vptr); });
            ({ __auto_type _val = SLOP_STR("two"); void* _vptr = slop_arena_alloc(arena, sizeof(_val)); memcpy(_vptr, &_val, sizeof(_val)); slop_map_put(arena, m, &(int64_t){2}, _vptr); });
            for (size_t _i = 0; _i < m->cap; _i++) {
                if (m->entries[_i].occupied) {
                    int64_t k = *(int64_t*)m->entries[_i].key;
                    slop_string v = *(slop_string*)m->entries[_i].value;
                    count = (count + k);
                }
            }
            return (count == 3);
        }
        slop_arena_free(arena);
    }
}

uint8_t test_set_map_foreach_test_for_each_map_kv_struct_values(void) {
    {
        #ifdef SLOP_DEBUG
        SLOP_PRE((4096) > 0, "with-arena size must be positive");
        #endif
        slop_arena _arena = slop_arena_new(4096);
        #ifdef SLOP_DEBUG
        SLOP_PRE(_arena.base != NULL, "arena allocation failed");
        #endif
        slop_arena* arena = &_arena;
        {
            __auto_type m = slop_map_new_ptr(arena, 16, sizeof(slop_string), slop_hash_string, slop_eq_string);
            int64_t sum = 0;
            ({ __auto_type _val = (test_set_map_foreach_Point){0, 0}; void* _vptr = slop_arena_alloc(arena, sizeof(_val)); memcpy(_vptr, &_val, sizeof(_val)); slop_map_put(arena, m, &(SLOP_STR("origin")), _vptr); });
            ({ __auto_type _val = (test_set_map_foreach_Point){3, 4}; void* _vptr = slop_arena_alloc(arena, sizeof(_val)); memcpy(_vptr, &_val, sizeof(_val)); slop_map_put(arena, m, &(SLOP_STR("point1")), _vptr); });
            for (size_t _i = 0; _i < m->cap; _i++) {
                if (m->entries[_i].occupied) {
                    slop_string k = *(slop_string*)m->entries[_i].key;
                    test_set_map_foreach_Point p = *(test_set_map_foreach_Point*)m->entries[_i].value;
                    sum = (sum + (p.x + p.y));
                }
            }
            return (sum == 7);
        }
        slop_arena_free(arena);
    }
}

uint8_t test_set_map_foreach_test_for_each_map_keys_only(void) {
    {
        #ifdef SLOP_DEBUG
        SLOP_PRE((4096) > 0, "with-arena size must be positive");
        #endif
        slop_arena _arena = slop_arena_new(4096);
        #ifdef SLOP_DEBUG
        SLOP_PRE(_arena.base != NULL, "arena allocation failed");
        #endif
        slop_arena* arena = &_arena;
        {
            __auto_type m = slop_map_new_ptr(arena, 16, sizeof(int64_t), slop_hash_int, slop_eq_int);
            int64_t sum = 0;
            ({ __auto_type _val = SLOP_STR("ten"); void* _vptr = slop_arena_alloc(arena, sizeof(_val)); memcpy(_vptr, &_val, sizeof(_val)); slop_map_put(arena, m, &(int64_t){10}, _vptr); });
            ({ __auto_type _val = SLOP_STR("twenty"); void* _vptr = slop_arena_alloc(arena, sizeof(_val)); memcpy(_vptr, &_val, sizeof(_val)); slop_map_put(arena, m, &(int64_t){20}, _vptr); });
            for (size_t _i = 0; _i < m->cap; _i++) {
                if (m->entries[_i].occupied) {
                    int64_t k = *(int64_t*)m->entries[_i].key;
                    sum = (sum + k);
                }
            }
            return (sum == 30);
        }
        slop_arena_free(arena);
    }
}

int main(void) {
    {
        int64_t failures = 0;
        if (test_set_map_foreach_test_for_each_set_int()) {
            printf("%s\n", "test-for-each-set-int: PASS");
        } else {
            printf("%s\n", "test-for-each-set-int: FAIL");
            failures = (failures + 1);
        }
        if (test_set_map_foreach_test_for_each_set_empty()) {
            printf("%s\n", "test-for-each-set-empty: PASS");
        } else {
            printf("%s\n", "test-for-each-set-empty: FAIL");
            failures = (failures + 1);
        }
        if (test_set_map_foreach_test_for_each_set_string()) {
            printf("%s\n", "test-for-each-set-string: PASS");
        } else {
            printf("%s\n", "test-for-each-set-string: FAIL");
            failures = (failures + 1);
        }
        if (test_set_map_foreach_test_for_each_set_struct()) {
            printf("%s\n", "test-for-each-set-struct: PASS");
        } else {
            printf("%s\n", "test-for-each-set-struct: FAIL");
            failures = (failures + 1);
        }
        if (test_set_map_foreach_test_for_each_map_kv_int()) {
            printf("%s\n", "test-for-each-map-kv-int: PASS");
        } else {
            printf("%s\n", "test-for-each-map-kv-int: FAIL");
            failures = (failures + 1);
        }
        if (test_set_map_foreach_test_for_each_map_kv_empty()) {
            printf("%s\n", "test-for-each-map-kv-empty: PASS");
        } else {
            printf("%s\n", "test-for-each-map-kv-empty: FAIL");
            failures = (failures + 1);
        }
        if (test_set_map_foreach_test_for_each_map_kv_string_values()) {
            printf("%s\n", "test-for-each-map-kv-string-values: PASS");
        } else {
            printf("%s\n", "test-for-each-map-kv-string-values: FAIL");
            failures = (failures + 1);
        }
        if (test_set_map_foreach_test_for_each_map_kv_struct_values()) {
            printf("%s\n", "test-for-each-map-kv-struct-values: PASS");
        } else {
            printf("%s\n", "test-for-each-map-kv-struct-values: FAIL");
            failures = (failures + 1);
        }
        if (test_set_map_foreach_test_for_each_map_keys_only()) {
            printf("%s\n", "test-for-each-map-keys-only: PASS");
        } else {
            printf("%s\n", "test-for-each-map-keys-only: FAIL");
            failures = (failures + 1);
        }
        printf("%s\n", "");
        if ((failures == 0)) {
            printf("%s\n", "All tests passed!");
            return 0;
        } else {
            printf("%lld", (long long)(failures));
            printf("%s\n", " test(s) failed");
            return 1;
        }
    }
}

