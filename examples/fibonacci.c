#include "slop_runtime.h"

#ifndef SLOP_FIBONACCI_H
#define SLOP_FIBONACCI_H

#include "slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>

/* ===== Primitive Type Aliases and Enums ===== */

typedef int64_t fibonacci_Natural;

typedef int64_t fibonacci_FibIndex;


/* ===== Forward Declarations ===== */


/* ===== Type Definitions (Topologically Sorted) ===== */

#ifndef SLOP_LIST_FIBONACCI_NATURAL_DEFINED
#define SLOP_LIST_FIBONACCI_NATURAL_DEFINED
typedef struct { fibonacci_Natural* data; size_t len; size_t cap; } slop_list_fibonacci_Natural;

#endif
#ifndef SLOP_OPTION_FIBONACCI_NATURAL_DEFINED
#define SLOP_OPTION_FIBONACCI_NATURAL_DEFINED
typedef struct { bool has_value; fibonacci_Natural value; } slop_option_fibonacci_Natural;

#endif

/* ===== Generated Generic Types ===== */

#ifndef SLOP_OPTION_FIBONACCI_NATURAL_DEFINED
#define SLOP_OPTION_FIBONACCI_NATURAL_DEFINED
typedef struct { bool has_value; fibonacci_Natural value; } slop_option_fibonacci_Natural;

#endif
#ifndef SLOP_LIST_FIBONACCI_NATURAL_DEFINED
#define SLOP_LIST_FIBONACCI_NATURAL_DEFINED
typedef struct { fibonacci_Natural* data; size_t len; size_t cap; } slop_list_fibonacci_Natural;

#endif

fibonacci_Natural fibonacci_fib(fibonacci_FibIndex n);
slop_list_fibonacci_Natural fibonacci_fibonacci_sequence(fibonacci_FibIndex count, slop_arena* arena);
void main(void);

#endif // SLOP_FIBONACCI_H

fibonacci_Natural fibonacci_fib(fibonacci_FibIndex n) {
    SLOP_PRE((n >= 0), "(>= n 0)");
    if ((n <= 1)) {
        return n;
    } else {
        return (fibonacci_fib((n - 1)) + fibonacci_fib((n - 2)));
    }
    SLOP_POST((_result >= 0), "(>= $result 0)");
}

slop_list_fibonacci_Natural fibonacci_fibonacci_sequence(fibonacci_FibIndex count, slop_arena* arena) {
    SLOP_PRE((count > 0), "(> count 0)");
    {
        __auto_type result = ((slop_list_fibonacci_Natural){ .data = (fibonacci_Natural*)slop_arena_alloc(arena, 16 * sizeof(fibonacci_Natural)), .len = 0, .cap = 16 });
        for (int64_t i = 0; i < count; i += 1) {
            ({ __auto_type _lst_p = &(result); __auto_type _item = (fibonacci_fib(i)); if (_lst_p->len >= _lst_p->cap) { size_t _nc = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _nd = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _nc * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_nd, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _nd; _lst_p->cap = _nc; } _lst_p->data[_lst_p->len++] = _item; });
        }
        return result;
    }
}

void main(void) {
    {
        slop_arena _arena = slop_arena_new(4096);
        slop_arena* arena = &_arena;
        {
            const uint8_t count = 10;
            {
                __auto_type seq = fibonacci_fibonacci_sequence(count, arena);
                {
                    __auto_type _foreach_list = seq;
                    for (size_t _foreach_i = 0; _foreach_i < _foreach_list.len; _foreach_i++) {
                        __auto_type n = _foreach_list.data[_foreach_i];
                        printf("%lld\n", (long long)n);
                    }
                }
            }
        }
        slop_arena_free(arena);
    }
}
