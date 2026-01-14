#include "slop_runtime.h"

#ifndef comprehensive_test_H
#define comprehensive_test_H
#include <stdint.h>
#include <stddef.h>
typedef int64_t comprehensive_test_Score;
typedef struct comprehensive_test_Player comprehensive_test_Player;
typedef uint8_t comprehensive_test_GameState;
struct comprehensive_test_Value;
typedef struct comprehensive_test_Value comprehensive_test_Value;
typedef int64_t comprehensive_test_Scores;
int64_t comprehensive_test_bitwise_ops(int64_t a, int64_t b);
int64_t comprehensive_test_sum_array();
int64_t comprehensive_test_count_down(int64_t n);
int64_t comprehensive_test_state_name(GameState s);
int64_t comprehensive_test_extract_value(Value v);
int64_t comprehensive_test_divide(int64_t a, int64_t b);
int64_t comprehensive_test_safe_divide_twice(int64_t a, int64_t b, int64_t c);
int64_t comprehensive_test_classify(int64_t n);
int64_t comprehensive_test_arena_test(void);
int64_t comprehensive_test_sequence_test(int64_t x);
int64_t comprehensive_test_get_address(int64_t x);
int64_t comprehensive_test_to_byte(int64_t n);
int64_t comprehensive_test_inline_c(void);
int64_t comprehensive_test_always_positive(int64_t x);
int64_t comprehensive_test_nested_calls(int64_t a, int64_t b);
int64_t comprehensive_test_option_test();
int64_t comprehensive_test_main(void);
#endif /* comprehensive_test_H */



/* Record: Player */
/* Enum: GameState */
/* Union: Value */
int64_t comprehensive_test_bitwise_ops(int64_t a, int64_t b) {
    return |(&(a, b), ^(a, _lt_lt(b, 2)));
}

int64_t comprehensive_test_sum_array() {
    int64_t total = 0;
    for (int64_t i = 0; i < 10; i++) {
        total = (total + @(scores, i));
    }
    return 0;
}

int64_t comprehensive_test_count_down(int64_t n) {
    int64_t count = 0;
    while ((n > 0)) {
        count = (count + 1);
        n = (n - 1);
    }
    return 0;
}

int64_t comprehensive_test_state_name(GameState s) {
    return 0;
}

int64_t comprehensive_test_extract_value(Value v) {
    return 0;
}

int64_t comprehensive_test_divide(int64_t a, int64_t b) {
    return ((b == 0) ? error("division by zero") : ok((a / b)));
}

int64_t comprehensive_test_safe_divide_twice(int64_t a, int64_t b, int64_t c) {
    int64_t first = _p(divide(a, b));
    int64_t second = _p(divide(first, c));
    return ok(second);
}

int64_t comprehensive_test_classify(int64_t n) {
    return 0;
}

int64_t comprehensive_test_arena_test(void) {
    int64_t p = arena_alloc(arena, sizeof(Player));
    p = score;
    return with_arena(1024, p);
}

int64_t comprehensive_test_sequence_test(int64_t x) {
    return do(printf("%s\n", "testing"), (x + 1));
}

int64_t comprehensive_test_get_address(int64_t x) {
    return &x;
}

int64_t comprehensive_test_to_byte(int64_t n) {
    return ((uint8_t)(n));
}

int64_t comprehensive_test_inline_c(void) {
    return c_inline("42");
}

int64_t comprehensive_test_always_positive(int64_t x) {
    return ((x < 1) ? 1 : x);
}

int64_t comprehensive_test_nested_calls(int64_t a, int64_t b) {
    return classify(bitwise_ops(a, b));
}

int64_t comprehensive_test_option_test() {
    return 0;
}

int64_t comprehensive_test_main(void) {
    return 0;
}


