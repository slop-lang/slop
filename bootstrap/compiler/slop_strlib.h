#ifndef SLOP_strlib_H
#define SLOP_strlib_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

typedef enum {
    strlib_ParseError_empty_string,
    strlib_ParseError_invalid_format,
    strlib_ParseError_overflow,
    strlib_ParseError_underflow
} strlib_ParseError;

typedef uint8_t strlib_AsciiChar;

static inline strlib_AsciiChar strlib_AsciiChar_new(int64_t v) {
SLOP_PRE(v >= 0 && v <= 127, "strlib_AsciiChar in range 0..127");
return (strlib_AsciiChar)v;
}

#ifndef SLOP_RESULT_INT_STRLIB_PARSEERROR_DEFINED
#define SLOP_RESULT_INT_STRLIB_PARSEERROR_DEFINED
typedef struct { bool is_ok; union { int64_t ok; strlib_ParseError err; } data; } slop_result_int_strlib_ParseError;
#endif

#ifndef SLOP_RESULT_DOUBLE_STRLIB_PARSEERROR_DEFINED
#define SLOP_RESULT_DOUBLE_STRLIB_PARSEERROR_DEFINED
typedef struct { bool is_ok; union { double ok; strlib_ParseError err; } data; } slop_result_double_strlib_ParseError;
#endif

int64_t strlib_min(int64_t a, int64_t b);
slop_string strlib_cstring_to_string(uint8_t* cstr);
uint8_t strlib_is_alpha(strlib_AsciiChar c);
uint8_t strlib_is_digit(strlib_AsciiChar c);
uint8_t strlib_is_alnum(strlib_AsciiChar c);
uint8_t strlib_is_space(strlib_AsciiChar c);
uint8_t strlib_is_upper(strlib_AsciiChar c);
uint8_t strlib_is_lower(strlib_AsciiChar c);
uint8_t strlib_is_ascii(int64_t c);
uint8_t strlib_is_printable(strlib_AsciiChar c);
uint8_t strlib_is_control(strlib_AsciiChar c);
strlib_AsciiChar strlib_char_to_upper(strlib_AsciiChar c);
strlib_AsciiChar strlib_char_to_lower(strlib_AsciiChar c);
slop_option_int strlib_index_of(slop_string haystack, slop_string needle);
slop_option_int strlib_last_index_of(slop_string haystack, slop_string needle);
uint8_t strlib_contains(slop_string haystack, slop_string needle);
uint8_t strlib_starts_with(slop_string s, slop_string prefix);
uint8_t strlib_ends_with(slop_string s, slop_string suffix);
int64_t strlib_count_occurrences(slop_string haystack, slop_string needle);
slop_string strlib_trim(slop_arena* arena, slop_string s);
slop_string strlib_trim_start(slop_arena* arena, slop_string s);
slop_string strlib_trim_end(slop_arena* arena, slop_string s);
slop_string strlib_pad_start(slop_arena* arena, slop_string s, int64_t target_len, strlib_AsciiChar pad_char);
slop_string strlib_pad_end(slop_arena* arena, slop_string s, int64_t target_len, strlib_AsciiChar pad_char);
slop_string strlib_reverse(slop_arena* arena, slop_string s);
slop_string strlib_repeat(slop_arena* arena, slop_string s, int64_t n);
slop_string strlib_substring(slop_arena* arena, slop_string s, int64_t start, int64_t len);
slop_string strlib_to_upper(slop_arena* arena, slop_string s);
slop_string strlib_to_lower(slop_arena* arena, slop_string s);
slop_string strlib_to_title(slop_arena* arena, slop_string s);
slop_string strlib_capitalize(slop_arena* arena, slop_string s);
slop_result_int_strlib_ParseError strlib_parse_int(slop_string s);
slop_result_double_strlib_ParseError strlib_parse_float(slop_string s);
slop_string strlib_float_to_string(slop_arena* arena, double f, uint8_t precision);
slop_string strlib_join(slop_arena* arena, slop_list_string strings, slop_string separator);
slop_string strlib_string_build(slop_arena* arena, slop_list_string strings);
slop_string strlib_replace(slop_arena* arena, slop_string s, slop_string old, slop_string new);
slop_string strlib_replace_all(slop_arena* arena, slop_string s, slop_string old, slop_string new);
int64_t strlib_compare(slop_string a, slop_string b);
int64_t strlib_compare_ignore_case(slop_string a, slop_string b);
strlib_AsciiChar strlib_char_at(slop_string s, int64_t index);
uint8_t strlib_char_is_symbol_start(strlib_AsciiChar c);
uint8_t strlib_char_is_symbol_char(strlib_AsciiChar c);
uint8_t strlib_char_is_operator(strlib_AsciiChar c);
void strlib_fill_bytes(uint8_t* ptr, uint8_t value, int64_t len);


#endif
