#ifndef SLOP_strlib_H
#define SLOP_strlib_H

#include "../runtime/slop_runtime.h"
#ifndef SLOP_RUNTIME_ABI
#error "this module was generated for SLOP runtime ABI 2026-1 (SLOP_RUNTIME_ABI 202601), but slop_runtime.h predates runtime ABI versioning: use the slop_runtime.h of the SLOP release that generated this code"
#elif SLOP_RUNTIME_ABI != 202601
#error "this module was generated for SLOP runtime ABI 2026-1 (SLOP_RUNTIME_ABI 202601), which this slop_runtime.h does not provide (SLOP_RUNTIME_ABI differs): regenerate the C with the SLOP release that matches the runtime, or use the slop_runtime.h of the release that generated it"
#endif
#include <stdint.h>
#include <stdbool.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

typedef enum {
    std_strlib_ParseError_empty_string,
    std_strlib_ParseError_invalid_format,
    std_strlib_ParseError_overflow,
    std_strlib_ParseError_underflow
} std_strlib_ParseError;

typedef uint8_t std_strlib_AsciiChar;

static inline std_strlib_AsciiChar std_strlib_AsciiChar_new(int64_t v) {
return SLOP_RANGE(std_strlib_AsciiChar, v, 1, 1, 0, 127, "AsciiChar (Int 0 .. 127)");
}

typedef uint8_t std_strlib_Byte;

static inline std_strlib_Byte std_strlib_Byte_new(int64_t v) {
return SLOP_RANGE(std_strlib_Byte, v, 1, 1, 0, 255, "Byte (Int 0 .. 255)");
}

#ifndef SLOP_RESULT_INT_STD_STRLIB_PARSEERROR_DEFINED
#define SLOP_RESULT_INT_STD_STRLIB_PARSEERROR_DEFINED
typedef struct { bool is_ok; union { int64_t ok; std_strlib_ParseError err; } data; } slop_result_int_std_strlib_ParseError;
#endif

#ifndef SLOP_RESULT_FLOAT_STD_STRLIB_PARSEERROR_DEFINED
#define SLOP_RESULT_FLOAT_STD_STRLIB_PARSEERROR_DEFINED
typedef struct { bool is_ok; union { double ok; std_strlib_ParseError err; } data; } slop_result_float_std_strlib_ParseError;
#endif

int64_t std_strlib_min(int64_t a, int64_t b);
slop_string std_strlib_cstring_to_string(uint8_t* cstr);
uint8_t std_strlib_is_alpha(std_strlib_Byte c);
uint8_t std_strlib_is_digit(std_strlib_Byte c);
uint8_t std_strlib_is_alnum(std_strlib_Byte c);
uint8_t std_strlib_is_space(std_strlib_Byte c);
uint8_t std_strlib_is_upper(std_strlib_Byte c);
uint8_t std_strlib_is_lower(std_strlib_Byte c);
uint8_t std_strlib_is_ascii(int64_t c);
uint8_t std_strlib_is_printable(std_strlib_Byte c);
uint8_t std_strlib_is_control(std_strlib_Byte c);
std_strlib_Byte std_strlib_char_to_upper(std_strlib_Byte c);
std_strlib_Byte std_strlib_char_to_lower(std_strlib_Byte c);
slop_option_int std_strlib_index_of(slop_string haystack, slop_string needle);
slop_option_int std_strlib_last_index_of(slop_string haystack, slop_string needle);
uint8_t std_strlib_contains(slop_string haystack, slop_string needle);
uint8_t std_strlib_starts_with(slop_string s, slop_string prefix);
uint8_t std_strlib_ends_with(slop_string s, slop_string suffix);
int64_t std_strlib_count_occurrences(slop_string haystack, slop_string needle);
slop_string std_strlib_trim(slop_arena* arena, slop_string s);
slop_string std_strlib_trim_start(slop_arena* arena, slop_string s);
slop_string std_strlib_trim_end(slop_arena* arena, slop_string s);
slop_string std_strlib_pad_start(slop_arena* arena, slop_string s, int64_t target_len, std_strlib_Byte pad_char);
slop_string std_strlib_pad_end(slop_arena* arena, slop_string s, int64_t target_len, std_strlib_Byte pad_char);
slop_string std_strlib_reverse(slop_arena* arena, slop_string s);
slop_string std_strlib_repeat(slop_arena* arena, slop_string s, int64_t n);
slop_string std_strlib_substring(slop_arena* arena, slop_string s, int64_t start, int64_t len);
slop_string std_strlib_to_upper(slop_arena* arena, slop_string s);
slop_string std_strlib_to_lower(slop_arena* arena, slop_string s);
slop_string std_strlib_to_title(slop_arena* arena, slop_string s);
slop_string std_strlib_capitalize(slop_arena* arena, slop_string s);
char* std_strlib_to_cstring_in(slop_arena* arena, slop_string s);
slop_result_int_std_strlib_ParseError std_strlib_parse_int(slop_string s);
slop_result_float_std_strlib_ParseError std_strlib_parse_float(slop_string s);
slop_string std_strlib_float_to_string(slop_arena* arena, double f, uint8_t precision);
slop_string std_strlib_join(slop_arena* arena, slop_list_string strings, slop_string separator);
slop_string std_strlib_string_build(slop_arena* arena, slop_list_string strings);
slop_string std_strlib_replace(slop_arena* arena, slop_string s, slop_string old, slop_string new);
slop_string std_strlib_replace_all(slop_arena* arena, slop_string s, slop_string old, slop_string new);
int64_t std_strlib_compare(slop_string a, slop_string b);
int64_t std_strlib_compare_ignore_case(slop_string a, slop_string b);
std_strlib_Byte std_strlib_char_at(slop_string s, int64_t index);
uint8_t std_strlib_char_is_symbol_start(std_strlib_Byte c);
uint8_t std_strlib_char_is_symbol_char(std_strlib_Byte c);
uint8_t std_strlib_char_is_operator(std_strlib_Byte c);
void std_strlib_fill_bytes(uint8_t* ptr, uint8_t value, int64_t len);


#endif
