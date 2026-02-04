#include "../runtime/slop_runtime.h"
#include "slop_strlib.h"

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

int64_t strlib_min(int64_t a, int64_t b) {
    if ((a < b)) {
        return a;
    } else {
        return b;
    }
}

slop_string strlib_cstring_to_string(uint8_t* cstr) {
    return (slop_string){.len = strlen(cstr), .data = cstr};
}

uint8_t strlib_is_alpha(strlib_AsciiChar c) {
    return (isalpha(((int64_t)(c))) != 0);
}

uint8_t strlib_is_digit(strlib_AsciiChar c) {
    return (isdigit(((int64_t)(c))) != 0);
}

uint8_t strlib_is_alnum(strlib_AsciiChar c) {
    return (isalnum(((int64_t)(c))) != 0);
}

uint8_t strlib_is_space(strlib_AsciiChar c) {
    return (isspace(((int64_t)(c))) != 0);
}

uint8_t strlib_is_upper(strlib_AsciiChar c) {
    return (isupper(((int64_t)(c))) != 0);
}

uint8_t strlib_is_lower(strlib_AsciiChar c) {
    return (islower(((int64_t)(c))) != 0);
}

uint8_t strlib_is_ascii(int64_t c) {
    return ((c >= 0) && (c <= 127));
}

uint8_t strlib_is_printable(strlib_AsciiChar c) {
    return (isprint(((int64_t)(c))) != 0);
}

uint8_t strlib_is_control(strlib_AsciiChar c) {
    return (iscntrl(((int64_t)(c))) != 0);
}

strlib_AsciiChar strlib_char_to_upper(strlib_AsciiChar c) {
    return ((strlib_AsciiChar)(toupper(((int64_t)(c)))));
}

strlib_AsciiChar strlib_char_to_lower(strlib_AsciiChar c) {
    return ((strlib_AsciiChar)(tolower(((int64_t)(c)))));
}

slop_option_int strlib_index_of(slop_string haystack, slop_string needle) {
    if ((needle.len == 0)) {
        return (slop_option_int){.has_value = 1, .value = 0};
    } else {
        {
            __auto_type hlen = ((int64_t)(haystack.len));
            __auto_type nlen = ((int64_t)(needle.len));
            if ((nlen > hlen)) {
                return (slop_option_int){.has_value = false};
            } else {
                {
                    __auto_type i = 0;
                    while ((i <= (hlen - nlen))) {
                        {
                            __auto_type match_found = 1;
                            __auto_type j = 0;
                            while (((j < nlen) && match_found)) {
                                if ((((int64_t)(haystack.data[(i + j)])) != ((int64_t)(needle.data[j])))) {
                                    match_found = 0;
                                } else {
                                    j = (j + 1);
                                }
                            }
                            if (match_found) {
                                return (slop_option_int){.has_value = 1, .value = ((int64_t)(i))};
                            }
                            i = (i + 1);
                        }
                    }
                    return (slop_option_int){.has_value = false};
                }
            }
        }
    }
}

slop_option_int strlib_last_index_of(slop_string haystack, slop_string needle) {
    if ((needle.len == 0)) {
        return (slop_option_int){.has_value = 1, .value = ((int64_t)(haystack.len))};
    } else {
        {
            __auto_type hlen = ((int64_t)(haystack.len));
            __auto_type nlen = ((int64_t)(needle.len));
            if ((nlen > hlen)) {
                return (slop_option_int){.has_value = false};
            } else {
                {
                    __auto_type i = (hlen - nlen);
                    while ((i >= 0)) {
                        {
                            __auto_type match_found = 1;
                            __auto_type j = 0;
                            while (((j < nlen) && match_found)) {
                                if ((((int64_t)(haystack.data[(i + j)])) != ((int64_t)(needle.data[j])))) {
                                    match_found = 0;
                                } else {
                                    j = (j + 1);
                                }
                            }
                            if (match_found) {
                                return (slop_option_int){.has_value = 1, .value = ((int64_t)(i))};
                            }
                            i = (i - 1);
                        }
                    }
                    return (slop_option_int){.has_value = false};
                }
            }
        }
    }
}

uint8_t strlib_contains(slop_string haystack, slop_string needle) {
    __auto_type _mv_0 = strlib_index_of(haystack, needle);
    if (_mv_0.has_value) {
        __auto_type _ = _mv_0.value;
        return 1;
    } else if (!_mv_0.has_value) {
        return 0;
    }
}

uint8_t strlib_starts_with(slop_string s, slop_string prefix) {
    if ((prefix.len > s.len)) {
        return 0;
    } else {
        return (strncmp(((uint8_t*)(s.data)), ((uint8_t*)(prefix.data)), prefix.len) == 0);
    }
}

uint8_t strlib_ends_with(slop_string s, slop_string suffix) {
    if ((suffix.len > s.len)) {
        return 0;
    } else {
        {
            __auto_type offset = (s.len - suffix.len);
            return (strncmp(((uint8_t*)((s.data + offset))), ((uint8_t*)(suffix.data)), suffix.len) == 0);
        }
    }
}

int64_t strlib_count_occurrences(slop_string haystack, slop_string needle) {
    if ((needle.len == 0)) {
        return 0;
    } else {
        {
            __auto_type count = 0;
            __auto_type pos = 0;
            __auto_type hlen = ((int64_t)(haystack.len));
            __auto_type nlen = ((int64_t)(needle.len));
            while ((pos <= (hlen - nlen))) {
                {
                    __auto_type match_found = 1;
                    __auto_type j = 0;
                    while (((j < nlen) && match_found)) {
                        if ((((int64_t)(haystack.data[(pos + j)])) != ((int64_t)(needle.data[j])))) {
                            match_found = 0;
                        } else {
                            j = (j + 1);
                        }
                    }
                    if (match_found) {
                        count = (count + 1);
                        pos = (pos + nlen);
                    } else {
                        pos = (pos + 1);
                    }
                }
            }
            return ((int64_t)(count));
        }
    }
}

slop_string strlib_trim(slop_arena* arena, slop_string s) {
    {
        __auto_type slen = ((int64_t)(s.len));
        if ((slen == 0)) {
            return s;
        } else {
            {
                __auto_type start = 0;
                __auto_type end = slen;
                while (((start < slen) && strlib_is_space(((strlib_AsciiChar)(s.data[start]))))) {
                    start = (start + 1);
                }
                while (((end > start) && strlib_is_space(((strlib_AsciiChar)(s.data[(end - 1)]))))) {
                    end = (end - 1);
                }
                {
                    __auto_type newlen = (end - start);
                    if ((newlen == 0)) {
                        return (slop_string){.len = ((uint64_t)(0)), .data = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 1); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })))};
                    } else {
                        {
                            __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (newlen + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                            memcpy(((void*)(buf)), ((void*)((s.data + start))), ((uint64_t)(newlen)));
                            return (slop_string){.len = ((uint64_t)(newlen)), .data = ((uint8_t*)(buf))};
                        }
                    }
                }
            }
        }
    }
}

slop_string strlib_trim_start(slop_arena* arena, slop_string s) {
    {
        __auto_type slen = ((int64_t)(s.len));
        if ((slen == 0)) {
            return s;
        } else {
            {
                __auto_type start = 0;
                while (((start < slen) && strlib_is_space(((strlib_AsciiChar)(s.data[start]))))) {
                    start = (start + 1);
                }
                {
                    __auto_type newlen = (slen - start);
                    if ((newlen == 0)) {
                        return (slop_string){.len = ((uint64_t)(0)), .data = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 1); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })))};
                    } else {
                        {
                            __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (newlen + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                            memcpy(((void*)(buf)), ((void*)((s.data + start))), ((uint64_t)(newlen)));
                            return (slop_string){.len = ((uint64_t)(newlen)), .data = ((uint8_t*)(buf))};
                        }
                    }
                }
            }
        }
    }
}

slop_string strlib_trim_end(slop_arena* arena, slop_string s) {
    {
        __auto_type slen = ((int64_t)(s.len));
        if ((slen == 0)) {
            return s;
        } else {
            {
                __auto_type end = slen;
                while (((end > 0) && strlib_is_space(((strlib_AsciiChar)(s.data[(end - 1)]))))) {
                    end = (end - 1);
                }
                if ((end == 0)) {
                    return (slop_string){.len = ((uint64_t)(0)), .data = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 1); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })))};
                } else {
                    {
                        __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (end + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                        memcpy(((void*)(buf)), ((void*)(s.data)), ((uint64_t)(end)));
                        return (slop_string){.len = ((uint64_t)(end)), .data = ((uint8_t*)(buf))};
                    }
                }
            }
        }
    }
}

slop_string strlib_pad_start(slop_arena* arena, slop_string s, int64_t target_len, strlib_AsciiChar pad_char) {
    {
        __auto_type slen = ((int64_t)(s.len));
        if ((slen >= target_len)) {
            return s;
        } else {
            {
                __auto_type pad_count = (target_len - slen);
                __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (target_len + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                memset(((void*)(buf)), ((int64_t)(pad_char)), ((uint64_t)(pad_count)));
                memcpy(((void*)((buf + pad_count))), ((void*)(s.data)), ((uint64_t)(slen)));
                return (slop_string){.len = ((uint64_t)(target_len)), .data = ((uint8_t*)(buf))};
            }
        }
    }
}

slop_string strlib_pad_end(slop_arena* arena, slop_string s, int64_t target_len, strlib_AsciiChar pad_char) {
    {
        __auto_type slen = ((int64_t)(s.len));
        if ((slen >= target_len)) {
            return s;
        } else {
            {
                __auto_type pad_count = (target_len - slen);
                __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (target_len + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                memcpy(((void*)(buf)), ((void*)(s.data)), ((uint64_t)(slen)));
                memset(((void*)((buf + slen))), ((int64_t)(pad_char)), ((uint64_t)(pad_count)));
                return (slop_string){.len = ((uint64_t)(target_len)), .data = ((uint8_t*)(buf))};
            }
        }
    }
}

slop_string strlib_reverse(slop_arena* arena, slop_string s) {
    {
        __auto_type slen = ((int64_t)(s.len));
        if ((slen == 0)) {
            return s;
        } else {
            {
                __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (slen + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                __auto_type i = 0;
                while ((i < slen)) {
                    buf[i] = s.data[((slen - 1) - i)];
                    i = (i + 1);
                }
                return (slop_string){.len = ((uint64_t)(slen)), .data = ((uint8_t*)(buf))};
            }
        }
    }
}

slop_string strlib_repeat(slop_arena* arena, slop_string s, int64_t n) {
    {
        __auto_type slen = ((int64_t)(s.len));
        if (((n == 0) || (slen == 0))) {
            return (slop_string){.len = ((uint64_t)(0)), .data = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 1); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })))};
        } else {
            {
                __auto_type total_len = (slen * n);
                __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (total_len + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                __auto_type i = 0;
                while ((i < n)) {
                    memcpy(((void*)((buf + (i * slen)))), ((void*)(s.data)), ((uint64_t)(slen)));
                    i = (i + 1);
                }
                return (slop_string){.len = ((uint64_t)(total_len)), .data = ((uint8_t*)(buf))};
            }
        }
    }
}

slop_string strlib_substring(slop_arena* arena, slop_string s, int64_t start, int64_t len) {
    SLOP_PRE(((start <= s.len)), "(<= start (. s len))");
    {
        __auto_type slen = ((int64_t)(s.len));
        __auto_type actual_len = ((((int64_t)(len))) < (((int64_t)((slen - ((int64_t)(start)))))) ? (((int64_t)(len))) : (((int64_t)((slen - ((int64_t)(start)))))));
        if ((actual_len == 0)) {
            return (slop_string){.len = ((uint64_t)(0)), .data = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 1); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })))};
        } else {
            {
                __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (actual_len + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                memcpy(((void*)(buf)), ((void*)((s.data + start))), ((uint64_t)(actual_len)));
                return (slop_string){.len = ((uint64_t)(actual_len)), .data = ((uint8_t*)(buf))};
            }
        }
    }
}

slop_string strlib_to_upper(slop_arena* arena, slop_string s) {
    {
        __auto_type slen = ((int64_t)(s.len));
        if ((slen == 0)) {
            return s;
        } else {
            {
                __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (slen + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                __auto_type i = 0;
                while ((i < slen)) {
                    buf[i] = ((uint8_t)(strlib_char_to_upper(((strlib_AsciiChar)(s.data[i])))));
                    i = (i + 1);
                }
                return (slop_string){.len = ((uint64_t)(slen)), .data = ((uint8_t*)(buf))};
            }
        }
    }
}

slop_string strlib_to_lower(slop_arena* arena, slop_string s) {
    {
        __auto_type slen = ((int64_t)(s.len));
        if ((slen == 0)) {
            return s;
        } else {
            {
                __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (slen + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                __auto_type i = 0;
                while ((i < slen)) {
                    buf[i] = ((uint8_t)(strlib_char_to_lower(((strlib_AsciiChar)(s.data[i])))));
                    i = (i + 1);
                }
                return (slop_string){.len = ((uint64_t)(slen)), .data = ((uint8_t*)(buf))};
            }
        }
    }
}

slop_string strlib_to_title(slop_arena* arena, slop_string s) {
    {
        __auto_type slen = ((int64_t)(s.len));
        if ((slen == 0)) {
            return s;
        } else {
            {
                __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (slen + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                __auto_type i = 0;
                __auto_type word_start = 1;
                while ((i < slen)) {
                    {
                        __auto_type c = ((strlib_AsciiChar)(s.data[i]));
                        if (strlib_is_space(c)) {
                            buf[i] = ((uint8_t)(c));
                            word_start = 1;
                        } else {
                            if (word_start) {
                                buf[i] = ((uint8_t)(strlib_char_to_upper(c)));
                                word_start = 0;
                            } else {
                                buf[i] = ((uint8_t)(strlib_char_to_lower(c)));
                            }
                        }
                        i = (i + 1);
                    }
                }
                return (slop_string){.len = ((uint64_t)(slen)), .data = ((uint8_t*)(buf))};
            }
        }
    }
}

slop_string strlib_capitalize(slop_arena* arena, slop_string s) {
    {
        __auto_type slen = ((int64_t)(s.len));
        if ((slen == 0)) {
            return s;
        } else {
            {
                __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (slen + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                buf[0] = ((uint8_t)(strlib_char_to_upper(((strlib_AsciiChar)(s.data[0])))));
                if ((slen > 1)) {
                    memcpy(((void*)((buf + 1))), ((void*)((s.data + 1))), ((uint64_t)((slen - 1))));
                }
                return (slop_string){.len = ((uint64_t)(slen)), .data = ((uint8_t*)(buf))};
            }
        }
    }
}

slop_result_int_strlib_ParseError strlib_parse_int(slop_string s) {
    if ((s.len == 0)) {
        return ((slop_result_int_strlib_ParseError){ .is_ok = false, .data.err = strlib_ParseError_empty_string });
    } else {
        {
            #ifdef SLOP_DEBUG
            SLOP_PRE((16) > 0, "with-arena size must be positive");
            #endif
            slop_arena _arena = slop_arena_new(16);
            #ifdef SLOP_DEBUG
            SLOP_PRE(_arena.base != NULL, "arena allocation failed");
            #endif
            slop_arena* arena = &_arena;
            {
                __auto_type endptr = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 8); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                __auto_type result = strtol(((char*)(s.data)), ((char**)(endptr)), 10);
                {
                    __auto_type end_val = (*((char**)(endptr)));
                    if ((end_val == ((char*)(s.data)))) {
                        return ((slop_result_int_strlib_ParseError){ .is_ok = false, .data.err = strlib_ParseError_invalid_format });
                    } else {
                        return ((slop_result_int_strlib_ParseError){ .is_ok = true, .data.ok = result });
                    }
                }
            }
            slop_arena_free(arena);
        }
    }
}

slop_result_double_strlib_ParseError strlib_parse_float(slop_string s) {
    if ((s.len == 0)) {
        return ((slop_result_double_strlib_ParseError){ .is_ok = false, .data.err = strlib_ParseError_empty_string });
    } else {
        {
            #ifdef SLOP_DEBUG
            SLOP_PRE((16) > 0, "with-arena size must be positive");
            #endif
            slop_arena _arena = slop_arena_new(16);
            #ifdef SLOP_DEBUG
            SLOP_PRE(_arena.base != NULL, "arena allocation failed");
            #endif
            slop_arena* arena = &_arena;
            {
                __auto_type endptr = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 8); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                __auto_type result = strtod(((char*)(s.data)), ((char**)(endptr)));
                {
                    __auto_type end_val = (*((char**)(endptr)));
                    if ((end_val == ((char*)(s.data)))) {
                        return ((slop_result_double_strlib_ParseError){ .is_ok = false, .data.err = strlib_ParseError_invalid_format });
                    } else {
                        return ((slop_result_double_strlib_ParseError){ .is_ok = true, .data.ok = result });
                    }
                }
            }
            slop_arena_free(arena);
        }
    }
}

slop_string strlib_float_to_string(slop_arena* arena, double f, uint8_t precision) {
    slop_string _retval;
    {
        __auto_type fmt_buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 8); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
        __auto_type out_buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 64); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
        fmt_buf[0] = ((uint8_t)(37));
        fmt_buf[1] = ((uint8_t)(46));
        if ((precision < 10)) {
            fmt_buf[2] = ((uint8_t)((48 + precision)));
            fmt_buf[3] = ((uint8_t)(102));
            fmt_buf[4] = ((uint8_t)(0));
        } else {
            fmt_buf[2] = ((uint8_t)((48 + (precision / 10))));
            fmt_buf[3] = ((uint8_t)((48 + (precision % 10))));
            fmt_buf[4] = ((uint8_t)(102));
            fmt_buf[5] = ((uint8_t)(0));
        }
        {
            __auto_type len = snprintf(((char*)(out_buf)), ((uint64_t)(64)), ((char*)(fmt_buf)), f);
            _retval = (slop_string){.len = ((uint64_t)(len)), .data = ((uint8_t*)(out_buf))};
        }
    }
    SLOP_POST(((_retval.len >= 1)), "(>= (. $result len) 1)");
    SLOP_POST(((_retval.data != NULL)), "(!= (. $result data) nil)");
    return _retval;
}

slop_string strlib_join(slop_arena* arena, slop_list_string strings, slop_string separator) {
    {
        __auto_type count = ((int64_t)(((int64_t)((strings).len))));
        if ((count == 0)) {
            return (slop_string){.len = ((uint64_t)(0)), .data = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 1); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })))};
        } else {
            if ((count == 1)) {
                __auto_type _mv_1 = ({ __auto_type _lst = strings; size_t _idx = (size_t)0; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1.has_value) {
                    __auto_type first_str = _mv_1.value;
                    return first_str;
                } else if (!_mv_1.has_value) {
                    return (slop_string){.len = ((uint64_t)(0)), .data = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 1); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })))};
                }
            } else {
                {
                    __auto_type total_len = 0;
                    __auto_type i = 0;
                    __auto_type sep_len = ((int64_t)(separator.len));
                    while ((i < count)) {
                        __auto_type _mv_2 = ({ __auto_type _lst = strings; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_2.has_value) {
                            __auto_type str = _mv_2.value;
                            total_len = (total_len + ((int64_t)(str.len)));
                        } else if (!_mv_2.has_value) {
                            total_len = total_len;
                        }
                        i = (i + 1);
                    }
                    total_len = (total_len + (sep_len * (count - 1)));
                    {
                        __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (total_len + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                        __auto_type pos = 0;
                        __auto_type j = 0;
                        while ((j < count)) {
                            __auto_type _mv_3 = ({ __auto_type _lst = strings; size_t _idx = (size_t)j; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_3.has_value) {
                                __auto_type str = _mv_3.value;
                                if ((str.len > 0)) {
                                    memcpy(((void*)((buf + pos))), ((void*)(str.data)), str.len);
                                }
                                pos = (pos + ((int64_t)(str.len)));
                            } else if (!_mv_3.has_value) {
                                pos = pos;
                            }
                            if ((j < (count - 1))) {
                                if ((sep_len > 0)) {
                                    memcpy(((void*)((buf + pos))), ((void*)(separator.data)), ((uint64_t)(sep_len)));
                                }
                                pos = (pos + sep_len);
                            }
                            j = (j + 1);
                        }
                        return (slop_string){.len = ((uint64_t)(total_len)), .data = ((uint8_t*)(buf))};
                    }
                }
            }
        }
    }
}

slop_string strlib_string_build(slop_arena* arena, slop_list_string strings) {
    return strlib_join(arena, strings, SLOP_STR(""));
}

slop_string strlib_replace(slop_arena* arena, slop_string s, slop_string old, slop_string new) {
    __auto_type _mv_4 = strlib_index_of(s, old);
    if (!_mv_4.has_value) {
        return s;
    } else if (_mv_4.has_value) {
        __auto_type idx = _mv_4.value;
        {
            __auto_type slen = ((int64_t)(s.len));
            __auto_type old_len = ((int64_t)(old.len));
            __auto_type new_len = ((int64_t)(new.len));
            __auto_type result_len = ((slen - old_len) + new_len);
            __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (result_len + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
            if ((idx > 0)) {
                memcpy(((void*)(buf)), ((void*)(s.data)), ((uint64_t)(idx)));
            }
            if ((new_len > 0)) {
                memcpy(((void*)((buf + idx))), ((void*)(new.data)), ((uint64_t)(new_len)));
            }
            {
                __auto_type after_idx = (idx + old_len);
                __auto_type after_len = (slen - after_idx);
                if ((after_len > 0)) {
                    memcpy(((void*)((buf + (idx + new_len)))), ((void*)((s.data + after_idx))), ((uint64_t)(after_len)));
                }
            }
            return (slop_string){.len = ((uint64_t)(result_len)), .data = ((uint8_t*)(buf))};
        }
    }
}

slop_string strlib_replace_all(slop_arena* arena, slop_string s, slop_string old, slop_string new) {
    if ((old.len == 0)) {
        return s;
    } else {
        {
            __auto_type old_len = ((int64_t)(old.len));
            __auto_type new_len = ((int64_t)(new.len));
            __auto_type slen = ((int64_t)(s.len));
            __auto_type count = 0;
            __auto_type pos = 0;
            while ((pos <= (slen - old_len))) {
                {
                    __auto_type match_found = 1;
                    __auto_type j = 0;
                    while (((j < old_len) && match_found)) {
                        if ((((int64_t)(s.data[(pos + j)])) != ((int64_t)(old.data[j])))) {
                            match_found = 0;
                        } else {
                            j = (j + 1);
                        }
                    }
                    if (match_found) {
                        count = (count + 1);
                        pos = (pos + old_len);
                    } else {
                        pos = (pos + 1);
                    }
                }
            }
            if ((count == 0)) {
                return s;
            } else {
                {
                    __auto_type result_len = (slen + (count * (new_len - old_len)));
                    __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (result_len + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                    __auto_type src_pos = 0;
                    __auto_type dst_pos = 0;
                    while ((src_pos < slen)) {
                        if ((((src_pos + old_len) <= slen) && ({ __auto_type match_found = 1; __auto_type k = 0; ({ while (((k < old_len) && match_found)) { (((((int64_t)(s.data[(src_pos + k)])) != ((int64_t)(old.data[k])))) ? ({ match_found = 0; (void)0; }) : ({ k = (k + 1); (void)0; })); } 0; }); match_found; }))) {
                            if ((new_len > 0)) {
                                memcpy(((void*)((buf + dst_pos))), ((void*)(new.data)), ((uint64_t)(new_len)));
                            }
                            dst_pos = (dst_pos + new_len);
                            src_pos = (src_pos + old_len);
                        } else {
                            buf[dst_pos] = s.data[src_pos];
                            dst_pos = (dst_pos + 1);
                            src_pos = (src_pos + 1);
                        }
                    }
                    return (slop_string){.len = ((uint64_t)(result_len)), .data = ((uint8_t*)(buf))};
                }
            }
        }
    }
}

int64_t strlib_compare(slop_string a, slop_string b) {
    {
        __auto_type result = strcmp(((uint8_t*)(a.data)), ((uint8_t*)(b.data)));
        if ((result < 0)) {
            return -1;
        } else if ((result > 0)) {
            return 1;
        } else {
            return 0;
        }
    }
}

int64_t strlib_compare_ignore_case(slop_string a, slop_string b) {
    {
        __auto_type alen = ((int64_t)(a.len));
        __auto_type blen = ((int64_t)(b.len));
        __auto_type min_len = ((alen) < (blen) ? (alen) : (blen));
        __auto_type i = 0;
        __auto_type result = 0;
        while (((i < min_len) && (result == 0))) {
            {
                __auto_type ca = strlib_char_to_lower(((strlib_AsciiChar)(a.data[i])));
                __auto_type cb = strlib_char_to_lower(((strlib_AsciiChar)(b.data[i])));
                if ((ca < cb)) {
                    result = -1;
                } else if ((ca > cb)) {
                    result = 1;
                } else {
                    i = (i + 1);
                }
            }
        }
        if ((result != 0)) {
            return result;
        } else {
            if ((alen < blen)) {
                return -1;
            } else if ((alen > blen)) {
                return 1;
            } else {
                return 0;
            }
        }
    }
}

strlib_AsciiChar strlib_char_at(slop_string s, int64_t index) {
    if ((index >= ((int64_t)(s.len)))) {
        return 0;
    } else {
        return ((strlib_AsciiChar)(s.data[index]));
    }
}

uint8_t strlib_char_is_symbol_start(strlib_AsciiChar c) {
    return ((strlib_is_alpha(c)) || ((c == 95)) || ((c == 64)) || ((c == 36)));
}

uint8_t strlib_char_is_symbol_char(strlib_AsciiChar c) {
    return ((strlib_is_alnum(c)) || ((c == 95)) || ((c == 45)) || ((c == 47)) || ((c == 42)) || ((c == 60)) || ((c == 62)) || ((c == 61)) || ((c == 33)) || ((c == 63)) || ((c == 46)) || ((c == 64)) || ((c == 36)));
}

uint8_t strlib_char_is_operator(strlib_AsciiChar c) {
    return (((c == 43)) || ((c == 45)) || ((c == 42)) || ((c == 47)) || ((c == 33)) || ((c == 60)) || ((c == 62)) || ((c == 61)) || ((c == 38)) || ((c == 124)) || ((c == 94)) || ((c == 37)) || ((c == 63)) || ((c == 46)));
}

void strlib_fill_bytes(uint8_t* ptr, uint8_t value, int64_t len) {
    memset(((void*)(ptr)), ((int64_t)(value)), ((uint64_t)(len)));
    0;
}

