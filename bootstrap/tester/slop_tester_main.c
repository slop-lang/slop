#include "../runtime/slop_runtime.h"
#include "slop_tester_main.h"

#define tester_main_SEEK_SET (0)
#define tester_main_SEEK_END (2)

slop_option_string tester_main_read_file(slop_arena* arena, char* filename);
void tester_main_print_str(char* s);
void tester_main_print_string(slop_string s);
void tester_main_print_json_string(slop_string s);
slop_string tester_main_lines_to_string(slop_arena* arena, slop_list_string lines);
void tester_main_print_int(int64_t n);
int tester_main_main(int64_t argc, uint8_t** argv);

slop_option_string tester_main_read_file(slop_arena* arena, char* filename) {
    {
        __auto_type file = fopen(filename, ((char*)(SLOP_STR("rb").data)));
        if ((file == NULL)) {
            return (slop_option_string){.has_value = false};
        } else {
            fseek(file, 0, tester_main_SEEK_END);
            {
                __auto_type size = ftell(file);
                fseek(file, 0, tester_main_SEEK_SET);
                {
                    __auto_type buf = ((uint8_t*)((uint8_t*)slop_arena_alloc(arena, (size + 1))));
                    fread(((void*)(buf)), 1, size, file);
                    buf[size] = 0;
                    fclose(file);
                    return (slop_option_string){.has_value = 1, .value = (slop_string){.len = ((uint64_t)(size)), .data = buf}};
                }
            }
        }
    }
}

void tester_main_print_str(char* s) {
    {
        __auto_type i = 0;
        while ((s[i] != 0)) {
            putchar(((int64_t)(s[i])));
            i = (i + 1);
        }
    }
}

void tester_main_print_string(slop_string s) {
    {
        __auto_type len = ((int64_t)(s.len));
        __auto_type data = s.data;
        __auto_type i = 0;
        while ((i < len)) {
            putchar(((int64_t)(data[i])));
            i = (i + 1);
        }
    }
}

void tester_main_print_json_string(slop_string s) {
    putchar(34);
    {
        __auto_type len = ((int64_t)(s.len));
        __auto_type data = s.data;
        __auto_type i = 0;
        while ((i < len)) {
            {
                __auto_type c = ((int64_t)(data[i]));
                if ((c == 34)) {
                    putchar(92);
                    putchar(34);
                } else if ((c == 92)) {
                    putchar(92);
                    putchar(92);
                } else if ((c == 10)) {
                    putchar(92);
                    putchar(110);
                } else if ((c == 13)) {
                    putchar(92);
                    putchar(114);
                } else if ((c == 9)) {
                    putchar(92);
                    putchar(116);
                } else {
                    putchar(c);
                }
            }
            i = (i + 1);
        }
    }
    putchar(34);
}

slop_string tester_main_lines_to_string(slop_arena* arena, slop_list_string lines) {
    {
        __auto_type len = ((int64_t)((lines).len));
        if ((len == 0)) {
            return SLOP_STR("");
        } else {
            {
                __auto_type total = 0;
                __auto_type i = 0;
                while ((i < len)) {
                    __auto_type _mv_204 = ({ __auto_type _lst = lines; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_204.has_value) {
                        __auto_type line = _mv_204.value;
                        total = (total + (((int64_t)(line.len)) + 1));
                    } else if (!_mv_204.has_value) {
                    }
                    i = (i + 1);
                }
                {
                    __auto_type buf = (uint8_t*)slop_arena_alloc(arena, (total + 1));
                    __auto_type pos = 0;
                    __auto_type j = 0;
                    while ((j < len)) {
                        __auto_type _mv_205 = ({ __auto_type _lst = lines; size_t _idx = (size_t)j; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_205.has_value) {
                            __auto_type line = _mv_205.value;
                            {
                                __auto_type line_len = ((int64_t)(line.len));
                                __auto_type line_data = line.data;
                                __auto_type k = 0;
                                while ((k < line_len)) {
                                    buf[pos] = line_data[k];
                                    pos = (pos + 1);
                                    k = (k + 1);
                                }
                                buf[pos] = 10;
                                pos = (pos + 1);
                            }
                        } else if (!_mv_205.has_value) {
                        }
                        j = (j + 1);
                    }
                    buf[pos] = 0;
                    return (slop_string){.len = ((uint64_t)(pos)), .data = buf};
                }
            }
        }
    }
}

void tester_main_print_int(int64_t n) {
    if ((n < 0)) {
        putchar(45);
        tester_main_print_int((0 - n));
    } else {
        if ((n < 10)) {
            putchar((48 + n));
        } else {
            tester_main_print_int((n / 10));
            putchar((48 + (n % 10)));
        }
    }
}

int main(int64_t argc, uint8_t** argv) {
    if ((argc < 2)) {
        tester_main_print_str(((char*)(SLOP_STR("Usage: slop-tester <input.slop>\n").data)));
        return 1;
    } else {
        {
            #ifdef SLOP_DEBUG
            SLOP_PRE((16777216) > 0, "with-arena size must be positive");
            #endif
            slop_arena _arena = slop_arena_new(16777216);
            #ifdef SLOP_DEBUG
            SLOP_PRE(_arena.base != NULL, "arena allocation failed");
            #endif
            slop_arena* arena = &_arena;
            __auto_type _mv_206 = tester_main_read_file(arena, ((char*)(argv[1])));
            if (_mv_206.has_value) {
                __auto_type source = _mv_206.value;
                {
                    __auto_type result = tester_generate_tests(arena, source);
                    if (result.success) {
                        putchar(123);
                        tester_main_print_str(((char*)(SLOP_STR("\"test_harness\":").data)));
                        {
                            __auto_type harness_str = tester_main_lines_to_string(arena, result.test_harness);
                            tester_main_print_json_string(harness_str);
                        }
                        putchar(44);
                        tester_main_print_str(((char*)(SLOP_STR("\"test_count\":").data)));
                        tester_main_print_int(result.test_count);
                        putchar(44);
                        tester_main_print_str(((char*)(SLOP_STR("\"module_name\":").data)));
                        tester_main_print_json_string(result.module_name);
                        putchar(125);
                        putchar(10);
                        return 0;
                    } else {
                        tester_main_print_str(((char*)(SLOP_STR("{\"error\":").data)));
                        tester_main_print_json_string(result.error_message);
                        tester_main_print_str(((char*)(SLOP_STR("}\n").data)));
                        return 1;
                    }
                }
            } else if (!_mv_206.has_value) {
                tester_main_print_str(((char*)(SLOP_STR("{\"error\":\"Could not read file\"}\n").data)));
                return 1;
            }
            slop_arena_free(arena);
        }
    }
}

