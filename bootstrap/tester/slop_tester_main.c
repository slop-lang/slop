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
slop_list_string tester_main_read_import_files(slop_arena* arena, uint8_t** argv, slop_list_int files);
uint8_t tester_main_collect_args(slop_arena* arena, int64_t argc, uint8_t** argv, slop_list_ctype_ModulePackage* packages, slop_list_int* files);
int tester_main_main(int argc, char** _c_argv);

slop_option_string tester_main_read_file(slop_arena* arena, char* filename) {
    {
        __auto_type file = fopen(filename, ((char*)(SLOP_STR("rb").data)));
        if (file == NULL) {
            return (slop_option_string){.has_value = false};
        } else {
            fseek(file, 0, tester_main_SEEK_END);
            {
                __auto_type size = ftell(file);
                fseek(file, 0, tester_main_SEEK_SET);
                {
                    __auto_type buf = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (size + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
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
        int64_t i = 0;
        while (s[i] != 0) {
            putchar(((int64_t)(s[i])));
            i = (i + 1);
        }
    }
}

void tester_main_print_string(slop_string s) {
    {
        __auto_type len = ((int64_t)(s.len));
        __auto_type data = s.data;
        int64_t i = 0;
        while (i < len) {
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
        int64_t i = 0;
        while (i < len) {
            {
                __auto_type c = ((int64_t)(data[i]));
                if (c == 34) {
                    putchar(92);
                    putchar(34);
                } else if (c == 92) {
                    putchar(92);
                    putchar(92);
                } else if (c == 10) {
                    putchar(92);
                    putchar(110);
                } else if (c == 13) {
                    putchar(92);
                    putchar(114);
                } else if (c == 9) {
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
        if (len == 0) {
            return SLOP_STR("");
        } else {
            {
                int64_t total = 0;
                int64_t i = 0;
                while (i < len) {
                    __auto_type _mv_1790 = ({ __auto_type _lst = lines; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1790.has_value) {
                        __auto_type line = _mv_1790.value;
                        total = (total + (((int64_t)(line.len)) + 1));
                    } else if (!_mv_1790.has_value) {
                    }
                    i = (i + 1);
                }
                {
                    __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (total + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                    int64_t pos = 0;
                    int64_t j = 0;
                    while (j < len) {
                        __auto_type _mv_1791 = ({ __auto_type _lst = lines; size_t _idx = (size_t)j; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1791.has_value) {
                            __auto_type line = _mv_1791.value;
                            {
                                __auto_type line_len = ((int64_t)(line.len));
                                __auto_type line_data = line.data;
                                int64_t k = 0;
                                while (k < line_len) {
                                    buf[pos] = line_data[k];
                                    pos = (pos + 1);
                                    k = (k + 1);
                                }
                                buf[pos] = 10;
                                pos = (pos + 1);
                            }
                        } else if (!_mv_1791.has_value) {
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
    if (n < 0) {
        putchar(45);
        tester_main_print_int((0 - n));
    } else {
        if (n < 10) {
            putchar((48 + n));
        } else {
            tester_main_print_int((n / 10));
            putchar((48 + (n % 10)));
        }
    }
}

slop_list_string tester_main_read_import_files(slop_arena* arena, uint8_t** argv, slop_list_int files) {
    {
        __auto_type sources = ((slop_list_string){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
        __auto_type count = ((int64_t)((files).len));
        int64_t i = 1;
        while (i < count) {
            __auto_type _mv_1792 = ({ __auto_type _lst = files; size_t _idx = (size_t)i; slop_option_int _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1792.has_value) {
                __auto_type idx = _mv_1792.value;
                {
                    __auto_type path_ptr = ((char*)(argv[idx]));
                    __auto_type _mv_1793 = tester_main_read_file(arena, path_ptr);
                    if (_mv_1793.has_value) {
                        __auto_type source = _mv_1793.value;
                        ({ __auto_type _lst_p = &(sources); __auto_type _item = (source); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    } else if (!_mv_1793.has_value) {
                    }
                }
            } else if (!_mv_1792.has_value) {
            }
            i = (i + 1);
        }
        return sources;
    }
}

uint8_t tester_main_collect_args(slop_arena* arena, int64_t argc, uint8_t** argv, slop_list_ctype_ModulePackage* packages, slop_list_int* files) {
    {
        int64_t i = 1;
        uint8_t ok = 1;
        while (i < argc) {
            {
                __auto_type arg = std_strlib_cstring_to_string(argv[i]);
                if (string_eq(arg, SLOP_STR("--package"))) {
                    if ((i + 1) < argc) {
                        __auto_type _mv_1794 = ctype_parse_module_package(arena, std_strlib_cstring_to_string(argv[(i + 1)]));
                        if (_mv_1794.has_value) {
                            __auto_type entry = _mv_1794.value;
                            ({ __auto_type _lst_p = &((*packages)); __auto_type _item = (entry); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        } else if (!_mv_1794.has_value) {
                            tester_main_print_str(((char*)(SLOP_STR("{\"error\":\"--package expects MODULE=NAME\"}\n").data)));
                            ok = 0;
                        }
                    } else {
                        tester_main_print_str(((char*)(SLOP_STR("{\"error\":\"--package expects MODULE=NAME\"}\n").data)));
                        ok = 0;
                    }
                    i = (i + 2);
                } else {
                    (void)(({ __auto_type _lst_p = &((*files)); __auto_type _item = (i); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; }));
                    i = (i + 1);
                }
            }
        }
        return ok;
    }
}

int main(int argc, char** _c_argv) {
    uint8_t** argv = (uint8_t**)_c_argv;
    (void)argc; (void)argv;
    if (argc >= 2) {
        if (string_eq(std_strlib_cstring_to_string(argv[1]), SLOP_STR("--version"))) {
            tester_main_print_str(((char*)(SLOP_STR("slop-tester 0.5.1\n").data)));
            return 0;
        }
    }
    if (argc < 2) {
        tester_main_print_str(((char*)(SLOP_STR("Usage: slop-tester [--package MODULE=NAME ...] <input.slop> [import-files...]\n").data)));
        return 1;
    } else {
        {
            #ifdef SLOP_DEBUG
            SLOP_PRE((67108864) > 0, "with-arena size must be positive");
            #endif
            slop_arena _arena_3 = slop_arena_new(67108864);
            #ifdef SLOP_DEBUG
            SLOP_PRE(_arena_3.base != NULL, "arena allocation failed");
            #endif
            slop_arena* arena = &_arena_3;
            {
                __auto_type packages = ((slop_list_ctype_ModulePackage){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
                __auto_type files = ((slop_list_int){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
                if (!(tester_main_collect_args(arena, argc, argv, (&packages), (&files)))) {
                    {
                        int _wa_ret = 1;
                        slop_arena_free(&_arena_3);
                        return _wa_ret;
                    }
                } else {
                    __auto_type _mv_1795 = ({ __auto_type _lst = files; size_t _idx = (size_t)0; slop_option_int _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (!_mv_1795.has_value) {
                        tester_main_print_str(((char*)(SLOP_STR("Usage: slop-tester [--package MODULE=NAME ...] <input.slop> [import-files...]\n").data)));
                        {
                            int _wa_ret = 1;
                            slop_arena_free(&_arena_3);
                            return _wa_ret;
                        }
                    } else if (_mv_1795.has_value) {
                        __auto_type input_idx = _mv_1795.value;
                        __auto_type _mv_1796 = tester_main_read_file(arena, ((char*)(argv[input_idx])));
                        if (_mv_1796.has_value) {
                            __auto_type source = _mv_1796.value;
                            {
                                __auto_type import_sources = tester_main_read_import_files(arena, argv, files);
                                __auto_type result = tester_generate_tests_with_imports(arena, source, import_sources, std_strlib_cstring_to_string(argv[input_idx]), packages);
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
                                    {
                                        int _wa_ret = 0;
                                        slop_arena_free(&_arena_3);
                                        return _wa_ret;
                                    }
                                } else {
                                    tester_main_print_str(((char*)(SLOP_STR("{\"error\":").data)));
                                    tester_main_print_json_string(result.error_message);
                                    tester_main_print_str(((char*)(SLOP_STR("}\n").data)));
                                    {
                                        int _wa_ret = 1;
                                        slop_arena_free(&_arena_3);
                                        return _wa_ret;
                                    }
                                }
                            }
                        } else if (!_mv_1796.has_value) {
                            tester_main_print_str(((char*)(SLOP_STR("{\"error\":\"Could not read file\"}\n").data)));
                            {
                                int _wa_ret = 1;
                                slop_arena_free(&_arena_3);
                                return _wa_ret;
                            }
                        }
                        SLOP_UNREACHABLE();
                    }
                    SLOP_UNREACHABLE();
                }
            }
            slop_arena_free(arena);
        }
    }
}

