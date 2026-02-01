#include "../runtime/slop_runtime.h"
#include "slop_transpiler_main.h"

#define transpiler_main_SEEK_SET (0)
#define transpiler_main_SEEK_END (2)

slop_option_string transpiler_main_read_file(slop_arena* arena, char* filename);
void transpiler_main_print_str(char* s);
void transpiler_main_print_string(slop_string s);
void transpiler_main_print_json_string(slop_arena* arena, slop_string s);
slop_string transpiler_main_lines_to_string(slop_arena* arena, slop_list_string lines);
slop_string transpiler_main_extract_module_name(slop_list_types_SExpr_ptr exprs);
int transpiler_main_main(int64_t argc, char** argv);
int64_t transpiler_main_transpile_single_file_with_ctx(context_TranspileContext* ctx, slop_string source, uint8_t first);
int64_t transpiler_main_transpile_single_file(slop_arena* arena, slop_string source, uint8_t first);
void transpiler_main_output_module_json(slop_arena* arena, context_TranspileContext* ctx, slop_string mod_name, uint8_t first);

slop_option_string transpiler_main_read_file(slop_arena* arena, char* filename) {
    {
        __auto_type file = fopen(filename, ((char*)(SLOP_STR("rb").data)));
        if ((file == NULL)) {
            return (slop_option_string){.has_value = false};
        } else {
            fseek(file, 0, transpiler_main_SEEK_END);
            {
                __auto_type size = ftell(file);
                fseek(file, 0, transpiler_main_SEEK_SET);
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

void transpiler_main_print_str(char* s) {
    {
        __auto_type i = 0;
        while ((s[i] != 0)) {
            putchar(((int64_t)(s[i])));
            i = (i + 1);
        }
    }
}

void transpiler_main_print_string(slop_string s) {
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

void transpiler_main_print_json_string(slop_arena* arena, slop_string s) {
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

slop_string transpiler_main_lines_to_string(slop_arena* arena, slop_list_string lines) {
    {
        __auto_type len = ((int64_t)((lines).len));
        if ((len == 0)) {
            return SLOP_STR("");
        } else {
            {
                __auto_type total = 0;
                __auto_type i = 0;
                while ((i < len)) {
                    __auto_type _mv_1311 = ({ __auto_type _lst = lines; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1311.has_value) {
                        __auto_type line = _mv_1311.value;
                        total = (total + (((int64_t)(line.len)) + 1));
                    } else if (!_mv_1311.has_value) {
                    }
                    i = (i + 1);
                }
                {
                    __auto_type buf = (uint8_t*)slop_arena_alloc(arena, (total + 1));
                    __auto_type pos = 0;
                    __auto_type j = 0;
                    while ((j < len)) {
                        __auto_type _mv_1312 = ({ __auto_type _lst = lines; size_t _idx = (size_t)j; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1312.has_value) {
                            __auto_type line = _mv_1312.value;
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
                        } else if (!_mv_1312.has_value) {
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

slop_string transpiler_main_extract_module_name(slop_list_types_SExpr_ptr exprs) {
    if ((((int64_t)((exprs).len)) < 1)) {
        return SLOP_STR("unknown");
    } else {
        __auto_type _mv_1313 = ({ __auto_type _lst = exprs; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1313.has_value) {
            __auto_type first_expr = _mv_1313.value;
            __auto_type _mv_1314 = (*first_expr);
            switch (_mv_1314.tag) {
                case types_SExpr_lst:
                {
                    __auto_type lst = _mv_1314.data.lst;
                    {
                        __auto_type items = lst.items;
                        if ((((int64_t)((items).len)) < 2)) {
                            return SLOP_STR("unknown");
                        } else {
                            __auto_type _mv_1315 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1315.has_value) {
                                __auto_type head = _mv_1315.value;
                                __auto_type _mv_1316 = (*head);
                                switch (_mv_1316.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1316.data.sym;
                                        if (string_eq(sym.name, SLOP_STR("module"))) {
                                            __auto_type _mv_1317 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1317.has_value) {
                                                __auto_type name_expr = _mv_1317.value;
                                                __auto_type _mv_1318 = (*name_expr);
                                                switch (_mv_1318.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type name_sym = _mv_1318.data.sym;
                                                        return name_sym.name;
                                                    }
                                                    default: {
                                                        return SLOP_STR("unknown");
                                                    }
                                                }
                                            } else if (!_mv_1317.has_value) {
                                                return SLOP_STR("unknown");
                                            }
                                        } else {
                                            return SLOP_STR("unknown");
                                        }
                                    }
                                    default: {
                                        return SLOP_STR("unknown");
                                    }
                                }
                            } else if (!_mv_1315.has_value) {
                                return SLOP_STR("unknown");
                            }
                        }
                    }
                }
                default: {
                    return SLOP_STR("unknown");
                }
            }
        } else if (!_mv_1313.has_value) {
            return SLOP_STR("unknown");
        }
    }
}

int main(int64_t argc, char** argv) {
    if ((argc < 2)) {
        transpiler_main_print_str(((char*)(SLOP_STR("Usage: slop-transpiler <input.slop> [input2.slop ...]\n").data)));
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
            {
                __auto_type ctx = context_context_new(arena);
                context_ctx_set_prefixing(ctx, 1);
                putchar(123);
                {
                    __auto_type i = 1;
                    __auto_type first = 1;
                    while ((i < argc)) {
                        {
                            __auto_type filename = argv[i];
                            __auto_type filename_ptr = ((uint8_t*)(filename));
                            __auto_type filename_str = (slop_string){.len = strlen(filename_ptr), .data = filename_ptr};
                            context_ctx_set_file(ctx, filename_str);
                            __auto_type _mv_1319 = transpiler_main_read_file(arena, filename);
                            if (_mv_1319.has_value) {
                                __auto_type source = _mv_1319.value;
                                {
                                    __auto_type result = transpiler_main_transpile_single_file_with_ctx(ctx, source, first);
                                    first = 0;
                                }
                            } else if (!_mv_1319.has_value) {
                                transpiler_main_print_str(((char*)(SLOP_STR("Error: Could not read file\n").data)));
                            }
                        }
                        i = (i + 1);
                    }
                }
                putchar(125);
                putchar(10);
                return 0;
            }
            slop_arena_free(arena);
        }
    }
}

int64_t transpiler_main_transpile_single_file_with_ctx(context_TranspileContext* ctx, slop_string source, uint8_t first) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type parse_result = parser_parse(arena, source);
        __auto_type _mv_1320 = parse_result;
        if (_mv_1320.is_ok) {
            __auto_type exprs = _mv_1320.data.ok;
            {
                __auto_type mod_name = transpiler_main_extract_module_name(exprs);
                context_ctx_reset_for_new_module(ctx, mod_name);
                transpiler_transpile_file(ctx, exprs);
                if (context_ctx_has_errors(ctx)) {
                    context_ctx_report_errors(ctx);
                    exit(1);
                }
                transpiler_main_output_module_json(arena, ctx, mod_name, first);
                return 0;
            }
        } else if (!_mv_1320.is_ok) {
            __auto_type err = _mv_1320.data.err;
            transpiler_main_print_str(((char*)(SLOP_STR("Parse error at line ").data)));
            transpiler_main_print_string(int_to_string(arena, err.line));
            transpiler_main_print_str(((char*)(SLOP_STR(", col ").data)));
            transpiler_main_print_string(int_to_string(arena, err.col));
            transpiler_main_print_str(((char*)(SLOP_STR(": ").data)));
            transpiler_main_print_string(err.message);
            putchar(10);
            return 1;
        }
    }
}

int64_t transpiler_main_transpile_single_file(slop_arena* arena, slop_string source, uint8_t first) {
    {
        __auto_type parse_result = parser_parse(arena, source);
        __auto_type _mv_1321 = parse_result;
        if (_mv_1321.is_ok) {
            __auto_type exprs = _mv_1321.data.ok;
            {
                __auto_type mod_name = transpiler_main_extract_module_name(exprs);
                __auto_type ctx = context_context_new(arena);
                context_ctx_set_prefixing(ctx, 1);
                context_ctx_reset_for_new_module(ctx, mod_name);
                transpiler_transpile_file(ctx, exprs);
                if (context_ctx_has_errors(ctx)) {
                    context_ctx_report_errors(ctx);
                    exit(1);
                }
                transpiler_main_output_module_json(arena, ctx, mod_name, first);
                return 0;
            }
        } else if (!_mv_1321.is_ok) {
            __auto_type err = _mv_1321.data.err;
            transpiler_main_print_str(((char*)(SLOP_STR("Parse error at line ").data)));
            transpiler_main_print_string(int_to_string(arena, err.line));
            transpiler_main_print_str(((char*)(SLOP_STR(", col ").data)));
            transpiler_main_print_string(int_to_string(arena, err.col));
            transpiler_main_print_str(((char*)(SLOP_STR(": ").data)));
            transpiler_main_print_string(err.message);
            putchar(10);
            return 1;
        }
    }
}

void transpiler_main_output_module_json(slop_arena* arena, context_TranspileContext* ctx, slop_string mod_name, uint8_t first) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (!(first)) {
        putchar(44);
    }
    transpiler_main_print_json_string(arena, mod_name);
    putchar(58);
    putchar(123);
    transpiler_main_print_str(((char*)(SLOP_STR("\"header\":").data)));
    {
        __auto_type header_lines = context_ctx_get_header(ctx);
        __auto_type header_str = transpiler_main_lines_to_string(arena, header_lines);
        transpiler_main_print_json_string(arena, header_str);
    }
    putchar(44);
    transpiler_main_print_str(((char*)(SLOP_STR("\"impl\":").data)));
    {
        __auto_type impl_lines = context_ctx_get_output(ctx);
        __auto_type impl_str = transpiler_main_lines_to_string(arena, impl_lines);
        transpiler_main_print_json_string(arena, impl_str);
    }
    putchar(125);
}

