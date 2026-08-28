#include "../runtime/slop_runtime.h"
#include "slop_compiler.h"

void compiler_print_str(uint8_t* s);
void compiler_print_string(slop_string s);
void compiler_print_json_string(slop_arena* arena, slop_string s);
slop_string compiler_lines_to_string(slop_arena* arena, slop_list_string lines);
slop_string compiler_extract_module_name(slop_list_types_SExpr_ptr exprs);
slop_string compiler_argv_to_string(uint8_t** argv, int64_t index);
void compiler_type_check_with_env(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void compiler_check_all_functions(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
uint8_t compiler_is_annotation_form(types_SExpr* item);
uint8_t compiler_is_valid_toplevel_form(types_SExpr* item);
slop_string compiler_get_form_name(types_SExpr* item);
void compiler_check_module_functions(env_TypeEnv* env, types_SExpr* module_form);
int64_t compiler_count_errors(slop_list_types_Diagnostic diagnostics);
void compiler_print_diagnostic(slop_arena* arena, slop_string filename, types_Diagnostic diag);
void compiler_output_diagnostics_text(slop_arena* arena, slop_string filename, slop_list_types_Diagnostic diagnostics);
void compiler_output_diagnostics_json(slop_arena* arena, slop_list_types_Diagnostic diagnostics);
void compiler_output_single_diagnostic_json(slop_arena* arena, types_Diagnostic diag);
void compiler_output_check_module_json(slop_arena* arena, slop_string mod_name, slop_list_types_Diagnostic diagnostics, uint8_t first);
int64_t compiler_check_single_file(env_TypeEnv* env, slop_arena* arena, uint8_t* filename, compiler_OutputFormat format, uint8_t first);
types_ResolvedType* compiler_resolve_type_string(env_TypeEnv* env, slop_arena* arena, slop_string type_str);
void compiler_parse_and_bind_params(env_TypeEnv* env, slop_arena* arena, slop_string params_str);
uint8_t compiler_types_names_equal(types_ResolvedType* a, types_ResolvedType* b);
int64_t compiler_check_expr_mode(slop_arena* arena, env_TypeEnv* env, slop_string expr_str, slop_string type_str, slop_string context_file, slop_string params_str);
void compiler_output_expr_result(slop_arena* arena, uint8_t valid, slop_string inferred_type, slop_string expected_type, slop_list_types_Diagnostic diagnostics);
int64_t compiler_transpile_single_file(env_TypeEnv* env, context_TranspileContext* ctx, slop_arena* arena, uint8_t* filename, uint8_t first);
void compiler_output_transpile_module_json(slop_arena* arena, context_TranspileContext* ctx, slop_string mod_name, uint8_t first);
slop_string compiler_emit_sexpr_inner(slop_arena* arena, types_SExpr* expr);
slop_string compiler_emit_typed_sexpr(slop_arena* arena, types_SExpr* expr);
slop_string compiler_emit_typed_list(slop_arena* arena, slop_list_types_SExpr_ptr items);
slop_string compiler_emit_typed_toplevel(slop_arena* arena, types_SExpr* expr);
slop_string compiler_emit_typed_module(slop_arena* arena, types_SExpr* module_form);
slop_string compiler_emit_typed_ast(slop_arena* arena, slop_list_types_SExpr_ptr ast);
int64_t compiler_typed_ast_single_file(env_TypeEnv* env, slop_arena* arena, uint8_t* filename, compiler_OutputFormat format, uint8_t first);
int compiler_main(int argc, char** _c_argv);

void compiler_print_str(uint8_t* s) {
    SLOP_PRE(((s != NULL)), "(!= s nil)");
    {
        int64_t i = 0;
        while (s[i] != 0) {
            putchar(((int64_t)(s[i])));
            i = (i + 1);
        }
    }
}

void compiler_print_string(slop_string s) {
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

void compiler_print_json_string(slop_arena* arena, slop_string s) {
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

slop_string compiler_lines_to_string(slop_arena* arena, slop_list_string lines) {
    {
        __auto_type len = ((int64_t)((lines).len));
        if (len == 0) {
            return SLOP_STR("");
        } else {
            {
                int64_t total = 0;
                int64_t i = 0;
                while (i < len) {
                    __auto_type _mv_1868 = ({ __auto_type _lst = lines; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1868.has_value) {
                        __auto_type line = _mv_1868.value;
                        total = (total + (((int64_t)(line.len)) + 1));
                    } else if (!_mv_1868.has_value) {
                    }
                    i = (i + 1);
                }
                {
                    __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (total + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                    int64_t pos = 0;
                    int64_t j = 0;
                    while (j < len) {
                        __auto_type _mv_1869 = ({ __auto_type _lst = lines; size_t _idx = (size_t)j; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1869.has_value) {
                            __auto_type line = _mv_1869.value;
                            {
                                __auto_type line_len = ((int64_t)(line.len));
                                __auto_type line_data = line.data;
                                __auto_type k = 0;
                                while (k < line_len) {
                                    buf[pos] = line_data[k];
                                    pos = (pos + 1);
                                    k = (k + 1);
                                }
                                buf[pos] = 10;
                                pos = (pos + 1);
                            }
                        } else if (!_mv_1869.has_value) {
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

slop_string compiler_extract_module_name(slop_list_types_SExpr_ptr exprs) {
    if (((int64_t)((exprs).len)) < 1) {
        return SLOP_STR("unknown");
    } else {
        __auto_type _mv_1870 = ({ __auto_type _lst = exprs; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1870.has_value) {
            __auto_type first_expr = _mv_1870.value;
            __auto_type _mv_1871 = (*first_expr);
            switch (_mv_1871.tag) {
                case types_SExpr_lst:
                {
                    __auto_type lst = _mv_1871.data.lst;
                    {
                        __auto_type items = lst.items;
                        if (((int64_t)((items).len)) < 2) {
                            return SLOP_STR("unknown");
                        } else {
                            __auto_type _mv_1872 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1872.has_value) {
                                __auto_type head = _mv_1872.value;
                                __auto_type _mv_1873 = (*head);
                                switch (_mv_1873.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1873.data.sym;
                                        if (string_eq(sym.name, SLOP_STR("module"))) {
                                            __auto_type _mv_1874 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1874.has_value) {
                                                __auto_type name_expr = _mv_1874.value;
                                                __auto_type _mv_1875 = (*name_expr);
                                                switch (_mv_1875.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type name_sym = _mv_1875.data.sym;
                                                        return name_sym.name;
                                                    }
                                                    default: {
                                                        return SLOP_STR("unknown");
                                                    }
                                                }
                                            } else if (!_mv_1874.has_value) {
                                                return SLOP_STR("unknown");
                                            }
                                            SLOP_UNREACHABLE();
                                        } else {
                                            return SLOP_STR("unknown");
                                        }
                                    }
                                    default: {
                                        return SLOP_STR("unknown");
                                    }
                                }
                            } else if (!_mv_1872.has_value) {
                                return SLOP_STR("unknown");
                            }
                            SLOP_UNREACHABLE();
                        }
                    }
                }
                default: {
                    return SLOP_STR("unknown");
                }
            }
        } else if (!_mv_1870.has_value) {
            return SLOP_STR("unknown");
        }
        SLOP_UNREACHABLE();
    }
}

slop_string compiler_argv_to_string(uint8_t** argv, int64_t index) {
    {
        __auto_type ptr = argv[index];
        return (slop_string){.len = strlen(ptr), .data = ptr};
    }
}

void compiler_type_check_with_env(env_TypeEnv* env, slop_list_types_SExpr_ptr ast) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((((int64_t)((ast).len)) > 0)), "(> (list-len ast) 0)");
    collect_collect_module(env, ast);
    resolve_resolve_imports(env, ast);
    compiler_check_all_functions(env, ast);
}

void compiler_check_all_functions(env_TypeEnv* env, slop_list_types_SExpr_ptr ast) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type len = ((int64_t)((ast).len));
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_1876 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1876.has_value) {
                __auto_type expr = _mv_1876.value;
                if (parser_is_form(expr, SLOP_STR("fn"))) {
                    {
                        __auto_type _ = infer_infer_fn_body(env, expr);
                    }
                } else if (parser_is_form(expr, SLOP_STR("module"))) {
                    compiler_check_module_functions(env, expr);
                } else {
                }
            } else if (!_mv_1876.has_value) {
            }
        }
    }
}

uint8_t compiler_is_annotation_form(types_SExpr* item) {
    if (parser_sexpr_is_list(item)) {
        __auto_type _mv_1877 = parser_sexpr_list_get(item, 0);
        if (_mv_1877.has_value) {
            __auto_type head = _mv_1877.value;
            return ((uint8_t)(({ __auto_type name = parser_sexpr_get_symbol_name(head); (((name.len > 0)) ? (name.data[0] == 64) : 0); })));
        } else if (!_mv_1877.has_value) {
            return 0;
        }
        SLOP_UNREACHABLE();
    } else {
        return 0;
    }
}

uint8_t compiler_is_valid_toplevel_form(types_SExpr* item) {
    if (parser_is_form(item, SLOP_STR("fn"))) {
        return 1;
    } else if (parser_is_form(item, SLOP_STR("type"))) {
        return 1;
    } else if (parser_is_form(item, SLOP_STR("const"))) {
        return 1;
    } else if (parser_is_form(item, SLOP_STR("ffi"))) {
        return 1;
    } else if (parser_is_form(item, SLOP_STR("ffi-struct"))) {
        return 1;
    } else if (parser_is_form(item, SLOP_STR("import"))) {
        return 1;
    } else if (parser_is_form(item, SLOP_STR("export"))) {
        return 1;
    } else if (compiler_is_annotation_form(item)) {
        return 1;
    } else {
        return 0;
    }
}

slop_string compiler_get_form_name(types_SExpr* item) {
    if (parser_sexpr_is_list(item)) {
        __auto_type _mv_1878 = parser_sexpr_list_get(item, 0);
        if (_mv_1878.has_value) {
            __auto_type head = _mv_1878.value;
            return parser_sexpr_get_symbol_name(head);
        } else if (!_mv_1878.has_value) {
            return SLOP_STR("<empty>");
        }
        SLOP_UNREACHABLE();
    } else {
        return SLOP_STR("<non-list>");
    }
}

void compiler_check_module_functions(env_TypeEnv* env, types_SExpr* module_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((module_form != NULL)), "(!= module-form nil)");
    if (parser_sexpr_is_list(module_form)) {
        __auto_type _mv_1879 = parser_sexpr_list_get(module_form, 1);
        if (_mv_1879.has_value) {
            __auto_type name_expr = _mv_1879.value;
            {
                __auto_type mod_name = parser_sexpr_get_symbol_name(name_expr);
                if (!(string_eq(mod_name, SLOP_STR("")))) {
                    env_env_set_module(env, (slop_option_string){.has_value = 1, .value = mod_name});
                }
            }
        } else if (!_mv_1879.has_value) {
        }
        {
            __auto_type len = parser_sexpr_list_len(module_form);
            for (int64_t i = 2; i < len; i++) {
                __auto_type _mv_1880 = parser_sexpr_list_get(module_form, i);
                if (_mv_1880.has_value) {
                    __auto_type item = _mv_1880.value;
                    if (parser_is_form(item, SLOP_STR("fn"))) {
                        {
                            __auto_type _ = infer_infer_fn_body(env, item);
                        }
                    } else if (compiler_is_valid_toplevel_form(item)) {
                    } else {
                        {
                            __auto_type arena = env_env_arena(env);
                            __auto_type msg = string_concat(arena, SLOP_STR("Unknown top-level form: "), compiler_get_form_name(item));
                            env_env_add_error(env, msg, parser_sexpr_line(item), parser_sexpr_col(item));
                        }
                    }
                } else if (!_mv_1880.has_value) {
                }
            }
        }
    }
}

int64_t compiler_count_errors(slop_list_types_Diagnostic diagnostics) {
    {
        __auto_type len = ((int64_t)((diagnostics).len));
        int64_t errors = 0;
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1881 = ({ __auto_type _lst = diagnostics; size_t _idx = (size_t)i; slop_option_types_Diagnostic _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1881.has_value) {
                __auto_type diag = _mv_1881.value;
                __auto_type _mv_1882 = diag.level;
                if (_mv_1882 == types_DiagnosticLevel_diag_error) {
                    errors = (errors + 1);
                } else if (_mv_1882 == types_DiagnosticLevel_diag_warning) {
                }
            } else if (!_mv_1881.has_value) {
            }
            i = (i + 1);
        }
        return errors;
    }
}

void compiler_print_diagnostic(slop_arena* arena, slop_string filename, types_Diagnostic diag) {
    printf("%.*s", (int)(filename).len, (filename).data);
    printf("%s", ":");
    printf("%lld", (long long)(diag.line));
    printf("%s", ":");
    printf("%lld", (long long)(diag.col));
    printf("%s", ": ");
    __auto_type _mv_1883 = diag.level;
    if (_mv_1883 == types_DiagnosticLevel_diag_warning) {
        printf("%s", "warning: ");
    } else if (_mv_1883 == types_DiagnosticLevel_diag_error) {
        printf("%s", "error: ");
    }
    printf("%.*s\n", (int)(diag.message).len, (diag.message).data);
}

void compiler_output_diagnostics_text(slop_arena* arena, slop_string filename, slop_list_types_Diagnostic diagnostics) {
    {
        __auto_type len = ((int64_t)((diagnostics).len));
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1884 = ({ __auto_type _lst = diagnostics; size_t _idx = (size_t)i; slop_option_types_Diagnostic _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1884.has_value) {
                __auto_type diag = _mv_1884.value;
                compiler_print_diagnostic(arena, filename, diag);
            } else if (!_mv_1884.has_value) {
            }
            i = (i + 1);
        }
    }
}

void compiler_output_diagnostics_json(slop_arena* arena, slop_list_types_Diagnostic diagnostics) {
    putchar(91);
    {
        __auto_type len = ((int64_t)((diagnostics).len));
        int64_t i = 0;
        while (i < len) {
            if (i > 0) {
                putchar(44);
            }
            __auto_type _mv_1885 = ({ __auto_type _lst = diagnostics; size_t _idx = (size_t)i; slop_option_types_Diagnostic _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1885.has_value) {
                __auto_type diag = _mv_1885.value;
                compiler_output_single_diagnostic_json(arena, diag);
            } else if (!_mv_1885.has_value) {
            }
            i = (i + 1);
        }
    }
    putchar(93);
}

void compiler_output_single_diagnostic_json(slop_arena* arena, types_Diagnostic diag) {
    putchar(123);
    compiler_print_str(((uint8_t*)(SLOP_STR("\"level\":").data)));
    __auto_type _mv_1886 = diag.level;
    if (_mv_1886 == types_DiagnosticLevel_diag_warning) {
        compiler_print_str(((uint8_t*)(SLOP_STR("\"warning\"").data)));
    } else if (_mv_1886 == types_DiagnosticLevel_diag_error) {
        compiler_print_str(((uint8_t*)(SLOP_STR("\"error\"").data)));
    }
    putchar(44);
    compiler_print_str(((uint8_t*)(SLOP_STR("\"line\":").data)));
    compiler_print_string(int_to_string(arena, diag.line));
    putchar(44);
    compiler_print_str(((uint8_t*)(SLOP_STR("\"col\":").data)));
    compiler_print_string(int_to_string(arena, diag.col));
    putchar(44);
    compiler_print_str(((uint8_t*)(SLOP_STR("\"message\":").data)));
    compiler_print_json_string(arena, diag.message);
    putchar(125);
}

void compiler_output_check_module_json(slop_arena* arena, slop_string mod_name, slop_list_types_Diagnostic diagnostics, uint8_t first) {
    if (!(first)) {
        putchar(44);
    }
    compiler_print_json_string(arena, mod_name);
    putchar(58);
    putchar(123);
    compiler_print_str(((uint8_t*)(SLOP_STR("\"diagnostics\":").data)));
    compiler_output_diagnostics_json(arena, diagnostics);
    putchar(125);
}

int64_t compiler_check_single_file(env_TypeEnv* env, slop_arena* arena, uint8_t* filename, compiler_OutputFormat format, uint8_t first) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((filename != NULL)), "(!= filename nil)");
    {
        __auto_type filename_str = strlib_cstring_to_string(filename);
        __auto_type _mv_1887 = file_file_open(filename_str, file_FileMode_read);
        if (!_mv_1887.is_ok) {
            __auto_type e = _mv_1887.data.err;
            printf("%s", "Error: Could not open file: ");
            printf("%.*s\n", (int)(filename_str).len, (filename_str).data);
            return 1;
        } else if (_mv_1887.is_ok) {
            __auto_type f = _mv_1887.data.ok;
            __auto_type _mv_1888 = file_file_read_all(arena, (&f));
            if (!_mv_1888.is_ok) {
                __auto_type e = _mv_1888.data.err;
                file_file_close((&f));
                printf("%s", "Error: Could not read file: ");
                printf("%.*s\n", (int)(filename_str).len, (filename_str).data);
                return 1;
            } else if (_mv_1888.is_ok) {
                __auto_type source = _mv_1888.data.ok;
                file_file_close((&f));
                __auto_type _mv_1889 = parser_parse(arena, source);
                if (_mv_1889.is_ok) {
                    __auto_type ast = _mv_1889.data.ok;
                    {
                        __auto_type mod_name = compiler_extract_module_name(ast);
                        env_env_clear_imports(env);
                        env_env_clear_diagnostics(env);
                        compiler_type_check_with_env(env, ast);
                        {
                            __auto_type diagnostics = env_env_get_diagnostics(env);
                            if (format == compiler_OutputFormat_fmt_json) {
                                compiler_output_check_module_json(arena, mod_name, diagnostics, first);
                            }
                            if (format == compiler_OutputFormat_fmt_text) {
                                compiler_output_diagnostics_text(arena, filename_str, diagnostics);
                            }
                            return compiler_count_errors(diagnostics);
                        }
                    }
                } else if (!_mv_1889.is_ok) {
                    __auto_type parse_err = _mv_1889.data.err;
                    printf("%.*s", (int)(filename_str).len, (filename_str).data);
                    printf("%s", ":");
                    printf("%lld", (long long)(parse_err.line));
                    printf("%s", ":");
                    printf("%lld", (long long)(parse_err.col));
                    printf("%s", ": error: ");
                    printf("%.*s\n", (int)(parse_err.message).len, (parse_err.message).data);
                    return 1;
                }
                SLOP_UNREACHABLE();
            }
            SLOP_UNREACHABLE();
        }
        SLOP_UNREACHABLE();
    }
}

types_ResolvedType* compiler_resolve_type_string(env_TypeEnv* env, slop_arena* arena, slop_string type_str) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1890 = parser_parse(arena, type_str);
    if (_mv_1890.is_ok) {
        __auto_type type_ast = _mv_1890.data.ok;
        if (((int64_t)((type_ast).len)) == 0) {
            return env_env_get_int_type(env);
        } else {
            __auto_type _mv_1891 = ({ __auto_type _lst = type_ast; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1891.has_value) {
                __auto_type type_expr = _mv_1891.value;
                if (parser_sexpr_is_list(type_expr)) {
                    return infer_resolve_complex_type_expr(env, type_expr);
                } else {
                    {
                        __auto_type name = parser_sexpr_get_symbol_name(type_expr);
                        if (string_eq(name, SLOP_STR(""))) {
                            return env_env_get_int_type(env);
                        } else {
                            return infer_resolve_simple_type(env, name);
                        }
                    }
                }
            } else if (!_mv_1891.has_value) {
                return env_env_get_int_type(env);
            }
            SLOP_UNREACHABLE();
        }
    } else if (!_mv_1890.is_ok) {
        __auto_type _ = _mv_1890.data.err;
        return env_env_get_int_type(env);
    }
    SLOP_UNREACHABLE();
}

void compiler_parse_and_bind_params(env_TypeEnv* env, slop_arena* arena, slop_string params_str) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1892 = parser_parse(arena, params_str);
    if (_mv_1892.is_ok) {
        __auto_type params_ast = _mv_1892.data.ok;
        if (((int64_t)((params_ast).len)) > 0) {
            __auto_type _mv_1893 = ({ __auto_type _lst = params_ast; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1893.has_value) {
                __auto_type params_list = _mv_1893.value;
                __auto_type _mv_1894 = (*params_list);
                switch (_mv_1894.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type lst = _mv_1894.data.lst;
                        {
                            __auto_type items = lst.items;
                            __auto_type len = ((int64_t)((items).len));
                            for (int64_t i = 0; i < len; i++) {
                                __auto_type _mv_1895 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1895.has_value) {
                                    __auto_type param = _mv_1895.value;
                                    __auto_type _mv_1896 = (*param);
                                    switch (_mv_1896.tag) {
                                        case types_SExpr_lst:
                                        {
                                            __auto_type param_lst = _mv_1896.data.lst;
                                            {
                                                __auto_type param_items = param_lst.items;
                                                if (((int64_t)((param_items).len)) >= 2) {
                                                    __auto_type _mv_1897 = ({ __auto_type _lst = param_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_1897.has_value) {
                                                        __auto_type name_expr = _mv_1897.value;
                                                        __auto_type _mv_1898 = (*name_expr);
                                                        switch (_mv_1898.tag) {
                                                            case types_SExpr_sym:
                                                            {
                                                                __auto_type name_sym = _mv_1898.data.sym;
                                                                {
                                                                    __auto_type param_name = name_sym.name;
                                                                    __auto_type _mv_1899 = ({ __auto_type _lst = param_items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                    if (_mv_1899.has_value) {
                                                                        __auto_type type_expr = _mv_1899.value;
                                                                        __auto_type _mv_1900 = (*type_expr);
                                                                        switch (_mv_1900.tag) {
                                                                            case types_SExpr_sym:
                                                                            {
                                                                                __auto_type type_sym = _mv_1900.data.sym;
                                                                                {
                                                                                    __auto_type param_type = compiler_resolve_type_string(env, arena, type_sym.name);
                                                                                    env_env_bind_var(env, param_name, param_type);
                                                                                }
                                                                                break;
                                                                            }
                                                                            case types_SExpr_lst:
                                                                            {
                                                                                __auto_type _ = _mv_1900.data.lst;
                                                                                {
                                                                                    __auto_type param_type = infer_resolve_complex_type_expr(env, type_expr);
                                                                                    env_env_bind_var(env, param_name, param_type);
                                                                                }
                                                                                break;
                                                                            }
                                                                            default: {
                                                                                env_env_bind_var(env, param_name, env_env_get_int_type(env));
                                                                                break;
                                                                            }
                                                                        }
                                                                    } else if (!_mv_1899.has_value) {
                                                                    }
                                                                }
                                                                break;
                                                            }
                                                            default: {
                                                                break;
                                                            }
                                                        }
                                                    } else if (!_mv_1897.has_value) {
                                                    }
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_1895.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1893.has_value) {
            }
        }
    } else if (!_mv_1892.is_ok) {
        __auto_type _ = _mv_1892.data.err;
    }
}

uint8_t compiler_types_names_equal(types_ResolvedType* a, types_ResolvedType* b) {
    SLOP_PRE(((a != NULL)), "(!= a nil)");
    SLOP_PRE(((b != NULL)), "(!= b nil)");
    {
        __auto_type a_name = (*a).name;
        __auto_type b_name = (*b).name;
        __auto_type a_kind = (*a).kind;
        __auto_type b_kind = (*b).kind;
        if (string_eq(a_name, b_name)) {
            return 1;
        } else if (string_eq(a_name, SLOP_STR("T")) || string_eq(b_name, SLOP_STR("T"))) {
            return 1;
        } else if (string_eq(a_name, SLOP_STR("Unknown")) || string_eq(b_name, SLOP_STR("Unknown"))) {
            return 1;
        } else if ((a_kind == types_ResolvedTypeKind_rk_option) && (b_kind == types_ResolvedTypeKind_rk_option)) {
            __auto_type _mv_1901 = (*a).inner_type;
            if (_mv_1901.has_value) {
                __auto_type a_inner = _mv_1901.value;
                __auto_type _mv_1902 = (*b).inner_type;
                if (_mv_1902.has_value) {
                    __auto_type b_inner = _mv_1902.value;
                    return compiler_types_names_equal(a_inner, b_inner);
                } else if (!_mv_1902.has_value) {
                    return 1;
                }
                SLOP_UNREACHABLE();
            } else if (!_mv_1901.has_value) {
                return 1;
            }
            SLOP_UNREACHABLE();
        } else if ((a_kind == types_ResolvedTypeKind_rk_result) && (b_kind == types_ResolvedTypeKind_rk_result)) {
            {
                __auto_type ok_match = ({ __auto_type _mv = (*a).inner_type; _mv.has_value ? ({ __auto_type a_inner = _mv.value; ({ __auto_type _mv = (*b).inner_type; _mv.has_value ? ({ __auto_type b_inner = _mv.value; compiler_types_names_equal(a_inner, b_inner); }) : (1); }); }) : (1); });
                __auto_type err_match = ({ __auto_type _mv = (*a).inner_type2; _mv.has_value ? ({ __auto_type a_inner2 = _mv.value; ({ __auto_type _mv = (*b).inner_type2; _mv.has_value ? ({ __auto_type b_inner2 = _mv.value; compiler_types_names_equal(a_inner2, b_inner2); }) : (1); }); }) : (1); });
                return (ok_match && err_match);
            }
        } else if ((a_kind == types_ResolvedTypeKind_rk_ptr) && (b_kind == types_ResolvedTypeKind_rk_ptr)) {
            __auto_type _mv_1903 = (*a).inner_type;
            if (_mv_1903.has_value) {
                __auto_type a_inner = _mv_1903.value;
                __auto_type _mv_1904 = (*b).inner_type;
                if (_mv_1904.has_value) {
                    __auto_type b_inner = _mv_1904.value;
                    return compiler_types_names_equal(a_inner, b_inner);
                } else if (!_mv_1904.has_value) {
                    return 1;
                }
                SLOP_UNREACHABLE();
            } else if (!_mv_1903.has_value) {
                return 1;
            }
            SLOP_UNREACHABLE();
        } else if (a_kind == types_ResolvedTypeKind_rk_range) {
            __auto_type _mv_1905 = (*a).inner_type;
            if (_mv_1905.has_value) {
                __auto_type base = _mv_1905.value;
                return compiler_types_names_equal(base, b);
            } else if (!_mv_1905.has_value) {
                return 0;
            }
            SLOP_UNREACHABLE();
        } else if (b_kind == types_ResolvedTypeKind_rk_range) {
            __auto_type _mv_1906 = (*b).inner_type;
            if (_mv_1906.has_value) {
                __auto_type base = _mv_1906.value;
                return compiler_types_names_equal(a, base);
            } else if (!_mv_1906.has_value) {
                return 0;
            }
            SLOP_UNREACHABLE();
        } else if ((a_kind == types_ResolvedTypeKind_rk_primitive) && (b_kind == types_ResolvedTypeKind_rk_primitive)) {
            {
                __auto_type a_match = ({ __auto_type _mv = (*a).inner_type; _mv.has_value ? ({ __auto_type a_base = _mv.value; compiler_types_names_equal(a_base, b); }) : (0); });
                __auto_type b_match = ({ __auto_type _mv = (*b).inner_type; _mv.has_value ? ({ __auto_type b_base = _mv.value; compiler_types_names_equal(a, b_base); }) : (0); });
                return (a_match || b_match);
            }
        } else if (a_kind == types_ResolvedTypeKind_rk_primitive) {
            __auto_type _mv_1907 = (*a).inner_type;
            if (_mv_1907.has_value) {
                __auto_type a_base = _mv_1907.value;
                return compiler_types_names_equal(a_base, b);
            } else if (!_mv_1907.has_value) {
                return 0;
            }
            SLOP_UNREACHABLE();
        } else if (b_kind == types_ResolvedTypeKind_rk_primitive) {
            __auto_type _mv_1908 = (*b).inner_type;
            if (_mv_1908.has_value) {
                __auto_type b_base = _mv_1908.value;
                return compiler_types_names_equal(a, b_base);
            } else if (!_mv_1908.has_value) {
                return 0;
            }
            SLOP_UNREACHABLE();
        } else {
            return 0;
        }
    }
}

int64_t compiler_check_expr_mode(slop_arena* arena, env_TypeEnv* env, slop_string expr_str, slop_string type_str, slop_string context_file, slop_string params_str) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    if (string_len(context_file) > 0) {
        __auto_type _mv_1909 = file_file_open(context_file, file_FileMode_read);
        if (!_mv_1909.is_ok) {
            __auto_type _ = _mv_1909.data.err;
        } else if (_mv_1909.is_ok) {
            __auto_type f = _mv_1909.data.ok;
            __auto_type _mv_1910 = file_file_read_all(arena, (&f));
            if (!_mv_1910.is_ok) {
                __auto_type _ = _mv_1910.data.err;
                file_file_close((&f));
            } else if (_mv_1910.is_ok) {
                __auto_type source = _mv_1910.data.ok;
                file_file_close((&f));
                __auto_type _mv_1911 = parser_parse(arena, source);
                if (_mv_1911.is_ok) {
                    __auto_type context_ast = _mv_1911.data.ok;
                    collect_collect_module(env, context_ast);
                    resolve_resolve_imports(env, context_ast);
                    env_env_clear_diagnostics(env);
                } else if (!_mv_1911.is_ok) {
                    __auto_type _ = _mv_1911.data.err;
                }
            }
        }
    }
    env_env_push_scope(env);
    if (string_len(params_str) > 0) {
        compiler_parse_and_bind_params(env, arena, params_str);
    }
    {
        __auto_type result = ({ __auto_type _mv = parser_parse(arena, expr_str); int64_t _mr; if (_mv.is_ok) { __auto_type expr_ast = _mv.data.ok; _mr = (((((int64_t)((expr_ast).len)) == 0)) ? ({ compiler_print_str(((uint8_t*)(SLOP_STR("{\"valid\":false,\"diagnostics\":[{\"level\":\"error\",\"line\":1,\"col\":1,\"message\":\"Empty expression\"}]}\n").data))); 1; }) : ({ __auto_type _mv = ({ __auto_type _lst = expr_ast; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type expr = _mv.value; ({ ({ __auto_type inferred_type = infer_infer_expr(env, expr); ({ __auto_type expected_type = compiler_resolve_type_string(env, arena, type_str); __auto_type diagnostics = env_env_get_diagnostics(env); __auto_type num_errors = compiler_count_errors(diagnostics); ({ __auto_type type_match = compiler_types_names_equal(inferred_type, expected_type); __auto_type final_diagnostics = env_env_get_diagnostics(env); __auto_type final_errors = compiler_count_errors(final_diagnostics); __auto_type is_valid = (type_match && (final_errors == 0)); compiler_output_expr_result(arena, is_valid, (*inferred_type).name, type_str, final_diagnostics); ((is_valid) ? 0 : 1); }); }); }); }); }) : (({ compiler_print_str(((uint8_t*)(SLOP_STR("{\"valid\":false,\"diagnostics\":[{\"level\":\"error\",\"line\":1,\"col\":1,\"message\":\"Empty expression\"}]}\n").data))); 1; })); })); } else { __auto_type parse_err = _mv.data.err; _mr = ({ compiler_print_str(((uint8_t*)(SLOP_STR("{\"valid\":false,\"diagnostics\":[{\"level\":\"error\",\"line\":").data))); compiler_print_string(int_to_string(arena, parse_err.line)); compiler_print_str(((uint8_t*)(SLOP_STR(",\"col\":").data))); compiler_print_string(int_to_string(arena, parse_err.col)); compiler_print_str(((uint8_t*)(SLOP_STR(",\"message\":").data))); compiler_print_json_string(arena, parse_err.message); compiler_print_str(((uint8_t*)(SLOP_STR("}]}\n").data))); 1; }); } _mr; });
        env_env_pop_scope(env);
        return result;
    }
}

void compiler_output_expr_result(slop_arena* arena, uint8_t valid, slop_string inferred_type, slop_string expected_type, slop_list_types_Diagnostic diagnostics) {
    compiler_print_str(((uint8_t*)(SLOP_STR("{\"valid\":").data)));
    if (valid) {
        compiler_print_str(((uint8_t*)(SLOP_STR("true").data)));
    } else {
        compiler_print_str(((uint8_t*)(SLOP_STR("false").data)));
    }
    compiler_print_str(((uint8_t*)(SLOP_STR(",\"inferred_type\":").data)));
    compiler_print_json_string(arena, inferred_type);
    compiler_print_str(((uint8_t*)(SLOP_STR(",\"expected_type\":").data)));
    compiler_print_json_string(arena, expected_type);
    compiler_print_str(((uint8_t*)(SLOP_STR(",\"diagnostics\":").data)));
    compiler_output_diagnostics_json(arena, diagnostics);
    compiler_print_str(((uint8_t*)(SLOP_STR("}\n").data)));
}

int64_t compiler_transpile_single_file(env_TypeEnv* env, context_TranspileContext* ctx, slop_arena* arena, uint8_t* filename, uint8_t first) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((filename != NULL)), "(!= filename nil)");
    {
        __auto_type filename_str = strlib_cstring_to_string(filename);
        context_ctx_set_file(ctx, filename_str);
        __auto_type _mv_1912 = file_file_open(filename_str, file_FileMode_read);
        if (!_mv_1912.is_ok) {
            __auto_type e = _mv_1912.data.err;
            printf("%s", "Error: Could not open file: ");
            printf("%.*s\n", (int)(filename_str).len, (filename_str).data);
            return 1;
        } else if (_mv_1912.is_ok) {
            __auto_type f = _mv_1912.data.ok;
            __auto_type _mv_1913 = file_file_read_all(arena, (&f));
            if (!_mv_1913.is_ok) {
                __auto_type e = _mv_1913.data.err;
                file_file_close((&f));
                printf("%s", "Error: Could not read file: ");
                printf("%.*s\n", (int)(filename_str).len, (filename_str).data);
                return 1;
            } else if (_mv_1913.is_ok) {
                __auto_type source = _mv_1913.data.ok;
                file_file_close((&f));
                __auto_type _mv_1914 = parser_parse(arena, source);
                if (_mv_1914.is_ok) {
                    __auto_type ast = _mv_1914.data.ok;
                    {
                        __auto_type mod_name = compiler_extract_module_name(ast);
                        env_env_clear_imports(env);
                        env_env_clear_diagnostics(env);
                        compiler_type_check_with_env(env, ast);
                        context_ctx_reset_for_new_module(ctx, mod_name);
                        transpiler_transpile_file(ctx, ast);
                        if (context_ctx_has_warnings(ctx)) {
                            context_ctx_report_warnings(ctx);
                        }
                        if (context_ctx_has_errors(ctx)) {
                            context_ctx_report_errors(ctx);
                            return 1;
                        }
                        compiler_output_transpile_module_json(arena, ctx, mod_name, first);
                        return 0;
                    }
                } else if (!_mv_1914.is_ok) {
                    __auto_type parse_err = _mv_1914.data.err;
                    printf("%.*s", (int)(filename_str).len, (filename_str).data);
                    printf("%s", ":");
                    printf("%lld", (long long)(parse_err.line));
                    printf("%s", ":");
                    printf("%lld", (long long)(parse_err.col));
                    printf("%s", ": error: ");
                    printf("%.*s\n", (int)(parse_err.message).len, (parse_err.message).data);
                    return 1;
                }
                SLOP_UNREACHABLE();
            }
            SLOP_UNREACHABLE();
        }
        SLOP_UNREACHABLE();
    }
}

void compiler_output_transpile_module_json(slop_arena* arena, context_TranspileContext* ctx, slop_string mod_name, uint8_t first) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (!(first)) {
        putchar(44);
    }
    compiler_print_json_string(arena, mod_name);
    putchar(58);
    putchar(123);
    compiler_print_str(((uint8_t*)(SLOP_STR("\"header\":").data)));
    {
        __auto_type header_lines = context_ctx_get_header(ctx);
        __auto_type header_str = compiler_lines_to_string(arena, header_lines);
        compiler_print_json_string(arena, header_str);
    }
    putchar(44);
    compiler_print_str(((uint8_t*)(SLOP_STR("\"impl\":").data)));
    {
        __auto_type impl_lines = context_ctx_get_output(ctx);
        __auto_type impl_str = compiler_lines_to_string(arena, impl_lines);
        compiler_print_json_string(arena, impl_str);
    }
    putchar(125);
}

slop_string compiler_emit_sexpr_inner(slop_arena* arena, types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_1915 = (*expr);
    switch (_mv_1915.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1915.data.sym;
            return sym.name;
        }
        case types_SExpr_str:
        {
            __auto_type str = _mv_1915.data.str;
            return string_concat(arena, SLOP_STR("\""), string_concat(arena, str.value, SLOP_STR("\"")));
        }
        case types_SExpr_num:
        {
            __auto_type num = _mv_1915.data.num;
            return num.raw;
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1915.data.lst;
            return compiler_emit_typed_list(arena, lst.items);
        }
    }
    SLOP_UNREACHABLE();
}

slop_string compiler_emit_typed_sexpr(slop_arena* arena, types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type type_opt = ctype_get_node_resolved_type(expr);
        __auto_type inner = compiler_emit_sexpr_inner(arena, expr);
        __auto_type _mv_1916 = type_opt;
        if (_mv_1916.has_value) {
            __auto_type rt = _mv_1916.value;
            {
                __auto_type type_str = types_resolved_type_to_slop_string(arena, rt);
                return string_concat(arena, SLOP_STR("(typed "), string_concat(arena, type_str, string_concat(arena, SLOP_STR(" "), string_concat(arena, inner, SLOP_STR(")")))));
            }
        } else if (!_mv_1916.has_value) {
            return inner;
        }
        SLOP_UNREACHABLE();
    }
}

slop_string compiler_emit_typed_list(slop_arena* arena, slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type result = SLOP_STR("(");
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1917 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1917.has_value) {
                __auto_type item = _mv_1917.value;
                {
                    __auto_type child_str = compiler_emit_typed_sexpr(arena, item);
                    if (i > 0) {
                        result = string_concat(arena, result, string_concat(arena, SLOP_STR(" "), child_str));
                    } else {
                        result = string_concat(arena, result, child_str);
                    }
                }
            } else if (!_mv_1917.has_value) {
            }
            i = (i + 1);
        }
        return string_concat(arena, result, SLOP_STR(")"));
    }
}

slop_string compiler_emit_typed_toplevel(slop_arena* arena, types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    if (parser_is_form(expr, SLOP_STR("fn"))) {
        return compiler_emit_typed_sexpr(arena, expr);
    } else if (parser_is_form(expr, SLOP_STR("module"))) {
        return compiler_emit_typed_module(arena, expr);
    } else {
        return compiler_emit_typed_sexpr(arena, expr);
    }
}

slop_string compiler_emit_typed_module(slop_arena* arena, types_SExpr* module_form) {
    SLOP_PRE(((module_form != NULL)), "(!= module-form nil)");
    if (parser_sexpr_is_list(module_form)) {
        {
            __auto_type len = parser_sexpr_list_len(module_form);
            __auto_type result = SLOP_STR("(");
            int64_t i = 0;
            while (i < len) {
                __auto_type _mv_1918 = parser_sexpr_list_get(module_form, i);
                if (_mv_1918.has_value) {
                    __auto_type item = _mv_1918.value;
                    {
                        __auto_type child_str = ((parser_is_form(item, SLOP_STR("fn"))) ? compiler_emit_typed_sexpr(arena, item) : compiler_emit_typed_sexpr(arena, item));
                        if (i > 0) {
                            result = string_concat(arena, result, string_concat(arena, SLOP_STR(" "), child_str));
                        } else {
                            result = string_concat(arena, result, child_str);
                        }
                    }
                } else if (!_mv_1918.has_value) {
                }
                i = (i + 1);
            }
            return string_concat(arena, result, SLOP_STR(")"));
        }
    } else {
        return compiler_emit_typed_sexpr(arena, module_form);
    }
}

slop_string compiler_emit_typed_ast(slop_arena* arena, slop_list_types_SExpr_ptr ast) {
    {
        __auto_type len = ((int64_t)((ast).len));
        __auto_type result = SLOP_STR("");
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1919 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1919.has_value) {
                __auto_type expr = _mv_1919.value;
                {
                    __auto_type form_str = compiler_emit_typed_toplevel(arena, expr);
                    if (i > 0) {
                        result = string_concat(arena, result, string_concat(arena, SLOP_STR("\n"), form_str));
                    } else {
                        result = form_str;
                    }
                }
            } else if (!_mv_1919.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

int64_t compiler_typed_ast_single_file(env_TypeEnv* env, slop_arena* arena, uint8_t* filename, compiler_OutputFormat format, uint8_t first) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((filename != NULL)), "(!= filename nil)");
    {
        __auto_type filename_str = strlib_cstring_to_string(filename);
        __auto_type _mv_1920 = file_file_open(filename_str, file_FileMode_read);
        if (!_mv_1920.is_ok) {
            __auto_type e = _mv_1920.data.err;
            printf("%s", "Error: Could not open file: ");
            printf("%.*s\n", (int)(filename_str).len, (filename_str).data);
            return 1;
        } else if (_mv_1920.is_ok) {
            __auto_type f = _mv_1920.data.ok;
            __auto_type _mv_1921 = file_file_read_all(arena, (&f));
            if (!_mv_1921.is_ok) {
                __auto_type e = _mv_1921.data.err;
                file_file_close((&f));
                printf("%s", "Error: Could not read file: ");
                printf("%.*s\n", (int)(filename_str).len, (filename_str).data);
                return 1;
            } else if (_mv_1921.is_ok) {
                __auto_type source = _mv_1921.data.ok;
                file_file_close((&f));
                __auto_type _mv_1922 = parser_parse(arena, source);
                if (_mv_1922.is_ok) {
                    __auto_type ast = _mv_1922.data.ok;
                    {
                        __auto_type mod_name = compiler_extract_module_name(ast);
                        env_env_clear_imports(env);
                        env_env_clear_diagnostics(env);
                        compiler_type_check_with_env(env, ast);
                        {
                            __auto_type typed_str = compiler_emit_typed_ast(arena, ast);
                            if (format == compiler_OutputFormat_fmt_json) {
                                if (!(first)) {
                                    putchar(44);
                                }
                                compiler_print_json_string(arena, mod_name);
                                putchar(58);
                                putchar(123);
                                compiler_print_str(((uint8_t*)(SLOP_STR("\"typed-ast\":").data)));
                                compiler_print_json_string(arena, typed_str);
                                putchar(125);
                                return 0;
                            } else {
                                if (!(first)) {
                                    putchar(10);
                                }
                                compiler_print_string(typed_str);
                                return 0;
                            }
                        }
                    }
                } else if (!_mv_1922.is_ok) {
                    __auto_type parse_err = _mv_1922.data.err;
                    printf("%.*s", (int)(filename_str).len, (filename_str).data);
                    printf("%s", ":");
                    printf("%lld", (long long)(parse_err.line));
                    printf("%s", ":");
                    printf("%lld", (long long)(parse_err.col));
                    printf("%s", ": error: ");
                    printf("%.*s\n", (int)(parse_err.message).len, (parse_err.message).data);
                    return 1;
                }
                SLOP_UNREACHABLE();
            }
            SLOP_UNREACHABLE();
        }
        SLOP_UNREACHABLE();
    }
}

int main(int argc, char** _c_argv) {
    uint8_t** argv = (uint8_t**)_c_argv;
    if (argc >= 2) {
        if (string_eq(compiler_argv_to_string(argv, 1), SLOP_STR("--version"))) {
            printf("%s\n", "slop-compiler 0.2.1");
            return 0;
        }
    }
    if (argc < 2) {
        printf("%s\n", "Usage: slop-compiler <command> [options] <files...>");
        printf("%s\n", "");
        printf("%s\n", "Commands:");
        printf("%s\n", "  check [--json] [--expr EXPR --type TYPE] <files...>");
        printf("%s\n", "  typed-ast [--json] <files...>");
        printf("%s\n", "  transpile <files...>");
        return 1;
    } else {
        {
            __auto_type cmd = compiler_argv_to_string(argv, 1);
            if (string_eq(cmd, SLOP_STR("check"))) {
                if (argc < 3) {
                    printf("%s\n", "Usage: slop-compiler check [--json] <file.slop> [file2.slop ...]");
                    printf("%s\n", "       slop-compiler check --expr EXPR --type TYPE [--context FILE] [--params PARAMS]");
                    return 1;
                } else {
                    {
                        #ifdef SLOP_DEBUG
                        SLOP_PRE((4194304) > 0, "with-arena size must be positive");
                        #endif
                        slop_arena _arena = slop_arena_new(4194304);
                        #ifdef SLOP_DEBUG
                        SLOP_PRE(_arena.base != NULL, "arena allocation failed");
                        #endif
                        slop_arena* arena = &_arena;
                        if (string_eq(compiler_argv_to_string(argv, 2), SLOP_STR("--expr"))) {
                            {
                                __auto_type env = env_env_new(arena);
                                slop_string expr_str = SLOP_STR("");
                                slop_string type_str = SLOP_STR("Int");
                                slop_string context_file = SLOP_STR("");
                                slop_string params_str = SLOP_STR("");
                                int64_t i = 3;
                                if (i < argc) {
                                    expr_str = compiler_argv_to_string(argv, i);
                                    i = (i + 1);
                                }
                                while (i < argc) {
                                    {
                                        __auto_type arg = compiler_argv_to_string(argv, i);
                                        if (string_eq(arg, SLOP_STR("--type"))) {
                                            if ((i + 1) < argc) {
                                                type_str = compiler_argv_to_string(argv, (i + 1));
                                                i = (i + 2);
                                            }
                                        } else if (string_eq(arg, SLOP_STR("--context"))) {
                                            if ((i + 1) < argc) {
                                                context_file = compiler_argv_to_string(argv, (i + 1));
                                                i = (i + 2);
                                            }
                                        } else if (string_eq(arg, SLOP_STR("--params"))) {
                                            if ((i + 1) < argc) {
                                                params_str = compiler_argv_to_string(argv, (i + 1));
                                                i = (i + 2);
                                            }
                                        } else {
                                            i = (i + 1);
                                        }
                                    }
                                }
                                if (string_len(expr_str) == 0) {
                                    printf("%s\n", "Error: --expr requires an expression argument");
                                    return 1;
                                } else {
                                    return compiler_check_expr_mode(arena, env, expr_str, type_str, context_file, params_str);
                                }
                            }
                        } else {
                            {
                                __auto_type env = env_env_new(arena);
                                int64_t total_errors = 0;
                                __auto_type format = compiler_OutputFormat_fmt_text;
                                int64_t file_start = 2;
                                if (string_eq(compiler_argv_to_string(argv, 2), SLOP_STR("--json"))) {
                                    format = compiler_OutputFormat_fmt_json;
                                    file_start = 3;
                                }
                                if (format == compiler_OutputFormat_fmt_json) {
                                    putchar(123);
                                }
                                {
                                    int64_t i = file_start;
                                    uint8_t first = 1;
                                    while (i < argc) {
                                        {
                                            __auto_type filename = argv[i];
                                            __auto_type errors = compiler_check_single_file(env, arena, filename, format, first);
                                            total_errors = (total_errors + errors);
                                            first = 0;
                                        }
                                        i = (i + 1);
                                    }
                                }
                                if (format == compiler_OutputFormat_fmt_json) {
                                    putchar(125);
                                    putchar(10);
                                }
                                if (total_errors > 0) {
                                    return 1;
                                } else {
                                    return 0;
                                }
                            }
                        }
                        slop_arena_free(arena);
                    }
                }
            } else if (string_eq(cmd, SLOP_STR("transpile"))) {
                if (argc < 3) {
                    printf("%s\n", "Usage: slop-compiler transpile <file.slop> [file2.slop ...]");
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
                            __auto_type env = env_env_new(arena);
                            __auto_type ctx = context_context_new(arena);
                            context_ctx_set_prefixing(ctx, 1);
                            putchar(123);
                            {
                                int64_t i = 2;
                                uint8_t first = 1;
                                uint8_t had_error = 0;
                                while (i < argc) {
                                    {
                                        __auto_type filename = argv[i];
                                        __auto_type result = compiler_transpile_single_file(env, ctx, arena, filename, first);
                                        if (result != 0) {
                                            had_error = 1;
                                        }
                                        first = 0;
                                    }
                                    i = (i + 1);
                                }
                                putchar(125);
                                putchar(10);
                                if (had_error) {
                                    return 1;
                                } else {
                                    return 0;
                                }
                            }
                        }
                        slop_arena_free(arena);
                    }
                }
            } else if (string_eq(cmd, SLOP_STR("typed-ast"))) {
                if (argc < 3) {
                    printf("%s\n", "Usage: slop-compiler typed-ast [--json] <file.slop> [file2.slop ...]");
                    return 1;
                } else {
                    {
                        #ifdef SLOP_DEBUG
                        SLOP_PRE((4194304) > 0, "with-arena size must be positive");
                        #endif
                        slop_arena _arena = slop_arena_new(4194304);
                        #ifdef SLOP_DEBUG
                        SLOP_PRE(_arena.base != NULL, "arena allocation failed");
                        #endif
                        slop_arena* arena = &_arena;
                        {
                            __auto_type env = env_env_new(arena);
                            __auto_type format = compiler_OutputFormat_fmt_text;
                            int64_t file_start = 2;
                            int64_t total_errors = 0;
                            if (string_eq(compiler_argv_to_string(argv, 2), SLOP_STR("--json"))) {
                                format = compiler_OutputFormat_fmt_json;
                                file_start = 3;
                            }
                            if (format == compiler_OutputFormat_fmt_json) {
                                putchar(123);
                            }
                            {
                                int64_t i = file_start;
                                uint8_t first = 1;
                                while (i < argc) {
                                    {
                                        __auto_type filename = argv[i];
                                        __auto_type errors = compiler_typed_ast_single_file(env, arena, filename, format, first);
                                        total_errors = (total_errors + errors);
                                        first = 0;
                                    }
                                    i = (i + 1);
                                }
                            }
                            if (format == compiler_OutputFormat_fmt_json) {
                                putchar(125);
                                putchar(10);
                            }
                            if (total_errors > 0) {
                                return 1;
                            } else {
                                return 0;
                            }
                        }
                        slop_arena_free(arena);
                    }
                }
            } else {
                printf("%s", "Unknown command: ");
                printf("%.*s\n", (int)(cmd).len, (cmd).data);
                printf("%s\n", "Usage: slop-compiler <check|typed-ast|transpile> [options] <files...>");
                return 1;
            }
        }
    }
}

