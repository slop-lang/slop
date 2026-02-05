#include "../runtime/slop_runtime.h"
#include "slop_checker.h"

slop_result_env_TypeEnv_ptr_types_TypeError checker_type_check(slop_arena* arena, slop_list_types_SExpr_ptr ast);
void checker_type_check_with_env(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void checker_check_all_functions(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
uint8_t checker_is_annotation_form(types_SExpr* item);
uint8_t checker_is_valid_toplevel_form(types_SExpr* item);
slop_string checker_get_form_name(types_SExpr* item);
void checker_check_module_functions(env_TypeEnv* env, types_SExpr* module_form);
void checker_print_str(uint8_t* s);
void checker_print_string(slop_string s);
void checker_print_json_string(slop_arena* arena, slop_string s);
slop_string checker_extract_module_name(slop_list_types_SExpr_ptr exprs);
void checker_print_diagnostic(slop_arena* arena, slop_string filename, types_Diagnostic diag);
void checker_output_diagnostics_text(slop_arena* arena, slop_string filename, slop_list_types_Diagnostic diagnostics);
void checker_output_diagnostics_json(slop_arena* arena, slop_list_types_Diagnostic diagnostics);
void checker_output_single_diagnostic_json(slop_arena* arena, types_Diagnostic diag);
void checker_output_module_json(slop_arena* arena, slop_string mod_name, slop_list_types_Diagnostic diagnostics, uint8_t first);
int64_t checker_check_single_file(env_TypeEnv* env, slop_arena* arena, uint8_t* filename, checker_OutputFormat format, uint8_t first);
int64_t checker_count_errors(slop_list_types_Diagnostic diagnostics);
slop_string checker_argv_to_string(uint8_t** argv, int64_t index);
types_ResolvedType* checker_resolve_type_string(env_TypeEnv* env, slop_arena* arena, slop_string type_str);
void checker_parse_and_bind_params(env_TypeEnv* env, slop_arena* arena, slop_string params_str);
uint8_t checker_types_names_equal(types_ResolvedType* a, types_ResolvedType* b);
int64_t checker_check_expr_mode(slop_arena* arena, env_TypeEnv* env, slop_string expr_str, slop_string type_str, slop_string context_file, slop_string params_str);
void checker_output_expr_result(slop_arena* arena, uint8_t valid, slop_string inferred_type, slop_string expected_type, slop_list_types_Diagnostic diagnostics);
int checker_main(int64_t argc, uint8_t** argv);

slop_result_env_TypeEnv_ptr_types_TypeError checker_type_check(slop_arena* arena, slop_list_types_SExpr_ptr ast) {
    SLOP_PRE(((((int64_t)((ast).len)) > 0)), "(> (list-len ast) 0)");
    {
        __auto_type env = env_env_new(arena);
        collect_collect_module(env, ast);
        resolve_resolve_imports(env, ast);
        checker_check_all_functions(env, ast);
        return ((slop_result_env_TypeEnv_ptr_types_TypeError){ .is_ok = true, .data.ok = env });
    }
}

void checker_type_check_with_env(env_TypeEnv* env, slop_list_types_SExpr_ptr ast) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((((int64_t)((ast).len)) > 0)), "(> (list-len ast) 0)");
    collect_collect_module(env, ast);
    resolve_resolve_imports(env, ast);
    checker_check_all_functions(env, ast);
}

void checker_check_all_functions(env_TypeEnv* env, slop_list_types_SExpr_ptr ast) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type len = ((int64_t)((ast).len));
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_338 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_338.has_value) {
                __auto_type expr = _mv_338.value;
                if (parser_is_form(expr, SLOP_STR("fn"))) {
                    {
                        __auto_type _ = infer_infer_fn_body(env, expr);
                    }
                } else if (parser_is_form(expr, SLOP_STR("module"))) {
                    checker_check_module_functions(env, expr);
                } else {
                }
            } else if (!_mv_338.has_value) {
            }
        }
    }
}

uint8_t checker_is_annotation_form(types_SExpr* item) {
    if (parser_sexpr_is_list(item)) {
        __auto_type _mv_339 = parser_sexpr_list_get(item, 0);
        if (_mv_339.has_value) {
            __auto_type head = _mv_339.value;
            return ((uint8_t)(({ __auto_type name = parser_sexpr_get_symbol_name(head); (((name.len > 0)) ? (name.data[0] == 64) : 0); })));
        } else if (!_mv_339.has_value) {
            return 0;
        }
    } else {
        return 0;
    }
}

uint8_t checker_is_valid_toplevel_form(types_SExpr* item) {
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
    } else if (checker_is_annotation_form(item)) {
        return 1;
    } else {
        return 0;
    }
}

slop_string checker_get_form_name(types_SExpr* item) {
    if (parser_sexpr_is_list(item)) {
        __auto_type _mv_340 = parser_sexpr_list_get(item, 0);
        if (_mv_340.has_value) {
            __auto_type head = _mv_340.value;
            return parser_sexpr_get_symbol_name(head);
        } else if (!_mv_340.has_value) {
            return SLOP_STR("<empty>");
        }
    } else {
        return SLOP_STR("<non-list>");
    }
}

void checker_check_module_functions(env_TypeEnv* env, types_SExpr* module_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((module_form != NULL)), "(!= module-form nil)");
    if (parser_sexpr_is_list(module_form)) {
        __auto_type _mv_341 = parser_sexpr_list_get(module_form, 1);
        if (_mv_341.has_value) {
            __auto_type name_expr = _mv_341.value;
            {
                __auto_type mod_name = parser_sexpr_get_symbol_name(name_expr);
                if (!(string_eq(mod_name, SLOP_STR("")))) {
                    env_env_set_module(env, (slop_option_string){.has_value = 1, .value = mod_name});
                }
            }
        } else if (!_mv_341.has_value) {
        }
        {
            __auto_type len = parser_sexpr_list_len(module_form);
            for (int64_t i = 2; i < len; i++) {
                __auto_type _mv_342 = parser_sexpr_list_get(module_form, i);
                if (_mv_342.has_value) {
                    __auto_type item = _mv_342.value;
                    if (parser_is_form(item, SLOP_STR("fn"))) {
                        {
                            __auto_type _ = infer_infer_fn_body(env, item);
                        }
                    } else if (checker_is_valid_toplevel_form(item)) {
                    } else {
                        {
                            __auto_type arena = env_env_arena(env);
                            __auto_type msg = string_concat(arena, SLOP_STR("Unknown top-level form: "), checker_get_form_name(item));
                            env_env_add_error(env, msg, parser_sexpr_line(item), parser_sexpr_col(item));
                        }
                    }
                } else if (!_mv_342.has_value) {
                }
            }
        }
    }
}

void checker_print_str(uint8_t* s) {
    SLOP_PRE(((s != NULL)), "(!= s nil)");
    {
        int64_t i = 0;
        while ((s[i] != 0)) {
            putchar(((int64_t)(s[i])));
            i = (i + 1);
        }
    }
}

void checker_print_string(slop_string s) {
    {
        __auto_type len = ((int64_t)(s.len));
        __auto_type data = s.data;
        int64_t i = 0;
        while ((i < len)) {
            putchar(((int64_t)(data[i])));
            i = (i + 1);
        }
    }
}

void checker_print_json_string(slop_arena* arena, slop_string s) {
    putchar(34);
    {
        __auto_type len = ((int64_t)(s.len));
        __auto_type data = s.data;
        int64_t i = 0;
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

slop_string checker_extract_module_name(slop_list_types_SExpr_ptr exprs) {
    if ((((int64_t)((exprs).len)) < 1)) {
        return SLOP_STR("unknown");
    } else {
        __auto_type _mv_343 = ({ __auto_type _lst = exprs; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_343.has_value) {
            __auto_type first_expr = _mv_343.value;
            __auto_type _mv_344 = (*first_expr);
            switch (_mv_344.tag) {
                case types_SExpr_lst:
                {
                    __auto_type lst = _mv_344.data.lst;
                    {
                        __auto_type items = lst.items;
                        if ((((int64_t)((items).len)) < 2)) {
                            return SLOP_STR("unknown");
                        } else {
                            __auto_type _mv_345 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_345.has_value) {
                                __auto_type head = _mv_345.value;
                                __auto_type _mv_346 = (*head);
                                switch (_mv_346.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_346.data.sym;
                                        if (string_eq(sym.name, SLOP_STR("module"))) {
                                            __auto_type _mv_347 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_347.has_value) {
                                                __auto_type name_expr = _mv_347.value;
                                                __auto_type _mv_348 = (*name_expr);
                                                switch (_mv_348.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type name_sym = _mv_348.data.sym;
                                                        return name_sym.name;
                                                    }
                                                    default: {
                                                        return SLOP_STR("unknown");
                                                    }
                                                }
                                            } else if (!_mv_347.has_value) {
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
                            } else if (!_mv_345.has_value) {
                                return SLOP_STR("unknown");
                            }
                        }
                    }
                }
                default: {
                    return SLOP_STR("unknown");
                }
            }
        } else if (!_mv_343.has_value) {
            return SLOP_STR("unknown");
        }
    }
}

void checker_print_diagnostic(slop_arena* arena, slop_string filename, types_Diagnostic diag) {
    printf("%.*s", (int)(filename).len, (filename).data);
    printf("%s", ":");
    printf("%lld", (long long)(diag.line));
    printf("%s", ":");
    printf("%lld", (long long)(diag.col));
    printf("%s", ": ");
    __auto_type _mv_349 = diag.level;
    if (_mv_349 == types_DiagnosticLevel_diag_warning) {
        printf("%s", "warning: ");
    } else if (_mv_349 == types_DiagnosticLevel_diag_error) {
        printf("%s", "error: ");
    }
    printf("%.*s\n", (int)(diag.message).len, (diag.message).data);
}

void checker_output_diagnostics_text(slop_arena* arena, slop_string filename, slop_list_types_Diagnostic diagnostics) {
    {
        __auto_type len = ((int64_t)((diagnostics).len));
        int64_t i = 0;
        while ((i < len)) {
            __auto_type _mv_350 = ({ __auto_type _lst = diagnostics; size_t _idx = (size_t)i; slop_option_types_Diagnostic _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_350.has_value) {
                __auto_type diag = _mv_350.value;
                checker_print_diagnostic(arena, filename, diag);
            } else if (!_mv_350.has_value) {
            }
            i = (i + 1);
        }
    }
}

void checker_output_diagnostics_json(slop_arena* arena, slop_list_types_Diagnostic diagnostics) {
    putchar(91);
    {
        __auto_type len = ((int64_t)((diagnostics).len));
        int64_t i = 0;
        while ((i < len)) {
            if ((i > 0)) {
                putchar(44);
            }
            __auto_type _mv_351 = ({ __auto_type _lst = diagnostics; size_t _idx = (size_t)i; slop_option_types_Diagnostic _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_351.has_value) {
                __auto_type diag = _mv_351.value;
                checker_output_single_diagnostic_json(arena, diag);
            } else if (!_mv_351.has_value) {
            }
            i = (i + 1);
        }
    }
    putchar(93);
}

void checker_output_single_diagnostic_json(slop_arena* arena, types_Diagnostic diag) {
    putchar(123);
    checker_print_str(((uint8_t*)(SLOP_STR("\"level\":").data)));
    __auto_type _mv_352 = diag.level;
    if (_mv_352 == types_DiagnosticLevel_diag_warning) {
        checker_print_str(((uint8_t*)(SLOP_STR("\"warning\"").data)));
    } else if (_mv_352 == types_DiagnosticLevel_diag_error) {
        checker_print_str(((uint8_t*)(SLOP_STR("\"error\"").data)));
    }
    putchar(44);
    checker_print_str(((uint8_t*)(SLOP_STR("\"line\":").data)));
    checker_print_string(int_to_string(arena, diag.line));
    putchar(44);
    checker_print_str(((uint8_t*)(SLOP_STR("\"col\":").data)));
    checker_print_string(int_to_string(arena, diag.col));
    putchar(44);
    checker_print_str(((uint8_t*)(SLOP_STR("\"message\":").data)));
    checker_print_json_string(arena, diag.message);
    putchar(125);
}

void checker_output_module_json(slop_arena* arena, slop_string mod_name, slop_list_types_Diagnostic diagnostics, uint8_t first) {
    if (!(first)) {
        putchar(44);
    }
    checker_print_json_string(arena, mod_name);
    putchar(58);
    putchar(123);
    checker_print_str(((uint8_t*)(SLOP_STR("\"diagnostics\":").data)));
    checker_output_diagnostics_json(arena, diagnostics);
    putchar(125);
}

int64_t checker_check_single_file(env_TypeEnv* env, slop_arena* arena, uint8_t* filename, checker_OutputFormat format, uint8_t first) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((filename != NULL)), "(!= filename nil)");
    {
        __auto_type filename_str = strlib_cstring_to_string(filename);
        __auto_type _mv_353 = file_file_open(filename_str, file_FileMode_read);
        if (!_mv_353.is_ok) {
            __auto_type e = _mv_353.data.err;
            printf("%s", "Error: Could not open file: ");
            printf("%.*s\n", (int)(filename_str).len, (filename_str).data);
            return 1;
        } else if (_mv_353.is_ok) {
            __auto_type f = _mv_353.data.ok;
            __auto_type _mv_354 = file_file_read_all(arena, (&f));
            if (!_mv_354.is_ok) {
                __auto_type e = _mv_354.data.err;
                file_file_close((&f));
                printf("%s", "Error: Could not read file: ");
                printf("%.*s\n", (int)(filename_str).len, (filename_str).data);
                return 1;
            } else if (_mv_354.is_ok) {
                __auto_type source = _mv_354.data.ok;
                file_file_close((&f));
                __auto_type _mv_355 = parser_parse(arena, source);
                if (_mv_355.is_ok) {
                    __auto_type ast = _mv_355.data.ok;
                    {
                        __auto_type mod_name = checker_extract_module_name(ast);
                        env_env_clear_imports(env);
                        env_env_clear_diagnostics(env);
                        checker_type_check_with_env(env, ast);
                        {
                            __auto_type diagnostics = env_env_get_diagnostics(env);
                            if ((format == checker_OutputFormat_fmt_json)) {
                                checker_output_module_json(arena, mod_name, diagnostics, first);
                            }
                            if ((format == checker_OutputFormat_fmt_text)) {
                                checker_output_diagnostics_text(arena, filename_str, diagnostics);
                            }
                            return checker_count_errors(diagnostics);
                        }
                    }
                } else if (!_mv_355.is_ok) {
                    __auto_type parse_err = _mv_355.data.err;
                    printf("%.*s", (int)(filename_str).len, (filename_str).data);
                    printf("%s", ":");
                    printf("%lld", (long long)(parse_err.line));
                    printf("%s", ":");
                    printf("%lld", (long long)(parse_err.col));
                    printf("%s", ": error: ");
                    printf("%.*s\n", (int)(parse_err.message).len, (parse_err.message).data);
                    return 1;
                }
            }
        }
    }
}

int64_t checker_count_errors(slop_list_types_Diagnostic diagnostics) {
    {
        __auto_type len = ((int64_t)((diagnostics).len));
        int64_t errors = 0;
        int64_t i = 0;
        while ((i < len)) {
            __auto_type _mv_356 = ({ __auto_type _lst = diagnostics; size_t _idx = (size_t)i; slop_option_types_Diagnostic _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_356.has_value) {
                __auto_type diag = _mv_356.value;
                __auto_type _mv_357 = diag.level;
                if (_mv_357 == types_DiagnosticLevel_diag_error) {
                    errors = (errors + 1);
                } else if (_mv_357 == types_DiagnosticLevel_diag_warning) {
                }
            } else if (!_mv_356.has_value) {
            }
            i = (i + 1);
        }
        return errors;
    }
}

slop_string checker_argv_to_string(uint8_t** argv, int64_t index) {
    {
        __auto_type ptr = argv[index];
        return (slop_string){.len = strlen(ptr), .data = ptr};
    }
}

types_ResolvedType* checker_resolve_type_string(env_TypeEnv* env, slop_arena* arena, slop_string type_str) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_358 = parser_parse(arena, type_str);
    if (_mv_358.is_ok) {
        __auto_type type_ast = _mv_358.data.ok;
        if ((((int64_t)((type_ast).len)) == 0)) {
            return env_env_get_int_type(env);
        } else {
            __auto_type _mv_359 = ({ __auto_type _lst = type_ast; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_359.has_value) {
                __auto_type type_expr = _mv_359.value;
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
            } else if (!_mv_359.has_value) {
                return env_env_get_int_type(env);
            }
        }
    } else if (!_mv_358.is_ok) {
        __auto_type _ = _mv_358.data.err;
        return env_env_get_int_type(env);
    }
}

void checker_parse_and_bind_params(env_TypeEnv* env, slop_arena* arena, slop_string params_str) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_360 = parser_parse(arena, params_str);
    if (_mv_360.is_ok) {
        __auto_type params_ast = _mv_360.data.ok;
        if ((((int64_t)((params_ast).len)) > 0)) {
            __auto_type _mv_361 = ({ __auto_type _lst = params_ast; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_361.has_value) {
                __auto_type params_list = _mv_361.value;
                __auto_type _mv_362 = (*params_list);
                switch (_mv_362.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type lst = _mv_362.data.lst;
                        {
                            __auto_type items = lst.items;
                            __auto_type len = ((int64_t)((items).len));
                            ({ for (int64_t i = 0; i < len; i++) { ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type param = _mv.value; ({ __auto_type _mv = (*param); switch (_mv.tag) { case types_SExpr_lst: { __auto_type param_lst = _mv.data.lst; ({ __auto_type param_items = param_lst.items; (((((int64_t)((param_items).len)) >= 2)) ? ({ ({ __auto_type _mv = ({ __auto_type _lst = param_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type name_expr = _mv.value; ({ __auto_type _mv = (*name_expr); switch (_mv.tag) { case types_SExpr_sym: { __auto_type name_sym = _mv.data.sym; ({ __auto_type param_name = name_sym.name; ({ __auto_type _mv = ({ __auto_type _lst = param_items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type type_expr = _mv.value; ({ __auto_type _mv = (*type_expr); switch (_mv.tag) { case types_SExpr_sym: { __auto_type type_sym = _mv.data.sym; ({ __auto_type param_type = checker_resolve_type_string(env, arena, type_sym.name); env_env_bind_var(env, param_name, param_type); }); break; } case types_SExpr_lst: { __auto_type _ = _mv.data.lst; ({ __auto_type param_type = infer_resolve_complex_type_expr(env, type_expr); env_env_bind_var(env, param_name, param_type); }); break; } default: { env_env_bind_var(env, param_name, env_env_get_int_type(env)); break; }  } (void)0; }); } else { ({ (void)0; }); } (void)0; }); }); break; } default: { ({ (void)0; }); break; }  } (void)0; }); } else { ({ (void)0; }); } (void)0; }); 0; }) : ({ (void)0; })); }); break; } default: { ({ (void)0; }); break; }  } (void)0; }); } else { ({ (void)0; }); } (void)0; }); } 0; });
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_361.has_value) {
            }
        }
    } else if (!_mv_360.is_ok) {
        __auto_type _ = _mv_360.data.err;
    }
}

uint8_t checker_types_names_equal(types_ResolvedType* a, types_ResolvedType* b) {
    SLOP_PRE(((a != NULL)), "(!= a nil)");
    SLOP_PRE(((b != NULL)), "(!= b nil)");
    {
        __auto_type a_name = (*a).name;
        __auto_type b_name = (*b).name;
        __auto_type a_kind = (*a).kind;
        __auto_type b_kind = (*b).kind;
        if (string_eq(a_name, b_name)) {
            return 1;
        } else if ((string_eq(a_name, SLOP_STR("T")) || string_eq(b_name, SLOP_STR("T")))) {
            return 1;
        } else if ((string_eq(a_name, SLOP_STR("Unknown")) || string_eq(b_name, SLOP_STR("Unknown")))) {
            return 1;
        } else if (((a_kind == types_ResolvedTypeKind_rk_option) && (b_kind == types_ResolvedTypeKind_rk_option))) {
            __auto_type _mv_363 = (*a).inner_type;
            if (_mv_363.has_value) {
                __auto_type a_inner = _mv_363.value;
                __auto_type _mv_364 = (*b).inner_type;
                if (_mv_364.has_value) {
                    __auto_type b_inner = _mv_364.value;
                    return checker_types_names_equal(a_inner, b_inner);
                } else if (!_mv_364.has_value) {
                    return 1;
                }
            } else if (!_mv_363.has_value) {
                return 1;
            }
        } else if (((a_kind == types_ResolvedTypeKind_rk_result) && (b_kind == types_ResolvedTypeKind_rk_result))) {
            {
                __auto_type ok_match = ({ __auto_type _mv = (*a).inner_type; _mv.has_value ? ({ __auto_type a_inner = _mv.value; ({ __auto_type _mv = (*b).inner_type; _mv.has_value ? ({ __auto_type b_inner = _mv.value; checker_types_names_equal(a_inner, b_inner); }) : (1); }); }) : (1); });
                __auto_type err_match = ({ __auto_type _mv = (*a).inner_type2; _mv.has_value ? ({ __auto_type a_inner2 = _mv.value; ({ __auto_type _mv = (*b).inner_type2; _mv.has_value ? ({ __auto_type b_inner2 = _mv.value; checker_types_names_equal(a_inner2, b_inner2); }) : (1); }); }) : (1); });
                return (ok_match && err_match);
            }
        } else if (((a_kind == types_ResolvedTypeKind_rk_ptr) && (b_kind == types_ResolvedTypeKind_rk_ptr))) {
            __auto_type _mv_365 = (*a).inner_type;
            if (_mv_365.has_value) {
                __auto_type a_inner = _mv_365.value;
                __auto_type _mv_366 = (*b).inner_type;
                if (_mv_366.has_value) {
                    __auto_type b_inner = _mv_366.value;
                    return checker_types_names_equal(a_inner, b_inner);
                } else if (!_mv_366.has_value) {
                    return 1;
                }
            } else if (!_mv_365.has_value) {
                return 1;
            }
        } else if ((a_kind == types_ResolvedTypeKind_rk_range)) {
            __auto_type _mv_367 = (*a).inner_type;
            if (_mv_367.has_value) {
                __auto_type base = _mv_367.value;
                return checker_types_names_equal(base, b);
            } else if (!_mv_367.has_value) {
                return 0;
            }
        } else if ((b_kind == types_ResolvedTypeKind_rk_range)) {
            __auto_type _mv_368 = (*b).inner_type;
            if (_mv_368.has_value) {
                __auto_type base = _mv_368.value;
                return checker_types_names_equal(a, base);
            } else if (!_mv_368.has_value) {
                return 0;
            }
        } else if (((a_kind == types_ResolvedTypeKind_rk_primitive) && (b_kind == types_ResolvedTypeKind_rk_primitive))) {
            {
                __auto_type a_match = ({ __auto_type _mv = (*a).inner_type; _mv.has_value ? ({ __auto_type a_base = _mv.value; checker_types_names_equal(a_base, b); }) : (0); });
                __auto_type b_match = ({ __auto_type _mv = (*b).inner_type; _mv.has_value ? ({ __auto_type b_base = _mv.value; checker_types_names_equal(a, b_base); }) : (0); });
                return (a_match || b_match);
            }
        } else if ((a_kind == types_ResolvedTypeKind_rk_primitive)) {
            __auto_type _mv_369 = (*a).inner_type;
            if (_mv_369.has_value) {
                __auto_type a_base = _mv_369.value;
                return checker_types_names_equal(a_base, b);
            } else if (!_mv_369.has_value) {
                return 0;
            }
        } else if ((b_kind == types_ResolvedTypeKind_rk_primitive)) {
            __auto_type _mv_370 = (*b).inner_type;
            if (_mv_370.has_value) {
                __auto_type b_base = _mv_370.value;
                return checker_types_names_equal(a, b_base);
            } else if (!_mv_370.has_value) {
                return 0;
            }
        } else {
            return 0;
        }
    }
}

int64_t checker_check_expr_mode(slop_arena* arena, env_TypeEnv* env, slop_string expr_str, slop_string type_str, slop_string context_file, slop_string params_str) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    if ((string_len(context_file) > 0)) {
        __auto_type _mv_371 = file_file_open(context_file, file_FileMode_read);
        if (!_mv_371.is_ok) {
            __auto_type _ = _mv_371.data.err;
        } else if (_mv_371.is_ok) {
            __auto_type f = _mv_371.data.ok;
            __auto_type _mv_372 = file_file_read_all(arena, (&f));
            if (!_mv_372.is_ok) {
                __auto_type _ = _mv_372.data.err;
                file_file_close((&f));
            } else if (_mv_372.is_ok) {
                __auto_type source = _mv_372.data.ok;
                file_file_close((&f));
                __auto_type _mv_373 = parser_parse(arena, source);
                if (_mv_373.is_ok) {
                    __auto_type context_ast = _mv_373.data.ok;
                    collect_collect_module(env, context_ast);
                    resolve_resolve_imports(env, context_ast);
                } else if (!_mv_373.is_ok) {
                    __auto_type _ = _mv_373.data.err;
                }
            }
        }
    }
    env_env_push_scope(env);
    if ((string_len(params_str) > 0)) {
        checker_parse_and_bind_params(env, arena, params_str);
    }
    {
        __auto_type result = ({ __auto_type _mv = parser_parse(arena, expr_str); int64_t _mr; if (_mv.is_ok) { __auto_type expr_ast = _mv.data.ok; _mr = (((((int64_t)((expr_ast).len)) == 0)) ? ({ checker_print_str(((uint8_t*)(SLOP_STR("{\"valid\":false,\"diagnostics\":[{\"level\":\"error\",\"line\":1,\"col\":1,\"message\":\"Empty expression\"}]}\n").data))); 1; }) : ({ __auto_type _mv = ({ __auto_type _lst = expr_ast; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type expr = _mv.value; ({ ({ __auto_type inferred_type = infer_infer_expr(env, expr); ({ __auto_type expected_type = checker_resolve_type_string(env, arena, type_str); __auto_type diagnostics = env_env_get_diagnostics(env); __auto_type num_errors = checker_count_errors(diagnostics); ({ __auto_type type_match = checker_types_names_equal(inferred_type, expected_type); __auto_type final_diagnostics = env_env_get_diagnostics(env); __auto_type final_errors = checker_count_errors(final_diagnostics); __auto_type is_valid = (type_match && (final_errors == 0)); checker_output_expr_result(arena, is_valid, (*inferred_type).name, type_str, final_diagnostics); ((is_valid) ? 0 : 1); }); }); }); }); }) : (({ checker_print_str(((uint8_t*)(SLOP_STR("{\"valid\":false,\"diagnostics\":[{\"level\":\"error\",\"line\":1,\"col\":1,\"message\":\"Empty expression\"}]}\n").data))); 1; })); })); } else { __auto_type parse_err = _mv.data.err; _mr = ({ checker_print_str(((uint8_t*)(SLOP_STR("{\"valid\":false,\"diagnostics\":[{\"level\":\"error\",\"line\":").data))); checker_print_string(int_to_string(arena, parse_err.line)); checker_print_str(((uint8_t*)(SLOP_STR(",\"col\":").data))); checker_print_string(int_to_string(arena, parse_err.col)); checker_print_str(((uint8_t*)(SLOP_STR(",\"message\":").data))); checker_print_json_string(arena, parse_err.message); checker_print_str(((uint8_t*)(SLOP_STR("}]}\n").data))); 1; }); } _mr; });
        env_env_pop_scope(env);
        return result;
    }
}

void checker_output_expr_result(slop_arena* arena, uint8_t valid, slop_string inferred_type, slop_string expected_type, slop_list_types_Diagnostic diagnostics) {
    checker_print_str(((uint8_t*)(SLOP_STR("{\"valid\":").data)));
    if (valid) {
        checker_print_str(((uint8_t*)(SLOP_STR("true").data)));
    } else {
        checker_print_str(((uint8_t*)(SLOP_STR("false").data)));
    }
    checker_print_str(((uint8_t*)(SLOP_STR(",\"inferred_type\":").data)));
    checker_print_json_string(arena, inferred_type);
    checker_print_str(((uint8_t*)(SLOP_STR(",\"expected_type\":").data)));
    checker_print_json_string(arena, expected_type);
    checker_print_str(((uint8_t*)(SLOP_STR(",\"diagnostics\":").data)));
    checker_output_diagnostics_json(arena, diagnostics);
    checker_print_str(((uint8_t*)(SLOP_STR("}\n").data)));
}

int main(int64_t argc, uint8_t** argv) {
    if ((argc < 2)) {
        printf("%s\n", "Usage: slop-checker [--json] <file.slop> [file2.slop ...]");
        printf("%s\n", "       slop-checker --expr EXPR --type TYPE [--context FILE] [--params PARAMS]");
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
            if (string_eq(checker_argv_to_string(argv, 1), SLOP_STR("--expr"))) {
                {
                    __auto_type env = env_env_new(arena);
                    slop_string expr_str = SLOP_STR("");
                    slop_string type_str = SLOP_STR("Int");
                    slop_string context_file = SLOP_STR("");
                    slop_string params_str = SLOP_STR("");
                    int64_t i = 2;
                    if ((i < argc)) {
                        expr_str = checker_argv_to_string(argv, i);
                        i = (i + 1);
                    }
                    while ((i < argc)) {
                        {
                            __auto_type arg = checker_argv_to_string(argv, i);
                            if (string_eq(arg, SLOP_STR("--type"))) {
                                if (((i + 1) < argc)) {
                                    type_str = checker_argv_to_string(argv, (i + 1));
                                    i = (i + 2);
                                }
                            } else if (string_eq(arg, SLOP_STR("--context"))) {
                                if (((i + 1) < argc)) {
                                    context_file = checker_argv_to_string(argv, (i + 1));
                                    i = (i + 2);
                                }
                            } else if (string_eq(arg, SLOP_STR("--params"))) {
                                if (((i + 1) < argc)) {
                                    params_str = checker_argv_to_string(argv, (i + 1));
                                    i = (i + 2);
                                }
                            } else {
                                i = (i + 1);
                            }
                        }
                    }
                    if ((string_len(expr_str) == 0)) {
                        printf("%s\n", "Error: --expr requires an expression argument");
                        return 1;
                    } else {
                        return checker_check_expr_mode(arena, env, expr_str, type_str, context_file, params_str);
                    }
                }
            } else {
                {
                    __auto_type env = env_env_new(arena);
                    int64_t total_errors = 0;
                    __auto_type format = checker_OutputFormat_fmt_text;
                    int64_t file_start = 1;
                    if (string_eq(checker_argv_to_string(argv, 1), SLOP_STR("--json"))) {
                        format = checker_OutputFormat_fmt_json;
                        file_start = 2;
                    }
                    if ((format == checker_OutputFormat_fmt_json)) {
                        putchar(123);
                    }
                    {
                        int64_t i = file_start;
                        uint8_t first = 1;
                        while ((i < argc)) {
                            {
                                __auto_type filename = argv[i];
                                __auto_type errors = checker_check_single_file(env, arena, filename, format, first);
                                total_errors = (total_errors + errors);
                                first = 0;
                            }
                            i = (i + 1);
                        }
                    }
                    if ((format == checker_OutputFormat_fmt_json)) {
                        putchar(125);
                        putchar(10);
                    }
                    if ((total_errors > 0)) {
                        return 1;
                    } else {
                        return 0;
                    }
                }
            }
            slop_arena_free(arena);
        }
    }
}

