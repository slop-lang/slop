#include "../runtime/slop_runtime.h"
#include "slop_tester.h"

slop_string tester_extract_module_name(slop_list_types_SExpr_ptr exprs);
slop_list_string tester_extract_imports(slop_arena* arena, slop_list_types_SExpr_ptr exprs);
tester_TestResult tester_generate_tests(slop_arena* arena, slop_string source);

slop_string tester_extract_module_name(slop_list_types_SExpr_ptr exprs) {
    if ((((int64_t)((exprs).len)) < 1)) {
        return SLOP_STR("");
    } else {
        __auto_type _mv_198 = ({ __auto_type _lst = exprs; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_198.has_value) {
            __auto_type first_expr = _mv_198.value;
            if (parser_is_form(first_expr, SLOP_STR("module"))) {
                if ((parser_sexpr_list_len(first_expr) >= 2)) {
                    __auto_type _mv_199 = parser_sexpr_list_get(first_expr, 1);
                    if (_mv_199.has_value) {
                        __auto_type name_expr = _mv_199.value;
                        if (parser_sexpr_is_symbol(name_expr)) {
                            return parser_sexpr_get_symbol_name(name_expr);
                        } else {
                            return SLOP_STR("");
                        }
                    } else if (!_mv_199.has_value) {
                        return SLOP_STR("");
                    }
                } else {
                    return SLOP_STR("");
                }
            } else {
                return SLOP_STR("");
            }
        } else if (!_mv_198.has_value) {
            return SLOP_STR("");
        }
    }
}

slop_list_string tester_extract_imports(slop_arena* arena, slop_list_types_SExpr_ptr exprs) {
    {
        __auto_type result = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        if ((((int64_t)((exprs).len)) > 0)) {
            __auto_type _mv_200 = ({ __auto_type _lst = exprs; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_200.has_value) {
                __auto_type module_expr = _mv_200.value;
                if (parser_is_form(module_expr, SLOP_STR("module"))) {
                    {
                        __auto_type mod_len = parser_sexpr_list_len(module_expr);
                        __auto_type i = 2;
                        while ((i < mod_len)) {
                            __auto_type _mv_201 = parser_sexpr_list_get(module_expr, i);
                            if (_mv_201.has_value) {
                                __auto_type child = _mv_201.value;
                                if (parser_is_form(child, SLOP_STR("import"))) {
                                    if ((parser_sexpr_list_len(child) >= 2)) {
                                        __auto_type _mv_202 = parser_sexpr_list_get(child, 1);
                                        if (_mv_202.has_value) {
                                            __auto_type name_expr = _mv_202.value;
                                            if (parser_sexpr_is_symbol(name_expr)) {
                                                ({ __auto_type _lst_p = &(result); __auto_type _item = (parser_sexpr_get_symbol_name(name_expr)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                            }
                                        } else if (!_mv_202.has_value) {
                                        }
                                    }
                                }
                            } else if (!_mv_201.has_value) {
                            }
                            i = (i + 1);
                        }
                    }
                }
            } else if (!_mv_200.has_value) {
            }
        }
        return result;
    }
}

tester_TestResult tester_generate_tests(slop_arena* arena, slop_string source) {
    __auto_type _mv_203 = parser_parse(arena, source);
    if (_mv_203.is_ok) {
        __auto_type exprs = _mv_203.data.ok;
        {
            __auto_type mod_name = tester_extract_module_name(exprs);
            __auto_type imports = tester_extract_imports(arena, exprs);
            {
                __auto_type test_cases = extract_extract_examples_from_ast(arena, exprs);
                __auto_type test_count = ((int64_t)((test_cases).len));
                if ((test_count == 0)) {
                    return (tester_TestResult){1, ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }), 0, mod_name, SLOP_STR("")};
                } else {
                    {
                        __auto_type prefix = (((((int64_t)(mod_name.len)) > 0)) ? ctype_to_c_name(arena, mod_name) : SLOP_STR(""));
                        __auto_type types = type_extract_extract_types_from_ast(arena, exprs, mod_name);
                        {
                            __auto_type harness_lines = emit_emit_test_harness_typed(arena, test_cases, prefix, types, imports);
                            return (tester_TestResult){1, harness_lines, test_count, mod_name, SLOP_STR("")};
                        }
                    }
                }
            }
        }
    } else if (!_mv_203.is_ok) {
        __auto_type err = _mv_203.data.err;
        {
            __auto_type error_msg = string_concat(arena, SLOP_STR("Parse error at line "), string_concat(arena, int_to_string(arena, err.line), string_concat(arena, SLOP_STR(", col "), string_concat(arena, int_to_string(arena, err.col), string_concat(arena, SLOP_STR(": "), err.message)))));
            return (tester_TestResult){0, ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }), 0, SLOP_STR(""), error_msg};
        }
    }
}

