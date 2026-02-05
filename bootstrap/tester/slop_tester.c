#include "../runtime/slop_runtime.h"
#include "slop_tester.h"

slop_string tester_extract_module_name(slop_list_types_SExpr_ptr exprs);
slop_list_type_extract_ImportEntry tester_extract_imports(slop_arena* arena, slop_list_types_SExpr_ptr exprs);
tester_TestResult tester_generate_tests(slop_arena* arena, slop_string source);
tester_TestResult tester_generate_tests_with_imports(slop_arena* arena, slop_string source, slop_list_string import_sources);
void tester_extract_types_from_module_ast(slop_arena* arena, slop_list_types_SExpr_ptr ast, type_extract_TypeRegistry* types, slop_string prefix);
void tester_extract_types_from_module_form(slop_arena* arena, types_SExpr* module_form, type_extract_TypeRegistry* types, slop_string prefix);
void tester_extract_single_type_def(slop_arena* arena, types_SExpr* type_form, type_extract_TypeRegistry* types, slop_string prefix);
slop_string tester_make_prefixed_c_name(slop_arena* arena, slop_string prefix, slop_string name);
slop_string tester_convert_to_c_ident(slop_arena* arena, slop_string name);
type_extract_TstTypeEntry* tester_type_entry_new_local(slop_arena* arena, slop_string name, slop_string c_name, int64_t kind);
type_extract_TstTypeEntry* tester_extract_record_type_entry(slop_arena* arena, slop_string name, slop_string c_name, types_SExpr* def);
type_extract_TstTypeEntry* tester_extract_union_type_entry(slop_arena* arena, slop_string name, slop_string c_name, types_SExpr* def);
type_extract_TstTypeEntry* tester_extract_enum_type_entry(slop_arena* arena, slop_string name, slop_string c_name, types_SExpr* def);
slop_string tester_sexpr_to_string_simple(slop_arena* arena, types_SExpr* expr);

slop_string tester_extract_module_name(slop_list_types_SExpr_ptr exprs) {
    if ((((int64_t)((exprs).len)) < 1)) {
        return SLOP_STR("");
    } else {
        __auto_type _mv_1477 = ({ __auto_type _lst = exprs; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1477.has_value) {
            __auto_type first_expr = _mv_1477.value;
            if (parser_is_form(first_expr, SLOP_STR("module"))) {
                if ((parser_sexpr_list_len(first_expr) >= 2)) {
                    __auto_type _mv_1478 = parser_sexpr_list_get(first_expr, 1);
                    if (_mv_1478.has_value) {
                        __auto_type name_expr = _mv_1478.value;
                        if (parser_sexpr_is_symbol(name_expr)) {
                            return parser_sexpr_get_symbol_name(name_expr);
                        } else {
                            return SLOP_STR("");
                        }
                    } else if (!_mv_1478.has_value) {
                        return SLOP_STR("");
                    }
                } else {
                    return SLOP_STR("");
                }
            } else {
                return SLOP_STR("");
            }
        } else if (!_mv_1477.has_value) {
            return SLOP_STR("");
        }
    }
}

slop_list_type_extract_ImportEntry tester_extract_imports(slop_arena* arena, slop_list_types_SExpr_ptr exprs) {
    {
        __auto_type result = ((slop_list_type_extract_ImportEntry){ .data = (type_extract_ImportEntry*)slop_arena_alloc(arena, 16 * sizeof(type_extract_ImportEntry)), .len = 0, .cap = 16 });
        if ((((int64_t)((exprs).len)) > 0)) {
            __auto_type _mv_1479 = ({ __auto_type _lst = exprs; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1479.has_value) {
                __auto_type module_expr = _mv_1479.value;
                if (parser_is_form(module_expr, SLOP_STR("module"))) {
                    {
                        __auto_type mod_len = parser_sexpr_list_len(module_expr);
                        __auto_type i = 2;
                        while ((i < mod_len)) {
                            __auto_type _mv_1480 = parser_sexpr_list_get(module_expr, i);
                            if (_mv_1480.has_value) {
                                __auto_type child = _mv_1480.value;
                                if (parser_is_form(child, SLOP_STR("import"))) {
                                    if ((parser_sexpr_list_len(child) >= 3)) {
                                        __auto_type _mv_1481 = parser_sexpr_list_get(child, 1);
                                        if (_mv_1481.has_value) {
                                            __auto_type name_expr = _mv_1481.value;
                                            if (parser_sexpr_is_symbol(name_expr)) {
                                                {
                                                    __auto_type mod_name = parser_sexpr_get_symbol_name(name_expr);
                                                    __auto_type symbols = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                                                    __auto_type _mv_1482 = parser_sexpr_list_get(child, 2);
                                                    if (_mv_1482.has_value) {
                                                        __auto_type sym_list = _mv_1482.value;
                                                        {
                                                            __auto_type sym_len = parser_sexpr_list_len(sym_list);
                                                            __auto_type j = 0;
                                                            while ((j < sym_len)) {
                                                                __auto_type _mv_1483 = parser_sexpr_list_get(sym_list, j);
                                                                if (_mv_1483.has_value) {
                                                                    __auto_type sym_expr = _mv_1483.value;
                                                                    if (parser_sexpr_is_symbol(sym_expr)) {
                                                                        ({ __auto_type _lst_p = &(symbols); __auto_type _item = (parser_sexpr_get_symbol_name(sym_expr)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                                    }
                                                                } else if (!_mv_1483.has_value) {
                                                                }
                                                                j = (j + 1);
                                                            }
                                                        }
                                                    } else if (!_mv_1482.has_value) {
                                                    }
                                                    ({ __auto_type _lst_p = &(result); __auto_type _item = ((type_extract_ImportEntry){mod_name, symbols}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                }
                                            }
                                        } else if (!_mv_1481.has_value) {
                                        }
                                    }
                                }
                            } else if (!_mv_1480.has_value) {
                            }
                            i = (i + 1);
                        }
                    }
                }
            } else if (!_mv_1479.has_value) {
            }
        }
        return result;
    }
}

tester_TestResult tester_generate_tests(slop_arena* arena, slop_string source) {
    __auto_type _mv_1484 = parser_parse(arena, source);
    if (_mv_1484.is_ok) {
        __auto_type exprs = _mv_1484.data.ok;
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
                        __auto_type types = type_extract_extract_types_from_ast_with_imports(arena, exprs, mod_name, imports);
                        __auto_type tctx = test_emit_init_transpile_context(arena, exprs, mod_name);
                        {
                            __auto_type harness_lines = test_emit_emit_test_harness_typed(arena, test_cases, prefix, types, imports, tctx);
                            return (tester_TestResult){1, harness_lines, test_count, mod_name, SLOP_STR("")};
                        }
                    }
                }
            }
        }
    } else if (!_mv_1484.is_ok) {
        __auto_type err = _mv_1484.data.err;
        {
            __auto_type error_msg = string_concat(arena, SLOP_STR("Parse error at line "), string_concat(arena, int_to_string(arena, err.line), string_concat(arena, SLOP_STR(", col "), string_concat(arena, int_to_string(arena, err.col), string_concat(arena, SLOP_STR(": "), err.message)))));
            return (tester_TestResult){0, ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }), 0, SLOP_STR(""), error_msg};
        }
    }
}

tester_TestResult tester_generate_tests_with_imports(slop_arena* arena, slop_string source, slop_list_string import_sources) {
    __auto_type _mv_1485 = parser_parse(arena, source);
    if (_mv_1485.is_ok) {
        __auto_type exprs = _mv_1485.data.ok;
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
                        __auto_type types = type_extract_extract_types_from_ast_with_imports(arena, exprs, mod_name, imports);
                        __auto_type tctx = test_emit_init_transpile_context(arena, exprs, mod_name);
                        {
                            __auto_type import_count = ((int64_t)((import_sources).len));
                            __auto_type i = 0;
                            while ((i < import_count)) {
                                __auto_type _mv_1486 = ({ __auto_type _lst = import_sources; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1486.has_value) {
                                    __auto_type import_src = _mv_1486.value;
                                    __auto_type _mv_1487 = parser_parse(arena, import_src);
                                    if (_mv_1487.is_ok) {
                                        __auto_type import_exprs = _mv_1487.data.ok;
                                        {
                                            __auto_type import_mod_name = tester_extract_module_name(import_exprs);
                                            __auto_type import_prefix = (((((int64_t)(import_mod_name.len)) > 0)) ? ctype_to_c_name(arena, import_mod_name) : SLOP_STR(""));
                                            tester_extract_types_from_module_ast(arena, import_exprs, types, import_prefix);
                                            test_emit_init_transpile_context_for_imports(arena, tctx, import_exprs, import_mod_name);
                                            context_ctx_set_module(tctx, (slop_option_string){.has_value = 1, .value = mod_name});
                                        }
                                    } else if (!_mv_1487.is_ok) {
                                        __auto_type _ = _mv_1487.data.err;
                                    }
                                } else if (!_mv_1486.has_value) {
                                }
                                i = (i + 1);
                            }
                        }
                        context_ctx_set_module(tctx, (slop_option_string){.has_value = 1, .value = mod_name});
                        test_emit_re_prescan_main_module(arena, tctx, exprs);
                        {
                            __auto_type harness_lines = test_emit_emit_test_harness_typed(arena, test_cases, prefix, types, imports, tctx);
                            return (tester_TestResult){1, harness_lines, test_count, mod_name, SLOP_STR("")};
                        }
                    }
                }
            }
        }
    } else if (!_mv_1485.is_ok) {
        __auto_type err = _mv_1485.data.err;
        {
            __auto_type error_msg = string_concat(arena, SLOP_STR("Parse error at line "), string_concat(arena, int_to_string(arena, err.line), string_concat(arena, SLOP_STR(", col "), string_concat(arena, int_to_string(arena, err.col), string_concat(arena, SLOP_STR(": "), err.message)))));
            return (tester_TestResult){0, ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }), 0, SLOP_STR(""), error_msg};
        }
    }
}

void tester_extract_types_from_module_ast(slop_arena* arena, slop_list_types_SExpr_ptr ast, type_extract_TypeRegistry* types, slop_string prefix) {
    {
        __auto_type len = ((int64_t)((ast).len));
        int64_t i = 0;
        while ((i < len)) {
            __auto_type _mv_1488 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1488.has_value) {
                __auto_type expr = _mv_1488.value;
                if (parser_is_form(expr, SLOP_STR("module"))) {
                    tester_extract_types_from_module_form(arena, expr, types, prefix);
                }
                if (parser_is_form(expr, SLOP_STR("type"))) {
                    tester_extract_single_type_def(arena, expr, types, prefix);
                }
            } else if (!_mv_1488.has_value) {
            }
            i = (i + 1);
        }
    }
}

void tester_extract_types_from_module_form(slop_arena* arena, types_SExpr* module_form, type_extract_TypeRegistry* types, slop_string prefix) {
    {
        __auto_type len = parser_sexpr_list_len(module_form);
        int64_t i = 2;
        while ((i < len)) {
            __auto_type _mv_1489 = parser_sexpr_list_get(module_form, i);
            if (_mv_1489.has_value) {
                __auto_type form = _mv_1489.value;
                if (parser_is_form(form, SLOP_STR("type"))) {
                    tester_extract_single_type_def(arena, form, types, prefix);
                }
            } else if (!_mv_1489.has_value) {
            }
            i = (i + 1);
        }
    }
}

void tester_extract_single_type_def(slop_arena* arena, types_SExpr* type_form, type_extract_TypeRegistry* types, slop_string prefix) {
    if ((parser_sexpr_list_len(type_form) >= 3)) {
        __auto_type _mv_1490 = parser_sexpr_list_get(type_form, 1);
        if (_mv_1490.has_value) {
            __auto_type name_expr = _mv_1490.value;
            if (parser_sexpr_is_symbol(name_expr)) {
                {
                    __auto_type type_name = parser_sexpr_get_symbol_name(name_expr);
                    __auto_type c_name = tester_make_prefixed_c_name(arena, prefix, type_name);
                    __auto_type _mv_1491 = parser_sexpr_list_get(type_form, 2);
                    if (_mv_1491.has_value) {
                        __auto_type def_expr = _mv_1491.value;
                        if (parser_is_form(def_expr, SLOP_STR("record"))) {
                            {
                                __auto_type entry = tester_extract_record_type_entry(arena, type_name, c_name, def_expr);
                                type_extract_registry_add_type(arena, types, entry);
                            }
                        } else if (parser_is_form(def_expr, SLOP_STR("union"))) {
                            {
                                __auto_type entry = tester_extract_union_type_entry(arena, type_name, c_name, def_expr);
                                type_extract_registry_add_type(arena, types, entry);
                            }
                        } else if (parser_is_form(def_expr, SLOP_STR("enum"))) {
                            {
                                __auto_type entry = tester_extract_enum_type_entry(arena, type_name, c_name, def_expr);
                                type_extract_registry_add_type(arena, types, entry);
                            }
                        } else {
                        }
                    } else if (!_mv_1491.has_value) {
                    }
                }
            }
        } else if (!_mv_1490.has_value) {
        }
    }
}

slop_string tester_make_prefixed_c_name(slop_arena* arena, slop_string prefix, slop_string name) {
    if ((((int64_t)(prefix.len)) == 0)) {
        return tester_convert_to_c_ident(arena, name);
    } else {
        return string_concat(arena, prefix, string_concat(arena, SLOP_STR("_"), tester_convert_to_c_ident(arena, name)));
    }
}

slop_string tester_convert_to_c_ident(slop_arena* arena, slop_string name) {
    {
        __auto_type len = ((int64_t)(name.len));
        __auto_type buf = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (len + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        int64_t i = 0;
        while ((i < len)) {
            {
                __auto_type c = name.data[i];
                if ((c == 45)) {
                    buf[i] = 95;
                } else {
                    buf[i] = c;
                }
            }
            i = (i + 1);
        }
        buf[len] = 0;
        return (slop_string){.len = name.len, .data = buf};
    }
}

type_extract_TstTypeEntry* tester_type_entry_new_local(slop_arena* arena, slop_string name, slop_string c_name, int64_t kind) {
    {
        __auto_type entry = ((type_extract_TstTypeEntry*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 256); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        (*entry).name = name;
        (*entry).c_name = c_name;
        (*entry).kind = ((type_extract_TstTypeEntryKind)(kind));
        (*entry).fields = ((slop_list_type_extract_TstFieldEntry){ .data = (type_extract_TstFieldEntry*)slop_arena_alloc(arena, 16 * sizeof(type_extract_TstFieldEntry)), .len = 0, .cap = 16 });
        (*entry).variants = ((slop_list_type_extract_VariantEntry){ .data = (type_extract_VariantEntry*)slop_arena_alloc(arena, 16 * sizeof(type_extract_VariantEntry)), .len = 0, .cap = 16 });
        (*entry).enum_values = ((slop_list_type_extract_EnumValueEntry){ .data = (type_extract_EnumValueEntry*)slop_arena_alloc(arena, 16 * sizeof(type_extract_EnumValueEntry)), .len = 0, .cap = 16 });
        (*entry).inner_type = SLOP_STR("");
        return entry;
    }
}

type_extract_TstTypeEntry* tester_extract_record_type_entry(slop_arena* arena, slop_string name, slop_string c_name, types_SExpr* def) {
    {
        __auto_type entry = tester_type_entry_new_local(arena, name, c_name, 0);
        __auto_type len = parser_sexpr_list_len(def);
        int64_t i = 1;
        while ((i < len)) {
            __auto_type _mv_1492 = parser_sexpr_list_get(def, i);
            if (_mv_1492.has_value) {
                __auto_type field_def = _mv_1492.value;
                if ((parser_sexpr_list_len(field_def) >= 2)) {
                    __auto_type _mv_1493 = parser_sexpr_list_get(field_def, 0);
                    if (_mv_1493.has_value) {
                        __auto_type field_name_expr = _mv_1493.value;
                        if (parser_sexpr_is_symbol(field_name_expr)) {
                            {
                                __auto_type field_name = parser_sexpr_get_symbol_name(field_name_expr);
                                __auto_type _mv_1494 = parser_sexpr_list_get(field_def, 1);
                                if (_mv_1494.has_value) {
                                    __auto_type field_type_expr = _mv_1494.value;
                                    {
                                        __auto_type field_type = tester_sexpr_to_string_simple(arena, field_type_expr);
                                        __auto_type fe = (type_extract_TstFieldEntry){field_name, field_type};
                                        ({ __auto_type _lst_p = &((*entry).fields); __auto_type _item = (fe); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    }
                                } else if (!_mv_1494.has_value) {
                                }
                            }
                        }
                    } else if (!_mv_1493.has_value) {
                    }
                }
            } else if (!_mv_1492.has_value) {
            }
            i = (i + 1);
        }
        return entry;
    }
}

type_extract_TstTypeEntry* tester_extract_union_type_entry(slop_arena* arena, slop_string name, slop_string c_name, types_SExpr* def) {
    {
        __auto_type entry = tester_type_entry_new_local(arena, name, c_name, 1);
        __auto_type len = parser_sexpr_list_len(def);
        int64_t i = 1;
        int64_t idx = 0;
        while ((i < len)) {
            __auto_type _mv_1495 = parser_sexpr_list_get(def, i);
            if (_mv_1495.has_value) {
                __auto_type variant_def = _mv_1495.value;
                {
                    __auto_type vlen = parser_sexpr_list_len(variant_def);
                    if ((vlen >= 1)) {
                        __auto_type _mv_1496 = parser_sexpr_list_get(variant_def, 0);
                        if (_mv_1496.has_value) {
                            __auto_type variant_name_expr = _mv_1496.value;
                            if (parser_sexpr_is_symbol(variant_name_expr)) {
                                {
                                    __auto_type variant_name = parser_sexpr_get_symbol_name(variant_name_expr);
                                    __auto_type payload_type = (((vlen >= 2)) ? ({ __auto_type _mv = parser_sexpr_list_get(variant_def, 1); _mv.has_value ? ({ __auto_type pt_expr = _mv.value; tester_sexpr_to_string_simple(arena, pt_expr); }) : (SLOP_STR("")); }) : SLOP_STR(""));
                                    __auto_type ve = (type_extract_VariantEntry){variant_name, idx, payload_type};
                                    ({ __auto_type _lst_p = &((*entry).variants); __auto_type _item = (ve); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    idx = (idx + 1);
                                }
                            }
                        } else if (!_mv_1496.has_value) {
                        }
                    }
                }
            } else if (!_mv_1495.has_value) {
            }
            i = (i + 1);
        }
        return entry;
    }
}

type_extract_TstTypeEntry* tester_extract_enum_type_entry(slop_arena* arena, slop_string name, slop_string c_name, types_SExpr* def) {
    {
        __auto_type entry = tester_type_entry_new_local(arena, name, c_name, 2);
        __auto_type len = parser_sexpr_list_len(def);
        int64_t i = 1;
        int64_t idx = 0;
        while ((i < len)) {
            __auto_type _mv_1497 = parser_sexpr_list_get(def, i);
            if (_mv_1497.has_value) {
                __auto_type val_expr = _mv_1497.value;
                if (parser_sexpr_is_symbol(val_expr)) {
                    {
                        __auto_type val_name = parser_sexpr_get_symbol_name(val_expr);
                        __auto_type eve = (type_extract_EnumValueEntry){val_name, idx};
                        ({ __auto_type _lst_p = &((*entry).enum_values); __auto_type _item = (eve); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        idx = (idx + 1);
                    }
                }
            } else if (!_mv_1497.has_value) {
            }
            i = (i + 1);
        }
        return entry;
    }
}

slop_string tester_sexpr_to_string_simple(slop_arena* arena, types_SExpr* expr) {
    __auto_type _mv_1498 = (*expr);
    switch (_mv_1498.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1498.data.sym;
            return sym.name;
        }
        case types_SExpr_num:
        {
            __auto_type num = _mv_1498.data.num;
            return num.raw;
        }
        case types_SExpr_str:
        {
            __auto_type str = _mv_1498.data.str;
            return str.value;
        }
        case types_SExpr_lst:
        {
            __auto_type l = _mv_1498.data.lst;
            {
                __auto_type items = l.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type result = SLOP_STR("");
                __auto_type i = 0;
                while ((i < len)) {
                    __auto_type _mv_1499 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1499.has_value) {
                        __auto_type child = _mv_1499.value;
                        {
                            __auto_type child_str = tester_sexpr_to_string_simple(arena, child);
                            if ((i == 0)) {
                                result = child_str;
                            } else {
                                result = string_concat(arena, result, string_concat(arena, SLOP_STR(" "), child_str));
                            }
                        }
                    } else if (!_mv_1499.has_value) {
                    }
                    i = (i + 1);
                }
                return result;
            }
        }
    }
}

