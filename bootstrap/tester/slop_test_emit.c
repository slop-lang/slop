#include "../runtime/slop_runtime.h"
#include "slop_test_emit.h"

types_SExpr* test_emit_make_sexpr_sym(slop_arena* arena, slop_string name);
types_SExpr* test_emit_make_sexpr_num(slop_arena* arena, slop_string raw);
types_SExpr* test_emit_make_sexpr_list(slop_arena* arena, slop_list_types_SExpr_ptr items);
uint8_t test_emit_is_wildcard_like_symbol(slop_string name);
uint8_t test_emit_has_ellipsis(types_SExpr* expr);
uint8_t test_emit_args_have_ellipsis(slop_list_types_SExpr_ptr args);
uint8_t test_emit_is_type_constructor_name(slop_string name);
uint8_t test_emit_contains_wildcard(types_SExpr* expr);
types_SExpr* test_emit_replace_wildcards(slop_arena* arena, types_SExpr* expr);
slop_string test_emit_replace_wildcard_tokens(slop_arena* arena, slop_string s);
slop_string test_emit_transpile_expr_safe(slop_arena* arena, context_TranspileContext* tctx, types_SExpr* expr);
slop_string test_emit_prefix_symbol(slop_arena* arena, slop_string name, slop_string prefix, type_extract_TypeRegistry types);
test_emit_EmitContext* test_emit_emit_ctx_new_typed(slop_arena* arena, type_extract_TypeRegistry* types, context_TranspileContext* tctx);
void test_emit_emit(test_emit_EmitContext* ctx, slop_string line);
slop_list_string test_emit_emit_ctx_get_lines(test_emit_EmitContext* ctx);
types_SExpr* test_emit_build_call_sexpr(slop_arena* arena, slop_string fn_name, slop_list_types_SExpr_ptr args, uint8_t needs_arena, int64_t arena_pos);
slop_string test_emit_escape_string(slop_arena* arena, slop_string s);
slop_list_string test_emit_emit_test_harness_typed(slop_arena* arena, slop_list_extract_TestCase_ptr tests, slop_string module_prefix, type_extract_TypeRegistry* types, slop_list_type_extract_ImportEntry imports, context_TranspileContext* tctx);
uint8_t test_emit_any_test_needs_arena(slop_list_extract_TestCase_ptr tests);
void test_emit_emit_test_function_typed(test_emit_EmitContext* ctx, extract_TestCase tc, int64_t index, slop_string prefix, type_extract_TypeRegistry* types, context_TranspileContext* tctx);
void test_emit_emit_main_function(test_emit_EmitContext* ctx, int64_t test_count, uint8_t needs_arena);
slop_string test_emit_make_c_fn_name(slop_arena* arena, slop_string fn_name, slop_option_string module_name, slop_string prefix);
slop_string test_emit_build_args_display_typed(slop_arena* arena, slop_list_types_SExpr_ptr args, type_extract_TypeRegistry types);
test_emit_CompareInfo test_emit_build_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_option_string return_type, slop_string prefix, type_extract_TypeRegistry types, slop_option_string eq_fn, context_TranspileContext* tctx);
test_emit_CompareInfo test_emit_build_record_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types, context_TranspileContext* tctx);
test_emit_CompareInfo test_emit_build_record_comparison_inner(slop_arena* arena, type_extract_TypeRegistry types, slop_string record_name, slop_list_types_SExpr_ptr field_values, slop_string c_expected, slop_string decl_type);
slop_string test_emit_get_record_decl_type(slop_arena* arena, type_extract_TypeRegistry types, slop_string record_name);
slop_string test_emit_get_record_name_from_expr(types_SExpr* expr);
slop_list_types_SExpr_ptr test_emit_get_record_field_values(slop_arena* arena, types_SExpr* expr);
uint8_t test_emit_is_wildcard_expr(types_SExpr* expr);
slop_string test_emit_build_record_field_comparisons_with_values(slop_arena* arena, slop_list_type_extract_TstFieldEntry fields, slop_list_types_SExpr_ptr field_values, slop_string result_accessor, slop_string expected_var);
slop_string test_emit_build_single_field_comparison_with_accessor(slop_arena* arena, slop_string fname, slop_string ftype, slop_string result_accessor, slop_string expected_var);
uint8_t test_emit_is_likely_struct_type(slop_string type_name);
slop_string test_emit_get_first_symbol_name(types_SExpr* expr);
test_emit_CompareInfo test_emit_build_union_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types, slop_string ret_type_str, context_TranspileContext* tctx);
slop_string test_emit_build_union_payload_comparison(slop_arena* arena, slop_string payload_type, slop_string c_variant, slop_string expected_var, type_extract_TypeRegistry types);
slop_string test_emit_build_union_record_payload_comparison(slop_arena* arena, slop_list_type_extract_TstFieldEntry fields, slop_string c_variant, slop_string expected_var);
slop_string test_emit_build_union_field_comparison(slop_arena* arena, slop_string fname, slop_string ftype, slop_string c_variant, slop_string expected_var);
uint8_t test_emit_is_union_constructor_typed(types_SExpr* expr, type_extract_TypeRegistry types);
slop_string test_emit_get_union_variant_name(types_SExpr* expr);
uint8_t test_emit_is_enum_value_typed(types_SExpr* expr, type_extract_TypeRegistry types);
uint8_t test_emit_is_record_constructor_typed(types_SExpr* expr, type_extract_TypeRegistry types);
slop_string test_emit_emit_string_slice(slop_string s, int64_t start);
slop_string test_emit_get_some_inner_typed(slop_arena* arena, types_SExpr* expr, context_TranspileContext* tctx);
slop_string test_emit_get_ok_inner_typed(slop_arena* arena, types_SExpr* expr, context_TranspileContext* tctx);
slop_string test_emit_get_error_inner_typed(slop_arena* arena, types_SExpr* expr, context_TranspileContext* tctx);
types_SExpr* test_emit_get_some_inner_expr(types_SExpr* expected);
types_SExpr* test_emit_get_ok_inner_expr(types_SExpr* expected);
uint8_t test_emit_is_none_value(types_SExpr* expr);
uint8_t test_emit_is_some_value(types_SExpr* expr);
uint8_t test_emit_is_ok_value(types_SExpr* expr);
uint8_t test_emit_is_error_value(types_SExpr* expr);
slop_string test_emit_extract_list_element_type(slop_arena* arena, slop_string list_type_str);
slop_string test_emit_build_eq_function_name(slop_arena* arena, slop_string type_name, slop_string prefix, type_extract_TypeRegistry types);
test_emit_CompareInfo test_emit_build_list_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types, slop_string ret_type_str, slop_option_string eq_fn, context_TranspileContext* tctx);
context_TranspileContext* test_emit_init_transpile_context(slop_arena* arena, slop_list_types_SExpr_ptr ast, slop_string module_name);
void test_emit_init_transpile_context_for_imports(slop_arena* arena, context_TranspileContext* tctx, slop_list_types_SExpr_ptr import_ast, slop_string import_mod_name);
void test_emit_re_prescan_main_module(slop_arena* arena, context_TranspileContext* tctx, slop_list_types_SExpr_ptr ast);
void test_emit_register_all_field_types(context_TranspileContext* tctx, slop_list_types_SExpr_ptr body_forms);
void test_emit_register_type_fields(context_TranspileContext* tctx, types_SExpr* type_form);

types_SExpr* test_emit_make_sexpr_sym(slop_arena* arena, slop_string name) {
    {
        __auto_type node = ((types_SExpr*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 128); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        (*node) = ((types_SExpr){ .tag = types_SExpr_sym, .data.sym = (types_SExprSymbol){name, 0, 0, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
        return node;
    }
}

types_SExpr* test_emit_make_sexpr_num(slop_arena* arena, slop_string raw) {
    {
        __auto_type node = ((types_SExpr*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 128); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        (*node) = ((types_SExpr){ .tag = types_SExpr_num, .data.num = (types_SExprNumber){0, 0, 0, raw, 0, 0, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
        return node;
    }
}

types_SExpr* test_emit_make_sexpr_list(slop_arena* arena, slop_list_types_SExpr_ptr items) {
    {
        __auto_type node = ((types_SExpr*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 128); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        (*node) = ((types_SExpr){ .tag = types_SExpr_lst, .data.lst = (types_SExprList){items, 0, 0, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
        return node;
    }
}

uint8_t test_emit_is_wildcard_like_symbol(slop_string name) {
    if ((string_len(name) < 1)) {
        return 0;
    } else {
        {
            __auto_type first_char = strlib_char_at(name, 0);
            if (!(((first_char >= 97) && (first_char <= 122)))) {
                return 0;
            } else {
                if (string_eq(name, SLOP_STR("true"))) {
                    return 0;
                } else if (string_eq(name, SLOP_STR("false"))) {
                    return 0;
                } else if (string_eq(name, SLOP_STR("none"))) {
                    return 0;
                } else if (string_eq(name, SLOP_STR("some"))) {
                    return 0;
                } else if (string_eq(name, SLOP_STR("ok"))) {
                    return 0;
                } else if (string_eq(name, SLOP_STR("error"))) {
                    return 0;
                } else if (string_eq(name, SLOP_STR("list"))) {
                    return 0;
                } else if (string_eq(name, SLOP_STR("arena"))) {
                    return 0;
                } else if (string_eq(name, SLOP_STR("record"))) {
                    return 0;
                } else if (string_eq(name, SLOP_STR("record-new"))) {
                    return 0;
                } else if (string_eq(name, SLOP_STR("union-new"))) {
                    return 0;
                } else if (string_eq(name, SLOP_STR("quote"))) {
                    return 0;
                } else if (string_eq(name, SLOP_STR("cast"))) {
                    return 0;
                } else if (strlib_contains(name, SLOP_STR("-"))) {
                    return 0;
                } else {
                    return 1;
                }
            }
        }
    }
}

uint8_t test_emit_has_ellipsis(types_SExpr* expr) {
    __auto_type _mv_1408 = (*expr);
    switch (_mv_1408.tag) {
        case types_SExpr_sym:
        {
            __auto_type s = _mv_1408.data.sym;
            return string_eq(s.name, SLOP_STR(".."));
        }
        case types_SExpr_lst:
        {
            __auto_type l = _mv_1408.data.lst;
            {
                __auto_type items = l.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type i = 0;
                __auto_type found = 0;
                while (((i < len) && !(found))) {
                    __auto_type _mv_1409 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1409.has_value) {
                        __auto_type item = _mv_1409.value;
                        if (test_emit_has_ellipsis(item)) {
                            found = 1;
                        }
                    } else if (!_mv_1409.has_value) {
                    }
                    i = (i + 1);
                }
                return found;
            }
        }
        case types_SExpr_num:
        {
            __auto_type _ = _mv_1408.data.num;
            return 0;
        }
        case types_SExpr_str:
        {
            __auto_type _ = _mv_1408.data.str;
            return 0;
        }
    }
}

uint8_t test_emit_args_have_ellipsis(slop_list_types_SExpr_ptr args) {
    {
        __auto_type len = ((int64_t)((args).len));
        int64_t i = 0;
        uint8_t found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_1410 = ({ __auto_type _lst = args; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1410.has_value) {
                __auto_type arg = _mv_1410.value;
                if (test_emit_has_ellipsis(arg)) {
                    found = 1;
                }
            } else if (!_mv_1410.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

uint8_t test_emit_is_type_constructor_name(slop_string name) {
    if ((string_len(name) < 1)) {
        return 0;
    } else {
        {
            __auto_type c = strlib_char_at(name, 0);
            return ((c >= 65) && (c <= 90));
        }
    }
}

uint8_t test_emit_contains_wildcard(types_SExpr* expr) {
    __auto_type _mv_1411 = (*expr);
    switch (_mv_1411.tag) {
        case types_SExpr_sym:
        {
            __auto_type s = _mv_1411.data.sym;
            return ((string_eq(s.name, SLOP_STR("_"))) || (string_eq(s.name, SLOP_STR(".."))) || (string_eq(s.name, SLOP_STR("."))) || (test_emit_is_wildcard_like_symbol(s.name)));
        }
        case types_SExpr_lst:
        {
            __auto_type l = _mv_1411.data.lst;
            {
                __auto_type items = l.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type i = 0;
                __auto_type found = 0;
                while (((i < len) && !(found))) {
                    __auto_type _mv_1412 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1412.has_value) {
                        __auto_type item = _mv_1412.value;
                        if (test_emit_contains_wildcard(item)) {
                            found = 1;
                        }
                    } else if (!_mv_1412.has_value) {
                    }
                    i = (i + 1);
                }
                return found;
            }
        }
        case types_SExpr_num:
        {
            __auto_type _ = _mv_1411.data.num;
            return 0;
        }
        case types_SExpr_str:
        {
            __auto_type _ = _mv_1411.data.str;
            return 0;
        }
    }
}

types_SExpr* test_emit_replace_wildcards(slop_arena* arena, types_SExpr* expr) {
    __auto_type _mv_1413 = (*expr);
    switch (_mv_1413.tag) {
        case types_SExpr_sym:
        {
            __auto_type s = _mv_1413.data.sym;
            if (((string_eq(s.name, SLOP_STR("_"))) || (string_eq(s.name, SLOP_STR(".."))) || (string_eq(s.name, SLOP_STR("."))))) {
                return test_emit_make_sexpr_sym(arena, SLOP_STR("__SLOP_WILDCARD__"));
            } else {
                return expr;
            }
        }
        case types_SExpr_lst:
        {
            __auto_type l = _mv_1413.data.lst;
            {
                __auto_type items = l.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type new_items = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
                __auto_type i = 0;
                __auto_type in_type_constructor = (((len > 0)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type first = _mv.value; ({ __auto_type _mv = (*first); uint8_t _mr = {0}; switch (_mv.tag) { case types_SExpr_sym: { __auto_type s = _mv.data.sym; _mr = test_emit_is_type_constructor_name(s.name); break; } default: { _mr = 0; break; }  } _mr; }); }) : (0); }) : 0);
                while ((i < len)) {
                    __auto_type _mv_1414 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1414.has_value) {
                        __auto_type item = _mv_1414.value;
                        if ((in_type_constructor && (i > 0))) {
                            __auto_type _mv_1415 = (*item);
                            switch (_mv_1415.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type s = _mv_1415.data.sym;
                                    if (((string_eq(s.name, SLOP_STR(".."))) && (((i + 1) < len)) && (({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)(i + 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type next_item = _mv.value; ({ __auto_type _mv = (*next_item); uint8_t _mr = {0}; switch (_mv.tag) { case types_SExpr_sym: { __auto_type ns = _mv.data.sym; _mr = string_eq(ns.name, SLOP_STR(".")); break; } default: { _mr = 0; break; }  } _mr; }); }) : (0); })))) {
                                    } else if (((string_eq(s.name, SLOP_STR("_"))) || (string_eq(s.name, SLOP_STR(".."))) || (string_eq(s.name, SLOP_STR("."))) || (test_emit_is_wildcard_like_symbol(s.name)))) {
                                        ({ __auto_type _lst_p = &(new_items); __auto_type _item = (test_emit_make_sexpr_sym(arena, SLOP_STR("__SLOP_WILDCARD__"))); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    } else {
                                        ({ __auto_type _lst_p = &(new_items); __auto_type _item = (test_emit_replace_wildcards(arena, item)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    }
                                    break;
                                }
                                default: {
                                    ({ __auto_type _lst_p = &(new_items); __auto_type _item = (test_emit_replace_wildcards(arena, item)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    break;
                                }
                            }
                        } else {
                            ({ __auto_type _lst_p = &(new_items); __auto_type _item = (test_emit_replace_wildcards(arena, item)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        }
                    } else if (!_mv_1414.has_value) {
                    }
                    i = (i + 1);
                }
                return test_emit_make_sexpr_list(arena, new_items);
            }
        }
        case types_SExpr_num:
        {
            __auto_type _ = _mv_1413.data.num;
            return expr;
        }
        case types_SExpr_str:
        {
            __auto_type _ = _mv_1413.data.str;
            return expr;
        }
    }
}

slop_string test_emit_replace_wildcard_tokens(slop_arena* arena, slop_string s) {
    if (!(strlib_contains(s, SLOP_STR("__SLOP_WILDCARD__")))) {
        return s;
    } else {
        {
            __auto_type needle_len = 17;
            __auto_type src_len = ((int64_t)(s.len));
            __auto_type buf = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (src_len + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
            int64_t src_pos = 0;
            int64_t dst_pos = 0;
            while ((src_pos < src_len)) {
                if (((((src_pos + needle_len) <= src_len)) && ((s.data[src_pos] == 95)) && ((s.data[(src_pos + 1)] == 95)) && (string_eq(strlib_substring(arena, s, src_pos, needle_len), SLOP_STR("__SLOP_WILDCARD__"))))) {
                    buf[dst_pos] = 123;
                    buf[(dst_pos + 1)] = 48;
                    buf[(dst_pos + 2)] = 125;
                    dst_pos = (dst_pos + 3);
                    src_pos = (src_pos + needle_len);
                } else {
                    buf[dst_pos] = s.data[src_pos];
                    dst_pos = (dst_pos + 1);
                    src_pos = (src_pos + 1);
                }
            }
            buf[dst_pos] = 0;
            return (slop_string){.len = ((uint64_t)(dst_pos)), .data = buf};
        }
    }
}

slop_string test_emit_transpile_expr_safe(slop_arena* arena, context_TranspileContext* tctx, types_SExpr* expr) {
    return test_emit_replace_wildcard_tokens(arena, expr_transpile_expr(tctx, test_emit_replace_wildcards(arena, expr)));
}

slop_string test_emit_prefix_symbol(slop_arena* arena, slop_string name, slop_string prefix, type_extract_TypeRegistry types) {
    if (string_eq(name, SLOP_STR("arena"))) {
        return SLOP_STR("test_arena");
    } else {
        __auto_type _mv_1416 = type_extract_registry_lookup_import(types, name);
        if (_mv_1416.has_value) {
            __auto_type mod_name = _mv_1416.value;
            return string_concat(arena, ctype_to_c_name(arena, mod_name), string_concat(arena, SLOP_STR("_"), ctype_to_c_name(arena, name)));
        } else if (!_mv_1416.has_value) {
            if ((((int64_t)(prefix.len)) > 0)) {
                return string_concat(arena, prefix, string_concat(arena, SLOP_STR("_"), ctype_to_c_name(arena, name)));
            } else {
                return ctype_to_c_name(arena, name);
            }
        }
    }
}

test_emit_EmitContext* test_emit_emit_ctx_new_typed(slop_arena* arena, type_extract_TypeRegistry* types, context_TranspileContext* tctx) {
    {
        __auto_type ctx = ((test_emit_EmitContext*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 128); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        (*ctx) = (test_emit_EmitContext){((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }), arena, types, tctx, 1};
        return ctx;
    }
}

void test_emit_emit(test_emit_EmitContext* ctx, slop_string line) {
    ({ __auto_type _lst_p = &((*ctx).lines); __auto_type _item = (line); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_list_string test_emit_emit_ctx_get_lines(test_emit_EmitContext* ctx) {
    return (*ctx).lines;
}

types_SExpr* test_emit_build_call_sexpr(slop_arena* arena, slop_string fn_name, slop_list_types_SExpr_ptr args, uint8_t needs_arena, int64_t arena_pos) {
    {
        __auto_type call_items = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
        __auto_type len = ((int64_t)((args).len));
        int64_t i = 0;
        int64_t arg_idx = 0;
        ({ __auto_type _lst_p = &(call_items); __auto_type _item = (test_emit_make_sexpr_sym(arena, fn_name)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
        while ((i < len)) {
            if ((needs_arena && (arg_idx == arena_pos))) {
                ({ __auto_type _lst_p = &(call_items); __auto_type _item = (test_emit_make_sexpr_sym(arena, SLOP_STR("arena"))); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                arg_idx = (arg_idx + 1);
            }
            __auto_type _mv_1417 = ({ __auto_type _lst = args; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1417.has_value) {
                __auto_type arg = _mv_1417.value;
                ({ __auto_type _lst_p = &(call_items); __auto_type _item = (arg); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            } else if (!_mv_1417.has_value) {
            }
            i = (i + 1);
            arg_idx = (arg_idx + 1);
        }
        if ((needs_arena && (arena_pos >= len))) {
            ({ __auto_type _lst_p = &(call_items); __auto_type _item = (test_emit_make_sexpr_sym(arena, SLOP_STR("arena"))); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
        }
        return test_emit_make_sexpr_list(arena, call_items);
    }
}

slop_string test_emit_escape_string(slop_arena* arena, slop_string s) {
    {
        __auto_type len = ((int64_t)(s.len));
        __auto_type buf = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, ((len * 2) + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        int64_t i = 0;
        int64_t out = 0;
        while ((i < len)) {
            {
                __auto_type c = s.data[i];
                if ((c == 10)) {
                    buf[out] = 92;
                    buf[(out + 1)] = 110;
                    out = (out + 2);
                } else if ((c == 13)) {
                    buf[out] = 92;
                    buf[(out + 1)] = 114;
                    out = (out + 2);
                } else if ((c == 9)) {
                    buf[out] = 92;
                    buf[(out + 1)] = 116;
                    out = (out + 2);
                } else if ((c == 34)) {
                    buf[out] = 92;
                    buf[(out + 1)] = 34;
                    out = (out + 2);
                } else if ((c == 92)) {
                    buf[out] = 92;
                    buf[(out + 1)] = 92;
                    out = (out + 2);
                } else {
                    buf[out] = c;
                    out = (out + 1);
                }
            }
            i = (i + 1);
        }
        buf[out] = 0;
        return (slop_string){.len = ((uint64_t)(out)), .data = buf};
    }
}

slop_list_string test_emit_emit_test_harness_typed(slop_arena* arena, slop_list_extract_TestCase_ptr tests, slop_string module_prefix, type_extract_TypeRegistry* types, slop_list_type_extract_ImportEntry imports, context_TranspileContext* tctx) {
    {
        __auto_type ctx = test_emit_emit_ctx_new_typed(arena, types, tctx);
        test_emit_emit(ctx, SLOP_STR("// ===== SLOP Test Harness (Native Generated - Type Aware) ====="));
        {
            __auto_type type_count = ((int64_t)(((*types).types).len));
            test_emit_emit(ctx, string_concat(arena, SLOP_STR("// DEBUG: TypeRegistry has "), string_concat(arena, int_to_string(arena, type_count), SLOP_STR(" type(s)"))));
        }
        test_emit_emit(ctx, SLOP_STR(""));
        test_emit_emit(ctx, SLOP_STR("#include <stdio.h>"));
        test_emit_emit(ctx, SLOP_STR("#include <string.h>"));
        test_emit_emit(ctx, SLOP_STR("#include <math.h>"));
        {
            __auto_type import_count = ((int64_t)((imports).len));
            int64_t j = 0;
            while ((j < import_count)) {
                __auto_type _mv_1418 = ({ __auto_type _lst = imports; size_t _idx = (size_t)j; slop_option_type_extract_ImportEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1418.has_value) {
                    __auto_type entry = _mv_1418.value;
                    {
                        __auto_type c_name = ctype_to_c_name(arena, entry.module_name);
                        test_emit_emit(ctx, string_concat(arena, SLOP_STR("#include \"slop_"), string_concat(arena, c_name, SLOP_STR(".h\""))));
                    }
                } else if (!_mv_1418.has_value) {
                }
                j = (j + 1);
            }
        }
        test_emit_emit(ctx, SLOP_STR(""));
        test_emit_emit(ctx, SLOP_STR("static int tests_passed = 0;"));
        test_emit_emit(ctx, SLOP_STR("static int tests_failed = 0;"));
        test_emit_emit(ctx, SLOP_STR(""));
        {
            __auto_type any_needs_arena = test_emit_any_test_needs_arena(tests);
            if (any_needs_arena) {
                test_emit_emit(ctx, SLOP_STR("// Global test arena for functions that need one"));
                test_emit_emit(ctx, SLOP_STR("static slop_arena test_arena_storage;"));
                test_emit_emit(ctx, SLOP_STR("static slop_arena* test_arena = NULL;"));
                test_emit_emit(ctx, SLOP_STR(""));
            }
            {
                __auto_type test_count = ((int64_t)((tests).len));
                int64_t i = 0;
                while ((i < test_count)) {
                    __auto_type _mv_1419 = ({ __auto_type _lst = tests; size_t _idx = (size_t)i; slop_option_extract_TestCase_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1419.has_value) {
                        __auto_type tc = _mv_1419.value;
                        test_emit_emit_test_function_typed(ctx, (*tc), i, module_prefix, types, tctx);
                    } else if (!_mv_1419.has_value) {
                    }
                    i = (i + 1);
                }
                test_emit_emit_main_function(ctx, test_count, any_needs_arena);
            }
        }
        return test_emit_emit_ctx_get_lines(ctx);
    }
}

uint8_t test_emit_any_test_needs_arena(slop_list_extract_TestCase_ptr tests) {
    {
        __auto_type len = ((int64_t)((tests).len));
        int64_t i = 0;
        uint8_t found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_1420 = ({ __auto_type _lst = tests; size_t _idx = (size_t)i; slop_option_extract_TestCase_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1420.has_value) {
                __auto_type tc = _mv_1420.value;
                if ((*tc).needs_arena) {
                    found = 1;
                }
            } else if (!_mv_1420.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

void test_emit_emit_test_function_typed(test_emit_EmitContext* ctx, extract_TestCase tc, int64_t index, slop_string prefix, type_extract_TypeRegistry* types, context_TranspileContext* tctx) {
    {
        __auto_type arena = (*ctx).arena;
        __auto_type fn_name = tc.fn_name;
        __auto_type c_fn_name = test_emit_make_c_fn_name(arena, fn_name, tc.module_name, prefix);
        __auto_type args_display = test_emit_build_args_display_typed(arena, tc.args, (*types));
        __auto_type call_sexpr = test_emit_build_call_sexpr(arena, fn_name, tc.args, tc.needs_arena, tc.arena_position);
        __auto_type call_expr = test_emit_transpile_expr_safe(arena, tctx, call_sexpr);
        test_emit_emit(ctx, string_concat(arena, SLOP_STR("void test_"), string_concat(arena, int_to_string(arena, index), SLOP_STR("(void) {"))));
        test_emit_emit(ctx, string_concat(arena, SLOP_STR("    printf(\"  "), string_concat(arena, fn_name, string_concat(arena, SLOP_STR("("), string_concat(arena, test_emit_escape_string(arena, args_display), SLOP_STR(") -> \");"))))));
        if ((strlib_contains(call_expr, SLOP_STR("__SLOP_WILDCARD__")) || test_emit_args_have_ellipsis(tc.args))) {
            test_emit_emit(ctx, SLOP_STR("    printf(\"SKIP (wildcard args)\\n\");"));
            test_emit_emit(ctx, SLOP_STR("    tests_passed++;"));
            test_emit_emit(ctx, SLOP_STR("}"));
            test_emit_emit(ctx, SLOP_STR(""));
        } else {
            test_emit_emit(ctx, string_concat(arena, SLOP_STR("    typeof("), string_concat(arena, call_expr, string_concat(arena, SLOP_STR(") result = "), string_concat(arena, call_expr, SLOP_STR(";"))))));
            {
                __auto_type compare_info = test_emit_build_comparison_typed(arena, tc.expected, tc.return_type, prefix, (*types), tc.eq_fn, tctx);
                test_emit_emit(ctx, string_concat(arena, SLOP_STR("    if ("), string_concat(arena, compare_info.compare_expr, SLOP_STR(") {"))));
                test_emit_emit(ctx, SLOP_STR("        printf(\"PASS\\n\");"));
                test_emit_emit(ctx, SLOP_STR("        tests_passed++;"));
                test_emit_emit(ctx, SLOP_STR("    } else {"));
                {
                    __auto_type fail_str = string_concat(arena, SLOP_STR("        printf(\"FAIL (got "), string_concat(arena, compare_info.result_fmt, string_concat(arena, SLOP_STR(", expected "), string_concat(arena, compare_info.expected_fmt, string_concat(arena, SLOP_STR(")\\n\", "), string_concat(arena, compare_info.result_args, string_concat(arena, SLOP_STR(", "), string_concat(arena, compare_info.expected_args, SLOP_STR(");")))))))));
                    test_emit_emit(ctx, fail_str);
                }
                test_emit_emit(ctx, SLOP_STR("        tests_failed++;"));
                test_emit_emit(ctx, SLOP_STR("    }"));
                test_emit_emit(ctx, SLOP_STR("}"));
                test_emit_emit(ctx, SLOP_STR(""));
            }
        }
    }
}

void test_emit_emit_main_function(test_emit_EmitContext* ctx, int64_t test_count, uint8_t needs_arena) {
    {
        __auto_type arena = (*ctx).arena;
        test_emit_emit(ctx, SLOP_STR("int main(void) {"));
        if (needs_arena) {
            test_emit_emit(ctx, SLOP_STR("    // Create test arena (1MB)"));
            test_emit_emit(ctx, SLOP_STR("    test_arena_storage = slop_arena_new(1024 * 1024);"));
            test_emit_emit(ctx, SLOP_STR("    test_arena = &test_arena_storage;"));
        }
        {
            __auto_type count_str = int_to_string(arena, test_count);
            __auto_type print_stmt = string_concat(arena, SLOP_STR("    printf(\"Running "), string_concat(arena, count_str, SLOP_STR(" test(s)...\\n\");")));
            test_emit_emit(ctx, print_stmt);
        }
        {
            int64_t i = 0;
            while ((i < test_count)) {
                {
                    __auto_type call = string_concat(arena, SLOP_STR("    test_"), string_concat(arena, int_to_string(arena, i), SLOP_STR("();")));
                    test_emit_emit(ctx, call);
                }
                i = (i + 1);
            }
        }
        test_emit_emit(ctx, SLOP_STR("    printf(\"\\n%d passed, %d failed\\n\", tests_passed, tests_failed);"));
        if (needs_arena) {
            test_emit_emit(ctx, SLOP_STR("    slop_arena_free(test_arena);"));
        }
        test_emit_emit(ctx, SLOP_STR("    return tests_failed > 0 ? 1 : 0;"));
        test_emit_emit(ctx, SLOP_STR("}"));
    }
}

slop_string test_emit_make_c_fn_name(slop_arena* arena, slop_string fn_name, slop_option_string module_name, slop_string prefix) {
    {
        __auto_type c_name = ctype_to_c_name(arena, fn_name);
        __auto_type _mv_1421 = module_name;
        if (_mv_1421.has_value) {
            __auto_type mod = _mv_1421.value;
            return string_concat(arena, ctype_to_c_name(arena, mod), string_concat(arena, SLOP_STR("_"), c_name));
        } else if (!_mv_1421.has_value) {
            if ((((int64_t)(prefix.len)) > 0)) {
                return string_concat(arena, prefix, string_concat(arena, SLOP_STR("_"), c_name));
            } else {
                return c_name;
            }
        }
    }
}

slop_string test_emit_build_args_display_typed(slop_arena* arena, slop_list_types_SExpr_ptr args, type_extract_TypeRegistry types) {
    {
        __auto_type len = ((int64_t)((args).len));
        __auto_type result = SLOP_STR("");
        uint8_t first = 1;
        int64_t i = 0;
        while ((i < len)) {
            __auto_type _mv_1422 = ({ __auto_type _lst = args; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1422.has_value) {
                __auto_type arg = _mv_1422.value;
                {
                    __auto_type arg_str = parser_pretty_print(arena, arg);
                    if (first) {
                        result = arg_str;
                        first = 0;
                    } else {
                        result = string_concat(arena, result, string_concat(arena, SLOP_STR(", "), arg_str));
                    }
                }
            } else if (!_mv_1422.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

test_emit_CompareInfo test_emit_build_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_option_string return_type, slop_string prefix, type_extract_TypeRegistry types, slop_option_string eq_fn, context_TranspileContext* tctx) {
    {
        __auto_type ret_type_str = ({ __auto_type _mv = return_type; _mv.has_value ? ({ __auto_type s = _mv.value; s; }) : (SLOP_STR("Int")); });
        if (test_emit_is_union_constructor_typed(expected, types)) {
            return test_emit_build_union_comparison_typed(arena, expected, prefix, types, ret_type_str, tctx);
        } else {
            if (strlib_contains(ret_type_str, SLOP_STR("Option"))) {
                if (test_emit_is_none_value(expected)) {
                    return (test_emit_CompareInfo){SLOP_STR("!result.has_value"), SLOP_STR("%s"), SLOP_STR("result.has_value ? \"some(...)\" : \"none\""), SLOP_STR("%s"), SLOP_STR("\"none\"")};
                } else {
                    if (test_emit_is_some_value(expected)) {
                        {
                            __auto_type inner_expected = test_emit_get_some_inner_typed(arena, expected, tctx);
                            __auto_type inner_expr = test_emit_get_some_inner_expr(expected);
                            if (strlib_contains(ret_type_str, SLOP_STR("String"))) {
                                return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("result.has_value && slop_string_eq(result.value, "), string_concat(arena, inner_expected, SLOP_STR(")"))), SLOP_STR("%s"), SLOP_STR("result.has_value ? \"some(...)\" : \"none\""), SLOP_STR("%s"), SLOP_STR("\"some(...)\"")};
                            } else if (test_emit_is_record_constructor_typed(inner_expr, types)) {
                                {
                                    __auto_type record_name = test_emit_get_record_name_from_expr(inner_expr);
                                    __auto_type field_values = test_emit_get_record_field_values(arena, inner_expr);
                                    __auto_type _mv_1423 = type_extract_registry_get_record_fields(types, record_name);
                                    if (_mv_1423.has_value) {
                                        __auto_type fields = _mv_1423.value;
                                        {
                                            __auto_type expected_var_name = SLOP_STR("expected_value");
                                            __auto_type compare_expr = test_emit_build_record_field_comparisons_with_values(arena, fields, field_values, SLOP_STR("result.value"), expected_var_name);
                                            return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("({ typeof(result.value) "), string_concat(arena, expected_var_name, string_concat(arena, SLOP_STR(" = "), string_concat(arena, inner_expected, string_concat(arena, SLOP_STR("; result.has_value && "), string_concat(arena, compare_expr, SLOP_STR("; })"))))))), SLOP_STR("%s"), SLOP_STR("result.has_value ? \"some(...)\" : \"none\""), SLOP_STR("%s"), SLOP_STR("\"some(...)\"")};
                                        }
                                    } else if (!_mv_1423.has_value) {
                                        return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("({ typeof(result.value) expected_value = "), string_concat(arena, inner_expected, SLOP_STR("; result.has_value && memcmp(&result.value, &expected_value, sizeof(result.value)) == 0; })"))), SLOP_STR("%s"), SLOP_STR("result.has_value ? \"some(...)\" : \"none\""), SLOP_STR("%s"), SLOP_STR("\"some(...)\"")};
                                    }
                                }
                            } else {
                                return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("result.has_value && result.value == "), inner_expected), SLOP_STR("%s"), SLOP_STR("result.has_value ? \"some(...)\" : \"none\""), SLOP_STR("%s"), SLOP_STR("\"some(...)\"")};
                            }
                        }
                    } else {
                        {
                            __auto_type c_expected = test_emit_transpile_expr_safe(arena, tctx, expected);
                            return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("result == "), c_expected), SLOP_STR("%lld"), SLOP_STR("(long long)result"), SLOP_STR("%lld"), string_concat(arena, SLOP_STR("(long long)"), c_expected)};
                        }
                    }
                }
            } else {
                if (strlib_contains(ret_type_str, SLOP_STR("Result"))) {
                    if (test_emit_is_ok_value(expected)) {
                        {
                            __auto_type inner_expr = test_emit_get_ok_inner_expr(expected);
                            if (test_emit_contains_wildcard(inner_expr)) {
                                return (test_emit_CompareInfo){SLOP_STR("result.is_ok"), SLOP_STR("%s"), SLOP_STR("result.is_ok ? \"ok(...)\" : \"error(...)\""), SLOP_STR("%s"), SLOP_STR("\"ok(...)\"")};
                            } else {
                                {
                                    __auto_type inner_expected = test_emit_get_ok_inner_typed(arena, expected, tctx);
                                    if (test_emit_is_union_constructor_typed(inner_expr, types)) {
                                        {
                                            __auto_type expected_var = SLOP_STR("expected_ok");
                                            __auto_type variant_name = test_emit_get_union_variant_name(inner_expr);
                                            __auto_type c_variant = ctype_to_c_name(arena, variant_name);
                                            __auto_type is_string_variant = strlib_contains(strlib_to_lower(arena, variant_name), SLOP_STR("string"));
                                            return (test_emit_CompareInfo){({ __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("({ typeof(result.data.ok) ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(" = ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (inner_expected); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("; result.is_ok && result.data.ok.tag == ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".tag && ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ((is_string_variant) ? ({ ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("slop_string_eq(result.data.ok.data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(", ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(")")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); }) : ({ ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("result.data.ok.data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(" == ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); })); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("; })")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); strlib_string_build(arena, parts); }), SLOP_STR("%s"), SLOP_STR("result.is_ok ? \"ok(...)\" : \"error(...)\""), SLOP_STR("%s"), SLOP_STR("\"ok(...)\"")};
                                        }
                                    } else {
                                        if (test_emit_is_record_constructor_typed(inner_expr, types)) {
                                            {
                                                __auto_type record_name = test_emit_get_record_name_from_expr(inner_expr);
                                                __auto_type field_values = test_emit_get_record_field_values(arena, inner_expr);
                                                __auto_type _mv_1424 = type_extract_registry_get_record_fields(types, record_name);
                                                if (_mv_1424.has_value) {
                                                    __auto_type fields = _mv_1424.value;
                                                    {
                                                        __auto_type expected_var_name = SLOP_STR("expected_ok");
                                                        __auto_type compare_expr = test_emit_build_record_field_comparisons_with_values(arena, fields, field_values, SLOP_STR("result.data.ok"), expected_var_name);
                                                        return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("({ typeof(result.data.ok) "), string_concat(arena, expected_var_name, string_concat(arena, SLOP_STR(" = "), string_concat(arena, inner_expected, string_concat(arena, SLOP_STR("; result.is_ok && "), string_concat(arena, compare_expr, SLOP_STR("; })"))))))), SLOP_STR("%s"), SLOP_STR("result.is_ok ? \"ok(...)\" : \"error(...)\""), SLOP_STR("%s"), SLOP_STR("\"ok(...)\"")};
                                                    }
                                                } else if (!_mv_1424.has_value) {
                                                    return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("({ typeof(result.data.ok) expected_ok = "), string_concat(arena, inner_expected, SLOP_STR("; result.is_ok && memcmp(&result.data.ok, &expected_ok, sizeof(result.data.ok)) == 0; })"))), SLOP_STR("%s"), SLOP_STR("result.is_ok ? \"ok(...)\" : \"error(...)\""), SLOP_STR("%s"), SLOP_STR("\"ok(...)\"")};
                                                }
                                            }
                                        } else {
                                            {
                                                __auto_type first_name = test_emit_get_first_symbol_name(inner_expr);
                                                if ((test_emit_is_likely_struct_type(first_name) || string_eq(first_name, SLOP_STR("record")))) {
                                                    return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("({ typeof(result.data.ok) expected_ok = "), string_concat(arena, inner_expected, SLOP_STR("; result.is_ok && memcmp(&result.data.ok, &expected_ok, sizeof(result.data.ok)) == 0; })"))), SLOP_STR("%s"), SLOP_STR("result.is_ok ? \"ok(...)\" : \"error(...)\""), SLOP_STR("%s"), SLOP_STR("\"ok(...)\"")};
                                                } else {
                                                    return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("result.is_ok && result.data.ok == "), inner_expected), SLOP_STR("%s"), SLOP_STR("result.is_ok ? \"ok(...)\" : \"error(...)\""), SLOP_STR("%s"), SLOP_STR("\"ok(...)\"")};
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        if (test_emit_is_error_value(expected)) {
                            {
                                __auto_type inner_expected = test_emit_get_error_inner_typed(arena, expected, tctx);
                                __auto_type inner_expr = test_emit_get_ok_inner_expr(expected);
                                if (test_emit_is_union_constructor_typed(inner_expr, types)) {
                                    {
                                        __auto_type expected_var = SLOP_STR("expected_err");
                                        __auto_type variant_name = test_emit_get_union_variant_name(inner_expr);
                                        __auto_type c_variant = ctype_to_c_name(arena, variant_name);
                                        __auto_type is_string_variant = strlib_contains(strlib_to_lower(arena, variant_name), SLOP_STR("string"));
                                        return (test_emit_CompareInfo){({ __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("({ typeof(result.data.err) ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(" = ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (inner_expected); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("; !result.is_ok && result.data.err.tag == ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".tag && ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ((is_string_variant) ? ({ ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("slop_string_eq(result.data.err.data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(", ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(")")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); }) : ({ ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("result.data.err.data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(" == ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); })); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("; })")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); strlib_string_build(arena, parts); }), SLOP_STR("%s"), SLOP_STR("result.is_ok ? \"ok(...)\" : \"error(...)\""), SLOP_STR("%s"), SLOP_STR("\"error(...)\"")};
                                    }
                                } else {
                                    return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("!result.is_ok && result.data.err == "), inner_expected), SLOP_STR("%s"), SLOP_STR("result.is_ok ? \"ok(...)\" : \"error(...)\""), SLOP_STR("%s"), SLOP_STR("\"error(...)\"")};
                                }
                            }
                        } else {
                            {
                                __auto_type c_expected = test_emit_transpile_expr_safe(arena, tctx, expected);
                                return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("result == "), c_expected), SLOP_STR("%lld"), SLOP_STR("(long long)result"), SLOP_STR("%lld"), string_concat(arena, SLOP_STR("(long long)"), c_expected)};
                            }
                        }
                    }
                } else {
                    if (strlib_contains(ret_type_str, SLOP_STR("String"))) {
                        {
                            __auto_type c_expected = test_emit_transpile_expr_safe(arena, tctx, expected);
                            return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("slop_string_eq(result, "), string_concat(arena, c_expected, SLOP_STR(")"))), SLOP_STR("\\\"%.*s\\\""), SLOP_STR("(int)result.len, result.data"), SLOP_STR("\\\"%.*s\\\""), ({ __auto_type part1 = string_concat(arena, SLOP_STR("(int)("), c_expected); __auto_type part2 = string_concat(arena, part1, SLOP_STR(").len, (")); __auto_type part3 = string_concat(arena, part2, c_expected); __auto_type part4 = string_concat(arena, part3, SLOP_STR(").data")); part4; })};
                        }
                    } else {
                        if (strlib_contains(ret_type_str, SLOP_STR("List"))) {
                            return test_emit_build_list_comparison_typed(arena, expected, prefix, types, ret_type_str, eq_fn, tctx);
                        } else {
                            if (strlib_contains(ret_type_str, SLOP_STR("Bool"))) {
                                {
                                    __auto_type c_expected = test_emit_transpile_expr_safe(arena, tctx, expected);
                                    return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("result == "), c_expected), SLOP_STR("%s"), SLOP_STR("result ? \"true\" : \"false\""), SLOP_STR("%s"), string_concat(arena, c_expected, SLOP_STR(" ? \"true\" : \"false\""))};
                                }
                            } else {
                                if (strlib_contains(ret_type_str, SLOP_STR("Float"))) {
                                    {
                                        __auto_type c_expected = test_emit_transpile_expr_safe(arena, tctx, expected);
                                        {
                                            __auto_type fabs1 = string_concat(arena, SLOP_STR("fabs(result - "), c_expected);
                                            __auto_type fabs2 = string_concat(arena, fabs1, SLOP_STR(") < (fabs("));
                                            __auto_type fabs3 = string_concat(arena, fabs2, c_expected);
                                            __auto_type fabs4 = string_concat(arena, fabs3, SLOP_STR(") * 1e-6 + 1e-9)"));
                                            return (test_emit_CompareInfo){fabs4, SLOP_STR("%g"), SLOP_STR("result"), SLOP_STR("%g"), c_expected};
                                        }
                                    }
                                } else {
                                    if (test_emit_is_enum_value_typed(expected, types)) {
                                        {
                                            __auto_type c_expected = test_emit_transpile_expr_safe(arena, tctx, expected);
                                            return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("result == "), c_expected), SLOP_STR("%d"), SLOP_STR("(int)result"), SLOP_STR("%d"), string_concat(arena, SLOP_STR("(int)"), c_expected)};
                                        }
                                    } else {
                                        if (test_emit_is_record_constructor_typed(expected, types)) {
                                            return test_emit_build_record_comparison_typed(arena, expected, prefix, types, tctx);
                                        } else {
                                            {
                                                __auto_type c_expected = test_emit_transpile_expr_safe(arena, tctx, expected);
                                                return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("result == "), c_expected), SLOP_STR("%lld"), SLOP_STR("(long long)result"), SLOP_STR("%lld"), string_concat(arena, SLOP_STR("(long long)"), c_expected)};
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

test_emit_CompareInfo test_emit_build_record_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types, context_TranspileContext* tctx) {
    {
        __auto_type record_name = test_emit_get_record_name_from_expr(expected);
        __auto_type c_expected = test_emit_transpile_expr_safe(arena, tctx, expected);
        __auto_type field_values = test_emit_get_record_field_values(arena, expected);
        __auto_type decl_type = test_emit_get_record_decl_type(arena, types, record_name);
        return test_emit_build_record_comparison_inner(arena, types, record_name, field_values, c_expected, decl_type);
    }
}

test_emit_CompareInfo test_emit_build_record_comparison_inner(slop_arena* arena, type_extract_TypeRegistry types, slop_string record_name, slop_list_types_SExpr_ptr field_values, slop_string c_expected, slop_string decl_type) {
    __auto_type _mv_1425 = type_extract_registry_get_record_fields(types, record_name);
    if (_mv_1425.has_value) {
        __auto_type fields = _mv_1425.value;
        {
            __auto_type expected_var_name = SLOP_STR("expected_value");
            __auto_type compare_expr = test_emit_build_record_field_comparisons_with_values(arena, fields, field_values, SLOP_STR("result"), expected_var_name);
            return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("({ typeof(result) "), string_concat(arena, expected_var_name, string_concat(arena, SLOP_STR(" = "), string_concat(arena, c_expected, string_concat(arena, SLOP_STR("; "), string_concat(arena, compare_expr, SLOP_STR("; })"))))))), SLOP_STR("%s"), SLOP_STR("\"<record>\""), SLOP_STR("%s"), SLOP_STR("\"<expected>\"")};
        }
    } else if (!_mv_1425.has_value) {
        {
            __auto_type expected_var_name = SLOP_STR("expected_value");
            return (test_emit_CompareInfo){string_concat(arena, SLOP_STR("({ typeof(result) "), string_concat(arena, expected_var_name, string_concat(arena, SLOP_STR(" = "), string_concat(arena, c_expected, string_concat(arena, SLOP_STR("; memcmp(&result, &"), string_concat(arena, expected_var_name, SLOP_STR(", sizeof(result)) == 0; })"))))))), SLOP_STR("%s"), SLOP_STR("\"<record>\""), SLOP_STR("%s"), SLOP_STR("\"<expected>\"")};
        }
    }
}

slop_string test_emit_get_record_decl_type(slop_arena* arena, type_extract_TypeRegistry types, slop_string record_name) {
    __auto_type _mv_1426 = type_extract_registry_lookup(types, record_name);
    if (_mv_1426.has_value) {
        __auto_type entry = _mv_1426.value;
        return (*entry).c_name;
    } else if (!_mv_1426.has_value) {
        return SLOP_STR("");
    }
}

slop_string test_emit_get_record_name_from_expr(types_SExpr* expr) {
    __auto_type _mv_1427 = (*expr);
    switch (_mv_1427.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1427.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_1428 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1428.has_value) {
                        __auto_type first = _mv_1428.value;
                        if (parser_sexpr_is_symbol(first)) {
                            return parser_sexpr_get_symbol_name(first);
                        } else {
                            return SLOP_STR("");
                        }
                    } else if (!_mv_1428.has_value) {
                        return SLOP_STR("");
                    }
                }
            }
        }
        default: {
            return SLOP_STR("");
        }
    }
}

slop_list_types_SExpr_ptr test_emit_get_record_field_values(slop_arena* arena, types_SExpr* expr) {
    __auto_type _mv_1429 = (*expr);
    switch (_mv_1429.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1429.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len < 2)) {
                    return items;
                } else {
                    {
                        __auto_type result = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
                        __auto_type i = 1;
                        while ((i < len)) {
                            __auto_type _mv_1430 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1430.has_value) {
                                __auto_type val = _mv_1430.value;
                                ({ __auto_type _lst_p = &(result); __auto_type _item = (val); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            } else if (!_mv_1430.has_value) {
                            }
                            i = (i + 1);
                        }
                        return result;
                    }
                }
            }
        }
        default: {
            return ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
        }
    }
}

uint8_t test_emit_is_wildcard_expr(types_SExpr* expr) {
    __auto_type _mv_1431 = (*expr);
    switch (_mv_1431.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1431.data.sym;
            return string_eq(sym.name, SLOP_STR("_"));
        }
        default: {
            return 0;
        }
    }
}

slop_string test_emit_build_record_field_comparisons_with_values(slop_arena* arena, slop_list_type_extract_TstFieldEntry fields, slop_list_types_SExpr_ptr field_values, slop_string result_accessor, slop_string expected_var) {
    {
        __auto_type len = ((int64_t)((fields).len));
        __auto_type comp_result = SLOP_STR("1");
        int64_t i = 0;
        while ((i < len)) {
            __auto_type _mv_1432 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_type_extract_TstFieldEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1432.has_value) {
                __auto_type field = _mv_1432.value;
                {
                    __auto_type is_wildcard = ({ __auto_type _mv = ({ __auto_type _lst = field_values; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type val = _mv.value; test_emit_is_wildcard_expr(val); }) : (0); });
                    if (!(is_wildcard)) {
                        {
                            __auto_type fname = ctype_to_c_name(arena, field.name);
                            __auto_type ftype = field.type_name;
                            __auto_type field_cmp = test_emit_build_single_field_comparison_with_accessor(arena, fname, ftype, result_accessor, expected_var);
                            comp_result = string_concat(arena, comp_result, string_concat(arena, SLOP_STR(" && "), field_cmp));
                        }
                    }
                }
            } else if (!_mv_1432.has_value) {
            }
            i = (i + 1);
        }
        return comp_result;
    }
}

slop_string test_emit_build_single_field_comparison_with_accessor(slop_arena* arena, slop_string fname, slop_string ftype, slop_string result_accessor, slop_string expected_var) {
    {
        __auto_type r_field = string_concat(arena, result_accessor, string_concat(arena, SLOP_STR("."), fname));
        __auto_type e_field = string_concat(arena, expected_var, string_concat(arena, SLOP_STR("."), fname));
        if (strlib_contains(ftype, SLOP_STR("List"))) {
            return string_concat(arena, r_field, string_concat(arena, SLOP_STR(".len == "), string_concat(arena, e_field, SLOP_STR(".len"))));
        } else if ((strlib_starts_with(ftype, SLOP_STR("Option")) || strlib_starts_with(ftype, SLOP_STR("(Option")))) {
            if (strlib_contains(ftype, SLOP_STR("String"))) {
                {
                    __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("(")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (r_field); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".has_value == ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (e_field); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".has_value && (!")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (e_field); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".has_value || slop_string_eq(")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (r_field); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".value, ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (e_field); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".value)))")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    return strlib_string_build(arena, parts);
                }
            } else {
                return string_concat(arena, SLOP_STR("memcmp(&"), string_concat(arena, r_field, string_concat(arena, SLOP_STR(", &"), string_concat(arena, e_field, string_concat(arena, SLOP_STR(", sizeof("), string_concat(arena, r_field, SLOP_STR(")) == 0")))))));
            }
        } else if (string_eq(ftype, SLOP_STR("String"))) {
            return string_concat(arena, SLOP_STR("slop_string_eq("), string_concat(arena, r_field, string_concat(arena, SLOP_STR(", "), string_concat(arena, e_field, SLOP_STR(")")))));
        } else if (test_emit_is_likely_struct_type(ftype)) {
            return string_concat(arena, SLOP_STR("memcmp(&"), string_concat(arena, r_field, string_concat(arena, SLOP_STR(", &"), string_concat(arena, e_field, string_concat(arena, SLOP_STR(", sizeof("), string_concat(arena, r_field, SLOP_STR(")) == 0")))))));
        } else {
            return string_concat(arena, r_field, string_concat(arena, SLOP_STR(" == "), e_field));
        }
    }
}

uint8_t test_emit_is_likely_struct_type(slop_string type_name) {
    if ((string_len(type_name) < 1)) {
        return 0;
    } else {
        {
            __auto_type first_char = strlib_char_at(type_name, 0);
            if (!(((first_char >= 65) && (first_char <= 90)))) {
                return 0;
            } else {
                if (string_eq(type_name, SLOP_STR("Int"))) {
                    return 0;
                } else if (string_eq(type_name, SLOP_STR("Bool"))) {
                    return 0;
                } else if (string_eq(type_name, SLOP_STR("Float"))) {
                    return 0;
                } else if (string_eq(type_name, SLOP_STR("F32"))) {
                    return 0;
                } else if (string_eq(type_name, SLOP_STR("U8"))) {
                    return 0;
                } else if (string_eq(type_name, SLOP_STR("U16"))) {
                    return 0;
                } else if (string_eq(type_name, SLOP_STR("U32"))) {
                    return 0;
                } else if (string_eq(type_name, SLOP_STR("U64"))) {
                    return 0;
                } else if (string_eq(type_name, SLOP_STR("Char"))) {
                    return 0;
                } else if (string_eq(type_name, SLOP_STR("String"))) {
                    return 0;
                } else if (string_eq(type_name, SLOP_STR("Unit"))) {
                    return 0;
                } else if (string_eq(type_name, SLOP_STR("Void"))) {
                    return 0;
                } else {
                    return 1;
                }
            }
        }
    }
}

slop_string test_emit_get_first_symbol_name(types_SExpr* expr) {
    __auto_type _mv_1433 = (*expr);
    switch (_mv_1433.tag) {
        case types_SExpr_sym:
        {
            __auto_type s = _mv_1433.data.sym;
            return s.name;
        }
        case types_SExpr_lst:
        {
            __auto_type l = _mv_1433.data.lst;
            if ((((int64_t)((l.items).len)) > 0)) {
                __auto_type _mv_1434 = ({ __auto_type _lst = l.items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1434.has_value) {
                    __auto_type first = _mv_1434.value;
                    __auto_type _mv_1435 = (*first);
                    switch (_mv_1435.tag) {
                        case types_SExpr_sym:
                        {
                            __auto_type s = _mv_1435.data.sym;
                            return s.name;
                        }
                        case types_SExpr_lst:
                        {
                            __auto_type _ = _mv_1435.data.lst;
                            return SLOP_STR("");
                        }
                        case types_SExpr_num:
                        {
                            __auto_type _ = _mv_1435.data.num;
                            return SLOP_STR("");
                        }
                        case types_SExpr_str:
                        {
                            __auto_type _ = _mv_1435.data.str;
                            return SLOP_STR("");
                        }
                    }
                } else if (!_mv_1434.has_value) {
                    return SLOP_STR("");
                }
            } else {
                return SLOP_STR("");
            }
        }
        case types_SExpr_num:
        {
            __auto_type _ = _mv_1433.data.num;
            return SLOP_STR("");
        }
        case types_SExpr_str:
        {
            __auto_type _ = _mv_1433.data.str;
            return SLOP_STR("");
        }
    }
}

test_emit_CompareInfo test_emit_build_union_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types, slop_string ret_type_str, context_TranspileContext* tctx) {
    {
        __auto_type c_expected = test_emit_transpile_expr_safe(arena, tctx, expected);
        __auto_type expected_var_name = SLOP_STR("expected_value");
        __auto_type variant_name = test_emit_get_union_variant_name(expected);
        __auto_type c_variant = ctype_to_c_name(arena, variant_name);
        {
            __auto_type payload_cmp = ({ __auto_type _mv = type_extract_registry_get_variant_info(types, variant_name); _mv.has_value ? ({ __auto_type ve = _mv.value; ({ __auto_type payload_type = ve.payload_type; test_emit_build_union_payload_comparison(arena, payload_type, c_variant, expected_var_name, types); }); }) : (string_concat(arena, SLOP_STR("memcmp(&result.data, &"), string_concat(arena, expected_var_name, SLOP_STR(".data, sizeof(result.data)) == 0")))); });
            return (test_emit_CompareInfo){({ __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("({ typeof(result) ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(" = ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_expected); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("; result.tag == ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".tag && ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (payload_cmp); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("; })")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); strlib_string_build(arena, parts); }), SLOP_STR("%s"), SLOP_STR("\"<union>\""), SLOP_STR("%s"), SLOP_STR("\"<expected>\"")};
        }
    }
}

slop_string test_emit_build_union_payload_comparison(slop_arena* arena, slop_string payload_type, slop_string c_variant, slop_string expected_var, type_extract_TypeRegistry types) {
    if (string_eq(payload_type, SLOP_STR(""))) {
        return SLOP_STR("1");
    } else if (string_eq(payload_type, SLOP_STR("String"))) {
        return string_concat(arena, SLOP_STR("slop_string_eq(result.data."), string_concat(arena, c_variant, string_concat(arena, SLOP_STR(", "), string_concat(arena, expected_var, string_concat(arena, SLOP_STR(".data."), string_concat(arena, c_variant, SLOP_STR(")")))))));
    } else {
        __auto_type _mv_1436 = type_extract_registry_get_record_fields(types, payload_type);
        if (_mv_1436.has_value) {
            __auto_type fields = _mv_1436.value;
            return test_emit_build_union_record_payload_comparison(arena, fields, c_variant, expected_var);
        } else if (!_mv_1436.has_value) {
            return string_concat(arena, SLOP_STR("memcmp(&result.data."), string_concat(arena, c_variant, string_concat(arena, SLOP_STR(", &"), string_concat(arena, expected_var, string_concat(arena, SLOP_STR(".data."), string_concat(arena, c_variant, string_concat(arena, SLOP_STR(", sizeof(result.data."), string_concat(arena, c_variant, SLOP_STR("))")))))))));
        }
    }
}

slop_string test_emit_build_union_record_payload_comparison(slop_arena* arena, slop_list_type_extract_TstFieldEntry fields, slop_string c_variant, slop_string expected_var) {
    {
        __auto_type len = ((int64_t)((fields).len));
        __auto_type result = SLOP_STR("1");
        int64_t i = 0;
        while ((i < len)) {
            __auto_type _mv_1437 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_type_extract_TstFieldEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1437.has_value) {
                __auto_type field = _mv_1437.value;
                {
                    __auto_type fname = ctype_to_c_name(arena, field.name);
                    __auto_type ftype = field.type_name;
                    __auto_type field_cmp = test_emit_build_union_field_comparison(arena, fname, ftype, c_variant, expected_var);
                    result = string_concat(arena, result, string_concat(arena, SLOP_STR(" && "), field_cmp));
                }
            } else if (!_mv_1437.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_string test_emit_build_union_field_comparison(slop_arena* arena, slop_string fname, slop_string ftype, slop_string c_variant, slop_string expected_var) {
    {
        __auto_type result_path = string_concat(arena, SLOP_STR("result.data."), string_concat(arena, c_variant, string_concat(arena, SLOP_STR("."), fname)));
        __auto_type expected_path = string_concat(arena, expected_var, string_concat(arena, SLOP_STR(".data."), string_concat(arena, c_variant, string_concat(arena, SLOP_STR("."), fname))));
        if (string_eq(ftype, SLOP_STR("String"))) {
            return string_concat(arena, SLOP_STR("slop_string_eq("), string_concat(arena, result_path, string_concat(arena, SLOP_STR(", "), string_concat(arena, expected_path, SLOP_STR(")")))));
        } else if ((string_eq(ftype, SLOP_STR("(Option String)")) || string_eq(ftype, SLOP_STR("Option String")))) {
            {
                __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("(")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                ({ __auto_type _lst_p = &(parts); __auto_type _item = (result_path); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".has_value == ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_path); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".has_value && (!")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                ({ __auto_type _lst_p = &(parts); __auto_type _item = (result_path); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".has_value || slop_string_eq(")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                ({ __auto_type _lst_p = &(parts); __auto_type _item = (result_path); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".value, ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_path); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".value)))")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                return strlib_string_build(arena, parts);
            }
        } else if (strlib_contains(ftype, SLOP_STR("List"))) {
            return string_concat(arena, result_path, string_concat(arena, SLOP_STR(".len == "), string_concat(arena, expected_path, SLOP_STR(".len"))));
        } else {
            return string_concat(arena, result_path, string_concat(arena, SLOP_STR(" == "), expected_path));
        }
    }
}

uint8_t test_emit_is_union_constructor_typed(types_SExpr* expr, type_extract_TypeRegistry types) {
    __auto_type _mv_1438 = (*expr);
    switch (_mv_1438.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1438.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return 0;
                } else {
                    __auto_type _mv_1439 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1439.has_value) {
                        __auto_type first = _mv_1439.value;
                        if (parser_sexpr_is_symbol(first)) {
                            {
                                __auto_type name = parser_sexpr_get_symbol_name(first);
                                if (string_eq(name, SLOP_STR("union-new"))) {
                                    return (((int64_t)((items).len)) >= 3);
                                } else {
                                    if (((string_eq(name, SLOP_STR("none"))) || (string_eq(name, SLOP_STR("some"))) || (string_eq(name, SLOP_STR("ok"))) || (string_eq(name, SLOP_STR("error"))))) {
                                        return 0;
                                    } else {
                                        __auto_type _mv_1440 = type_extract_registry_lookup_variant(types, name);
                                        if (_mv_1440.has_value) {
                                            __auto_type _ = _mv_1440.value;
                                            return 1;
                                        } else if (!_mv_1440.has_value) {
                                            return 0;
                                        }
                                    }
                                }
                            }
                        } else {
                            return 0;
                        }
                    } else if (!_mv_1439.has_value) {
                        return 0;
                    }
                }
            }
        }
        default: {
            return 0;
        }
    }
}

slop_string test_emit_get_union_variant_name(types_SExpr* expr) {
    __auto_type _mv_1441 = (*expr);
    switch (_mv_1441.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1441.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_1442 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1442.has_value) {
                        __auto_type first = _mv_1442.value;
                        if (parser_sexpr_is_symbol(first)) {
                            {
                                __auto_type name = parser_sexpr_get_symbol_name(first);
                                if (string_eq(name, SLOP_STR("union-new"))) {
                                    __auto_type _mv_1443 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_1443.has_value) {
                                        __auto_type variant_expr = _mv_1443.value;
                                        if (parser_sexpr_is_symbol(variant_expr)) {
                                            return parser_sexpr_get_symbol_name(variant_expr);
                                        } else {
                                            return SLOP_STR("");
                                        }
                                    } else if (!_mv_1443.has_value) {
                                        return SLOP_STR("");
                                    }
                                } else {
                                    return name;
                                }
                            }
                        } else {
                            return SLOP_STR("");
                        }
                    } else if (!_mv_1442.has_value) {
                        return SLOP_STR("");
                    }
                }
            }
        }
        default: {
            return SLOP_STR("");
        }
    }
}

uint8_t test_emit_is_enum_value_typed(types_SExpr* expr, type_extract_TypeRegistry types) {
    __auto_type _mv_1444 = (*expr);
    switch (_mv_1444.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1444.data.sym;
            {
                __auto_type name = sym.name;
                if (strlib_starts_with(name, SLOP_STR("'"))) {
                    {
                        __auto_type variant_name = test_emit_emit_string_slice(name, 1);
                        __auto_type _mv_1445 = type_extract_registry_lookup_enum_value(types, variant_name);
                        if (_mv_1445.has_value) {
                            __auto_type _ = _mv_1445.value;
                            return 1;
                        } else if (!_mv_1445.has_value) {
                            return 0;
                        }
                    }
                } else {
                    return 0;
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1444.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 2)) {
                    return 0;
                } else {
                    __auto_type _mv_1446 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1446.has_value) {
                        __auto_type first = _mv_1446.value;
                        if ((parser_sexpr_is_symbol(first) && string_eq(parser_sexpr_get_symbol_name(first), SLOP_STR("quote")))) {
                            __auto_type _mv_1447 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1447.has_value) {
                                __auto_type quoted = _mv_1447.value;
                                if (parser_sexpr_is_symbol(quoted)) {
                                    __auto_type _mv_1448 = type_extract_registry_lookup_enum_value(types, parser_sexpr_get_symbol_name(quoted));
                                    if (_mv_1448.has_value) {
                                        __auto_type _ = _mv_1448.value;
                                        return 1;
                                    } else if (!_mv_1448.has_value) {
                                        return 0;
                                    }
                                } else {
                                    return 0;
                                }
                            } else if (!_mv_1447.has_value) {
                                return 0;
                            }
                        } else {
                            return 0;
                        }
                    } else if (!_mv_1446.has_value) {
                        return 0;
                    }
                }
            }
        }
        default: {
            return 0;
        }
    }
}

uint8_t test_emit_is_record_constructor_typed(types_SExpr* expr, type_extract_TypeRegistry types) {
    __auto_type _mv_1449 = (*expr);
    switch (_mv_1449.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1449.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return 0;
                } else {
                    __auto_type _mv_1450 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1450.has_value) {
                        __auto_type first = _mv_1450.value;
                        if (parser_sexpr_is_symbol(first)) {
                            {
                                __auto_type name = parser_sexpr_get_symbol_name(first);
                                if ((string_eq(name, SLOP_STR("none")) || (string_eq(name, SLOP_STR("some")) || (string_eq(name, SLOP_STR("ok")) || (string_eq(name, SLOP_STR("error")) || string_eq(name, SLOP_STR("list"))))))) {
                                    return 0;
                                } else {
                                    __auto_type _mv_1451 = type_extract_registry_lookup(types, name);
                                    if (_mv_1451.has_value) {
                                        __auto_type entry = _mv_1451.value;
                                        return type_extract_registry_is_record(types, name);
                                    } else if (!_mv_1451.has_value) {
                                        return 0;
                                    }
                                }
                            }
                        } else {
                            return 0;
                        }
                    } else if (!_mv_1450.has_value) {
                        return 0;
                    }
                }
            }
        }
        default: {
            return 0;
        }
    }
}

slop_string test_emit_emit_string_slice(slop_string s, int64_t start) {
    if ((start >= ((int64_t)(s.len)))) {
        return SLOP_STR("");
    } else {
        return (slop_string){.len = ((uint64_t)((s.len - ((uint64_t)(start))))), .data = ((uint8_t*)((((int64_t)(s.data)) + start)))};
    }
}

slop_string test_emit_get_some_inner_typed(slop_arena* arena, types_SExpr* expr, context_TranspileContext* tctx) {
    if ((parser_sexpr_list_len(expr) > 1)) {
        __auto_type _mv_1452 = parser_sexpr_list_get(expr, 1);
        if (_mv_1452.has_value) {
            __auto_type inner = _mv_1452.value;
            return test_emit_transpile_expr_safe(arena, tctx, inner);
        } else if (!_mv_1452.has_value) {
            return SLOP_STR("0");
        }
    } else {
        return SLOP_STR("0");
    }
}

slop_string test_emit_get_ok_inner_typed(slop_arena* arena, types_SExpr* expr, context_TranspileContext* tctx) {
    return test_emit_get_some_inner_typed(arena, expr, tctx);
}

slop_string test_emit_get_error_inner_typed(slop_arena* arena, types_SExpr* expr, context_TranspileContext* tctx) {
    return test_emit_get_some_inner_typed(arena, expr, tctx);
}

types_SExpr* test_emit_get_some_inner_expr(types_SExpr* expected) {
    __auto_type _mv_1453 = (*expected);
    switch (_mv_1453.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1453.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) > 1)) {
                    __auto_type _mv_1454 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1454.has_value) {
                        __auto_type inner = _mv_1454.value;
                        return inner;
                    } else if (!_mv_1454.has_value) {
                        return expected;
                    }
                } else {
                    return expected;
                }
            }
        }
        default: {
            return expected;
        }
    }
}

types_SExpr* test_emit_get_ok_inner_expr(types_SExpr* expected) {
    __auto_type _mv_1455 = (*expected);
    switch (_mv_1455.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1455.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) > 1)) {
                    __auto_type _mv_1456 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1456.has_value) {
                        __auto_type inner = _mv_1456.value;
                        return inner;
                    } else if (!_mv_1456.has_value) {
                        return expected;
                    }
                } else {
                    return expected;
                }
            }
        }
        default: {
            return expected;
        }
    }
}

uint8_t test_emit_is_none_value(types_SExpr* expr) {
    __auto_type _mv_1457 = (*expr);
    switch (_mv_1457.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1457.data.sym;
            return string_eq(sym.name, SLOP_STR("none"));
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1457.data.lst;
            {
                __auto_type items = lst.items;
                return ((((int64_t)((items).len)) == 1) && ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type first = _mv.value; (parser_sexpr_is_symbol(first) && string_eq(parser_sexpr_get_symbol_name(first), SLOP_STR("none"))); }) : (0); }));
            }
        }
        default: {
            return 0;
        }
    }
}

uint8_t test_emit_is_some_value(types_SExpr* expr) {
    return parser_is_form(expr, SLOP_STR("some"));
}

uint8_t test_emit_is_ok_value(types_SExpr* expr) {
    return parser_is_form(expr, SLOP_STR("ok"));
}

uint8_t test_emit_is_error_value(types_SExpr* expr) {
    return parser_is_form(expr, SLOP_STR("error"));
}

slop_string test_emit_extract_list_element_type(slop_arena* arena, slop_string list_type_str) {
    {
        __auto_type len = ((int64_t)(list_type_str.len));
        if ((len < 7)) {
            return SLOP_STR("");
        } else {
            {
                __auto_type start = 6;
                __auto_type end_offset = 1;
                if ((((list_type_str.data[0] == 40)) && ((list_type_str.data[1] == 76)) && ((list_type_str.data[2] == 105)) && ((list_type_str.data[3] == 115)) && ((list_type_str.data[4] == 116)) && ((list_type_str.data[5] == 32)))) {
                    {
                        __auto_type elem_len = ((len - start) - end_offset);
                        __auto_type buf = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (elem_len + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
                        {
                            int64_t i = 0;
                            while ((i < elem_len)) {
                                buf[i] = list_type_str.data[(start + i)];
                                i = (i + 1);
                            }
                        }
                        buf[elem_len] = 0;
                        return (slop_string){.len = ((uint64_t)(elem_len)), .data = buf};
                    }
                } else {
                    return SLOP_STR("");
                }
            }
        }
    }
}

slop_string test_emit_build_eq_function_name(slop_arena* arena, slop_string type_name, slop_string prefix, type_extract_TypeRegistry types) {
    {
        __auto_type type_c = strlib_to_lower(arena, ctype_to_c_name(arena, type_name));
        __auto_type _mv_1458 = type_extract_registry_lookup_import(types, type_name);
        if (_mv_1458.has_value) {
            __auto_type mod_name = _mv_1458.value;
            {
                __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                ({ __auto_type _lst_p = &(parts); __auto_type _item = (ctype_to_c_name(arena, mod_name)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("_")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                ({ __auto_type _lst_p = &(parts); __auto_type _item = (type_c); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("_eq")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                return strlib_string_build(arena, parts);
            }
        } else if (!_mv_1458.has_value) {
            if ((((int64_t)(prefix.len)) > 0)) {
                {
                    __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (prefix); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("_")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (type_c); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("_eq")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    return strlib_string_build(arena, parts);
                }
            } else {
                {
                    __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (type_c); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("_eq")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    return strlib_string_build(arena, parts);
                }
            }
        }
    }
}

test_emit_CompareInfo test_emit_build_list_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types, slop_string ret_type_str, slop_option_string eq_fn, context_TranspileContext* tctx) {
    __auto_type _mv_1459 = (*expected);
    switch (_mv_1459.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1459.data.lst;
            {
                __auto_type elements = lst.items;
                __auto_type total_count = ((int64_t)((elements).len));
                {
                    __auto_type start_idx = ((((total_count > 0) && ({ __auto_type _mv = ({ __auto_type _lst = elements; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type first_elem = _mv.value; (parser_sexpr_is_symbol(first_elem) && string_eq(parser_sexpr_get_symbol_name(first_elem), SLOP_STR("list"))); }) : (0); }))) ? 1 : 0);
                    __auto_type elem_count = (total_count - start_idx);
                    if ((elem_count == 0)) {
                        return (test_emit_CompareInfo){SLOP_STR("result.len == 0"), SLOP_STR("len=%lld"), SLOP_STR("(long long)result.len"), SLOP_STR("len=%lld"), SLOP_STR("0LL")};
                    } else {
                        {
                            __auto_type has_wildcard = 0;
                            __auto_type j = start_idx;
                            while ((j < total_count)) {
                                __auto_type _mv_1460 = ({ __auto_type _lst = elements; size_t _idx = (size_t)j; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1460.has_value) {
                                    __auto_type elem = _mv_1460.value;
                                    if (test_emit_is_wildcard_expr(elem)) {
                                        has_wildcard = 1;
                                    }
                                } else if (!_mv_1460.has_value) {
                                }
                                j = (j + 1);
                            }
                            {
                                __auto_type len_str = int_to_string(arena, elem_count);
                                if (has_wildcard) {
                                    return (test_emit_CompareInfo){({ __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("result.len == ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (len_str); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); strlib_string_build(arena, parts); }), SLOP_STR("len=%lld"), SLOP_STR("(long long)result.len"), SLOP_STR("len=%lld"), ({ __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("(long long)")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (len_str); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); strlib_string_build(arena, parts); })};
                                } else {
                                    {
                                        __auto_type elem_type = test_emit_extract_list_element_type(arena, ret_type_str);
                                        __auto_type is_complex = (type_extract_registry_is_record(types, elem_type) || type_extract_registry_is_union(types, elem_type));
                                        {
                                            __auto_type arr_init = SLOP_STR("{");
                                            __auto_type i = start_idx;
                                            __auto_type first = 1;
                                            while ((i < total_count)) {
                                                __auto_type _mv_1461 = ({ __auto_type _lst = elements; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1461.has_value) {
                                                    __auto_type elem = _mv_1461.value;
                                                    {
                                                        __auto_type elem_c = test_emit_transpile_expr_safe(arena, tctx, elem);
                                                        if (first) {
                                                            arr_init = string_concat(arena, arr_init, elem_c);
                                                            first = 0;
                                                        } else {
                                                            arr_init = string_concat(arena, arr_init, string_concat(arena, SLOP_STR(", "), elem_c));
                                                        }
                                                    }
                                                } else if (!_mv_1461.has_value) {
                                                }
                                                i = (i + 1);
                                            }
                                            arr_init = string_concat(arena, arr_init, SLOP_STR("}"));
                                            if (!(is_complex)) {
                                                {
                                                    __auto_type cmp_parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                                                    ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (SLOP_STR("(result.len == ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                    ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (len_str); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                    ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (SLOP_STR(" && memcmp(result.data, (typeof(*result.data)[])")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                    ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (arr_init); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                    ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (SLOP_STR(", sizeof(typeof(*result.data)) * ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                    ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (len_str); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                    ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (SLOP_STR(") == 0)")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                    return (test_emit_CompareInfo){strlib_string_build(arena, cmp_parts), SLOP_STR("len=%lld"), SLOP_STR("(long long)result.len"), SLOP_STR("len=%lld"), ({ __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("(long long)")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (len_str); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); strlib_string_build(arena, parts); })};
                                                }
                                            } else {
                                                {
                                                    __auto_type eq_fn_name = ({ __auto_type _mv = eq_fn; _mv.has_value ? ({ __auto_type fn_name = _mv.value; test_emit_prefix_symbol(arena, fn_name, prefix, types); }) : (test_emit_build_eq_function_name(arena, elem_type, prefix, types)); });
                                                    {
                                                        __auto_type cmp_parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                                                        ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (SLOP_STR("({ typeof(*result.data) _expected[] = ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                        ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (arr_init); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                        ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (SLOP_STR("; result.len == ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                        ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (len_str); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                        {
                                                            __auto_type k = 0;
                                                            while ((k < elem_count)) {
                                                                ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (SLOP_STR(" && ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                                ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (eq_fn_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                                ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (SLOP_STR("(result.data[")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                                ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (int_to_string(arena, k)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                                ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (SLOP_STR("], _expected[")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                                ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (int_to_string(arena, k)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                                ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (SLOP_STR("])")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                                k = (k + 1);
                                                            }
                                                        }
                                                        ({ __auto_type _lst_p = &(cmp_parts); __auto_type _item = (SLOP_STR("; })")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                        return (test_emit_CompareInfo){strlib_string_build(arena, cmp_parts), SLOP_STR("len=%lld"), SLOP_STR("(long long)result.len"), SLOP_STR("len=%lld"), ({ __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("(long long)")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (len_str); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); strlib_string_build(arena, parts); })};
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        default: {
            return (test_emit_CompareInfo){SLOP_STR("result.len == 0"), SLOP_STR("len=%lld"), SLOP_STR("(long long)result.len"), SLOP_STR("len=%lld"), SLOP_STR("0LL")};
        }
    }
}

context_TranspileContext* test_emit_init_transpile_context(slop_arena* arena, slop_list_types_SExpr_ptr ast, slop_string module_name) {
    {
        __auto_type tctx = context_context_new(arena);
        context_ctx_set_single_output_mode(tctx, 1);
        context_ctx_set_skip_trampoline_generation(tctx, 1);
        if ((((int64_t)(module_name.len)) > 0)) {
            context_ctx_set_module(tctx, (slop_option_string){.has_value = 1, .value = module_name});
            context_ctx_set_prefixing(tctx, 1);
        }
        context_ctx_bind_var(tctx, (context_VarEntry){SLOP_STR("arena"), SLOP_STR("test_arena"), SLOP_STR("slop_arena*"), SLOP_STR("Arena"), 1, 0, 0, SLOP_STR(""), SLOP_STR("")});
        if ((((int64_t)((ast).len)) > 0)) {
            __auto_type _mv_1462 = ({ __auto_type _lst = ast; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1462.has_value) {
                __auto_type first_expr = _mv_1462.value;
                if (parser_is_form(first_expr, SLOP_STR("module"))) {
                    {
                        __auto_type mod_len = parser_sexpr_list_len(first_expr);
                        __auto_type body_forms = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
                        __auto_type i = 2;
                        if ((i < mod_len)) {
                            __auto_type _mv_1463 = parser_sexpr_list_get(first_expr, i);
                            if (_mv_1463.has_value) {
                                __auto_type maybe_export = _mv_1463.value;
                                if (parser_is_form(maybe_export, SLOP_STR("export"))) {
                                    i = (i + 1);
                                }
                            } else if (!_mv_1463.has_value) {
                            }
                        }
                        while ((i < mod_len)) {
                            __auto_type _mv_1464 = parser_sexpr_list_get(first_expr, i);
                            if (_mv_1464.has_value) {
                                __auto_type form = _mv_1464.value;
                                if (!((parser_is_form(form, SLOP_STR("import")) || parser_is_form(form, SLOP_STR("@doc"))))) {
                                    ({ __auto_type _lst_p = &(body_forms); __auto_type _item = (form); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                }
                            } else if (!_mv_1464.has_value) {
                            }
                            i = (i + 1);
                        }
                        transpiler_prescan_module(tctx, body_forms);
                        test_emit_register_all_field_types(tctx, body_forms);
                    }
                }
            } else if (!_mv_1462.has_value) {
            }
        }
        return tctx;
    }
}

void test_emit_init_transpile_context_for_imports(slop_arena* arena, context_TranspileContext* tctx, slop_list_types_SExpr_ptr import_ast, slop_string import_mod_name) {
    {
        __auto_type saved_module = ({ __auto_type _mv = context_ctx_get_module(tctx); _mv.has_value ? ({ __auto_type m = _mv.value; m; }) : (SLOP_STR("")); });
        if ((((int64_t)(import_mod_name.len)) > 0)) {
            context_ctx_set_module(tctx, (slop_option_string){.has_value = 1, .value = import_mod_name});
        }
        if ((((int64_t)((import_ast).len)) > 0)) {
            __auto_type _mv_1465 = ({ __auto_type _lst = import_ast; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1465.has_value) {
                __auto_type first_expr = _mv_1465.value;
                if (parser_is_form(first_expr, SLOP_STR("module"))) {
                    {
                        __auto_type mod_len = parser_sexpr_list_len(first_expr);
                        __auto_type body_forms = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
                        __auto_type i = 2;
                        if ((i < mod_len)) {
                            __auto_type _mv_1466 = parser_sexpr_list_get(first_expr, i);
                            if (_mv_1466.has_value) {
                                __auto_type maybe_export = _mv_1466.value;
                                if (parser_is_form(maybe_export, SLOP_STR("export"))) {
                                    i = (i + 1);
                                }
                            } else if (!_mv_1466.has_value) {
                            }
                        }
                        while ((i < mod_len)) {
                            __auto_type _mv_1467 = parser_sexpr_list_get(first_expr, i);
                            if (_mv_1467.has_value) {
                                __auto_type form = _mv_1467.value;
                                ({ __auto_type _lst_p = &(body_forms); __auto_type _item = (form); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            } else if (!_mv_1467.has_value) {
                            }
                            i = (i + 1);
                        }
                        transpiler_prescan_module(tctx, body_forms);
                        test_emit_register_all_field_types(tctx, body_forms);
                    }
                }
            } else if (!_mv_1465.has_value) {
            }
        }
        if ((((int64_t)(saved_module.len)) > 0)) {
            context_ctx_set_module(tctx, (slop_option_string){.has_value = 1, .value = saved_module});
        } else {
            context_ctx_set_module(tctx, ((slop_option_string){.has_value = false}));
        }
    }
}

void test_emit_re_prescan_main_module(slop_arena* arena, context_TranspileContext* tctx, slop_list_types_SExpr_ptr ast) {
    if ((((int64_t)((ast).len)) > 0)) {
        __auto_type _mv_1468 = ({ __auto_type _lst = ast; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1468.has_value) {
            __auto_type first_expr = _mv_1468.value;
            if (parser_is_form(first_expr, SLOP_STR("module"))) {
                {
                    __auto_type mod_len = parser_sexpr_list_len(first_expr);
                    __auto_type body_forms = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
                    __auto_type i = 2;
                    if ((i < mod_len)) {
                        __auto_type _mv_1469 = parser_sexpr_list_get(first_expr, i);
                        if (_mv_1469.has_value) {
                            __auto_type maybe_export = _mv_1469.value;
                            if (parser_is_form(maybe_export, SLOP_STR("export"))) {
                                i = (i + 1);
                            }
                        } else if (!_mv_1469.has_value) {
                        }
                    }
                    while ((i < mod_len)) {
                        __auto_type _mv_1470 = parser_sexpr_list_get(first_expr, i);
                        if (_mv_1470.has_value) {
                            __auto_type form = _mv_1470.value;
                            if (!((parser_is_form(form, SLOP_STR("import")) || parser_is_form(form, SLOP_STR("@doc"))))) {
                                ({ __auto_type _lst_p = &(body_forms); __auto_type _item = (form); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            }
                        } else if (!_mv_1470.has_value) {
                        }
                        i = (i + 1);
                    }
                    transpiler_prescan_module(tctx, body_forms);
                    test_emit_register_all_field_types(tctx, body_forms);
                }
            }
        } else if (!_mv_1468.has_value) {
        }
    }
}

void test_emit_register_all_field_types(context_TranspileContext* tctx, slop_list_types_SExpr_ptr body_forms) {
    {
        __auto_type len = ((int64_t)((body_forms).len));
        int64_t i = 0;
        while ((i < len)) {
            __auto_type _mv_1471 = ({ __auto_type _lst = body_forms; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1471.has_value) {
                __auto_type form = _mv_1471.value;
                if (parser_is_form(form, SLOP_STR("type"))) {
                    test_emit_register_type_fields(tctx, form);
                }
            } else if (!_mv_1471.has_value) {
            }
            i = (i + 1);
        }
    }
}

void test_emit_register_type_fields(context_TranspileContext* tctx, types_SExpr* type_form) {
    if ((parser_sexpr_list_len(type_form) >= 3)) {
        __auto_type _mv_1472 = parser_sexpr_list_get(type_form, 1);
        if (_mv_1472.has_value) {
            __auto_type name_expr = _mv_1472.value;
            if (parser_sexpr_is_symbol(name_expr)) {
                {
                    __auto_type type_name = parser_sexpr_get_symbol_name(name_expr);
                    __auto_type _mv_1473 = parser_sexpr_list_get(type_form, 2);
                    if (_mv_1473.has_value) {
                        __auto_type def_expr = _mv_1473.value;
                        if (parser_is_form(def_expr, SLOP_STR("record"))) {
                            {
                                __auto_type field_count = parser_sexpr_list_len(def_expr);
                                __auto_type j = 1;
                                while ((j < field_count)) {
                                    __auto_type _mv_1474 = parser_sexpr_list_get(def_expr, j);
                                    if (_mv_1474.has_value) {
                                        __auto_type field_def = _mv_1474.value;
                                        if ((parser_sexpr_list_len(field_def) >= 2)) {
                                            __auto_type _mv_1475 = parser_sexpr_list_get(field_def, 0);
                                            if (_mv_1475.has_value) {
                                                __auto_type field_name_expr = _mv_1475.value;
                                                if (parser_sexpr_is_symbol(field_name_expr)) {
                                                    {
                                                        __auto_type field_name = parser_sexpr_get_symbol_name(field_name_expr);
                                                        __auto_type _mv_1476 = parser_sexpr_list_get(field_def, 1);
                                                        if (_mv_1476.has_value) {
                                                            __auto_type field_type_expr = _mv_1476.value;
                                                            {
                                                                __auto_type arena = (*tctx).arena;
                                                                __auto_type c_type = context_to_c_type_prefixed(tctx, field_type_expr);
                                                                __auto_type slop_type = parser_pretty_print(arena, field_type_expr);
                                                                __auto_type is_ptr = ((parser_sexpr_is_symbol(field_type_expr)) ? strlib_starts_with(parser_sexpr_get_symbol_name(field_type_expr), SLOP_STR("Ptr")) : 0);
                                                                context_ctx_register_field_type(tctx, type_name, field_name, c_type, slop_type, is_ptr);
                                                                {
                                                                    __auto_type c_type_name = context_ctx_prefix_type(tctx, type_name);
                                                                    if (!(string_eq(c_type_name, type_name))) {
                                                                        context_ctx_register_field_type(tctx, c_type_name, field_name, c_type, slop_type, is_ptr);
                                                                    }
                                                                }
                                                            }
                                                        } else if (!_mv_1476.has_value) {
                                                        }
                                                    }
                                                }
                                            } else if (!_mv_1475.has_value) {
                                            }
                                        }
                                    } else if (!_mv_1474.has_value) {
                                    }
                                    j = (j + 1);
                                }
                            }
                        }
                    } else if (!_mv_1473.has_value) {
                    }
                }
            }
        } else if (!_mv_1472.has_value) {
        }
    }
}

