#include "../runtime/slop_runtime.h"
#include "slop_expr.h"

slop_string expr_escape_c_string(context_TranspileContext* ctx, slop_string s);
uint8_t expr_is_binop(slop_string op);
uint8_t expr_is_comparison_op(slop_string op);
uint8_t expr_is_unop(slop_string op);
slop_option_string expr_extract_symbol_name(types_SExpr* expr);
slop_string expr_transpile_literal(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_transpile_symbol(context_TranspileContext* ctx, slop_string name);
slop_string expr_get_prefixed_enum_value(context_TranspileContext* ctx, slop_string enum_name, slop_string variant_name);
slop_string expr_binop_to_c(slop_string op);
slop_string expr_transpile_binop(context_TranspileContext* ctx, slop_string op, slop_string left, slop_string right);
slop_string expr_transpile_variadic_binop(context_TranspileContext* ctx, slop_string op, slop_list_types_SExpr_ptr items, int64_t start_idx);
slop_string expr_get_builtin_type_c_name(slop_string type_name);
uint8_t expr_is_pointer_type_expr(types_SExpr* type_expr);
uint8_t expr_is_string_literal(types_SExpr* expr);
slop_string expr_transpile_builtin_constructor(context_TranspileContext* ctx, slop_string type_name, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_call(context_TranspileContext* ctx, slop_string fn_name, slop_string args);
slop_string expr_get_base_function_name(slop_arena* arena, slop_string fn_name);
slop_string expr_get_module_from_qualified_name(slop_arena* arena, slop_string fn_name);
slop_string expr_get_runtime_function_name(slop_string fn_name);
slop_string expr_transpile_enum_variant(context_TranspileContext* ctx, slop_string variant_name);
slop_string expr_transpile_ok(context_TranspileContext* ctx, slop_string value_c);
slop_string expr_transpile_error(context_TranspileContext* ctx, slop_string value_c);
slop_string expr_infer_option_type(context_TranspileContext* ctx, types_SExpr* val_expr);
slop_string expr_infer_list_expr_option_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_strip_pointer_suffix(slop_arena* arena, slop_string s);
slop_string expr_infer_list_element_option_type(context_TranspileContext* ctx, types_SExpr* list_expr);
slop_string expr_infer_field_access_list_type(context_TranspileContext* ctx, types_SExpr* field_expr);
slop_string expr_list_type_to_option_type(context_TranspileContext* ctx, slop_string c_type);
slop_string expr_substring_after_prefix(slop_arena* arena, slop_string s, slop_string prefix);
slop_string expr_extract_map_value_from_slop_type(slop_arena* arena, slop_string slop_type);
slop_string expr_slop_value_type_to_c_type(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_get_var_name_from_expr(types_SExpr* expr);
slop_string expr_extract_map_key_from_slop_type(slop_arena* arena, slop_string slop_type);
slop_string expr_resolve_type_alias_for_map(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_infer_expr_slop_type(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_infer_map_key_c_type_from_slop_type(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_infer_set_elem_c_type_from_slop_type(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_extract_map_value_from_inferred(context_TranspileContext* ctx, types_SExpr* map_expr);
slop_string expr_extract_list_elem_from_inferred(context_TranspileContext* ctx, types_SExpr* list_expr);
slop_string expr_infer_map_key_c_type(context_TranspileContext* ctx, types_SExpr* map_expr);
slop_string expr_extract_set_elem_from_slop_type(slop_arena* arena, slop_string slop_type);
slop_string expr_infer_set_elem_c_type(context_TranspileContext* ctx, types_SExpr* set_expr);
slop_string expr_compound_slop_type_to_id(slop_arena* arena, slop_string slop_type);
slop_string expr_slop_value_type_to_option_id(slop_arena* arena, slop_string slop_type);
slop_string expr_infer_map_value_option_type(context_TranspileContext* ctx, types_SExpr* map_expr);
slop_string expr_option_type_to_value_c_type(slop_arena* arena, slop_string option_type);
slop_string expr_infer_option_inner_slop_type(context_TranspileContext* ctx, types_SExpr* scrutinee);
slop_string expr_fix_ternary_none(context_TranspileContext* ctx, slop_string other_branch, slop_string this_branch);
slop_option_string expr_extract_option_type(slop_arena* arena, slop_string s);
slop_string expr_transpile_array_index(context_TranspileContext* ctx, types_SExpr* arr_expr, slop_string arr_c, slop_string idx_c);
uint8_t expr_is_pointer_expr(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_extract_sizeof_type(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_transpile_expr(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_transpile_list_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_fn_call(context_TranspileContext* ctx, slop_string fn_name, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_print(context_TranspileContext* ctx, types_SExpr* arg, uint8_t newline);
slop_string expr_transpile_print_string(context_TranspileContext* ctx, slop_string arg_c, slop_string nl);
slop_string expr_transpile_printf_call(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
uint8_t expr_string_contains(slop_string s, slop_string substr);
slop_option_string expr_get_expr_type_hint(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_transpile_union_constructor(context_TranspileContext* ctx, slop_string type_name, slop_string c_type_name, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_cond_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_match_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_list_types_SExpr_ptr expr_collect_match_patterns(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_get_expr_pattern_tag(types_SExpr* pat_expr);
uint8_t expr_is_option_patterns(slop_list_types_SExpr_ptr patterns);
uint8_t expr_is_result_patterns(slop_list_types_SExpr_ptr patterns);
uint8_t expr_is_union_expr_patterns(context_TranspileContext* ctx, slop_list_types_SExpr_ptr patterns);
slop_option_string expr_get_expr_binding_name(types_SExpr* pat_expr);
slop_string expr_get_match_branch_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr branch_items);
slop_string expr_transpile_branch_body_with_binding(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_list_types_SExpr_ptr branch_items, slop_string binding_name);
slop_string expr_build_option_match_expr(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_string scrutinee_c, slop_list_types_SExpr_ptr items);
slop_string expr_build_option_match_no_binding(context_TranspileContext* ctx, slop_string scrutinee_c, slop_string some_body, slop_string none_body, slop_string result_type);
slop_string expr_build_option_match_with_binding(context_TranspileContext* ctx, slop_arena* arena, slop_string scrutinee_c, slop_string binding, slop_string some_body, slop_string none_body, slop_string result_type);
slop_string expr_infer_cond_result_c_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_infer_match_result_c_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_slop_type_to_c_type(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_infer_expr_c_type(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_build_result_match_expr(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_string scrutinee_c, slop_list_types_SExpr_ptr items);
slop_string expr_build_union_match_expr(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_string scrutinee_c, slop_list_types_SExpr_ptr items);
slop_string expr_typed_none(context_TranspileContext* ctx, slop_string result_type, slop_string body);
slop_string expr_typed_none_arg(context_TranspileContext* ctx, slop_string expected_type, slop_string arg_c);
slop_string expr_build_union_case_expr(context_TranspileContext* ctx, slop_arena* arena, slop_string cases, types_SExpr* scrutinee, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, slop_string result_type);
slop_string expr_build_ternary_match_expr(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_let_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_binding_expr(context_TranspileContext* ctx, types_SExpr* binding);
uint8_t expr_binding_has_mut(slop_list_types_SExpr_ptr items);
slop_string expr_transpile_typed_init(context_TranspileContext* ctx, types_SExpr* init_expr, slop_string target_type);
slop_string expr_transpile_while_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_do_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_when_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_set_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_get_arena_for_list_push_expr(context_TranspileContext* ctx, types_SExpr* list_expr, slop_string list_c);
slop_string expr_get_arena_from_field_access(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_get_arena_from_base(context_TranspileContext* ctx, types_SExpr* base_expr);
slop_string expr_get_arena_for_list_push(context_TranspileContext* ctx, slop_string list_c);
uint8_t expr_is_ptr_to_ptr_map(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_transpile_record_new(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_record_fields(context_TranspileContext* ctx, slop_string type_name, slop_list_types_SExpr_ptr items, int64_t start_idx);
slop_string expr_build_inline_struct_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr type_items);
slop_string expr_transpile_inline_record_fields(context_TranspileContext* ctx, slop_string struct_def, slop_list_types_SExpr_ptr items, int64_t start_idx);
slop_string expr_transpile_list_literal(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_build_struct_key_info(context_TranspileContext* ctx, slop_string c_name);
slop_string expr_get_map_key_c_info(context_TranspileContext* ctx, types_SExpr* key_type_expr);
slop_string expr_get_struct_key_info_by_name(context_TranspileContext* ctx, slop_string name);
slop_string expr_transpile_map_new(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
uint8_t expr_is_c_primitive_type(slop_string t);
slop_string expr_wrap_map_key_as_ptr(context_TranspileContext* ctx, slop_string key_c, types_SExpr* key_expr, types_SExpr* container_expr);
slop_string expr_transpile_map_put(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_map_get(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_map_has(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_map_keys(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_set_new(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_set_put(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_set_has(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_set_remove(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_set_elements(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_set_literal(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_for_as_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_for_each_as_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_extract_first_type_arg(slop_arena* arena, slop_string slop_type, int64_t start);
slop_string expr_extract_second_type_arg(slop_arena* arena, slop_string slop_type, int64_t start);
slop_string expr_infer_result_ok_slop_type(context_TranspileContext* ctx, types_SExpr* scrutinee);
slop_string expr_infer_result_err_slop_type(context_TranspileContext* ctx, types_SExpr* scrutinee);
slop_string expr_infer_collection_element_slop_type(context_TranspileContext* ctx, types_SExpr* coll_expr);
slop_string expr_infer_elem_from_type(context_TranspileContext* ctx, types_SExpr* expr);

slop_string expr_escape_c_string(context_TranspileContext* ctx, slop_string s) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)(s.len));
        __auto_type data = s.data;
        {
            __auto_type buf = (uint8_t*)slop_arena_alloc(arena, ((len * 2) + 1));
            __auto_type out_pos = 0;
            __auto_type in_pos = 0;
            while ((in_pos < len)) {
                {
                    __auto_type c = ((int64_t)(data[in_pos]));
                    if ((c == 10)) {
                        buf[out_pos] = 92;
                        out_pos = (out_pos + 1);
                        buf[out_pos] = 110;
                        out_pos = (out_pos + 1);
                    } else if ((c == 13)) {
                        buf[out_pos] = 92;
                        out_pos = (out_pos + 1);
                        buf[out_pos] = 114;
                        out_pos = (out_pos + 1);
                    } else if ((c == 9)) {
                        buf[out_pos] = 92;
                        out_pos = (out_pos + 1);
                        buf[out_pos] = 116;
                        out_pos = (out_pos + 1);
                    } else if ((c == 92)) {
                        buf[out_pos] = 92;
                        out_pos = (out_pos + 1);
                        buf[out_pos] = 92;
                        out_pos = (out_pos + 1);
                    } else if ((c == 34)) {
                        buf[out_pos] = 92;
                        out_pos = (out_pos + 1);
                        buf[out_pos] = 34;
                        out_pos = (out_pos + 1);
                    } else {
                        buf[out_pos] = ((uint8_t)(c));
                        out_pos = (out_pos + 1);
                    }
                }
                in_pos = (in_pos + 1);
            }
            buf[out_pos] = 0;
            return (slop_string){.len = ((uint64_t)(out_pos)), .data = buf};
        }
    }
}

uint8_t expr_is_binop(slop_string op) {
    return ((string_eq(op, SLOP_STR("+"))) || (string_eq(op, SLOP_STR("-"))) || (string_eq(op, SLOP_STR("*"))) || (string_eq(op, SLOP_STR("/"))) || (string_eq(op, SLOP_STR("%"))) || (string_eq(op, SLOP_STR("and"))) || (string_eq(op, SLOP_STR("or"))) || (string_eq(op, SLOP_STR("bit-and"))) || (string_eq(op, SLOP_STR("bit-or"))) || (string_eq(op, SLOP_STR("bit-xor"))) || (string_eq(op, SLOP_STR("&"))) || (string_eq(op, SLOP_STR("|"))) || (string_eq(op, SLOP_STR("^"))) || (string_eq(op, SLOP_STR("<<"))) || (string_eq(op, SLOP_STR(">>"))));
}

uint8_t expr_is_comparison_op(slop_string op) {
    return ((string_eq(op, SLOP_STR("=="))) || (string_eq(op, SLOP_STR("="))) || (string_eq(op, SLOP_STR("!="))) || (string_eq(op, SLOP_STR("<"))) || (string_eq(op, SLOP_STR(">"))) || (string_eq(op, SLOP_STR("<="))) || (string_eq(op, SLOP_STR(">="))));
}

uint8_t expr_is_unop(slop_string op) {
    return ((string_eq(op, SLOP_STR("not"))) || (string_eq(op, SLOP_STR("bit-not"))) || (string_eq(op, SLOP_STR("-"))));
}

slop_option_string expr_extract_symbol_name(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_97 = (*expr);
    switch (_mv_97.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_97.data.sym;
            return (slop_option_string){.has_value = 1, .value = sym.name};
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_97.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 2)) {
                    return (slop_option_string){.has_value = false};
                } else {
                    __auto_type _mv_98 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_98.has_value) {
                        __auto_type head = _mv_98.value;
                        __auto_type _mv_99 = (*head);
                        switch (_mv_99.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type head_sym = _mv_99.data.sym;
                                if (string_eq(head_sym.name, SLOP_STR("quote"))) {
                                    __auto_type _mv_100 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_100.has_value) {
                                        __auto_type inner = _mv_100.value;
                                        __auto_type _mv_101 = (*inner);
                                        switch (_mv_101.tag) {
                                            case types_SExpr_sym:
                                            {
                                                __auto_type inner_sym = _mv_101.data.sym;
                                                return (slop_option_string){.has_value = 1, .value = inner_sym.name};
                                            }
                                            default: {
                                                return (slop_option_string){.has_value = false};
                                            }
                                        }
                                    } else if (!_mv_100.has_value) {
                                        return (slop_option_string){.has_value = false};
                                    }
                                } else {
                                    return (slop_option_string){.has_value = false};
                                }
                            }
                            default: {
                                return (slop_option_string){.has_value = false};
                            }
                        }
                    } else if (!_mv_98.has_value) {
                        return (slop_option_string){.has_value = false};
                    }
                }
            }
        }
        default: {
            return (slop_option_string){.has_value = false};
        }
    }
}

slop_string expr_transpile_literal(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_102 = (*expr);
    switch (_mv_102.tag) {
        case types_SExpr_num:
        {
            __auto_type num = _mv_102.data.num;
            if (num.is_float) {
                return num.raw;
            } else {
                return num.raw;
            }
        }
        case types_SExpr_str:
        {
            __auto_type str = _mv_102.data.str;
            return context_ctx_str3(ctx, SLOP_STR("SLOP_STR(\""), expr_escape_c_string(ctx, str.value), SLOP_STR("\")"));
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_102.data.sym;
            return expr_transpile_symbol(ctx, sym.name);
        }
        case types_SExpr_lst:
        {
            __auto_type _ = _mv_102.data.lst;
            return SLOP_STR("/* error: list is not a literal */");
        }
    }
}

slop_string expr_transpile_symbol(context_TranspileContext* ctx, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (string_eq(name, SLOP_STR("true"))) {
            return SLOP_STR("1");
        } else if (string_eq(name, SLOP_STR("false"))) {
            return SLOP_STR("0");
        } else if (string_eq(name, SLOP_STR("nil"))) {
            return SLOP_STR("NULL");
        } else if (string_eq(name, SLOP_STR("none"))) {
            return SLOP_STR("none");
        } else if (string_eq(name, SLOP_STR("unit"))) {
            return SLOP_STR("0");
        } else if (strlib_starts_with(name, SLOP_STR("'"))) {
            {
                __auto_type name_len = string_len(name);
                __auto_type variant_name = strlib_substring(arena, name, 1, ((int64_t)((name_len - 1))));
                __auto_type _mv_103 = context_ctx_lookup_enum_variant(ctx, variant_name);
                if (_mv_103.has_value) {
                    __auto_type enum_name = _mv_103.value;
                    return expr_get_prefixed_enum_value(ctx, enum_name, variant_name);
                } else if (!_mv_103.has_value) {
                    return ctype_to_c_name(arena, variant_name);
                }
            }
        } else if (strlib_contains(name, SLOP_STR("."))) {
            __auto_type _mv_104 = strlib_index_of(name, SLOP_STR("."));
            if (_mv_104.has_value) {
                __auto_type dot_pos = _mv_104.value;
                {
                    __auto_type base_name = strlib_substring(arena, name, 0, dot_pos);
                    __auto_type rest_len = ((int64_t)((string_len(name) - (dot_pos + 1))));
                    __auto_type rest_name = strlib_substring(arena, name, (dot_pos + 1), rest_len);
                    __auto_type c_rest = ctype_to_c_name(arena, rest_name);
                    __auto_type _mv_105 = context_ctx_lookup_var(ctx, base_name);
                    if (_mv_105.has_value) {
                        __auto_type var_entry = _mv_105.value;
                        {
                            __auto_type c_base = var_entry.c_name;
                            __auto_type is_ptr = var_entry.is_pointer;
                            __auto_type accessor = ((is_ptr) ? SLOP_STR("->") : SLOP_STR("."));
                            return context_ctx_str3(ctx, c_base, accessor, c_rest);
                        }
                    } else if (!_mv_105.has_value) {
                        __auto_type _mv_106 = context_ctx_lookup_type(ctx, base_name);
                        if (_mv_106.has_value) {
                            __auto_type type_info = _mv_106.value;
                            return expr_get_prefixed_enum_value(ctx, type_info.c_name, rest_name);
                        } else if (!_mv_106.has_value) {
                            return context_ctx_str3(ctx, base_name, SLOP_STR("_"), c_rest);
                        }
                    }
                }
            } else if (!_mv_104.has_value) {
                return ctype_to_c_name(arena, name);
            }
        } else {
            __auto_type _mv_107 = context_ctx_lookup_var(ctx, name);
            if (_mv_107.has_value) {
                __auto_type entry = _mv_107.value;
                return entry.c_name;
            } else if (!_mv_107.has_value) {
                __auto_type _mv_108 = context_ctx_lookup_enum_variant(ctx, name);
                if (_mv_108.has_value) {
                    __auto_type enum_name = _mv_108.value;
                    return expr_get_prefixed_enum_value(ctx, enum_name, name);
                } else if (!_mv_108.has_value) {
                    {
                        __auto_type c_name = ctype_to_c_name(arena, name);
                        __auto_type _mv_109 = context_ctx_lookup_func(ctx, name);
                        if (_mv_109.has_value) {
                            __auto_type func_entry = _mv_109.value;
                            return func_entry.c_name;
                        } else if (!_mv_109.has_value) {
                            return c_name;
                        }
                    }
                }
            }
        }
    }
}

slop_string expr_get_prefixed_enum_value(context_TranspileContext* ctx, slop_string enum_name, slop_string variant_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        return context_ctx_str3(ctx, enum_name, SLOP_STR("_"), ctype_to_c_name(arena, variant_name));
    }
}

slop_string expr_binop_to_c(slop_string op) {
    if (string_eq(op, SLOP_STR("+"))) {
        return SLOP_STR("+");
    } else if (string_eq(op, SLOP_STR("-"))) {
        return SLOP_STR("-");
    } else if (string_eq(op, SLOP_STR("*"))) {
        return SLOP_STR("*");
    } else if (string_eq(op, SLOP_STR("/"))) {
        return SLOP_STR("/");
    } else if (string_eq(op, SLOP_STR("%"))) {
        return SLOP_STR("%");
    } else if (string_eq(op, SLOP_STR("=="))) {
        return SLOP_STR("==");
    } else if (string_eq(op, SLOP_STR("="))) {
        return SLOP_STR("==");
    } else if (string_eq(op, SLOP_STR("!="))) {
        return SLOP_STR("!=");
    } else if (string_eq(op, SLOP_STR("<"))) {
        return SLOP_STR("<");
    } else if (string_eq(op, SLOP_STR(">"))) {
        return SLOP_STR(">");
    } else if (string_eq(op, SLOP_STR("<="))) {
        return SLOP_STR("<=");
    } else if (string_eq(op, SLOP_STR(">="))) {
        return SLOP_STR(">=");
    } else if (string_eq(op, SLOP_STR("and"))) {
        return SLOP_STR("&&");
    } else if (string_eq(op, SLOP_STR("or"))) {
        return SLOP_STR("||");
    } else if (string_eq(op, SLOP_STR("bit-and"))) {
        return SLOP_STR("&");
    } else if (string_eq(op, SLOP_STR("bit-or"))) {
        return SLOP_STR("|");
    } else if (string_eq(op, SLOP_STR("bit-xor"))) {
        return SLOP_STR("^");
    } else if (string_eq(op, SLOP_STR("&"))) {
        return SLOP_STR("&");
    } else if (string_eq(op, SLOP_STR("|"))) {
        return SLOP_STR("|");
    } else if (string_eq(op, SLOP_STR("^"))) {
        return SLOP_STR("^");
    } else if (string_eq(op, SLOP_STR("<<"))) {
        return SLOP_STR("<<");
    } else if (string_eq(op, SLOP_STR(">>"))) {
        return SLOP_STR(">>");
    } else {
        return op;
    }
}

slop_string expr_transpile_binop(context_TranspileContext* ctx, slop_string op, slop_string left, slop_string right) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type c_op = expr_binop_to_c(op);
        return context_ctx_str5(ctx, SLOP_STR("("), left, SLOP_STR(" "), c_op, context_ctx_str3(ctx, SLOP_STR(" "), right, SLOP_STR(")")));
    }
}

slop_string expr_transpile_variadic_binop(context_TranspileContext* ctx, slop_string op, slop_list_types_SExpr_ptr items, int64_t start_idx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type c_op = expr_binop_to_c(op);
        __auto_type len = ((int64_t)(((int64_t)((items).len))));
        if ((len <= (start_idx + 1))) {
            context_ctx_add_error_at(ctx, SLOP_STR("not enough operands"), context_list_first_line(items), context_list_first_col(items));
            return SLOP_STR("0");
        } else {
            {
                __auto_type result = SLOP_STR("(");
                __auto_type _mv_110 = ({ __auto_type _lst = items; size_t _idx = (size_t)start_idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_110.has_value) {
                    __auto_type first_arg = _mv_110.value;
                    result = context_ctx_str4(ctx, result, SLOP_STR("("), expr_transpile_expr(ctx, first_arg), SLOP_STR(")"));
                } else if (!_mv_110.has_value) {
                    result = result;
                }
                {
                    __auto_type i = (start_idx + 1);
                    while ((i < len)) {
                        __auto_type _mv_111 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_111.has_value) {
                            __auto_type arg = _mv_111.value;
                            {
                                __auto_type arg_str = context_ctx_str3(ctx, SLOP_STR(" ("), expr_transpile_expr(ctx, arg), SLOP_STR(")"));
                                result = context_ctx_str4(ctx, result, SLOP_STR(" "), c_op, arg_str);
                            }
                        } else if (!_mv_111.has_value) {
                            result = result;
                        }
                        i = (i + 1);
                    }
                }
                return context_ctx_str(ctx, result, SLOP_STR(")"));
            }
        }
    }
}

slop_string expr_get_builtin_type_c_name(slop_string type_name) {
    if (string_eq(type_name, SLOP_STR("Bytes"))) {
        return SLOP_STR("slop_bytes");
    } else if (string_eq(type_name, SLOP_STR("String"))) {
        return SLOP_STR("slop_string");
    } else {
        return SLOP_STR("");
    }
}

uint8_t expr_is_pointer_type_expr(types_SExpr* type_expr) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_112 = (*type_expr);
    switch (_mv_112.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_112.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_113 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_113.has_value) {
                        __auto_type head = _mv_113.value;
                        __auto_type _mv_114 = (*head);
                        switch (_mv_114.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_114.data.sym;
                                return (string_eq(sym.name, SLOP_STR("Ptr")) || string_eq(sym.name, SLOP_STR("ScopedPtr")));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_113.has_value) {
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

uint8_t expr_is_string_literal(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_115 = (*expr);
    switch (_mv_115.tag) {
        case types_SExpr_str:
        {
            __auto_type _ = _mv_115.data.str;
            return 1;
        }
        default: {
            return 0;
        }
    }
}

slop_string expr_transpile_builtin_constructor(context_TranspileContext* ctx, slop_string type_name, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (string_eq(type_name, SLOP_STR("Bytes"))) {
            if ((len < 4)) {
                return SLOP_STR("(slop_bytes){0}");
            } else {
                {
                    __auto_type data_c = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type e = _mv.value; expr_transpile_expr(ctx, e); }) : (SLOP_STR("NULL")); });
                    __auto_type len_c = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type e = _mv.value; expr_transpile_expr(ctx, e); }) : (SLOP_STR("0")); });
                    __auto_type cap_c = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type e = _mv.value; expr_transpile_expr(ctx, e); }) : (SLOP_STR("0")); });
                    return context_ctx_str(ctx, SLOP_STR("(slop_bytes){.len = "), context_ctx_str(ctx, len_c, context_ctx_str(ctx, SLOP_STR(", .cap = "), context_ctx_str(ctx, cap_c, context_ctx_str(ctx, SLOP_STR(", .data = "), context_ctx_str(ctx, data_c, SLOP_STR("}")))))));
                }
            }
        } else if (string_eq(type_name, SLOP_STR("String"))) {
            if ((len < 3)) {
                return SLOP_STR("(slop_string){0}");
            } else {
                {
                    __auto_type data_c = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type e = _mv.value; expr_transpile_expr(ctx, e); }) : (SLOP_STR("NULL")); });
                    __auto_type len_c = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type e = _mv.value; expr_transpile_expr(ctx, e); }) : (SLOP_STR("0")); });
                    return context_ctx_str(ctx, SLOP_STR("(slop_string){.len = "), context_ctx_str(ctx, len_c, context_ctx_str(ctx, SLOP_STR(", .data = "), context_ctx_str(ctx, data_c, SLOP_STR("}")))));
                }
            }
        } else {
            return SLOP_STR("(/* unknown builtin */)");
        }
    }
}

slop_string expr_transpile_call(context_TranspileContext* ctx, slop_string fn_name, slop_string args) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        {
            __auto_type runtime_name = expr_get_runtime_function_name(fn_name);
            if ((string_len(runtime_name) > 0)) {
                return context_ctx_str4(ctx, runtime_name, SLOP_STR("("), args, SLOP_STR(")"));
            } else {
                {
                    __auto_type base_name = expr_get_base_function_name(arena, fn_name);
                    __auto_type mod_name = expr_get_module_from_qualified_name(arena, fn_name);
                    __auto_type _mv_116 = context_ctx_lookup_var(ctx, fn_name);
                    if (_mv_116.has_value) {
                        __auto_type var_entry = _mv_116.value;
                        return context_ctx_str4(ctx, var_entry.c_name, SLOP_STR("("), args, SLOP_STR(")"));
                    } else if (!_mv_116.has_value) {
                        {
                            __auto_type c_name = ({ __auto_type _mv = context_ctx_lookup_func(ctx, base_name); _mv.has_value ? ({ __auto_type func_entry = _mv.value; func_entry.c_name; }) : ((((string_len(mod_name) > 0)) ? ctype_to_c_name(arena, fn_name) : context_ctx_prefix_type(ctx, ctype_to_c_name(arena, fn_name)))); });
                            return context_ctx_str4(ctx, c_name, SLOP_STR("("), args, SLOP_STR(")"));
                        }
                    }
                }
            }
        }
    }
}

slop_string expr_get_base_function_name(slop_arena* arena, slop_string fn_name) {
    {
        __auto_type len = ((int64_t)(string_len(fn_name)));
        __auto_type dot_pos = -1;
        __auto_type i = 0;
        while ((i < len)) {
            if ((strlib_char_at(fn_name, ((int64_t)(i))) == 46)) {
                dot_pos = i;
            } else {
            }
            i = (i + 1);
        }
        if ((dot_pos < 0)) {
            return fn_name;
        } else {
            {
                __auto_type start = (dot_pos + 1);
                __auto_type sublen = (len - start);
                return strlib_substring(arena, fn_name, ((int64_t)(start)), ((int64_t)(sublen)));
            }
        }
    }
}

slop_string expr_get_module_from_qualified_name(slop_arena* arena, slop_string fn_name) {
    {
        __auto_type len = ((int64_t)(string_len(fn_name)));
        __auto_type dot_pos = -1;
        __auto_type i = 0;
        while ((i < len)) {
            if ((strlib_char_at(fn_name, ((int64_t)(i))) == 46)) {
                dot_pos = i;
            } else {
            }
            i = (i + 1);
        }
        if ((dot_pos < 0)) {
            return SLOP_STR("");
        } else {
            return strlib_substring(arena, fn_name, 0, ((int64_t)(dot_pos)));
        }
    }
}

slop_string expr_get_runtime_function_name(slop_string fn_name) {
    if (string_eq(fn_name, SLOP_STR("string-eq"))) {
        return SLOP_STR("string_eq");
    } else if (string_eq(fn_name, SLOP_STR("string-concat"))) {
        return SLOP_STR("string_concat");
    } else if (string_eq(fn_name, SLOP_STR("string-len"))) {
        return SLOP_STR("string_len");
    } else if (string_eq(fn_name, SLOP_STR("string-new"))) {
        return SLOP_STR("string_new");
    } else if (string_eq(fn_name, SLOP_STR("int-to-string"))) {
        return SLOP_STR("int_to_string");
    } else if (string_eq(fn_name, SLOP_STR("float-to-string-short"))) {
        return SLOP_STR("float_to_string_short");
    } else if (string_eq(fn_name, SLOP_STR("parse-int"))) {
        return SLOP_STR("strlib_parse_int");
    } else if (string_eq(fn_name, SLOP_STR("parse-float"))) {
        return SLOP_STR("strlib_parse_float");
    } else if (string_eq(fn_name, SLOP_STR("list-len"))) {
        return SLOP_STR("list_len");
    } else if (string_eq(fn_name, SLOP_STR("list-new"))) {
        return SLOP_STR("list_new");
    } else if (string_eq(fn_name, SLOP_STR("list-push"))) {
        return SLOP_STR("list_push");
    } else if (string_eq(fn_name, SLOP_STR("list-get"))) {
        return SLOP_STR("list_get");
    } else if (string_eq(fn_name, SLOP_STR("bytes-len"))) {
        return SLOP_STR("bytes_len");
    } else if (string_eq(fn_name, SLOP_STR("bytes-new"))) {
        return SLOP_STR("bytes_new");
    } else if (string_eq(fn_name, SLOP_STR("unwrap"))) {
        return SLOP_STR("unwrap");
    } else if (string_eq(fn_name, SLOP_STR("printf"))) {
        return SLOP_STR("printf");
    } else if (string_eq(fn_name, SLOP_STR("fprintf"))) {
        return SLOP_STR("fprintf");
    } else if (string_eq(fn_name, SLOP_STR("sprintf"))) {
        return SLOP_STR("sprintf");
    } else if (string_eq(fn_name, SLOP_STR("snprintf"))) {
        return SLOP_STR("snprintf");
    } else if (string_eq(fn_name, SLOP_STR("malloc"))) {
        return SLOP_STR("malloc");
    } else if (string_eq(fn_name, SLOP_STR("free"))) {
        return SLOP_STR("free");
    } else if (string_eq(fn_name, SLOP_STR("memcpy"))) {
        return SLOP_STR("memcpy");
    } else if (string_eq(fn_name, SLOP_STR("memset"))) {
        return SLOP_STR("memset");
    } else if (string_eq(fn_name, SLOP_STR("strlen"))) {
        return SLOP_STR("strlen");
    } else if (string_eq(fn_name, SLOP_STR("strcmp"))) {
        return SLOP_STR("strcmp");
    } else if (string_eq(fn_name, SLOP_STR("exit"))) {
        return SLOP_STR("exit");
    } else if (string_eq(fn_name, SLOP_STR("abort"))) {
        return SLOP_STR("abort");
    } else {
        return SLOP_STR("");
    }
}

slop_string expr_transpile_enum_variant(context_TranspileContext* ctx, slop_string variant_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_117 = context_ctx_lookup_enum_variant(ctx, variant_name);
        if (_mv_117.has_value) {
            __auto_type enum_name = _mv_117.value;
            {
                __auto_type enum_c = ctype_to_c_name(arena, enum_name);
                __auto_type variant_c = ctype_to_c_name(arena, variant_name);
                return context_ctx_str3(ctx, enum_c, SLOP_STR("_"), variant_c);
            }
        } else if (!_mv_117.has_value) {
            return ctype_to_c_name(arena, variant_name);
        }
    }
}

slop_string expr_transpile_ok(context_TranspileContext* ctx, slop_string value_c) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    __auto_type _mv_118 = context_ctx_get_current_result_type(ctx);
    if (_mv_118.has_value) {
        __auto_type result_type = _mv_118.value;
        return context_ctx_str5(ctx, SLOP_STR("(("), result_type, SLOP_STR("){ .is_ok = true, .data.ok = "), value_c, SLOP_STR(" })"));
    } else if (!_mv_118.has_value) {
        return context_ctx_str3(ctx, SLOP_STR("(slop_result){ .is_ok = true, .data.ok = "), value_c, SLOP_STR(" }"));
    }
}

slop_string expr_transpile_error(context_TranspileContext* ctx, slop_string value_c) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    __auto_type _mv_119 = context_ctx_get_current_result_type(ctx);
    if (_mv_119.has_value) {
        __auto_type result_type = _mv_119.value;
        return context_ctx_str5(ctx, SLOP_STR("(("), result_type, SLOP_STR("){ .is_ok = false, .data.err = "), value_c, SLOP_STR(" })"));
    } else if (!_mv_119.has_value) {
        return context_ctx_str3(ctx, SLOP_STR("(slop_result){ .is_ok = false, .data.err = "), value_c, SLOP_STR(" }"));
    }
}

slop_string expr_infer_option_type(context_TranspileContext* ctx, types_SExpr* val_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((val_expr != NULL)), "(!= val-expr nil)");
    __auto_type _mv_120 = (*val_expr);
    switch (_mv_120.tag) {
        case types_SExpr_num:
        {
            __auto_type num = _mv_120.data.num;
            if (num.is_float) {
                return SLOP_STR("slop_option_double");
            } else {
                return SLOP_STR("slop_option_int");
            }
        }
        case types_SExpr_str:
        {
            __auto_type _ = _mv_120.data.str;
            return SLOP_STR("slop_option_string");
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_120.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_121 = context_ctx_lookup_var(ctx, name);
                if (_mv_121.has_value) {
                    __auto_type var_entry = _mv_121.value;
                    {
                        __auto_type c_type = var_entry.c_type;
                        __auto_type arena = (*ctx).arena;
                        if (string_eq(c_type, SLOP_STR("auto"))) {
                            return context_ctx_str3(ctx, SLOP_STR("/* TRANSPILER ERROR: cannot infer Option type for variable '"), name, SLOP_STR("' */"));
                        } else if (string_eq(c_type, SLOP_STR("int64_t"))) {
                            return SLOP_STR("slop_option_int");
                        } else if (string_eq(c_type, SLOP_STR("double"))) {
                            return SLOP_STR("slop_option_double");
                        } else if (string_eq(c_type, SLOP_STR("slop_string"))) {
                            return SLOP_STR("slop_option_string");
                        } else if (string_eq(c_type, SLOP_STR("char"))) {
                            return SLOP_STR("slop_option_char");
                        } else if (string_eq(c_type, SLOP_STR("uint8_t"))) {
                            return SLOP_STR("slop_option_u8");
                        } else if (strlib_ends_with(c_type, SLOP_STR("*"))) {
                            {
                                __auto_type base_type = expr_strip_pointer_suffix(arena, c_type);
                                return context_ctx_str3(ctx, SLOP_STR("slop_option_"), base_type, SLOP_STR("_ptr"));
                            }
                        } else {
                            return context_ctx_str3(ctx, SLOP_STR("slop_option_"), c_type, SLOP_STR(""));
                        }
                    }
                } else if (!_mv_121.has_value) {
                    return context_ctx_str3(ctx, SLOP_STR("/* TRANSPILER ERROR: unknown variable '"), name, SLOP_STR("' for Option type inference */"));
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_120.data.lst;
            return expr_infer_list_expr_option_type(ctx, lst.items);
        }
    }
}

slop_string expr_infer_list_expr_option_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type arena = (*ctx).arena;
        if ((len < 1)) {
            return SLOP_STR("/* TRANSPILER ERROR: empty list in option type inference */");
        } else {
            __auto_type _mv_122 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_122.has_value) {
                __auto_type head_expr = _mv_122.value;
                __auto_type _mv_123 = (*head_expr);
                switch (_mv_123.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_123.data.sym;
                        {
                            __auto_type op = sym.name;
                            if (string_eq(op, SLOP_STR("."))) {
                                if ((len < 3)) {
                                    return SLOP_STR("/* TRANSPILER ERROR: incomplete field access for option type inference */");
                                } else {
                                    __auto_type _mv_124 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_124.has_value) {
                                        __auto_type field_expr = _mv_124.value;
                                        __auto_type _mv_125 = (*field_expr);
                                        switch (_mv_125.tag) {
                                            case types_SExpr_sym:
                                            {
                                                __auto_type field_sym = _mv_125.data.sym;
                                                {
                                                    __auto_type field_name = field_sym.name;
                                                    if (string_eq(field_name, SLOP_STR("name"))) {
                                                        return SLOP_STR("slop_option_string");
                                                    } else if (string_eq(field_name, SLOP_STR("value"))) {
                                                        return SLOP_STR("slop_option_string");
                                                    } else if (string_eq(field_name, SLOP_STR("message"))) {
                                                        return SLOP_STR("slop_option_string");
                                                    } else if (string_eq(field_name, SLOP_STR("c-name"))) {
                                                        return SLOP_STR("slop_option_string");
                                                    } else if (string_eq(field_name, SLOP_STR("c-type"))) {
                                                        return SLOP_STR("slop_option_string");
                                                    } else if (string_eq(field_name, SLOP_STR("slop-name"))) {
                                                        return SLOP_STR("slop_option_string");
                                                    } else {
                                                        return context_ctx_str3(ctx, SLOP_STR("/* TRANSPILER ERROR: unknown field '"), field_name, SLOP_STR("' for option type inference */"));
                                                    }
                                                }
                                            }
                                            default: {
                                                return SLOP_STR("/* TRANSPILER ERROR: non-symbol field for option type inference */");
                                            }
                                        }
                                    } else if (!_mv_124.has_value) {
                                        return SLOP_STR("/* TRANSPILER ERROR: missing field for option type inference */");
                                    }
                                }
                            } else if ((string_eq(op, SLOP_STR("string-concat")) || (string_eq(op, SLOP_STR("string-copy")) || (string_eq(op, SLOP_STR("int-to-string")) || string_eq(op, SLOP_STR("substring")))))) {
                                return SLOP_STR("slop_option_string");
                            } else {
                                __auto_type _mv_126 = context_ctx_lookup_func(ctx, op);
                                if (_mv_126.has_value) {
                                    __auto_type func_entry = _mv_126.value;
                                    {
                                        __auto_type ret_type = func_entry.return_type;
                                        if (func_entry.returns_string) {
                                            return SLOP_STR("slop_option_string");
                                        } else if ((string_len(ret_type) > 0)) {
                                            if (string_eq(ret_type, SLOP_STR("slop_string"))) {
                                                return SLOP_STR("slop_option_string");
                                            } else if (string_eq(ret_type, SLOP_STR("int64_t"))) {
                                                return SLOP_STR("slop_option_int");
                                            } else if (string_eq(ret_type, SLOP_STR("double"))) {
                                                return SLOP_STR("slop_option_double");
                                            } else if (strlib_ends_with(ret_type, SLOP_STR("*"))) {
                                                {
                                                    __auto_type ctx_arena = (*ctx).arena;
                                                    __auto_type base_type = expr_strip_pointer_suffix(ctx_arena, ret_type);
                                                    return context_ctx_str3(ctx, SLOP_STR("slop_option_"), base_type, SLOP_STR("_ptr"));
                                                }
                                            } else {
                                                return context_ctx_str3(ctx, SLOP_STR("slop_option_"), ret_type, SLOP_STR(""));
                                            }
                                        } else {
                                            return context_ctx_str3(ctx, SLOP_STR("/* TRANSPILER ERROR: cannot infer Option type for function '"), op, SLOP_STR("' */"));
                                        }
                                    }
                                } else if (!_mv_126.has_value) {
                                    return context_ctx_str3(ctx, SLOP_STR("/* TRANSPILER ERROR: unknown function '"), op, SLOP_STR("' for Option type inference */"));
                                }
                            }
                        }
                    }
                    default: {
                        return SLOP_STR("/* TRANSPILER ERROR: non-symbol head in option type inference */");
                    }
                }
            } else if (!_mv_122.has_value) {
                return SLOP_STR("/* TRANSPILER ERROR: missing list head in option type inference */");
            }
        }
    }
}

slop_string expr_strip_pointer_suffix(slop_arena* arena, slop_string s) {
    {
        __auto_type len = string_len(s);
        if ((len < 1)) {
            return SLOP_STR("");
        } else {
            return strlib_substring(arena, s, ((int64_t)(0)), ((int64_t)((len - 1))));
        }
    }
}

slop_string expr_infer_list_element_option_type(context_TranspileContext* ctx, types_SExpr* list_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((list_expr != NULL)), "(!= list-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_127 = (*list_expr);
        switch (_mv_127.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_127.data.sym;
                {
                    __auto_type name = sym.name;
                    __auto_type _mv_128 = context_ctx_lookup_var(ctx, name);
                    if (_mv_128.has_value) {
                        __auto_type var_entry = _mv_128.value;
                        return expr_list_type_to_option_type(ctx, var_entry.c_type);
                    } else if (!_mv_128.has_value) {
                        return SLOP_STR("");
                    }
                }
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_127.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) < 3)) {
                        return SLOP_STR("");
                    } else {
                        __auto_type _mv_129 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_129.has_value) {
                            __auto_type head = _mv_129.value;
                            __auto_type _mv_130 = (*head);
                            switch (_mv_130.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_130.data.sym;
                                    if (string_eq(head_sym.name, SLOP_STR("."))) {
                                        __auto_type _mv_131 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_131.has_value) {
                                            __auto_type field_expr = _mv_131.value;
                                            return expr_infer_field_access_list_type(ctx, field_expr);
                                        } else if (!_mv_131.has_value) {
                                            return SLOP_STR("");
                                        }
                                    } else {
                                        return SLOP_STR("");
                                    }
                                }
                                default: {
                                    return SLOP_STR("");
                                }
                            }
                        } else if (!_mv_129.has_value) {
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
}

slop_string expr_infer_field_access_list_type(context_TranspileContext* ctx, types_SExpr* field_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((field_expr != NULL)), "(!= field-expr nil)");
    __auto_type _mv_132 = (*field_expr);
    switch (_mv_132.tag) {
        case types_SExpr_sym:
        {
            __auto_type field_sym = _mv_132.data.sym;
            {
                __auto_type field_name = field_sym.name;
                if (string_eq(field_name, SLOP_STR("items"))) {
                    return SLOP_STR("slop_option_types_SExpr_ptr");
                } else if (string_eq(field_name, SLOP_STR("variants"))) {
                    return SLOP_STR("slop_option_types_ResolvedVariant");
                } else if (string_eq(field_name, SLOP_STR("fields"))) {
                    return SLOP_STR("slop_option_types_ResolvedField");
                } else {
                    return SLOP_STR("");
                }
            }
        }
        default: {
            return SLOP_STR("");
        }
    }
}

slop_string expr_list_type_to_option_type(context_TranspileContext* ctx, slop_string c_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (string_eq(c_type, SLOP_STR("slop_list_string"))) {
            return SLOP_STR("slop_option_string");
        } else if (string_eq(c_type, SLOP_STR("slop_list_int"))) {
            return SLOP_STR("slop_option_int");
        } else if (string_eq(c_type, SLOP_STR("slop_list_double"))) {
            return SLOP_STR("slop_option_double");
        } else if (string_eq(c_type, SLOP_STR("slop_list_char"))) {
            return SLOP_STR("slop_option_char");
        } else if (string_eq(c_type, SLOP_STR("slop_list_u8"))) {
            return SLOP_STR("slop_option_u8");
        } else if (strlib_starts_with(c_type, SLOP_STR("slop_list_"))) {
            {
                __auto_type elem_type = expr_substring_after_prefix(arena, c_type, SLOP_STR("slop_list_"));
                return context_ctx_str3(ctx, SLOP_STR("slop_option_"), elem_type, SLOP_STR(""));
            }
        } else {
            return SLOP_STR("");
        }
    }
}

slop_string expr_substring_after_prefix(slop_arena* arena, slop_string s, slop_string prefix) {
    {
        __auto_type prefix_len = string_len(prefix);
        __auto_type s_len = string_len(s);
        if ((s_len <= prefix_len)) {
            return SLOP_STR("");
        } else {
            {
                __auto_type start = ((int64_t)(prefix_len));
                __auto_type len = ((int64_t)((s_len - prefix_len)));
                return strlib_substring(arena, s, start, len);
            }
        }
    }
}

slop_string expr_extract_map_value_from_slop_type(slop_arena* arena, slop_string slop_type) {
    {
        __auto_type len = string_len(slop_type);
        if ((len < 10)) {
            return SLOP_STR("");
        } else {
            if (!(strlib_starts_with(slop_type, SLOP_STR("(Map ")))) {
                return SLOP_STR("");
            } else {
                {
                    __auto_type i = 5;
                    __auto_type nesting = 1;
                    __auto_type key_space = 0;
                    __auto_type found_key = 0;
                    __auto_type end_idx = (len - 1);
                    while (((i < end_idx) && !(found_key))) {
                        {
                            __auto_type c = strlib_char_at(slop_type, ((int64_t)(i)));
                            if ((c == 40)) {
                                nesting = (nesting + 1);
                            } else if ((c == 41)) {
                                nesting = (nesting - 1);
                            } else if (((c == 32) && (nesting == 1))) {
                                key_space = i;
                                found_key = 1;
                            } else {
                            }
                        }
                        i = (i + 1);
                    }
                    if (!(found_key)) {
                        return SLOP_STR("");
                    } else {
                        {
                            __auto_type value_start = (key_space + 1);
                            __auto_type value_len = (end_idx - value_start);
                            if ((value_len > 0)) {
                                return strlib_substring(arena, slop_type, ((int64_t)(value_start)), ((int64_t)(value_len)));
                            } else {
                                return SLOP_STR("");
                            }
                        }
                    }
                }
            }
        }
    }
}

slop_string expr_slop_value_type_to_c_type(context_TranspileContext* ctx, slop_string slop_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (string_eq(slop_type, SLOP_STR("Int"))) {
        return SLOP_STR("int64_t");
    } else if (string_eq(slop_type, SLOP_STR("I8"))) {
        return SLOP_STR("int8_t");
    } else if (string_eq(slop_type, SLOP_STR("I16"))) {
        return SLOP_STR("int16_t");
    } else if (string_eq(slop_type, SLOP_STR("I32"))) {
        return SLOP_STR("int32_t");
    } else if (string_eq(slop_type, SLOP_STR("I64"))) {
        return SLOP_STR("int64_t");
    } else if (string_eq(slop_type, SLOP_STR("U8"))) {
        return SLOP_STR("uint8_t");
    } else if (string_eq(slop_type, SLOP_STR("U16"))) {
        return SLOP_STR("uint16_t");
    } else if (string_eq(slop_type, SLOP_STR("U32"))) {
        return SLOP_STR("uint32_t");
    } else if (string_eq(slop_type, SLOP_STR("U64"))) {
        return SLOP_STR("uint64_t");
    } else if (string_eq(slop_type, SLOP_STR("Char"))) {
        return SLOP_STR("char");
    } else if (string_eq(slop_type, SLOP_STR("Float"))) {
        return SLOP_STR("double");
    } else if (string_eq(slop_type, SLOP_STR("F32"))) {
        return SLOP_STR("float");
    } else if (string_eq(slop_type, SLOP_STR("Bool"))) {
        return SLOP_STR("uint8_t");
    } else if (string_eq(slop_type, SLOP_STR("String"))) {
        return SLOP_STR("slop_string");
    } else if (string_eq(slop_type, SLOP_STR("Bytes"))) {
        return SLOP_STR("slop_bytes");
    } else {
        {
            __auto_type arena = (*ctx).arena;
            __auto_type _mv_133 = context_ctx_lookup_type(ctx, slop_type);
            if (_mv_133.has_value) {
                __auto_type entry = _mv_133.value;
                return entry.c_name;
            } else if (!_mv_133.has_value) {
                return ctype_to_c_name(arena, slop_type);
            }
        }
    }
}

slop_string expr_get_var_name_from_expr(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_134 = (*expr);
    switch (_mv_134.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_134.data.sym;
            return sym.name;
        }
        default: {
            return SLOP_STR("");
        }
    }
}

slop_string expr_extract_map_key_from_slop_type(slop_arena* arena, slop_string slop_type) {
    {
        __auto_type len = string_len(slop_type);
        if ((len < 10)) {
            return SLOP_STR("");
        } else {
            if (!(strlib_starts_with(slop_type, SLOP_STR("(Map ")))) {
                return SLOP_STR("");
            } else {
                {
                    __auto_type i = 5;
                    __auto_type nesting = 1;
                    __auto_type key_space = 0;
                    __auto_type found_key = 0;
                    __auto_type end_idx = (len - 1);
                    while (((i < end_idx) && !(found_key))) {
                        {
                            __auto_type c = strlib_char_at(slop_type, ((int64_t)(i)));
                            if ((c == 40)) {
                                nesting = (nesting + 1);
                            } else if ((c == 41)) {
                                nesting = (nesting - 1);
                            } else if (((c == 32) && (nesting == 1))) {
                                key_space = i;
                                found_key = 1;
                            } else {
                            }
                        }
                        i = (i + 1);
                    }
                    if (!(found_key)) {
                        return SLOP_STR("");
                    } else {
                        {
                            __auto_type key_start = 5;
                            __auto_type key_len = (key_space - key_start);
                            if ((key_len > 0)) {
                                return strlib_substring(arena, slop_type, ((int64_t)(key_start)), ((int64_t)(key_len)));
                            } else {
                                return SLOP_STR("");
                            }
                        }
                    }
                }
            }
        }
    }
}

slop_string expr_resolve_type_alias_for_map(context_TranspileContext* ctx, slop_string slop_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (strlib_starts_with(slop_type, SLOP_STR("(Map "))) {
        return slop_type;
    } else if (strlib_starts_with(slop_type, SLOP_STR("(Set "))) {
        return slop_type;
    } else if (strlib_starts_with(slop_type, SLOP_STR("("))) {
        return slop_type;
    } else {
        __auto_type _mv_135 = context_ctx_lookup_type_alias(ctx, slop_type);
        if (_mv_135.has_value) {
            __auto_type alias_def = _mv_135.value;
            return alias_def;
        } else if (!_mv_135.has_value) {
            return slop_type;
        }
    }
}

slop_string expr_infer_expr_slop_type(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_136 = (*expr);
        switch (_mv_136.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_136.data.sym;
                {
                    __auto_type name = sym.name;
                    __auto_type _mv_137 = context_ctx_lookup_var(ctx, name);
                    if (_mv_137.has_value) {
                        __auto_type entry = _mv_137.value;
                        return entry.slop_type;
                    } else if (!_mv_137.has_value) {
                        return SLOP_STR("");
                    }
                }
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_136.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 1)) {
                        return SLOP_STR("");
                    } else {
                        __auto_type _mv_138 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_138.has_value) {
                            __auto_type head = _mv_138.value;
                            __auto_type _mv_139 = (*head);
                            switch (_mv_139.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_139.data.sym;
                                    {
                                        __auto_type op = head_sym.name;
                                        if ((string_eq(op, SLOP_STR(".")) && (len >= 3))) {
                                            __auto_type _mv_140 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_140.has_value) {
                                                __auto_type obj_expr = _mv_140.value;
                                                __auto_type _mv_141 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_141.has_value) {
                                                    __auto_type field_expr = _mv_141.value;
                                                    __auto_type _mv_142 = (*field_expr);
                                                    switch (_mv_142.tag) {
                                                        case types_SExpr_sym:
                                                        {
                                                            __auto_type field_sym = _mv_142.data.sym;
                                                            {
                                                                __auto_type field_name = field_sym.name;
                                                                {
                                                                    __auto_type obj_c_type = expr_infer_expr_c_type(ctx, obj_expr);
                                                                    __auto_type _mv_143 = context_ctx_lookup_field_slop_type(ctx, obj_c_type, field_name);
                                                                    if (_mv_143.has_value) {
                                                                        __auto_type slop_type = _mv_143.value;
                                                                        return slop_type;
                                                                    } else if (!_mv_143.has_value) {
                                                                        {
                                                                            __auto_type obj_slop_type = expr_infer_expr_slop_type(ctx, obj_expr);
                                                                            __auto_type _mv_144 = context_ctx_lookup_field_slop_type(ctx, obj_slop_type, field_name);
                                                                            if (_mv_144.has_value) {
                                                                                __auto_type slop_type2 = _mv_144.value;
                                                                                return slop_type2;
                                                                            } else if (!_mv_144.has_value) {
                                                                                return SLOP_STR("");
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                        default: {
                                                            return SLOP_STR("");
                                                        }
                                                    }
                                                } else if (!_mv_141.has_value) {
                                                    return SLOP_STR("");
                                                }
                                            } else if (!_mv_140.has_value) {
                                                return SLOP_STR("");
                                            }
                                        } else {
                                            return SLOP_STR("");
                                        }
                                    }
                                }
                                default: {
                                    return SLOP_STR("");
                                }
                            }
                        } else if (!_mv_138.has_value) {
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
}

slop_string expr_infer_map_key_c_type_from_slop_type(context_TranspileContext* ctx, slop_string slop_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if ((string_len(slop_type) == 0)) {
            return SLOP_STR("");
        } else {
            {
                __auto_type resolved_type = expr_resolve_type_alias_for_map(ctx, slop_type);
                __auto_type key_slop_type = expr_extract_map_key_from_slop_type(arena, resolved_type);
                if ((string_len(key_slop_type) > 0)) {
                    return expr_slop_value_type_to_c_type(ctx, key_slop_type);
                } else {
                    {
                        __auto_type elem_slop_type = expr_extract_set_elem_from_slop_type(arena, resolved_type);
                        if ((string_len(elem_slop_type) > 0)) {
                            return expr_slop_value_type_to_c_type(ctx, elem_slop_type);
                        } else {
                            return SLOP_STR("");
                        }
                    }
                }
            }
        }
    }
}

slop_string expr_infer_set_elem_c_type_from_slop_type(context_TranspileContext* ctx, slop_string slop_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if ((string_len(slop_type) == 0)) {
            return SLOP_STR("");
        } else {
            {
                __auto_type resolved_type = expr_resolve_type_alias_for_map(ctx, slop_type);
                __auto_type elem_slop_type = expr_extract_set_elem_from_slop_type(arena, resolved_type);
                if ((string_len(elem_slop_type) > 0)) {
                    return expr_slop_value_type_to_c_type(ctx, elem_slop_type);
                } else {
                    return SLOP_STR("");
                }
            }
        }
    }
}

slop_string expr_extract_map_value_from_inferred(context_TranspileContext* ctx, types_SExpr* map_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((map_expr != NULL)), "(!= map-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type inferred_slop_type = expr_infer_expr_slop_type(ctx, map_expr);
        if ((string_len(inferred_slop_type) == 0)) {
            return SLOP_STR("");
        } else {
            {
                __auto_type resolved_type = expr_resolve_type_alias_for_map(ctx, inferred_slop_type);
                return expr_extract_map_value_from_slop_type(arena, resolved_type);
            }
        }
    }
}

slop_string expr_extract_list_elem_from_inferred(context_TranspileContext* ctx, types_SExpr* list_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((list_expr != NULL)), "(!= list-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type inferred_slop_type = expr_infer_expr_slop_type(ctx, list_expr);
        if ((string_len(inferred_slop_type) == 0)) {
            return SLOP_STR("");
        } else {
            if (strlib_starts_with(inferred_slop_type, SLOP_STR("(List "))) {
                {
                    __auto_type elem_len = ((string_len(inferred_slop_type) - 6) - 1);
                    if ((elem_len > 0)) {
                        return strlib_substring(arena, inferred_slop_type, 6, ((int64_t)(elem_len)));
                    } else {
                        return SLOP_STR("");
                    }
                }
            } else {
                return SLOP_STR("");
            }
        }
    }
}

slop_string expr_infer_map_key_c_type(context_TranspileContext* ctx, types_SExpr* map_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((map_expr != NULL)), "(!= map-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_145 = (*map_expr);
        switch (_mv_145.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_145.data.sym;
                {
                    __auto_type name = sym.name;
                    __auto_type _mv_146 = context_ctx_lookup_var(ctx, name);
                    if (_mv_146.has_value) {
                        __auto_type var_entry = _mv_146.value;
                        {
                            __auto_type slop_type = var_entry.slop_type;
                            if ((string_len(slop_type) > 0)) {
                                {
                                    __auto_type resolved_type = expr_resolve_type_alias_for_map(ctx, slop_type);
                                    __auto_type key_slop_type = expr_extract_map_key_from_slop_type(arena, resolved_type);
                                    if ((string_len(key_slop_type) > 0)) {
                                        return expr_slop_value_type_to_c_type(ctx, key_slop_type);
                                    } else {
                                        {
                                            __auto_type elem_slop_type = expr_extract_set_elem_from_slop_type(arena, resolved_type);
                                            if ((string_len(elem_slop_type) > 0)) {
                                                return expr_slop_value_type_to_c_type(ctx, elem_slop_type);
                                            } else {
                                                return SLOP_STR("");
                                            }
                                        }
                                    }
                                }
                            } else {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_146.has_value) {
                        return SLOP_STR("");
                    }
                }
            }
            default: {
                return expr_infer_map_key_c_type_from_slop_type(ctx, expr_infer_expr_slop_type(ctx, map_expr));
            }
        }
    }
}

slop_string expr_extract_set_elem_from_slop_type(slop_arena* arena, slop_string slop_type) {
    {
        __auto_type len = string_len(slop_type);
        if ((len < 7)) {
            return SLOP_STR("");
        } else {
            if (!(strlib_starts_with(slop_type, SLOP_STR("(Set ")))) {
                return SLOP_STR("");
            } else {
                {
                    __auto_type elem_start = 5;
                    __auto_type elem_len = ((len - 1) - elem_start);
                    if ((elem_len > 0)) {
                        return strlib_substring(arena, slop_type, ((int64_t)(elem_start)), ((int64_t)(elem_len)));
                    } else {
                        return SLOP_STR("");
                    }
                }
            }
        }
    }
}

slop_string expr_infer_set_elem_c_type(context_TranspileContext* ctx, types_SExpr* set_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((set_expr != NULL)), "(!= set-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_147 = (*set_expr);
        switch (_mv_147.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_147.data.sym;
                {
                    __auto_type name = sym.name;
                    __auto_type _mv_148 = context_ctx_lookup_var(ctx, name);
                    if (_mv_148.has_value) {
                        __auto_type var_entry = _mv_148.value;
                        {
                            __auto_type slop_type = var_entry.slop_type;
                            if ((string_len(slop_type) > 0)) {
                                {
                                    __auto_type resolved_type = expr_resolve_type_alias_for_map(ctx, slop_type);
                                    __auto_type elem_slop_type = expr_extract_set_elem_from_slop_type(arena, resolved_type);
                                    if ((string_len(elem_slop_type) > 0)) {
                                        return expr_slop_value_type_to_c_type(ctx, elem_slop_type);
                                    } else {
                                        return SLOP_STR("");
                                    }
                                }
                            } else {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_148.has_value) {
                        return SLOP_STR("");
                    }
                }
            }
            default: {
                return expr_infer_set_elem_c_type_from_slop_type(ctx, expr_infer_expr_slop_type(ctx, set_expr));
            }
        }
    }
}

slop_string expr_compound_slop_type_to_id(slop_arena* arena, slop_string slop_type) {
    if (strlib_starts_with(slop_type, SLOP_STR("(Set "))) {
        {
            __auto_type inner = expr_extract_set_elem_from_slop_type(arena, slop_type);
            if ((string_len(inner) > 0)) {
                return string_concat(arena, SLOP_STR("set_"), expr_slop_value_type_to_option_id(arena, inner));
            } else {
                return ctype_to_c_name(arena, slop_type);
            }
        }
    } else if (strlib_starts_with(slop_type, SLOP_STR("(Map "))) {
        {
            __auto_type key_type = expr_extract_map_key_from_slop_type(arena, slop_type);
            __auto_type val_type = expr_extract_map_value_from_slop_type(arena, slop_type);
            if (((string_len(key_type) > 0) && (string_len(val_type) > 0))) {
                return string_concat(arena, SLOP_STR("map_"), string_concat(arena, expr_slop_value_type_to_option_id(arena, key_type), string_concat(arena, SLOP_STR("_"), expr_slop_value_type_to_option_id(arena, val_type))));
            } else {
                return ctype_to_c_name(arena, slop_type);
            }
        }
    } else if (strlib_starts_with(slop_type, SLOP_STR("(List "))) {
        {
            __auto_type len = string_len(slop_type);
            if ((len < 8)) {
                return ctype_to_c_name(arena, slop_type);
            } else {
                {
                    __auto_type inner_start = 6;
                    __auto_type inner_len = ((len - 1) - inner_start);
                    if ((inner_len > 0)) {
                        {
                            __auto_type inner = strlib_substring(arena, slop_type, ((int64_t)(inner_start)), ((int64_t)(inner_len)));
                            return string_concat(arena, SLOP_STR("list_"), expr_slop_value_type_to_option_id(arena, inner));
                        }
                    } else {
                        return ctype_to_c_name(arena, slop_type);
                    }
                }
            }
        }
    } else if (strlib_starts_with(slop_type, SLOP_STR("(Option "))) {
        {
            __auto_type len = string_len(slop_type);
            if ((len < 10)) {
                return ctype_to_c_name(arena, slop_type);
            } else {
                {
                    __auto_type inner_start = 8;
                    __auto_type inner_len = ((len - 1) - inner_start);
                    if ((inner_len > 0)) {
                        {
                            __auto_type inner = strlib_substring(arena, slop_type, ((int64_t)(inner_start)), ((int64_t)(inner_len)));
                            return string_concat(arena, SLOP_STR("option_"), expr_slop_value_type_to_option_id(arena, inner));
                        }
                    } else {
                        return ctype_to_c_name(arena, slop_type);
                    }
                }
            }
        }
    } else if (strlib_starts_with(slop_type, SLOP_STR("(Ptr "))) {
        {
            __auto_type len = string_len(slop_type);
            if ((len < 7)) {
                return ctype_to_c_name(arena, slop_type);
            } else {
                {
                    __auto_type inner_start = 5;
                    __auto_type inner_len = ((len - 1) - inner_start);
                    if ((inner_len > 0)) {
                        {
                            __auto_type inner = strlib_substring(arena, slop_type, ((int64_t)(inner_start)), ((int64_t)(inner_len)));
                            return string_concat(arena, expr_slop_value_type_to_option_id(arena, inner), SLOP_STR("_ptr"));
                        }
                    } else {
                        return ctype_to_c_name(arena, slop_type);
                    }
                }
            }
        }
    } else {
        return ctype_to_c_name(arena, slop_type);
    }
}

slop_string expr_slop_value_type_to_option_id(slop_arena* arena, slop_string slop_type) {
    if (string_eq(slop_type, SLOP_STR("Int"))) {
        return SLOP_STR("int");
    } else if (string_eq(slop_type, SLOP_STR("I8"))) {
        return SLOP_STR("int8_t");
    } else if (string_eq(slop_type, SLOP_STR("I16"))) {
        return SLOP_STR("int16_t");
    } else if (string_eq(slop_type, SLOP_STR("I32"))) {
        return SLOP_STR("int32_t");
    } else if (string_eq(slop_type, SLOP_STR("I64"))) {
        return SLOP_STR("int64_t");
    } else if (string_eq(slop_type, SLOP_STR("U8"))) {
        return SLOP_STR("uint8_t");
    } else if (string_eq(slop_type, SLOP_STR("U16"))) {
        return SLOP_STR("uint16_t");
    } else if (string_eq(slop_type, SLOP_STR("U32"))) {
        return SLOP_STR("uint32_t");
    } else if (string_eq(slop_type, SLOP_STR("U64"))) {
        return SLOP_STR("uint64_t");
    } else if (string_eq(slop_type, SLOP_STR("Char"))) {
        return SLOP_STR("char");
    } else if (string_eq(slop_type, SLOP_STR("Float"))) {
        return SLOP_STR("double");
    } else if (string_eq(slop_type, SLOP_STR("F32"))) {
        return SLOP_STR("float");
    } else if (string_eq(slop_type, SLOP_STR("Bool"))) {
        return SLOP_STR("uint8_t");
    } else if (string_eq(slop_type, SLOP_STR("String"))) {
        return SLOP_STR("string");
    } else if (string_eq(slop_type, SLOP_STR("Bytes"))) {
        return SLOP_STR("bytes");
    } else if (strlib_starts_with(slop_type, SLOP_STR("("))) {
        return expr_compound_slop_type_to_id(arena, slop_type);
    } else {
        return ctype_to_c_name(arena, slop_type);
    }
}

slop_string expr_infer_map_value_option_type(context_TranspileContext* ctx, types_SExpr* map_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((map_expr != NULL)), "(!= map-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_149 = (*map_expr);
        switch (_mv_149.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_149.data.sym;
                {
                    __auto_type name = sym.name;
                    __auto_type _mv_150 = context_ctx_lookup_var(ctx, name);
                    if (_mv_150.has_value) {
                        __auto_type var_entry = _mv_150.value;
                        {
                            __auto_type slop_type = var_entry.slop_type;
                            if ((string_len(slop_type) > 0)) {
                                {
                                    __auto_type value_slop_type = expr_extract_map_value_from_slop_type(arena, slop_type);
                                    if ((string_len(value_slop_type) > 0)) {
                                        {
                                            __auto_type option_id = expr_slop_value_type_to_option_id(arena, value_slop_type);
                                            return context_ctx_str(ctx, SLOP_STR("slop_option_"), option_id);
                                        }
                                    } else {
                                        return SLOP_STR("");
                                    }
                                }
                            } else {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_150.has_value) {
                        return SLOP_STR("");
                    }
                }
            }
            default: {
                return SLOP_STR("");
            }
        }
    }
}

slop_string expr_option_type_to_value_c_type(slop_arena* arena, slop_string option_type) {
    if (string_eq(option_type, SLOP_STR("slop_option_int"))) {
        return SLOP_STR("int64_t");
    } else if (string_eq(option_type, SLOP_STR("slop_option_string"))) {
        return SLOP_STR("slop_string");
    } else if (string_eq(option_type, SLOP_STR("slop_option_bool"))) {
        return SLOP_STR("uint8_t");
    } else if (string_eq(option_type, SLOP_STR("slop_option_double"))) {
        return SLOP_STR("double");
    } else if (string_eq(option_type, SLOP_STR("slop_option_char"))) {
        return SLOP_STR("char");
    } else if (string_eq(option_type, SLOP_STR("slop_option_u8"))) {
        return SLOP_STR("uint8_t");
    } else if (strlib_starts_with(option_type, SLOP_STR("slop_option_"))) {
        {
            __auto_type extracted = expr_substring_after_prefix(arena, option_type, SLOP_STR("slop_option_"));
            if (strlib_starts_with(extracted, SLOP_STR("set_"))) {
                return SLOP_STR("slop_map*");
            } else {
                return extracted;
            }
        }
    } else {
        return SLOP_STR("void");
    }
}

slop_string expr_infer_option_inner_slop_type(context_TranspileContext* ctx, types_SExpr* scrutinee) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((scrutinee != NULL)), "(!= scrutinee nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_151 = (*scrutinee);
        switch (_mv_151.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_151.data.sym;
                {
                    __auto_type name = sym.name;
                    __auto_type _mv_152 = context_ctx_lookup_var(ctx, name);
                    if (_mv_152.has_value) {
                        __auto_type var_entry = _mv_152.value;
                        {
                            __auto_type slop_type = var_entry.slop_type;
                            if (strlib_starts_with(slop_type, SLOP_STR("(Option "))) {
                                {
                                    __auto_type len = string_len(slop_type);
                                    if ((len > 9)) {
                                        {
                                            __auto_type inner_len = ((((int64_t)(len)) - 8) - 1);
                                            if ((inner_len > 0)) {
                                                return strlib_substring(arena, slop_type, 8, ((int64_t)(inner_len)));
                                            } else {
                                                return SLOP_STR("");
                                            }
                                        }
                                    } else {
                                        return SLOP_STR("");
                                    }
                                }
                            } else {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_152.has_value) {
                        return SLOP_STR("");
                    }
                }
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_151.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 2)) {
                        return SLOP_STR("");
                    } else {
                        __auto_type _mv_153 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_153.has_value) {
                            __auto_type head_expr = _mv_153.value;
                            __auto_type _mv_154 = (*head_expr);
                            switch (_mv_154.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_154.data.sym;
                                    {
                                        __auto_type op = sym.name;
                                        if (string_eq(op, SLOP_STR("map-get"))) {
                                            if ((len < 2)) {
                                                return SLOP_STR("");
                                            } else {
                                                __auto_type _mv_155 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_155.has_value) {
                                                    __auto_type map_expr = _mv_155.value;
                                                    __auto_type _mv_156 = (*map_expr);
                                                    switch (_mv_156.tag) {
                                                        case types_SExpr_sym:
                                                        {
                                                            __auto_type map_sym = _mv_156.data.sym;
                                                            {
                                                                __auto_type map_name = map_sym.name;
                                                                __auto_type _mv_157 = context_ctx_lookup_var(ctx, map_name);
                                                                if (_mv_157.has_value) {
                                                                    __auto_type var_entry = _mv_157.value;
                                                                    {
                                                                        __auto_type slop_type = var_entry.slop_type;
                                                                        if ((string_len(slop_type) > 0)) {
                                                                            {
                                                                                __auto_type resolved_type = expr_resolve_type_alias_for_map(ctx, slop_type);
                                                                                {
                                                                                    __auto_type value_type = expr_extract_map_value_from_slop_type(arena, resolved_type);
                                                                                    return expr_resolve_type_alias_for_map(ctx, value_type);
                                                                                }
                                                                            }
                                                                        } else {
                                                                            return SLOP_STR("");
                                                                        }
                                                                    }
                                                                } else if (!_mv_157.has_value) {
                                                                    return SLOP_STR("");
                                                                }
                                                            }
                                                        }
                                                        default: {
                                                            return expr_extract_map_value_from_inferred(ctx, map_expr);
                                                        }
                                                    }
                                                } else if (!_mv_155.has_value) {
                                                    return SLOP_STR("");
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("list-get"))) {
                                            if ((len < 2)) {
                                                return SLOP_STR("");
                                            } else {
                                                __auto_type _mv_158 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_158.has_value) {
                                                    __auto_type list_expr = _mv_158.value;
                                                    __auto_type _mv_159 = (*list_expr);
                                                    switch (_mv_159.tag) {
                                                        case types_SExpr_sym:
                                                        {
                                                            __auto_type list_sym = _mv_159.data.sym;
                                                            {
                                                                __auto_type list_name = list_sym.name;
                                                                __auto_type _mv_160 = context_ctx_lookup_var(ctx, list_name);
                                                                if (_mv_160.has_value) {
                                                                    __auto_type var_entry = _mv_160.value;
                                                                    {
                                                                        __auto_type slop_type = var_entry.slop_type;
                                                                        if (strlib_starts_with(slop_type, SLOP_STR("(List "))) {
                                                                            {
                                                                                __auto_type elem_len = ((string_len(slop_type) - 6) - 1);
                                                                                if ((elem_len > 0)) {
                                                                                    return strlib_substring(arena, slop_type, 6, ((int64_t)(elem_len)));
                                                                                } else {
                                                                                    return SLOP_STR("");
                                                                                }
                                                                            }
                                                                        } else {
                                                                            return SLOP_STR("");
                                                                        }
                                                                    }
                                                                } else if (!_mv_160.has_value) {
                                                                    return SLOP_STR("");
                                                                }
                                                            }
                                                        }
                                                        default: {
                                                            return expr_extract_list_elem_from_inferred(ctx, list_expr);
                                                        }
                                                    }
                                                } else if (!_mv_158.has_value) {
                                                    return SLOP_STR("");
                                                }
                                            }
                                        } else {
                                            return SLOP_STR("");
                                        }
                                    }
                                }
                                default: {
                                    return SLOP_STR("");
                                }
                            }
                        } else if (!_mv_153.has_value) {
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
}

slop_string expr_fix_ternary_none(context_TranspileContext* ctx, slop_string other_branch, slop_string this_branch) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if ((string_eq(this_branch, SLOP_STR("none")) && strlib_starts_with(other_branch, SLOP_STR("(slop_option_")))) {
        {
            __auto_type arena = (*ctx).arena;
            __auto_type _mv_161 = expr_extract_option_type(arena, other_branch);
            if (_mv_161.has_value) {
                __auto_type opt_type = _mv_161.value;
                return context_ctx_str3(ctx, SLOP_STR("("), opt_type, SLOP_STR("){.has_value = false}"));
            } else if (!_mv_161.has_value) {
                return this_branch;
            }
        }
    } else {
        return this_branch;
    }
}

slop_option_string expr_extract_option_type(slop_arena* arena, slop_string s) {
    if ((string_len(s) < 15)) {
        return (slop_option_string){.has_value = false};
    } else {
        {
            __auto_type i = 1;
            __auto_type len = string_len(s);
            __auto_type found_brace = 0;
            __auto_type end_idx = 0;
            while (((i < len) && !(found_brace))) {
                if ((strlib_char_at(s, ((int64_t)(i))) == 123)) {
                    found_brace = 1;
                    end_idx = (i - 2);
                } else {
                    i = (i + 1);
                }
            }
            if (found_brace) {
                return (slop_option_string){.has_value = 1, .value = strlib_substring(arena, s, 1, ((int64_t)(end_idx)))};
            } else {
                return (slop_option_string){.has_value = false};
            }
        }
    }
}

slop_string expr_transpile_array_index(context_TranspileContext* ctx, types_SExpr* arr_expr, slop_string arr_c, slop_string idx_c) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((arr_expr != NULL)), "(!= arr-expr nil)");
    __auto_type _mv_162 = (*arr_expr);
    switch (_mv_162.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_162.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_163 = context_ctx_lookup_var(ctx, name);
                if (_mv_163.has_value) {
                    __auto_type var_entry = _mv_163.value;
                    {
                        __auto_type c_type = var_entry.c_type;
                        if (((string_eq(c_type, SLOP_STR("slop_string"))) || (string_eq(c_type, SLOP_STR("string"))) || (strlib_starts_with(c_type, SLOP_STR("slop_list_"))))) {
                            return context_ctx_str5(ctx, SLOP_STR("("), arr_c, SLOP_STR(").data["), idx_c, SLOP_STR("]"));
                        } else {
                            return context_ctx_str4(ctx, arr_c, SLOP_STR("["), idx_c, SLOP_STR("]"));
                        }
                    }
                } else if (!_mv_163.has_value) {
                    return context_ctx_str4(ctx, arr_c, SLOP_STR("["), idx_c, SLOP_STR("]"));
                }
            }
        }
        default: {
            return context_ctx_str4(ctx, arr_c, SLOP_STR("["), idx_c, SLOP_STR("]"));
        }
    }
}

uint8_t expr_is_pointer_expr(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_164 = (*expr);
    switch (_mv_164.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_164.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_165 = context_ctx_lookup_var(ctx, name);
                if (_mv_165.has_value) {
                    __auto_type var_entry = _mv_165.value;
                    {
                        __auto_type c_type = var_entry.c_type;
                        return strlib_ends_with(c_type, SLOP_STR("*"));
                    }
                } else if (!_mv_165.has_value) {
                    return 0;
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_164.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) >= 1)) {
                    __auto_type _mv_166 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_166.has_value) {
                        __auto_type head_ptr = _mv_166.value;
                        __auto_type _mv_167 = (*head_ptr);
                        switch (_mv_167.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type head_sym = _mv_167.data.sym;
                                {
                                    __auto_type op = head_sym.name;
                                    if (string_eq(op, SLOP_STR("deref"))) {
                                        return 0;
                                    } else if (string_eq(op, SLOP_STR("addr"))) {
                                        return 1;
                                    } else if (string_eq(op, SLOP_STR("arena-alloc"))) {
                                        return 1;
                                    } else if ((string_eq(op, SLOP_STR("cast")) && (((int64_t)((items).len)) >= 2))) {
                                        __auto_type _mv_168 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_168.has_value) {
                                            __auto_type type_expr = _mv_168.value;
                                            return expr_is_pointer_type_expr(type_expr);
                                        } else if (!_mv_168.has_value) {
                                            return 0;
                                        }
                                    } else {
                                        return 0;
                                    }
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_166.has_value) {
                        return 0;
                    }
                } else {
                    return 0;
                }
            }
        }
        default: {
            return 0;
        }
    }
}

slop_string expr_extract_sizeof_type(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_169 = (*expr);
        switch (_mv_169.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_169.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len >= 2)) {
                        __auto_type _mv_170 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_170.has_value) {
                            __auto_type head_ptr = _mv_170.value;
                            __auto_type _mv_171 = (*head_ptr);
                            switch (_mv_171.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_171.data.sym;
                                    {
                                        __auto_type op = head_sym.name;
                                        if (string_eq(op, SLOP_STR("sizeof"))) {
                                            __auto_type _mv_172 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_172.has_value) {
                                                __auto_type type_expr = _mv_172.value;
                                                return context_to_c_type_prefixed(ctx, type_expr);
                                            } else if (!_mv_172.has_value) {
                                                return SLOP_STR("uint8_t");
                                            }
                                        } else if ((string_eq(op, SLOP_STR("*")) || (string_eq(op, SLOP_STR("+")) || (string_eq(op, SLOP_STR("-")) || string_eq(op, SLOP_STR("/")))))) {
                                            {
                                                __auto_type i = 1;
                                                __auto_type found = SLOP_STR("uint8_t");
                                                while ((i < len)) {
                                                    __auto_type _mv_173 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_173.has_value) {
                                                        __auto_type arg_expr = _mv_173.value;
                                                        {
                                                            __auto_type result = expr_extract_sizeof_type(ctx, arg_expr);
                                                            if (!(string_eq(result, SLOP_STR("uint8_t")))) {
                                                                found = result;
                                                            }
                                                        }
                                                    } else if (!_mv_173.has_value) {
                                                    }
                                                    i = (i + 1);
                                                }
                                                return found;
                                            }
                                        } else {
                                            return SLOP_STR("uint8_t");
                                        }
                                    }
                                }
                                default: {
                                    return SLOP_STR("uint8_t");
                                }
                            }
                        } else if (!_mv_170.has_value) {
                            return SLOP_STR("uint8_t");
                        }
                    } else {
                        return SLOP_STR("uint8_t");
                    }
                }
            }
            default: {
                return SLOP_STR("uint8_t");
            }
        }
    }
}

slop_string expr_transpile_expr(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_174 = (*expr);
    switch (_mv_174.tag) {
        case types_SExpr_num:
        {
            __auto_type _ = _mv_174.data.num;
            return expr_transpile_literal(ctx, expr);
        }
        case types_SExpr_str:
        {
            __auto_type _ = _mv_174.data.str;
            return expr_transpile_literal(ctx, expr);
        }
        case types_SExpr_sym:
        {
            __auto_type _ = _mv_174.data.sym;
            return expr_transpile_literal(ctx, expr);
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_174.data.lst;
            return expr_transpile_list_expr(ctx, lst.items);
        }
    }
}

slop_string expr_transpile_list_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type arena = (*ctx).arena;
        if ((len < 1)) {
            context_ctx_add_error_at(ctx, SLOP_STR("empty list"), context_list_first_line(items), context_list_first_col(items));
            return SLOP_STR("0");
        } else {
            __auto_type _mv_175 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_175.has_value) {
                __auto_type head_expr = _mv_175.value;
                __auto_type _mv_176 = (*head_expr);
                switch (_mv_176.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type head_sym = _mv_176.data.sym;
                        {
                            __auto_type op = head_sym.name;
                            if ((expr_is_binop(op) && (len < 3))) {
                                context_ctx_add_error_at(ctx, SLOP_STR("binary operator needs at least 2 operands"), context_list_first_line(items), context_list_first_col(items));
                                return SLOP_STR("0");
                            } else if ((expr_is_binop(op) && (len >= 3))) {
                                if ((len > 3)) {
                                    return expr_transpile_variadic_binop(ctx, op, items, 1);
                                } else {
                                    __auto_type _mv_177 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_177.has_value) {
                                        __auto_type left = _mv_177.value;
                                        __auto_type _mv_178 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_178.has_value) {
                                            __auto_type right = _mv_178.value;
                                            {
                                                __auto_type left_c = expr_transpile_expr(ctx, left);
                                                __auto_type right_c = expr_transpile_expr(ctx, right);
                                                return expr_transpile_binop(ctx, op, left_c, right_c);
                                            }
                                        } else if (!_mv_178.has_value) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("missing right operand"), context_list_first_line(items), context_list_first_col(items));
                                            return SLOP_STR("0");
                                        }
                                    } else if (!_mv_177.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing left operand"), context_list_first_line(items), context_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                }
                            } else if ((expr_is_comparison_op(op) && (len < 3))) {
                                context_ctx_add_error_at(ctx, SLOP_STR("comparison operator needs 2 operands"), context_list_first_line(items), context_list_first_col(items));
                                return SLOP_STR("0");
                            } else if ((expr_is_comparison_op(op) && (len >= 3))) {
                                __auto_type _mv_179 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_179.has_value) {
                                    __auto_type left = _mv_179.value;
                                    __auto_type _mv_180 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_180.has_value) {
                                        __auto_type right = _mv_180.value;
                                        {
                                            __auto_type left_c = expr_transpile_expr(ctx, left);
                                            __auto_type right_c = expr_transpile_expr(ctx, right);
                                            return expr_transpile_binop(ctx, op, left_c, right_c);
                                        }
                                    } else if (!_mv_180.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing right operand"), context_list_first_line(items), context_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                } else if (!_mv_179.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing left operand"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("not")) && (len < 2))) {
                                context_ctx_add_error_at(ctx, SLOP_STR("not needs an argument"), context_list_first_line(items), context_list_first_col(items));
                                return SLOP_STR("0");
                            } else if ((string_eq(op, SLOP_STR("not")) && (len >= 2))) {
                                __auto_type _mv_181 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_181.has_value) {
                                    __auto_type arg = _mv_181.value;
                                    return context_ctx_str3(ctx, SLOP_STR("!("), expr_transpile_expr(ctx, arg), SLOP_STR(")"));
                                } else if (!_mv_181.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing argument"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("if")) && (len < 4))) {
                                context_ctx_add_error_at(ctx, SLOP_STR("if expression needs condition, then, and else branches"), context_list_first_line(items), context_list_first_col(items));
                                return SLOP_STR("0");
                            } else if ((string_eq(op, SLOP_STR("if")) && (len >= 4))) {
                                __auto_type _mv_182 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_182.has_value) {
                                    __auto_type cond_expr = _mv_182.value;
                                    __auto_type _mv_183 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_183.has_value) {
                                        __auto_type then_expr = _mv_183.value;
                                        __auto_type _mv_184 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_184.has_value) {
                                            __auto_type else_expr = _mv_184.value;
                                            {
                                                __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                                                __auto_type then_c = expr_transpile_expr(ctx, then_expr);
                                                __auto_type else_c = expr_transpile_expr(ctx, else_expr);
                                                {
                                                    __auto_type final_else = expr_fix_ternary_none(ctx, then_c, else_c);
                                                    __auto_type final_then = expr_fix_ternary_none(ctx, else_c, then_c);
                                                    return context_ctx_str5(ctx, SLOP_STR("(("), cond_c, SLOP_STR(") ? "), context_ctx_str3(ctx, final_then, SLOP_STR(" : "), final_else), SLOP_STR(")"));
                                                }
                                            }
                                        } else if (!_mv_184.has_value) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("missing else"), context_list_first_line(items), context_list_first_col(items));
                                            return SLOP_STR("0");
                                        }
                                    } else if (!_mv_183.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing then"), context_list_first_line(items), context_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                } else if (!_mv_182.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing condition"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if (((string_eq(op, SLOP_STR("let")) || string_eq(op, SLOP_STR("let*"))) && (len >= 3))) {
                                return expr_transpile_let_expr(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("while")) && (len >= 3))) {
                                return expr_transpile_while_expr(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("do")) && (len >= 1))) {
                                return expr_transpile_do_expr(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("when")) && (len >= 2))) {
                                return expr_transpile_when_expr(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("set!")) && (len >= 3))) {
                                return expr_transpile_set_expr(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("match")) && (len >= 3))) {
                                return expr_transpile_match_expr(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("deref")) && (len >= 2))) {
                                __auto_type _mv_185 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_185.has_value) {
                                    __auto_type arg = _mv_185.value;
                                    return context_ctx_str3(ctx, SLOP_STR("(*"), expr_transpile_expr(ctx, arg), SLOP_STR(")"));
                                } else if (!_mv_185.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing argument"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR(".")) && (len >= 3))) {
                                __auto_type _mv_186 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_186.has_value) {
                                    __auto_type obj = _mv_186.value;
                                    __auto_type _mv_187 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_187.has_value) {
                                        __auto_type field_expr = _mv_187.value;
                                        __auto_type _mv_188 = (*field_expr);
                                        switch (_mv_188.tag) {
                                            case types_SExpr_sym:
                                            {
                                                __auto_type field_sym = _mv_188.data.sym;
                                                {
                                                    __auto_type obj_c = expr_transpile_expr(ctx, obj);
                                                    __auto_type field_c = ctype_to_c_name(arena, field_sym.name);
                                                    __auto_type is_ptr = expr_is_pointer_expr(ctx, obj);
                                                    if (is_ptr) {
                                                        return context_ctx_str3(ctx, obj_c, SLOP_STR("->"), field_c);
                                                    } else {
                                                        return context_ctx_str3(ctx, obj_c, SLOP_STR("."), field_c);
                                                    }
                                                }
                                            }
                                            default: {
                                                context_ctx_add_error_at(ctx, SLOP_STR("invalid field"), context_list_first_line(items), context_list_first_col(items));
                                                return SLOP_STR("0");
                                            }
                                        }
                                    } else if (!_mv_187.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing field"), context_list_first_line(items), context_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                } else if (!_mv_186.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing object"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("cast")) && (len >= 3))) {
                                __auto_type _mv_189 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_189.has_value) {
                                    __auto_type type_expr = _mv_189.value;
                                    __auto_type _mv_190 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_190.has_value) {
                                        __auto_type val_expr = _mv_190.value;
                                        {
                                            __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                            __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                            __auto_type is_ptr_cast = expr_is_pointer_type_expr(type_expr);
                                            __auto_type is_str_literal = expr_is_string_literal(val_expr);
                                            if ((is_ptr_cast && is_str_literal)) {
                                                return context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, c_type, context_ctx_str(ctx, SLOP_STR(")("), context_ctx_str(ctx, val_c, SLOP_STR(".data))")))));
                                            } else {
                                                return context_ctx_str5(ctx, SLOP_STR("(("), c_type, SLOP_STR(")("), val_c, SLOP_STR("))"));
                                            }
                                        }
                                    } else if (!_mv_190.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing cast value"), context_list_first_line(items), context_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                } else if (!_mv_189.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing cast type"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("c-inline")) && (len >= 2))) {
                                __auto_type _mv_191 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_191.has_value) {
                                    __auto_type str_expr = _mv_191.value;
                                    __auto_type _mv_192 = (*str_expr);
                                    switch (_mv_192.tag) {
                                        case types_SExpr_str:
                                        {
                                            __auto_type str = _mv_192.data.str;
                                            return str.value;
                                        }
                                        default: {
                                            context_ctx_add_error_at(ctx, SLOP_STR("c-inline requires string"), context_list_first_line(items), context_list_first_col(items));
                                            return SLOP_STR("");
                                        }
                                    }
                                } else if (!_mv_191.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing c-inline string"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("");
                                }
                            } else if ((string_eq(op, SLOP_STR("some")) && (len >= 2))) {
                                __auto_type _mv_193 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_193.has_value) {
                                    __auto_type val_expr = _mv_193.value;
                                    {
                                        __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                        __auto_type val_type = expr_infer_expr_c_type(ctx, val_expr);
                                        __auto_type option_type = (string_eq(val_type, SLOP_STR("slop_string")) ? SLOP_STR("slop_option_string") : (string_eq(val_type, SLOP_STR("int64_t")) ? SLOP_STR("slop_option_int") : (string_eq(val_type, SLOP_STR("double")) ? SLOP_STR("slop_option_double") : (string_eq(val_type, SLOP_STR("auto")) ? context_ctx_str3(ctx, SLOP_STR("/* TRANSPILER ERROR: cannot infer Option type for '"), val_c, SLOP_STR("' */")) : expr_infer_option_type(ctx, val_expr)))));
                                        return context_ctx_str5(ctx, SLOP_STR("("), option_type, SLOP_STR("){.has_value = 1, .value = "), val_c, SLOP_STR("}"));
                                    }
                                } else if (!_mv_193.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing some value"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("sizeof")) && (len >= 2))) {
                                __auto_type _mv_194 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_194.has_value) {
                                    __auto_type type_expr = _mv_194.value;
                                    {
                                        __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                        return context_ctx_str3(ctx, SLOP_STR("sizeof("), c_type, SLOP_STR(")"));
                                    }
                                } else if (!_mv_194.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing sizeof type"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("addr")) && (len >= 2))) {
                                __auto_type _mv_195 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_195.has_value) {
                                    __auto_type arg = _mv_195.value;
                                    return context_ctx_str3(ctx, SLOP_STR("(&"), expr_transpile_expr(ctx, arg), SLOP_STR(")"));
                                } else if (!_mv_195.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing addr argument"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("@")) && (len >= 3))) {
                                __auto_type _mv_196 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_196.has_value) {
                                    __auto_type arr_expr = _mv_196.value;
                                    __auto_type _mv_197 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_197.has_value) {
                                        __auto_type idx_expr = _mv_197.value;
                                        {
                                            __auto_type arr_c = expr_transpile_expr(ctx, arr_expr);
                                            __auto_type idx_c = expr_transpile_expr(ctx, idx_expr);
                                            return expr_transpile_array_index(ctx, arr_expr, arr_c, idx_c);
                                        }
                                    } else if (!_mv_197.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing index"), context_list_first_line(items), context_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                } else if (!_mv_196.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing array"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("arena-alloc")) && (len >= 3))) {
                                __auto_type _mv_198 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_198.has_value) {
                                    __auto_type arena_expr = _mv_198.value;
                                    __auto_type _mv_199 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_199.has_value) {
                                        __auto_type size_expr = _mv_199.value;
                                        {
                                            __auto_type arena_c = expr_transpile_expr(ctx, arena_expr);
                                            __auto_type _mv_200 = (*size_expr);
                                            switch (_mv_200.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type sym = _mv_200.data.sym;
                                                    {
                                                        __auto_type type_name = sym.name;
                                                        __auto_type _mv_201 = context_ctx_lookup_type(ctx, type_name);
                                                        if (_mv_201.has_value) {
                                                            __auto_type entry = _mv_201.value;
                                                            {
                                                                __auto_type c_type = entry.c_name;
                                                                return context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, c_type, context_ctx_str(ctx, SLOP_STR("*)slop_arena_alloc("), context_ctx_str(ctx, arena_c, context_ctx_str(ctx, SLOP_STR(", sizeof("), context_ctx_str(ctx, c_type, SLOP_STR(")))")))))));
                                                            }
                                                        } else if (!_mv_201.has_value) {
                                                            {
                                                                __auto_type size_c = expr_transpile_expr(ctx, size_expr);
                                                                __auto_type cast_type = expr_extract_sizeof_type(ctx, size_expr);
                                                                return context_ctx_str5(ctx, SLOP_STR("("), cast_type, SLOP_STR("*)slop_arena_alloc("), context_ctx_str3(ctx, arena_c, SLOP_STR(", "), size_c), SLOP_STR(")"));
                                                            }
                                                        }
                                                    }
                                                }
                                                default: {
                                                    {
                                                        __auto_type size_c = expr_transpile_expr(ctx, size_expr);
                                                        __auto_type cast_type = expr_extract_sizeof_type(ctx, size_expr);
                                                        return context_ctx_str5(ctx, SLOP_STR("("), cast_type, SLOP_STR("*)slop_arena_alloc("), context_ctx_str3(ctx, arena_c, SLOP_STR(", "), size_c), SLOP_STR(")"));
                                                    }
                                                }
                                            }
                                        }
                                    } else if (!_mv_199.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing arena-alloc size"), context_list_first_line(items), context_list_first_col(items));
                                        return SLOP_STR("NULL");
                                    }
                                } else if (!_mv_198.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing arena argument"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("NULL");
                                }
                            } else if ((string_eq(op, SLOP_STR("quote")) && (len >= 2))) {
                                __auto_type _mv_202 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_202.has_value) {
                                    __auto_type variant_expr = _mv_202.value;
                                    __auto_type _mv_203 = (*variant_expr);
                                    switch (_mv_203.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_203.data.sym;
                                            {
                                                __auto_type variant_name = sym.name;
                                                return expr_transpile_enum_variant(ctx, variant_name);
                                            }
                                        }
                                        default: {
                                            context_ctx_add_error_at(ctx, SLOP_STR("quote requires symbol"), context_list_first_line(items), context_list_first_col(items));
                                            return SLOP_STR("0");
                                        }
                                    }
                                } else if (!_mv_202.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing quote argument"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("record-new")) && (len >= 2))) {
                                return expr_transpile_record_new(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("list")) && (len >= 2))) {
                                return expr_transpile_list_literal(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("map-new")) && (len >= 2))) {
                                return expr_transpile_map_new(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("map-put")) && (len >= 4))) {
                                return expr_transpile_map_put(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("map-get")) && (len >= 3))) {
                                return expr_transpile_map_get(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("map-has")) && (len >= 3))) {
                                return expr_transpile_map_has(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("map-keys")) && (len >= 2))) {
                                return expr_transpile_map_keys(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("set")) && (len >= 2))) {
                                return expr_transpile_set_literal(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("set-new")) && (len >= 3))) {
                                return expr_transpile_set_new(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("set-put")) && (len >= 3))) {
                                return expr_transpile_set_put(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("set-has")) && (len >= 3))) {
                                return expr_transpile_set_has(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("set-remove")) && (len >= 3))) {
                                return expr_transpile_set_remove(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("set-elements")) && (len >= 2))) {
                                return expr_transpile_set_elements(ctx, items);
                            } else if ((string_eq(op, SLOP_STR("union-new")) && (len >= 3))) {
                                __auto_type _mv_204 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_204.has_value) {
                                    __auto_type type_expr = _mv_204.value;
                                    __auto_type _mv_205 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_205.has_value) {
                                        __auto_type tag_expr = _mv_205.value;
                                        __auto_type _mv_206 = (*type_expr);
                                        switch (_mv_206.tag) {
                                            case types_SExpr_sym:
                                            {
                                                __auto_type type_sym = _mv_206.data.sym;
                                                __auto_type _mv_207 = expr_extract_symbol_name(tag_expr);
                                                if (_mv_207.has_value) {
                                                    __auto_type tag_str = _mv_207.value;
                                                    {
                                                        __auto_type raw_type_name = type_sym.name;
                                                        __auto_type type_name = ({ __auto_type _mv = context_ctx_lookup_type(ctx, raw_type_name); _mv.has_value ? ({ __auto_type entry = _mv.value; entry.c_name; }) : (ctype_to_c_name(arena, raw_type_name)); });
                                                        __auto_type tag_name = ctype_to_c_name(arena, tag_str);
                                                        __auto_type tag_const = context_ctx_str(ctx, type_name, context_ctx_str(ctx, SLOP_STR("_"), tag_name));
                                                        if ((len >= 4)) {
                                                            __auto_type _mv_208 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_208.has_value) {
                                                                __auto_type val_expr = _mv_208.value;
                                                                {
                                                                    __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                                    return context_ctx_str3(ctx, SLOP_STR("(("), type_name, context_ctx_str3(ctx, SLOP_STR("){ .tag = "), tag_const, context_ctx_str5(ctx, SLOP_STR(", .data."), tag_name, SLOP_STR(" = "), val_c, SLOP_STR(" })"))));
                                                                }
                                                            } else if (!_mv_208.has_value) {
                                                                context_ctx_add_error_at(ctx, SLOP_STR("missing union value"), context_list_first_line(items), context_list_first_col(items));
                                                                return SLOP_STR("0");
                                                            }
                                                        } else {
                                                            return context_ctx_str3(ctx, SLOP_STR("(("), type_name, context_ctx_str3(ctx, SLOP_STR("){ .tag = "), tag_const, SLOP_STR(" })")));
                                                        }
                                                    }
                                                } else if (!_mv_207.has_value) {
                                                    context_ctx_add_error_at(ctx, SLOP_STR("union-new tag must be symbol"), context_list_first_line(items), context_list_first_col(items));
                                                    return SLOP_STR("0");
                                                }
                                            }
                                            default: {
                                                context_ctx_add_error_at(ctx, SLOP_STR("union-new type must be symbol"), context_list_first_line(items), context_list_first_col(items));
                                                return SLOP_STR("0");
                                            }
                                        }
                                    } else if (!_mv_205.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing union tag"), context_list_first_line(items), context_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                } else if (!_mv_204.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing union type"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("ok")) && (len >= 2))) {
                                __auto_type _mv_209 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_209.has_value) {
                                    __auto_type val_expr = _mv_209.value;
                                    {
                                        __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                        return expr_transpile_ok(ctx, val_c);
                                    }
                                } else if (!_mv_209.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing ok value"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("error")) && (len >= 2))) {
                                __auto_type _mv_210 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_210.has_value) {
                                    __auto_type val_expr = _mv_210.value;
                                    {
                                        __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                        return expr_transpile_error(ctx, val_c);
                                    }
                                } else if (!_mv_210.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing error value"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("?")) && (len >= 2))) {
                                __auto_type _mv_211 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_211.has_value) {
                                    __auto_type result_expr = _mv_211.value;
                                    {
                                        __auto_type result_c = expr_transpile_expr(ctx, result_expr);
                                        __auto_type _mv_212 = context_ctx_get_current_result_type(ctx);
                                        if (_mv_212.has_value) {
                                            __auto_type enclosing_type = _mv_212.value;
                                            return context_ctx_str5(ctx, SLOP_STR("({ __auto_type _tmp = "), result_c, SLOP_STR("; if (!_tmp.is_ok) return (("), enclosing_type, SLOP_STR("){ .is_ok = false, .data.err = _tmp.data.err }); _tmp.data.ok; })"));
                                        } else if (!_mv_212.has_value) {
                                            return context_ctx_str3(ctx, SLOP_STR("({ __auto_type _tmp = "), result_c, SLOP_STR("; if (!_tmp.is_ok) return _tmp; _tmp.data.ok; })"));
                                        }
                                    }
                                } else if (!_mv_211.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing ? argument"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("list-len")) && (len >= 2))) {
                                __auto_type _mv_213 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_213.has_value) {
                                    __auto_type list_expr = _mv_213.value;
                                    {
                                        __auto_type list_c = expr_transpile_expr(ctx, list_expr);
                                        return context_ctx_str3(ctx, SLOP_STR("((int64_t)(("), list_c, SLOP_STR(").len))"));
                                    }
                                } else if (!_mv_213.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing list-len argument"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("list-get")) && (len >= 3))) {
                                __auto_type _mv_214 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_214.has_value) {
                                    __auto_type list_expr = _mv_214.value;
                                    __auto_type _mv_215 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_215.has_value) {
                                        __auto_type idx_expr = _mv_215.value;
                                        {
                                            __auto_type list_c = expr_transpile_expr(ctx, list_expr);
                                            __auto_type idx_c = expr_transpile_expr(ctx, idx_expr);
                                            __auto_type option_type = expr_infer_list_element_option_type(ctx, list_expr);
                                            if ((string_len(option_type) > 0)) {
                                                return context_ctx_str(ctx, SLOP_STR("({ __auto_type _lst = "), context_ctx_str(ctx, list_c, context_ctx_str(ctx, SLOP_STR("; size_t _idx = (size_t)"), context_ctx_str(ctx, idx_c, context_ctx_str(ctx, SLOP_STR("; "), context_ctx_str(ctx, option_type, SLOP_STR(" _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; })")))))));
                                            } else {
                                                return context_ctx_str(ctx, SLOP_STR("({ __auto_type _lst = "), context_ctx_str(ctx, list_c, context_ctx_str(ctx, SLOP_STR("; size_t _idx = (size_t)"), context_ctx_str(ctx, idx_c, SLOP_STR("; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; })")))));
                                            }
                                        }
                                    } else if (!_mv_215.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing list-get index"), context_list_first_line(items), context_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                } else if (!_mv_214.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing list-get list argument"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("list-pop")) && (len >= 2))) {
                                __auto_type _mv_216 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_216.has_value) {
                                    __auto_type list_expr = _mv_216.value;
                                    {
                                        __auto_type list_c = expr_transpile_expr(ctx, list_expr);
                                        __auto_type option_type = expr_infer_list_element_option_type(ctx, list_expr);
                                        if ((string_len(option_type) > 0)) {
                                            return context_ctx_str(ctx, SLOP_STR("({ __auto_type _lst_p = &("), context_ctx_str(ctx, list_c, context_ctx_str(ctx, SLOP_STR("); "), context_ctx_str(ctx, option_type, SLOP_STR(" _r = {0}; if (_lst_p->len > 0) { _lst_p->len--; _r.has_value = true; _r.value = _lst_p->data[_lst_p->len]; } _r; })")))));
                                        } else {
                                            return context_ctx_str(ctx, SLOP_STR("({ __auto_type _lst_p = &("), context_ctx_str(ctx, list_c, SLOP_STR("); struct { bool has_value; __typeof__(_lst_p->data[0]) value; } _r = {0}; if (_lst_p->len > 0) { _lst_p->len--; _r.has_value = true; _r.value = _lst_p->data[_lst_p->len]; } _r; })")));
                                        }
                                    }
                                } else if (!_mv_216.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing list-pop list argument"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("list-new")) && (len >= 3))) {
                                __auto_type _mv_217 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_217.has_value) {
                                    __auto_type arena_expr = _mv_217.value;
                                    __auto_type _mv_218 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_218.has_value) {
                                        __auto_type type_expr = _mv_218.value;
                                        {
                                            __auto_type arena_c = expr_transpile_expr(ctx, arena_expr);
                                            __auto_type elem_c_type = context_to_c_type_prefixed(ctx, type_expr);
                                            __auto_type elem_id = ctype_type_to_identifier(arena, elem_c_type);
                                            __auto_type list_type = context_ctx_str(ctx, SLOP_STR("slop_list_"), elem_id);
                                            return context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, list_type, context_ctx_str(ctx, SLOP_STR("){ .data = ("), context_ctx_str(ctx, elem_c_type, context_ctx_str(ctx, SLOP_STR("*)slop_arena_alloc("), context_ctx_str(ctx, arena_c, context_ctx_str(ctx, SLOP_STR(", 16 * sizeof("), context_ctx_str(ctx, elem_c_type, SLOP_STR(")), .len = 0, .cap = 16 })")))))))));
                                        }
                                    } else if (!_mv_218.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing list-new type argument"), context_list_first_line(items), context_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                } else if (!_mv_217.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing list-new arena argument"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("list-push")) && (len >= 3))) {
                                __auto_type _mv_219 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_219.has_value) {
                                    __auto_type list_expr = _mv_219.value;
                                    __auto_type _mv_220 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_220.has_value) {
                                        __auto_type item_expr = _mv_220.value;
                                        {
                                            __auto_type list_c = expr_transpile_expr(ctx, list_expr);
                                            __auto_type item_c = expr_transpile_expr(ctx, item_expr);
                                            __auto_type arena_c = expr_get_arena_for_list_push_expr(ctx, list_expr, list_c);
                                            {
                                                __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _lst_p = &("), list_c);
                                                __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("); __auto_type _item = ("));
                                                __auto_type s3 = context_ctx_str(ctx, s2, item_c);
                                                __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR("); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc("));
                                                __auto_type s5 = context_ctx_str(ctx, s4, arena_c);
                                                __auto_type s6 = context_ctx_str(ctx, s5, SLOP_STR(", _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; })"));
                                                return s6;
                                            }
                                        }
                                    } else if (!_mv_220.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing list-push item"), context_list_first_line(items), context_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                } else if (!_mv_219.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing list-push list"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            } else if ((string_eq(op, SLOP_STR("none")) && (len == 1))) {
                                __auto_type _mv_221 = context_ctx_get_current_return_type(ctx);
                                if (_mv_221.has_value) {
                                    __auto_type ret_type = _mv_221.value;
                                    if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                                        return context_ctx_str3(ctx, SLOP_STR("(("), ret_type, SLOP_STR("){.has_value = false})"));
                                    } else {
                                        return SLOP_STR("none");
                                    }
                                } else if (!_mv_221.has_value) {
                                    return SLOP_STR("none");
                                }
                            } else if (string_eq(op, SLOP_STR("cond"))) {
                                return expr_transpile_cond_expr(ctx, items);
                            } else if (string_eq(op, SLOP_STR("for"))) {
                                return expr_transpile_for_as_expr(ctx, items);
                            } else if (string_eq(op, SLOP_STR("for-each"))) {
                                return expr_transpile_for_each_as_expr(ctx, items);
                            } else {
                                return expr_transpile_fn_call(ctx, op, items);
                            }
                        }
                    }
                    default: {
                        {
                            __auto_type head_c = expr_transpile_expr(ctx, head_expr);
                            __auto_type args = SLOP_STR("");
                            __auto_type i = 1;
                            while ((i < len)) {
                                __auto_type _mv_222 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_222.has_value) {
                                    __auto_type arg = _mv_222.value;
                                    {
                                        __auto_type arg_c = expr_transpile_expr(ctx, arg);
                                        if (string_eq(args, SLOP_STR(""))) {
                                            args = arg_c;
                                        } else {
                                            args = context_ctx_str3(ctx, args, SLOP_STR(", "), arg_c);
                                        }
                                    }
                                } else if (!_mv_222.has_value) {
                                }
                                i = (i + 1);
                            }
                            return context_ctx_str5(ctx, head_c, SLOP_STR("("), args, SLOP_STR(")"), SLOP_STR(""));
                        }
                    }
                }
            } else if (!_mv_175.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("empty list"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("0");
            }
        }
    }
}

slop_string expr_transpile_fn_call(context_TranspileContext* ctx, slop_string fn_name, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (string_eq(fn_name, SLOP_STR("println"))) {
            if ((len < 2)) {
                return SLOP_STR("printf(\"\\n\")");
            } else {
                __auto_type _mv_223 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_223.has_value) {
                    __auto_type arg = _mv_223.value;
                    return expr_transpile_print(ctx, arg, 1);
                } else if (!_mv_223.has_value) {
                    return SLOP_STR("printf(\"\\n\")");
                }
            }
        } else if (string_eq(fn_name, SLOP_STR("print"))) {
            if ((len < 2)) {
                context_ctx_add_error_at(ctx, SLOP_STR("print: missing argument"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("0");
            } else {
                __auto_type _mv_224 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_224.has_value) {
                    __auto_type arg = _mv_224.value;
                    return expr_transpile_print(ctx, arg, 0);
                } else if (!_mv_224.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("print: missing argument"), context_list_first_line(items), context_list_first_col(items));
                    return SLOP_STR("0");
                }
            }
        } else if (string_eq(fn_name, SLOP_STR("printf"))) {
            return expr_transpile_printf_call(ctx, items);
        } else if (string_eq(fn_name, SLOP_STR("min"))) {
            if ((len < 3)) {
                context_ctx_add_error_at(ctx, SLOP_STR("min: need 2 arguments"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("0");
            } else {
                __auto_type _mv_225 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_225.has_value) {
                    __auto_type a_expr = _mv_225.value;
                    __auto_type _mv_226 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_226.has_value) {
                        __auto_type b_expr = _mv_226.value;
                        {
                            __auto_type a_c = expr_transpile_expr(ctx, a_expr);
                            __auto_type b_c = expr_transpile_expr(ctx, b_expr);
                            __auto_type s1 = string_concat(arena, SLOP_STR("(("), a_c);
                            __auto_type s2 = string_concat(arena, s1, SLOP_STR(") < ("));
                            __auto_type s3 = string_concat(arena, s2, b_c);
                            __auto_type s4 = string_concat(arena, s3, SLOP_STR(") ? ("));
                            __auto_type s5 = string_concat(arena, s4, a_c);
                            __auto_type s6 = string_concat(arena, s5, SLOP_STR(") : ("));
                            __auto_type s7 = string_concat(arena, s6, b_c);
                            __auto_type s8 = string_concat(arena, s7, SLOP_STR("))"));
                            return s8;
                        }
                    } else if (!_mv_226.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("min: missing second argument"), context_list_first_line(items), context_list_first_col(items));
                        return SLOP_STR("0");
                    }
                } else if (!_mv_225.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("min: missing first argument"), context_list_first_line(items), context_list_first_col(items));
                    return SLOP_STR("0");
                }
            }
        } else if (string_eq(fn_name, SLOP_STR("max"))) {
            if ((len < 3)) {
                context_ctx_add_error_at(ctx, SLOP_STR("max: need 2 arguments"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("0");
            } else {
                __auto_type _mv_227 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_227.has_value) {
                    __auto_type a_expr = _mv_227.value;
                    __auto_type _mv_228 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_228.has_value) {
                        __auto_type b_expr = _mv_228.value;
                        {
                            __auto_type a_c = expr_transpile_expr(ctx, a_expr);
                            __auto_type b_c = expr_transpile_expr(ctx, b_expr);
                            __auto_type s1 = string_concat(arena, SLOP_STR("(("), a_c);
                            __auto_type s2 = string_concat(arena, s1, SLOP_STR(") > ("));
                            __auto_type s3 = string_concat(arena, s2, b_c);
                            __auto_type s4 = string_concat(arena, s3, SLOP_STR(") ? ("));
                            __auto_type s5 = string_concat(arena, s4, a_c);
                            __auto_type s6 = string_concat(arena, s5, SLOP_STR(") : ("));
                            __auto_type s7 = string_concat(arena, s6, b_c);
                            __auto_type s8 = string_concat(arena, s7, SLOP_STR("))"));
                            return s8;
                        }
                    } else if (!_mv_228.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("max: missing second argument"), context_list_first_line(items), context_list_first_col(items));
                        return SLOP_STR("0");
                    }
                } else if (!_mv_227.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("max: missing first argument"), context_list_first_line(items), context_list_first_col(items));
                    return SLOP_STR("0");
                }
            }
        } else {
            __auto_type _mv_229 = context_ctx_lookup_type(ctx, fn_name);
            if (_mv_229.has_value) {
                __auto_type type_entry = _mv_229.value;
                if (type_entry.is_union) {
                    return expr_transpile_union_constructor(ctx, fn_name, type_entry.c_name, items);
                } else {
                    {
                        __auto_type c_name = type_entry.c_name;
                        __auto_type type_name = fn_name;
                        __auto_type args = SLOP_STR("");
                        __auto_type i = 1;
                        __auto_type field_idx = 0;
                        while ((i < len)) {
                            __auto_type _mv_230 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_230.has_value) {
                                __auto_type arg = _mv_230.value;
                                {
                                    __auto_type arg_c = expr_transpile_expr(ctx, arg);
                                    __auto_type field_type_opt = context_ctx_lookup_field_type_by_index(ctx, type_name, field_idx);
                                    __auto_type final_arg = ({ __auto_type _mv = field_type_opt; _mv.has_value ? ({ __auto_type field_type = _mv.value; expr_typed_none_arg(ctx, field_type, arg_c); }) : (arg_c); });
                                    if (string_eq(args, SLOP_STR(""))) {
                                        args = final_arg;
                                    } else {
                                        args = context_ctx_str3(ctx, args, SLOP_STR(", "), final_arg);
                                    }
                                    field_idx = (field_idx + 1);
                                }
                            } else if (!_mv_230.has_value) {
                            }
                            i = (i + 1);
                        }
                        return context_ctx_str5(ctx, SLOP_STR("("), c_name, SLOP_STR("){"), args, SLOP_STR("}"));
                    }
                }
            } else if (!_mv_229.has_value) {
                {
                    __auto_type builtin_c_name = expr_get_builtin_type_c_name(fn_name);
                    if ((string_len(builtin_c_name) > 0)) {
                        return expr_transpile_builtin_constructor(ctx, fn_name, items);
                    } else {
                        __auto_type _mv_231 = context_ctx_lookup_enum_variant(ctx, fn_name);
                        if (_mv_231.has_value) {
                            __auto_type type_name = _mv_231.value;
                            {
                                __auto_type c_variant = ctype_to_c_name(arena, fn_name);
                                __auto_type c_tag_enum = context_ctx_str3(ctx, type_name, SLOP_STR("_"), c_variant);
                                if ((len >= 2)) {
                                    __auto_type _mv_232 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_232.has_value) {
                                        __auto_type value_expr = _mv_232.value;
                                        {
                                            __auto_type value_c = expr_transpile_expr(ctx, value_expr);
                                            return context_ctx_str3(ctx, SLOP_STR("(("), type_name, context_ctx_str3(ctx, SLOP_STR("){ .tag = "), c_tag_enum, context_ctx_str5(ctx, SLOP_STR(", .data."), c_variant, SLOP_STR(" = "), value_c, SLOP_STR(" })"))));
                                        }
                                    } else if (!_mv_232.has_value) {
                                        return context_ctx_str3(ctx, SLOP_STR("(("), type_name, context_ctx_str3(ctx, SLOP_STR("){ .tag = "), c_tag_enum, SLOP_STR(" })")));
                                    }
                                } else {
                                    return context_ctx_str3(ctx, SLOP_STR("(("), type_name, context_ctx_str3(ctx, SLOP_STR("){ .tag = "), c_tag_enum, SLOP_STR(" })")));
                                }
                            }
                        } else if (!_mv_231.has_value) {
                            {
                                __auto_type func_opt = context_ctx_lookup_func(ctx, fn_name);
                                __auto_type args = SLOP_STR("");
                                __auto_type i = 1;
                                __auto_type param_idx = 0;
                                while ((i < len)) {
                                    __auto_type _mv_233 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_233.has_value) {
                                        __auto_type arg = _mv_233.value;
                                        {
                                            __auto_type arg_c = expr_transpile_expr(ctx, arg);
                                            __auto_type expected_type = ({ __auto_type _mv = func_opt; _mv.has_value ? ({ __auto_type func_entry = _mv.value; ({ __auto_type _mv = ({ __auto_type _lst = func_entry.param_types; size_t _idx = (size_t)param_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type p = _mv.value; (*p).c_type; }) : (SLOP_STR("")); }); }) : (SLOP_STR("")); });
                                            __auto_type final_arg = expr_typed_none_arg(ctx, expected_type, arg_c);
                                            if (string_eq(args, SLOP_STR(""))) {
                                                args = final_arg;
                                            } else {
                                                args = context_ctx_str3(ctx, args, SLOP_STR(", "), final_arg);
                                            }
                                            param_idx = (param_idx + 1);
                                        }
                                    } else if (!_mv_233.has_value) {
                                    }
                                    i = (i + 1);
                                }
                                return expr_transpile_call(ctx, fn_name, args);
                            }
                        }
                    }
                }
            }
        }
    }
}

slop_string expr_transpile_print(context_TranspileContext* ctx, types_SExpr* arg, uint8_t newline) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((arg != NULL)), "(!= arg nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type nl = ((newline) ? SLOP_STR("\\n") : SLOP_STR(""));
        __auto_type _mv_234 = (*arg);
        switch (_mv_234.tag) {
            case types_SExpr_str:
            {
                __auto_type s = _mv_234.data.str;
                return context_ctx_str5(ctx, SLOP_STR("printf(\"%s"), nl, SLOP_STR("\", \""), s.value, SLOP_STR("\")"));
            }
            case types_SExpr_num:
            {
                __auto_type n = _mv_234.data.num;
                if (expr_string_contains(n.raw, SLOP_STR("."))) {
                    return context_ctx_str5(ctx, SLOP_STR("printf(\"%f"), nl, SLOP_STR("\", "), n.raw, SLOP_STR(")"));
                } else {
                    return context_ctx_str5(ctx, SLOP_STR("printf(\"%lld"), nl, SLOP_STR("\", (long long)("), n.raw, SLOP_STR("))"));
                }
            }
            default: {
                {
                    __auto_type arg_c = expr_transpile_expr(ctx, arg);
                    __auto_type _mv_235 = expr_get_expr_type_hint(ctx, arg);
                    if (_mv_235.has_value) {
                        __auto_type type_hint = _mv_235.value;
                        if ((string_eq(type_hint, SLOP_STR("String")) || string_eq(type_hint, SLOP_STR("slop_string")))) {
                            return expr_transpile_print_string(ctx, arg_c, nl);
                        } else if ((string_eq(type_hint, SLOP_STR("Bool")) || string_eq(type_hint, SLOP_STR("uint8_t")))) {
                            return context_ctx_str5(ctx, SLOP_STR("printf(\"%s"), nl, SLOP_STR("\", ("), arg_c, SLOP_STR(") ? \"true\" : \"false\")"));
                        } else if ((string_eq(type_hint, SLOP_STR("Float")) || string_eq(type_hint, SLOP_STR("double")))) {
                            return context_ctx_str5(ctx, SLOP_STR("printf(\"%f"), nl, SLOP_STR("\", "), arg_c, SLOP_STR(")"));
                        } else {
                            return context_ctx_str5(ctx, SLOP_STR("printf(\"%lld"), nl, SLOP_STR("\", (long long)("), arg_c, SLOP_STR("))"));
                        }
                    } else if (!_mv_235.has_value) {
                        return context_ctx_str5(ctx, SLOP_STR("printf(\"%lld"), nl, SLOP_STR("\", (long long)("), arg_c, SLOP_STR("))"));
                    }
                }
            }
        }
    }
}

slop_string expr_transpile_print_string(context_TranspileContext* ctx, slop_string arg_c, slop_string nl) {
    {
        __auto_type arena = (*ctx).arena;
        return string_concat(arena, string_concat(arena, string_concat(arena, SLOP_STR("printf(\"%.*s"), nl), string_concat(arena, SLOP_STR("\", (int)("), arg_c)), string_concat(arena, SLOP_STR(").len, ("), string_concat(arena, arg_c, SLOP_STR(").data)"))));
    }
}

slop_string expr_transpile_printf_call(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type args = SLOP_STR("");
        __auto_type i = 1;
        while ((i < len)) {
            __auto_type _mv_236 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_236.has_value) {
                __auto_type arg = _mv_236.value;
                {
                    __auto_type arg_c = ({ __auto_type _mv = (*arg); slop_string _mr = {0}; switch (_mv.tag) { case types_SExpr_str: { __auto_type s = _mv.data.str; _mr = context_ctx_str3(ctx, SLOP_STR("\""), expr_escape_c_string(ctx, s.value), SLOP_STR("\"")); break; } default: { _mr = expr_transpile_expr(ctx, arg); break; }  } _mr; });
                    if (string_eq(args, SLOP_STR(""))) {
                        args = arg_c;
                    } else {
                        args = context_ctx_str3(ctx, args, SLOP_STR(", "), arg_c);
                    }
                }
            } else if (!_mv_236.has_value) {
            }
            i = (i + 1);
        }
        return context_ctx_str3(ctx, SLOP_STR("printf("), args, SLOP_STR(")"));
    }
}

uint8_t expr_string_contains(slop_string s, slop_string substr) {
    return (strlib_count_occurrences(s, substr) > 0);
}

slop_option_string expr_get_expr_type_hint(context_TranspileContext* ctx, types_SExpr* expr) {
    __auto_type _mv_237 = (*expr);
    switch (_mv_237.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_237.data.sym;
            __auto_type _mv_238 = context_ctx_lookup_var(ctx, sym.name);
            if (_mv_238.has_value) {
                __auto_type entry = _mv_238.value;
                return (slop_option_string){.has_value = 1, .value = entry.c_type};
            } else if (!_mv_238.has_value) {
                return (slop_option_string){.has_value = false};
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_237.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) >= 1)) {
                    __auto_type _mv_239 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_239.has_value) {
                        __auto_type head = _mv_239.value;
                        __auto_type _mv_240 = (*head);
                        switch (_mv_240.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type head_sym = _mv_240.data.sym;
                                {
                                    __auto_type op = head_sym.name;
                                    if ((string_eq(op, SLOP_STR(".")) && (((int64_t)((items).len)) >= 3))) {
                                        __auto_type _mv_241 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_241.has_value) {
                                            __auto_type field_expr = _mv_241.value;
                                            __auto_type _mv_242 = (*field_expr);
                                            switch (_mv_242.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type field_sym = _mv_242.data.sym;
                                                    {
                                                        __auto_type field_name = field_sym.name;
                                                        if (string_eq(field_name, SLOP_STR("message"))) {
                                                            return (slop_option_string){.has_value = 1, .value = SLOP_STR("slop_string")};
                                                        } else if (string_eq(field_name, SLOP_STR("name"))) {
                                                            return (slop_option_string){.has_value = 1, .value = SLOP_STR("slop_string")};
                                                        } else if (string_eq(field_name, SLOP_STR("value"))) {
                                                            return (slop_option_string){.has_value = 1, .value = SLOP_STR("slop_string")};
                                                        } else if (string_eq(field_name, SLOP_STR("line"))) {
                                                            return (slop_option_string){.has_value = 1, .value = SLOP_STR("int64_t")};
                                                        } else if (string_eq(field_name, SLOP_STR("col"))) {
                                                            return (slop_option_string){.has_value = 1, .value = SLOP_STR("int64_t")};
                                                        } else {
                                                            return (slop_option_string){.has_value = false};
                                                        }
                                                    }
                                                }
                                                default: {
                                                    return (slop_option_string){.has_value = false};
                                                }
                                            }
                                        } else if (!_mv_241.has_value) {
                                            return (slop_option_string){.has_value = false};
                                        }
                                    } else {
                                        if (string_eq(op, SLOP_STR("pretty-print"))) {
                                            return (slop_option_string){.has_value = 1, .value = SLOP_STR("slop_string")};
                                        } else if (string_eq(op, SLOP_STR("string-copy"))) {
                                            return (slop_option_string){.has_value = 1, .value = SLOP_STR("slop_string")};
                                        } else if (string_eq(op, SLOP_STR("string-concat"))) {
                                            return (slop_option_string){.has_value = 1, .value = SLOP_STR("slop_string")};
                                        } else if (string_eq(op, SLOP_STR("int-to-string"))) {
                                            return (slop_option_string){.has_value = 1, .value = SLOP_STR("slop_string")};
                                        } else {
                                            __auto_type _mv_243 = context_ctx_lookup_func(ctx, op);
                                            if (_mv_243.has_value) {
                                                __auto_type func_entry = _mv_243.value;
                                                if (func_entry.returns_string) {
                                                    return (slop_option_string){.has_value = 1, .value = SLOP_STR("slop_string")};
                                                } else {
                                                    return (slop_option_string){.has_value = false};
                                                }
                                            } else if (!_mv_243.has_value) {
                                                return (slop_option_string){.has_value = false};
                                            }
                                        }
                                    }
                                }
                            }
                            default: {
                                return (slop_option_string){.has_value = false};
                            }
                        }
                    } else if (!_mv_239.has_value) {
                        return (slop_option_string){.has_value = false};
                    }
                } else {
                    return (slop_option_string){.has_value = false};
                }
            }
        }
        default: {
            return (slop_option_string){.has_value = false};
        }
    }
}

slop_string expr_transpile_union_constructor(context_TranspileContext* ctx, slop_string type_name, slop_string c_type_name, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if ((len < 2)) {
            return context_ctx_str3(ctx, SLOP_STR("(("), c_type_name, SLOP_STR("){})"));
        } else {
            __auto_type _mv_244 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_244.has_value) {
                __auto_type tag_expr = _mv_244.value;
                __auto_type _mv_245 = (*tag_expr);
                switch (_mv_245.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type tag_list = _mv_245.data.lst;
                        {
                            __auto_type tag_items = tag_list.items;
                            if ((((int64_t)((tag_items).len)) < 1)) {
                                return context_ctx_str3(ctx, SLOP_STR("(("), c_type_name, SLOP_STR("){})"));
                            } else {
                                __auto_type _mv_246 = ({ __auto_type _lst = tag_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_246.has_value) {
                                    __auto_type tag_name_expr = _mv_246.value;
                                    __auto_type _mv_247 = (*tag_name_expr);
                                    switch (_mv_247.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type tag_sym = _mv_247.data.sym;
                                            {
                                                __auto_type tag_name = tag_sym.name;
                                                __auto_type c_tag_name = ctype_to_c_name(arena, tag_name);
                                                __auto_type c_tag_enum = context_ctx_str(ctx, c_type_name, context_ctx_str(ctx, SLOP_STR("_"), c_tag_name));
                                                if ((((int64_t)((tag_items).len)) >= 2)) {
                                                    __auto_type _mv_248 = ({ __auto_type _lst = tag_items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_248.has_value) {
                                                        __auto_type value_expr = _mv_248.value;
                                                        {
                                                            __auto_type value_c = expr_transpile_expr(ctx, value_expr);
                                                            return context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, c_type_name, context_ctx_str(ctx, SLOP_STR("){ .tag = "), context_ctx_str(ctx, c_tag_enum, context_ctx_str(ctx, SLOP_STR(", .data."), context_ctx_str(ctx, c_tag_name, context_ctx_str(ctx, SLOP_STR(" = "), context_ctx_str(ctx, value_c, SLOP_STR(" })")))))))));
                                                        }
                                                    } else if (!_mv_248.has_value) {
                                                        return context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, c_type_name, context_ctx_str(ctx, SLOP_STR("){ .tag = "), context_ctx_str(ctx, c_tag_enum, SLOP_STR(" })")))));
                                                    }
                                                } else {
                                                    return context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, c_type_name, context_ctx_str(ctx, SLOP_STR("){ .tag = "), context_ctx_str(ctx, c_tag_enum, SLOP_STR(" })")))));
                                                }
                                            }
                                        }
                                        default: {
                                            return context_ctx_str3(ctx, SLOP_STR("(("), c_type_name, SLOP_STR("){})/* tag not symbol */"));
                                        }
                                    }
                                } else if (!_mv_246.has_value) {
                                    return context_ctx_str3(ctx, SLOP_STR("(("), c_type_name, SLOP_STR("){})/* no tag */"));
                                }
                            }
                        }
                    }
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_245.data.sym;
                        {
                            __auto_type tag_name = sym.name;
                            __auto_type c_tag_name = ctype_to_c_name(arena, tag_name);
                            __auto_type c_tag_enum = context_ctx_str(ctx, c_type_name, context_ctx_str(ctx, SLOP_STR("_"), c_tag_name));
                            return context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, c_type_name, context_ctx_str(ctx, SLOP_STR("){ .tag = "), context_ctx_str(ctx, c_tag_enum, SLOP_STR(" })")))));
                        }
                    }
                    default: {
                        return context_ctx_str3(ctx, SLOP_STR("(("), c_type_name, SLOP_STR("){})/* unknown tag form */"));
                    }
                }
            } else if (!_mv_244.has_value) {
                return context_ctx_str3(ctx, SLOP_STR("(("), c_type_name, SLOP_STR("){})/* no args */"));
            }
        }
    }
}

slop_string expr_transpile_cond_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result_type = expr_infer_cond_result_c_type(ctx, items);
        __auto_type result = SLOP_STR("");
        __auto_type i = 1;
        while ((i < len)) {
            __auto_type _mv_249 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_249.has_value) {
                __auto_type clause_expr = _mv_249.value;
                __auto_type _mv_250 = (*clause_expr);
                switch (_mv_250.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type clause_lst = _mv_250.data.lst;
                        {
                            __auto_type clause_items = clause_lst.items;
                            __auto_type clause_len = ((int64_t)((clause_items).len));
                            if ((clause_len >= 2)) {
                                __auto_type _mv_251 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_251.has_value) {
                                    __auto_type test_expr = _mv_251.value;
                                    __auto_type _mv_252 = (*test_expr);
                                    switch (_mv_252.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_252.data.sym;
                                            if (string_eq(sym.name, SLOP_STR("else"))) {
                                                __auto_type _mv_253 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)(clause_len - 1); struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_253.has_value) {
                                                    __auto_type body_expr = _mv_253.value;
                                                    {
                                                        __auto_type body_c = expr_transpile_expr(ctx, body_expr);
                                                        result = context_ctx_str(ctx, result, expr_typed_none(ctx, result_type, body_c));
                                                    }
                                                } else if (!_mv_253.has_value) {
                                                    result = context_ctx_str(ctx, result, SLOP_STR("0"));
                                                }
                                            } else {
                                                {
                                                    __auto_type test_c = expr_transpile_expr(ctx, test_expr);
                                                    __auto_type _mv_254 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)(clause_len - 1); struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_254.has_value) {
                                                        __auto_type body_expr = _mv_254.value;
                                                        {
                                                            __auto_type body_c = expr_typed_none(ctx, result_type, expr_transpile_expr(ctx, body_expr));
                                                            result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR("("), context_ctx_str(ctx, test_c, context_ctx_str(ctx, SLOP_STR(" ? "), context_ctx_str(ctx, body_c, SLOP_STR(" : "))))));
                                                        }
                                                    } else if (!_mv_254.has_value) {
                                                        result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR("("), context_ctx_str(ctx, test_c, SLOP_STR(" ? 0 : "))));
                                                    }
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            {
                                                __auto_type test_c = expr_transpile_expr(ctx, test_expr);
                                                __auto_type _mv_255 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)(clause_len - 1); struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_255.has_value) {
                                                    __auto_type body_expr = _mv_255.value;
                                                    {
                                                        __auto_type body_c = expr_typed_none(ctx, result_type, expr_transpile_expr(ctx, body_expr));
                                                        result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR("("), context_ctx_str(ctx, test_c, context_ctx_str(ctx, SLOP_STR(" ? "), context_ctx_str(ctx, body_c, SLOP_STR(" : "))))));
                                                    }
                                                } else if (!_mv_255.has_value) {
                                                    result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR("("), context_ctx_str(ctx, test_c, SLOP_STR(" ? 0 : "))));
                                                }
                                            }
                                            break;
                                        }
                                    }
                                } else if (!_mv_251.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_249.has_value) {
            }
            i = (i + 1);
        }
        if (string_eq(result, SLOP_STR(""))) {
            return SLOP_STR("0");
        } else {
            {
                __auto_type open_count = 0;
                __auto_type j = 0;
                __auto_type rlen = string_len(result);
                while ((j < ((int64_t)(rlen)))) {
                    {
                        __auto_type c = strlib_char_at(result, ((int64_t)(j)));
                        if ((c == 40)) {
                            open_count = (open_count + 1);
                        } else if ((c == 41)) {
                            open_count = (open_count - 1);
                        } else {
                        }
                    }
                    j = (j + 1);
                }
                while ((open_count > 0)) {
                    result = context_ctx_str(ctx, result, SLOP_STR(")"));
                    open_count = (open_count - 1);
                }
                return result;
            }
        }
    }
}

slop_string expr_transpile_match_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if ((len < 3)) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid match expr"), context_list_first_line(items), context_list_first_col(items));
            return SLOP_STR("0");
        } else {
            __auto_type _mv_256 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_256.has_value) {
                __auto_type scrutinee = _mv_256.value;
                {
                    __auto_type scrutinee_c = expr_transpile_expr(ctx, scrutinee);
                    __auto_type patterns = expr_collect_match_patterns(ctx, items);
                    if (expr_is_option_patterns(patterns)) {
                        return expr_build_option_match_expr(ctx, scrutinee, scrutinee_c, items);
                    } else if (expr_is_result_patterns(patterns)) {
                        return expr_build_result_match_expr(ctx, scrutinee, scrutinee_c, items);
                    } else if (expr_is_union_expr_patterns(ctx, patterns)) {
                        return expr_build_union_match_expr(ctx, scrutinee, scrutinee_c, items);
                    } else {
                        return expr_build_ternary_match_expr(ctx, scrutinee_c, items);
                    }
                }
            } else if (!_mv_256.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing match scrutinee"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("0");
            }
        }
    }
}

slop_list_types_SExpr_ptr expr_collect_match_patterns(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
        __auto_type i = 2;
        while ((i < len)) {
            __auto_type _mv_257 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_257.has_value) {
                __auto_type branch = _mv_257.value;
                __auto_type _mv_258 = (*branch);
                switch (_mv_258.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_258.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if ((((int64_t)((branch_items).len)) >= 1)) {
                                __auto_type _mv_259 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_259.has_value) {
                                    __auto_type pattern = _mv_259.value;
                                    ({ __auto_type _lst_p = &(result); __auto_type _item = (pattern); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                } else if (!_mv_259.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_257.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_string expr_get_expr_pattern_tag(types_SExpr* pat_expr) {
    SLOP_PRE(((pat_expr != NULL)), "(!= pat-expr nil)");
    __auto_type _mv_260 = (*pat_expr);
    switch (_mv_260.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_260.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_261 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_261.has_value) {
                        __auto_type head = _mv_261.value;
                        __auto_type _mv_262 = (*head);
                        switch (_mv_262.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_262.data.sym;
                                return sym.name;
                            }
                            default: {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_261.has_value) {
                        return SLOP_STR("");
                    }
                }
            }
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_260.data.sym;
            return sym.name;
        }
        default: {
            return SLOP_STR("");
        }
    }
}

uint8_t expr_is_option_patterns(slop_list_types_SExpr_ptr patterns) {
    {
        __auto_type len = ((int64_t)((patterns).len));
        __auto_type found = 0;
        __auto_type i = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_263 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_263.has_value) {
                __auto_type pat = _mv_263.value;
                {
                    __auto_type tag = expr_get_expr_pattern_tag(pat);
                    if ((string_eq(tag, SLOP_STR("some")) || string_eq(tag, SLOP_STR("none")))) {
                        found = 1;
                    }
                }
            } else if (!_mv_263.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

uint8_t expr_is_result_patterns(slop_list_types_SExpr_ptr patterns) {
    {
        __auto_type len = ((int64_t)((patterns).len));
        __auto_type found = 0;
        __auto_type i = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_264 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_264.has_value) {
                __auto_type pat = _mv_264.value;
                {
                    __auto_type tag = expr_get_expr_pattern_tag(pat);
                    if ((string_eq(tag, SLOP_STR("ok")) || string_eq(tag, SLOP_STR("error")))) {
                        found = 1;
                    }
                }
            } else if (!_mv_264.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

uint8_t expr_is_union_expr_patterns(context_TranspileContext* ctx, slop_list_types_SExpr_ptr patterns) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((patterns).len));
        __auto_type has_union_variant = 0;
        __auto_type i = 0;
        while (((i < len) && !(has_union_variant))) {
            __auto_type _mv_265 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_265.has_value) {
                __auto_type pat_expr = _mv_265.value;
                {
                    __auto_type tag = expr_get_expr_pattern_tag(pat_expr);
                    if (((!(string_eq(tag, SLOP_STR("")))) && (!(string_eq(tag, SLOP_STR("some")))) && (!(string_eq(tag, SLOP_STR("none")))) && (!(string_eq(tag, SLOP_STR("ok")))) && (!(string_eq(tag, SLOP_STR("error")))) && (!(string_eq(tag, SLOP_STR("else")))) && (!(string_eq(tag, SLOP_STR("_")))))) {
                        __auto_type _mv_266 = context_ctx_lookup_enum_variant(ctx, tag);
                        if (_mv_266.has_value) {
                            __auto_type _ = _mv_266.value;
                            has_union_variant = 1;
                        } else if (!_mv_266.has_value) {
                        }
                    }
                }
            } else if (!_mv_265.has_value) {
            }
            i = (i + 1);
        }
        return has_union_variant;
    }
}

slop_option_string expr_get_expr_binding_name(types_SExpr* pat_expr) {
    SLOP_PRE(((pat_expr != NULL)), "(!= pat-expr nil)");
    __auto_type _mv_267 = (*pat_expr);
    switch (_mv_267.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_267.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 2)) {
                    return (slop_option_string){.has_value = false};
                } else {
                    __auto_type _mv_268 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_268.has_value) {
                        __auto_type binding = _mv_268.value;
                        __auto_type _mv_269 = (*binding);
                        switch (_mv_269.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_269.data.sym;
                                return (slop_option_string){.has_value = 1, .value = sym.name};
                            }
                            default: {
                                return (slop_option_string){.has_value = false};
                            }
                        }
                    } else if (!_mv_268.has_value) {
                        return (slop_option_string){.has_value = false};
                    }
                }
            }
        }
        default: {
            return (slop_option_string){.has_value = false};
        }
    }
}

slop_string expr_get_match_branch_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr branch_items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((branch_items).len));
        if ((len < 2)) {
            return SLOP_STR("0");
        } else {
            __auto_type _mv_270 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)(len - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_270.has_value) {
                __auto_type body_expr = _mv_270.value;
                return expr_transpile_expr(ctx, body_expr);
            } else if (!_mv_270.has_value) {
                return SLOP_STR("0");
            }
        }
    }
}

slop_string expr_transpile_branch_body_with_binding(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_list_types_SExpr_ptr branch_items, slop_string binding_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((scrutinee != NULL)), "(!= scrutinee nil)");
    context_ctx_push_scope(ctx);
    if (!(string_eq(binding_name, SLOP_STR("")))) {
        {
            __auto_type arena = (*ctx).arena;
            __auto_type c_name = ctype_to_c_name(arena, binding_name);
            __auto_type inner_slop_type = expr_infer_option_inner_slop_type(ctx, scrutinee);
            context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_name, SLOP_STR("auto"), inner_slop_type, 0, 0});
        }
    }
    {
        __auto_type result = expr_get_match_branch_body(ctx, branch_items);
        context_ctx_pop_scope(ctx);
        return result;
    }
}

slop_string expr_build_option_match_expr(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_string scrutinee_c, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((scrutinee != NULL)), "(!= scrutinee nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type some_body = SLOP_STR("0");
        __auto_type none_body = SLOP_STR("0");
        __auto_type some_binding = SLOP_STR("");
        __auto_type i = 2;
        while ((i < len)) {
            __auto_type _mv_271 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_271.has_value) {
                __auto_type branch = _mv_271.value;
                __auto_type _mv_272 = (*branch);
                switch (_mv_272.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_272.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if ((((int64_t)((branch_items).len)) >= 2)) {
                                __auto_type _mv_273 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_273.has_value) {
                                    __auto_type pattern = _mv_273.value;
                                    {
                                        __auto_type tag = expr_get_expr_pattern_tag(pattern);
                                        if (string_eq(tag, SLOP_STR("some"))) {
                                            __auto_type _mv_274 = expr_get_expr_binding_name(pattern);
                                            if (_mv_274.has_value) {
                                                __auto_type name = _mv_274.value;
                                                some_binding = name;
                                                some_body = expr_transpile_branch_body_with_binding(ctx, scrutinee, branch_items, name);
                                            } else if (!_mv_274.has_value) {
                                                some_body = expr_get_match_branch_body(ctx, branch_items);
                                            }
                                        } else if (string_eq(tag, SLOP_STR("none"))) {
                                            none_body = expr_get_match_branch_body(ctx, branch_items);
                                        } else {
                                        }
                                    }
                                } else if (!_mv_273.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_271.has_value) {
            }
            i = (i + 1);
        }
        {
            __auto_type result_type = expr_infer_match_result_c_type(ctx, items);
            if (string_eq(some_binding, SLOP_STR(""))) {
                return expr_build_option_match_no_binding(ctx, scrutinee_c, some_body, none_body, result_type);
            } else {
                return expr_build_option_match_with_binding(ctx, arena, scrutinee_c, some_binding, some_body, none_body, result_type);
            }
        }
    }
}

slop_string expr_build_option_match_no_binding(context_TranspileContext* ctx, slop_string scrutinee_c, slop_string some_body, slop_string none_body, slop_string result_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (string_eq(result_type, SLOP_STR("void"))) {
        {
            __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrutinee_c);
            __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("; if (_mv.has_value) { "));
            __auto_type s3 = context_ctx_str(ctx, s2, some_body);
            __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR("; } else { "));
            __auto_type s5 = context_ctx_str(ctx, s4, none_body);
            __auto_type s6 = context_ctx_str(ctx, s5, SLOP_STR("; } (void)0; })"));
            return s6;
        }
    } else {
        {
            __auto_type typed_none_body = expr_typed_none(ctx, result_type, none_body);
            __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrutinee_c);
            __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("; _mv.has_value ? ("));
            __auto_type s3 = context_ctx_str(ctx, s2, some_body);
            __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR(") : ("));
            __auto_type s5 = context_ctx_str(ctx, s4, typed_none_body);
            __auto_type s6 = context_ctx_str(ctx, s5, SLOP_STR("); })"));
            return s6;
        }
    }
}

slop_string expr_build_option_match_with_binding(context_TranspileContext* ctx, slop_arena* arena, slop_string scrutinee_c, slop_string binding, slop_string some_body, slop_string none_body, slop_string result_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type var_c = ctype_to_c_name(arena, binding);
        if (string_eq(result_type, SLOP_STR("void"))) {
            {
                __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrutinee_c);
                __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("; if (_mv.has_value) { __auto_type "));
                __auto_type s3 = context_ctx_str(ctx, s2, var_c);
                __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR(" = _mv.value; "));
                __auto_type s5 = context_ctx_str(ctx, s4, some_body);
                __auto_type s6 = context_ctx_str(ctx, s5, SLOP_STR("; } else { "));
                __auto_type s7 = context_ctx_str(ctx, s6, none_body);
                __auto_type s8 = context_ctx_str(ctx, s7, SLOP_STR("; } (void)0; })"));
                return s8;
            }
        } else {
            {
                __auto_type typed_none_body = expr_typed_none(ctx, result_type, none_body);
                __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrutinee_c);
                __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("; _mv.has_value ? ({ __auto_type "));
                __auto_type s3 = context_ctx_str(ctx, s2, var_c);
                __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR(" = _mv.value; "));
                __auto_type s5 = context_ctx_str(ctx, s4, some_body);
                __auto_type s6 = context_ctx_str(ctx, s5, SLOP_STR("; }) : ("));
                __auto_type s7 = context_ctx_str(ctx, s6, typed_none_body);
                __auto_type s8 = context_ctx_str(ctx, s7, SLOP_STR("); })"));
                return s8;
            }
        }
    }
}

slop_string expr_infer_cond_result_c_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 2)) {
            return SLOP_STR("int64_t");
        } else {
            __auto_type _mv_275 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_275.has_value) {
                __auto_type first_clause = _mv_275.value;
                __auto_type _mv_276 = (*first_clause);
                switch (_mv_276.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type clause_lst = _mv_276.data.lst;
                        {
                            __auto_type clause_items = clause_lst.items;
                            __auto_type clause_len = ((int64_t)((clause_items).len));
                            if ((clause_len < 2)) {
                                return SLOP_STR("int64_t");
                            } else {
                                __auto_type _mv_277 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)(clause_len - 1); struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_277.has_value) {
                                    __auto_type body_expr = _mv_277.value;
                                    return expr_infer_expr_c_type(ctx, body_expr);
                                } else if (!_mv_277.has_value) {
                                    return SLOP_STR("int64_t");
                                }
                            }
                        }
                    }
                    default: {
                        return SLOP_STR("int64_t");
                    }
                }
            } else if (!_mv_275.has_value) {
                return SLOP_STR("int64_t");
            }
        }
    }
}

slop_string expr_infer_match_result_c_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 3)) {
            return SLOP_STR("int64_t");
        } else {
            __auto_type _mv_278 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_278.has_value) {
                __auto_type first_branch = _mv_278.value;
                __auto_type _mv_279 = (*first_branch);
                switch (_mv_279.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_279.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            __auto_type branch_len = ((int64_t)((branch_items).len));
                            if ((branch_len < 2)) {
                                return SLOP_STR("int64_t");
                            } else {
                                __auto_type _mv_280 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)(branch_len - 1); struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_280.has_value) {
                                    __auto_type body_expr = _mv_280.value;
                                    return expr_infer_expr_c_type(ctx, body_expr);
                                } else if (!_mv_280.has_value) {
                                    return SLOP_STR("int64_t");
                                }
                            }
                        }
                    }
                    default: {
                        return SLOP_STR("int64_t");
                    }
                }
            } else if (!_mv_278.has_value) {
                return SLOP_STR("int64_t");
            }
        }
    }
}

slop_string expr_slop_type_to_c_type(context_TranspileContext* ctx, slop_string slop_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_281 = context_ctx_lookup_type(ctx, slop_type);
        if (_mv_281.has_value) {
            __auto_type entry = _mv_281.value;
            return entry.c_name;
        } else if (!_mv_281.has_value) {
            if (string_eq(slop_type, SLOP_STR("String"))) {
                return SLOP_STR("slop_string");
            } else if (string_eq(slop_type, SLOP_STR("Int"))) {
                return SLOP_STR("int64_t");
            } else if (string_eq(slop_type, SLOP_STR("Bool"))) {
                return SLOP_STR("uint8_t");
            } else if (string_eq(slop_type, SLOP_STR("Unit"))) {
                return SLOP_STR("void");
            } else if (string_eq(slop_type, SLOP_STR("Arena"))) {
                return SLOP_STR("slop_arena*");
            } else if (strlib_starts_with(slop_type, SLOP_STR("(Ptr "))) {
                {
                    __auto_type inner = strlib_substring(arena, slop_type, 5, ((0) > ((((int64_t)(string_len(slop_type))) - 1)) ? (0) : ((((int64_t)(string_len(slop_type))) - 1))));
                    return context_ctx_str(ctx, expr_slop_type_to_c_type(ctx, inner), SLOP_STR("*"));
                }
            } else if ((strlib_starts_with(slop_type, SLOP_STR("(Map ")) || strlib_starts_with(slop_type, SLOP_STR("(Set ")))) {
                return SLOP_STR("slop_map*");
            } else if (strlib_starts_with(slop_type, SLOP_STR("(List "))) {
                {
                    __auto_type inner = strlib_substring(arena, slop_type, 6, ((0) > ((((int64_t)(string_len(slop_type))) - 1)) ? (0) : ((((int64_t)(string_len(slop_type))) - 1))));
                    return context_ctx_str(ctx, SLOP_STR("slop_list_"), expr_slop_type_to_c_type(ctx, inner));
                }
            } else if (strlib_starts_with(slop_type, SLOP_STR("(Option "))) {
                {
                    __auto_type inner = strlib_substring(arena, slop_type, 8, ((0) > ((((int64_t)(string_len(slop_type))) - 1)) ? (0) : ((((int64_t)(string_len(slop_type))) - 1))));
                    return context_ctx_str(ctx, SLOP_STR("slop_option_"), expr_slop_type_to_c_type(ctx, inner));
                }
            } else {
                return slop_type;
            }
        }
    }
}

slop_string expr_infer_expr_c_type(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_282 = (*expr);
    switch (_mv_282.tag) {
        case types_SExpr_str:
        {
            __auto_type _ = _mv_282.data.str;
            return SLOP_STR("slop_string");
        }
        case types_SExpr_num:
        {
            __auto_type num = _mv_282.data.num;
            if (num.is_float) {
                return SLOP_STR("double");
            } else {
                return SLOP_STR("int64_t");
            }
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_282.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_283 = context_ctx_lookup_var(ctx, name);
                if (_mv_283.has_value) {
                    __auto_type entry = _mv_283.value;
                    {
                        __auto_type c_type = entry.c_type;
                        __auto_type slop_type = entry.slop_type;
                        if ((string_eq(c_type, SLOP_STR("auto")) || (string_len(c_type) == 0))) {
                            if ((string_len(slop_type) > 0)) {
                                return expr_slop_type_to_c_type(ctx, slop_type);
                            } else {
                                return SLOP_STR("int64_t");
                            }
                        } else {
                            return c_type;
                        }
                    }
                } else if (!_mv_283.has_value) {
                    return SLOP_STR("int64_t");
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_282.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return SLOP_STR("int64_t");
                } else {
                    __auto_type _mv_284 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_284.has_value) {
                        __auto_type head = _mv_284.value;
                        __auto_type _mv_285 = (*head);
                        switch (_mv_285.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_285.data.sym;
                                {
                                    __auto_type op = sym.name;
                                    if (({ __auto_type _mv = context_ctx_lookup_func(ctx, op); _mv.has_value ? ({ __auto_type func_entry = _mv.value; func_entry.returns_string; }) : (0); })) {
                                        return SLOP_STR("slop_string");
                                    } else if ((string_eq(op, SLOP_STR("ctx-str")) || (string_eq(op, SLOP_STR("ctx-str3")) || (string_eq(op, SLOP_STR("ctx-str4")) || (string_eq(op, SLOP_STR("ctx-str5")) || (string_eq(op, SLOP_STR("string-concat")) || (string_eq(op, SLOP_STR("substring")) || (string_eq(op, SLOP_STR("to-c-name")) || (string_eq(op, SLOP_STR("to-c-type")) || (string_eq(op, SLOP_STR("to-c-type-prefixed")) || (string_eq(op, SLOP_STR("transpile-expr")) || (string_eq(op, SLOP_STR("transpile-literal")) || (string_eq(op, SLOP_STR("ctx-prefix-type")) || (string_eq(op, SLOP_STR("type-to-identifier")) || (string_eq(op, SLOP_STR("fix-ternary-none")) || (string_eq(op, SLOP_STR("transpile-enum-variant")) || string_eq(op, SLOP_STR("extract-module-name")))))))))))))))))) {
                                        return SLOP_STR("slop_string");
                                    } else if (string_eq(op, SLOP_STR("."))) {
                                        if ((((int64_t)((items).len)) < 3)) {
                                            return SLOP_STR("/* TRANSPILER ERROR: malformed field access */");
                                        } else {
                                            __auto_type _mv_286 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_286.has_value) {
                                                __auto_type obj_expr = _mv_286.value;
                                                __auto_type _mv_287 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_287.has_value) {
                                                    __auto_type field_expr = _mv_287.value;
                                                    __auto_type _mv_288 = (*field_expr);
                                                    switch (_mv_288.tag) {
                                                        case types_SExpr_sym:
                                                        {
                                                            __auto_type field_sym = _mv_288.data.sym;
                                                            {
                                                                __auto_type field_name = field_sym.name;
                                                                __auto_type obj_c_type = expr_infer_expr_c_type(ctx, obj_expr);
                                                                __auto_type _mv_289 = context_ctx_lookup_field_type(ctx, obj_c_type, field_name);
                                                                if (_mv_289.has_value) {
                                                                    __auto_type c_type = _mv_289.value;
                                                                    return c_type;
                                                                } else if (!_mv_289.has_value) {
                                                                    __auto_type _mv_290 = context_ctx_lookup_var(ctx, expr_get_var_name_from_expr(obj_expr));
                                                                    if (_mv_290.has_value) {
                                                                        __auto_type var_entry = _mv_290.value;
                                                                        {
                                                                            __auto_type obj_slop_type = var_entry.slop_type;
                                                                            __auto_type _mv_291 = context_ctx_lookup_field_type(ctx, obj_slop_type, field_name);
                                                                            if (_mv_291.has_value) {
                                                                                __auto_type c_type2 = _mv_291.value;
                                                                                return c_type2;
                                                                            } else if (!_mv_291.has_value) {
                                                                                return SLOP_STR("/* TRANSPILER ERROR: unknown field type */");
                                                                            }
                                                                        }
                                                                    } else if (!_mv_290.has_value) {
                                                                        return SLOP_STR("/* TRANSPILER ERROR: unknown object type */");
                                                                    }
                                                                }
                                                            }
                                                        }
                                                        default: {
                                                            return SLOP_STR("/* TRANSPILER ERROR: field name must be symbol */");
                                                        }
                                                    }
                                                } else if (!_mv_287.has_value) {
                                                    return SLOP_STR("/* TRANSPILER ERROR: missing field expression */");
                                                }
                                            } else if (!_mv_286.has_value) {
                                                return SLOP_STR("/* TRANSPILER ERROR: missing object expression */");
                                            }
                                        }
                                    } else if ((string_eq(op, SLOP_STR("let")) || string_eq(op, SLOP_STR("let*")))) {
                                        if ((((int64_t)((items).len)) < 3)) {
                                            return SLOP_STR("int64_t");
                                        } else {
                                            __auto_type _mv_292 = ({ __auto_type _lst = items; size_t _idx = (size_t)(((int64_t)((items).len)) - 1); struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_292.has_value) {
                                                __auto_type body = _mv_292.value;
                                                return expr_infer_expr_c_type(ctx, body);
                                            } else if (!_mv_292.has_value) {
                                                return SLOP_STR("int64_t");
                                            }
                                        }
                                    } else if (string_eq(op, SLOP_STR("do"))) {
                                        if ((((int64_t)((items).len)) < 2)) {
                                            return SLOP_STR("void");
                                        } else {
                                            __auto_type _mv_293 = ({ __auto_type _lst = items; size_t _idx = (size_t)(((int64_t)((items).len)) - 1); struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_293.has_value) {
                                                __auto_type last_expr = _mv_293.value;
                                                return expr_infer_expr_c_type(ctx, last_expr);
                                            } else if (!_mv_293.has_value) {
                                                return SLOP_STR("void");
                                            }
                                        }
                                    } else if (string_eq(op, SLOP_STR("cond"))) {
                                        return expr_infer_cond_result_c_type(ctx, items);
                                    } else if (string_eq(op, SLOP_STR("match"))) {
                                        return expr_infer_match_result_c_type(ctx, items);
                                    } else if (string_eq(op, SLOP_STR("if"))) {
                                        if ((((int64_t)((items).len)) < 3)) {
                                            return SLOP_STR("int64_t");
                                        } else {
                                            __auto_type _mv_294 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_294.has_value) {
                                                __auto_type then_expr = _mv_294.value;
                                                return expr_infer_expr_c_type(ctx, then_expr);
                                            } else if (!_mv_294.has_value) {
                                                return SLOP_STR("int64_t");
                                            }
                                        }
                                    } else if (string_eq(op, SLOP_STR("some"))) {
                                        if ((((int64_t)((items).len)) < 2)) {
                                            return SLOP_STR("/* TRANSPILER ERROR: some without value */");
                                        } else {
                                            __auto_type _mv_295 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_295.has_value) {
                                                __auto_type val_expr = _mv_295.value;
                                                {
                                                    __auto_type val_type = expr_infer_expr_c_type(ctx, val_expr);
                                                    if (string_eq(val_type, SLOP_STR("slop_string"))) {
                                                        return SLOP_STR("slop_option_string");
                                                    } else if (string_eq(val_type, SLOP_STR("int64_t"))) {
                                                        return SLOP_STR("slop_option_int");
                                                    } else if (string_eq(val_type, SLOP_STR("double"))) {
                                                        return SLOP_STR("slop_option_double");
                                                    } else if (strlib_ends_with(val_type, SLOP_STR("*"))) {
                                                        {
                                                            __auto_type ctx_arena = (*ctx).arena;
                                                            __auto_type base_type = expr_strip_pointer_suffix(ctx_arena, val_type);
                                                            return context_ctx_str3(ctx, SLOP_STR("slop_option_"), base_type, SLOP_STR("_ptr"));
                                                        }
                                                    } else {
                                                        return context_ctx_str3(ctx, SLOP_STR("slop_option_"), val_type, SLOP_STR(""));
                                                    }
                                                }
                                            } else if (!_mv_295.has_value) {
                                                return SLOP_STR("/* TRANSPILER ERROR: some with no value expression */");
                                            }
                                        }
                                    } else if (string_eq(op, SLOP_STR("none"))) {
                                        return SLOP_STR("slop_option_int");
                                    } else if (string_eq(op, SLOP_STR("list-push"))) {
                                        return SLOP_STR("void");
                                    } else if (string_eq(op, SLOP_STR("set!"))) {
                                        return SLOP_STR("void");
                                    } else if (string_eq(op, SLOP_STR("cast"))) {
                                        if ((((int64_t)((items).len)) < 2)) {
                                            return SLOP_STR("void*");
                                        } else {
                                            __auto_type _mv_296 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_296.has_value) {
                                                __auto_type type_expr = _mv_296.value;
                                                return context_to_c_type_prefixed(ctx, type_expr);
                                            } else if (!_mv_296.has_value) {
                                                return SLOP_STR("void*");
                                            }
                                        }
                                    } else if (string_eq(op, SLOP_STR("when"))) {
                                        return SLOP_STR("void");
                                    } else {
                                        __auto_type _mv_297 = context_ctx_lookup_type(ctx, op);
                                        if (_mv_297.has_value) {
                                            __auto_type type_entry = _mv_297.value;
                                            return type_entry.c_name;
                                        } else if (!_mv_297.has_value) {
                                            __auto_type _mv_298 = context_ctx_lookup_func(ctx, op);
                                            if (_mv_298.has_value) {
                                                __auto_type func_entry = _mv_298.value;
                                                {
                                                    __auto_type ret_type = func_entry.return_type;
                                                    if (func_entry.returns_string) {
                                                        return SLOP_STR("slop_string");
                                                    } else if (string_eq(ret_type, SLOP_STR("void"))) {
                                                        return SLOP_STR("void");
                                                    } else if ((string_len(ret_type) > 0)) {
                                                        return ret_type;
                                                    } else {
                                                        return SLOP_STR("int64_t");
                                                    }
                                                }
                                            } else if (!_mv_298.has_value) {
                                                return SLOP_STR("int64_t");
                                            }
                                        }
                                    }
                                }
                            }
                            default: {
                                return SLOP_STR("int64_t");
                            }
                        }
                    } else if (!_mv_284.has_value) {
                        return SLOP_STR("int64_t");
                    }
                }
            }
        }
        default: {
            return SLOP_STR("int64_t");
        }
    }
}

slop_string expr_build_result_match_expr(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_string scrutinee_c, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result_type = expr_infer_match_result_c_type(ctx, items);
        __auto_type ok_body = SLOP_STR("0");
        __auto_type err_body = SLOP_STR("0");
        __auto_type ok_binding = SLOP_STR("");
        __auto_type err_binding = SLOP_STR("");
        __auto_type i = 2;
        while ((i < len)) {
            __auto_type _mv_299 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_299.has_value) {
                __auto_type branch = _mv_299.value;
                __auto_type _mv_300 = (*branch);
                switch (_mv_300.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_300.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if ((((int64_t)((branch_items).len)) >= 2)) {
                                __auto_type _mv_301 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_301.has_value) {
                                    __auto_type pattern = _mv_301.value;
                                    {
                                        __auto_type tag = expr_get_expr_pattern_tag(pattern);
                                        if (string_eq(tag, SLOP_STR("ok"))) {
                                            __auto_type _mv_302 = expr_get_expr_binding_name(pattern);
                                            if (_mv_302.has_value) {
                                                __auto_type name = _mv_302.value;
                                                ok_binding = name;
                                                ok_body = expr_transpile_branch_body_with_binding(ctx, scrutinee, branch_items, name);
                                            } else if (!_mv_302.has_value) {
                                                ok_body = expr_get_match_branch_body(ctx, branch_items);
                                            }
                                        } else if (string_eq(tag, SLOP_STR("error"))) {
                                            __auto_type _mv_303 = expr_get_expr_binding_name(pattern);
                                            if (_mv_303.has_value) {
                                                __auto_type name = _mv_303.value;
                                                err_binding = name;
                                                err_body = expr_transpile_branch_body_with_binding(ctx, scrutinee, branch_items, name);
                                            } else if (!_mv_303.has_value) {
                                                err_body = expr_get_match_branch_body(ctx, branch_items);
                                            }
                                        } else {
                                        }
                                    }
                                } else if (!_mv_301.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_299.has_value) {
            }
            i = (i + 1);
        }
        {
            __auto_type ok_bind = ((string_eq(ok_binding, SLOP_STR(""))) ? SLOP_STR("") : context_ctx_str3(ctx, SLOP_STR("__auto_type "), ctype_to_c_name(arena, ok_binding), SLOP_STR(" = _mv.data.ok; ")));
            __auto_type err_bind = ((string_eq(err_binding, SLOP_STR(""))) ? SLOP_STR("") : context_ctx_str3(ctx, SLOP_STR("__auto_type "), ctype_to_c_name(arena, err_binding), SLOP_STR(" = _mv.data.err; ")));
            if (string_eq(result_type, SLOP_STR("void"))) {
                context_ctx_str(ctx, context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrutinee_c), context_ctx_str(ctx, SLOP_STR("; if (_mv.is_ok) { "), context_ctx_str(ctx, ok_bind, context_ctx_str(ctx, ok_body, context_ctx_str(ctx, SLOP_STR("; } else { "), context_ctx_str(ctx, err_bind, context_ctx_str(ctx, err_body, SLOP_STR("; } (void)0; })"))))))));
            }
            return context_ctx_str(ctx, context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrutinee_c), context_ctx_str(ctx, context_ctx_str3(ctx, SLOP_STR("; "), result_type, SLOP_STR(" _mr; if (_mv.is_ok) { ")), context_ctx_str(ctx, ok_bind, context_ctx_str(ctx, SLOP_STR("_mr = "), context_ctx_str(ctx, ok_body, context_ctx_str(ctx, SLOP_STR("; } else { "), context_ctx_str(ctx, err_bind, context_ctx_str(ctx, SLOP_STR("_mr = "), context_ctx_str(ctx, err_body, SLOP_STR("; } _mr; })"))))))))));
        }
    }
}

slop_string expr_build_union_match_expr(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_string scrutinee_c, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result_type = expr_infer_match_result_c_type(ctx, items);
        __auto_type cases = SLOP_STR("");
        __auto_type i = 2;
        while ((i < len)) {
            __auto_type _mv_304 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_304.has_value) {
                __auto_type branch = _mv_304.value;
                __auto_type _mv_305 = (*branch);
                switch (_mv_305.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_305.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if ((((int64_t)((branch_items).len)) >= 2)) {
                                __auto_type _mv_306 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_306.has_value) {
                                    __auto_type pattern = _mv_306.value;
                                    cases = expr_build_union_case_expr(ctx, arena, cases, scrutinee, pattern, branch_items, result_type);
                                } else if (!_mv_306.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_304.has_value) {
            }
            i = (i + 1);
        }
        if (string_eq(result_type, SLOP_STR("void"))) {
            {
                __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrutinee_c);
                __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("; switch (_mv.tag) { "));
                __auto_type s3 = context_ctx_str(ctx, s2, cases);
                __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR(" } (void)0; })"));
                return s4;
            }
        } else {
            {
                __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrutinee_c);
                __auto_type s2 = context_ctx_str(ctx, s1, context_ctx_str(ctx, SLOP_STR("; "), context_ctx_str(ctx, result_type, SLOP_STR(" _mr = {0}; switch (_mv.tag) { "))));
                __auto_type s3 = context_ctx_str(ctx, s2, cases);
                __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR(" } _mr; })"));
                return s4;
            }
        }
    }
}

slop_string expr_typed_none(context_TranspileContext* ctx, slop_string result_type, slop_string body) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if ((string_eq(body, SLOP_STR("none")) && strlib_starts_with(result_type, SLOP_STR("slop_option_")))) {
        return context_ctx_str3(ctx, SLOP_STR("("), result_type, SLOP_STR("){.has_value = false}"));
    } else {
        return body;
    }
}

slop_string expr_typed_none_arg(context_TranspileContext* ctx, slop_string expected_type, slop_string arg_c) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if ((string_eq(arg_c, SLOP_STR("none")) && strlib_starts_with(expected_type, SLOP_STR("slop_option_")))) {
        return context_ctx_str3(ctx, SLOP_STR("(("), expected_type, SLOP_STR("){.has_value = false})"));
    } else {
        return arg_c;
    }
}

slop_string expr_build_union_case_expr(context_TranspileContext* ctx, slop_arena* arena, slop_string cases, types_SExpr* scrutinee, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, slop_string result_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type tag = expr_get_expr_pattern_tag(pattern);
        __auto_type is_void = string_eq(result_type, SLOP_STR("void"));
        if ((string_eq(tag, SLOP_STR("else")) || string_eq(tag, SLOP_STR("_")))) {
            {
                __auto_type body = expr_typed_none(ctx, result_type, expr_get_match_branch_body(ctx, branch_items));
                if (is_void) {
                    return context_ctx_str(ctx, cases, context_ctx_str3(ctx, SLOP_STR("default: { "), body, SLOP_STR("; break; } ")));
                } else {
                    return context_ctx_str(ctx, cases, context_ctx_str3(ctx, SLOP_STR("default: { _mr = "), body, SLOP_STR("; break; } ")));
                }
            }
        } else {
            __auto_type _mv_307 = context_ctx_lookup_enum_variant(ctx, tag);
            if (_mv_307.has_value) {
                __auto_type type_name = _mv_307.value;
                {
                    __auto_type case_label = context_ctx_str4(ctx, type_name, SLOP_STR("_"), tag, SLOP_STR(""));
                    __auto_type binding_opt = expr_get_expr_binding_name(pattern);
                    __auto_type _mv_308 = binding_opt;
                    if (_mv_308.has_value) {
                        __auto_type binding_name = _mv_308.value;
                        {
                            __auto_type c_binding = ctype_to_c_name(arena, binding_name);
                            __auto_type body = expr_typed_none(ctx, result_type, expr_transpile_branch_body_with_binding(ctx, scrutinee, branch_items, binding_name));
                            __auto_type s1 = context_ctx_str(ctx, cases, SLOP_STR("case "));
                            __auto_type s2 = context_ctx_str(ctx, s1, case_label);
                            __auto_type s3 = context_ctx_str(ctx, s2, SLOP_STR(": { __auto_type "));
                            __auto_type s4 = context_ctx_str(ctx, s3, c_binding);
                            __auto_type s5 = context_ctx_str(ctx, s4, SLOP_STR(" = _mv.data."));
                            __auto_type s6 = context_ctx_str(ctx, s5, tag);
                            __auto_type s7 = ((is_void) ? context_ctx_str(ctx, s6, SLOP_STR("; ")) : context_ctx_str(ctx, s6, SLOP_STR("; _mr = ")));
                            __auto_type s8 = context_ctx_str(ctx, s7, body);
                            __auto_type s9 = context_ctx_str(ctx, s8, SLOP_STR("; break; } "));
                            return s9;
                        }
                    } else if (!_mv_308.has_value) {
                        {
                            __auto_type body = expr_typed_none(ctx, result_type, expr_get_match_branch_body(ctx, branch_items));
                            __auto_type s1 = context_ctx_str(ctx, cases, SLOP_STR("case "));
                            __auto_type s2 = context_ctx_str(ctx, s1, case_label);
                            __auto_type s3 = ((is_void) ? context_ctx_str(ctx, s2, SLOP_STR(": { ")) : context_ctx_str(ctx, s2, SLOP_STR(": { _mr = ")));
                            __auto_type s4 = context_ctx_str(ctx, s3, body);
                            __auto_type s5 = context_ctx_str(ctx, s4, SLOP_STR("; break; } "));
                            return s5;
                        }
                    }
                }
            } else if (!_mv_307.has_value) {
                return cases;
            }
        }
    }
}

slop_string expr_build_ternary_match_expr(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result = SLOP_STR("");
        __auto_type has_else = 0;
        __auto_type first_branch = 1;
        __auto_type i = (len - 1);
        while ((i >= 2)) {
            __auto_type _mv_309 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_309.has_value) {
                __auto_type branch = _mv_309.value;
                __auto_type _mv_310 = (*branch);
                switch (_mv_310.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_310.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if ((((int64_t)((branch_items).len)) >= 2)) {
                                __auto_type _mv_311 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_311.has_value) {
                                    __auto_type pattern = _mv_311.value;
                                    {
                                        __auto_type tag = expr_get_expr_pattern_tag(pattern);
                                        __auto_type body = expr_get_match_branch_body(ctx, branch_items);
                                        if ((string_eq(tag, SLOP_STR("else")) || string_eq(tag, SLOP_STR("_")))) {
                                            result = body;
                                            has_else = 1;
                                            first_branch = 0;
                                        } else if (first_branch) {
                                            result = body;
                                            first_branch = 0;
                                        } else {
                                            {
                                                __auto_type pattern_c = expr_transpile_expr(ctx, pattern);
                                                result = context_ctx_str(ctx, context_ctx_str(ctx, SLOP_STR("(("), scrutinee_c), context_ctx_str(ctx, SLOP_STR(" == "), context_ctx_str(ctx, pattern_c, context_ctx_str(ctx, SLOP_STR(") ? "), context_ctx_str(ctx, body, context_ctx_str(ctx, SLOP_STR(" : "), context_ctx_str(ctx, result, SLOP_STR(")"))))))));
                                            }
                                        }
                                    }
                                } else if (!_mv_311.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_309.has_value) {
            }
            i = (i - 1);
        }
        if (string_eq(result, SLOP_STR(""))) {
            return SLOP_STR("0");
        } else {
            return result;
        }
    }
}

slop_string expr_transpile_let_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if ((len < 3)) {
            return SLOP_STR("({ (void)0; })");
        } else {
            __auto_type _mv_312 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_312.has_value) {
                __auto_type bindings_expr = _mv_312.value;
                __auto_type _mv_313 = (*bindings_expr);
                switch (_mv_313.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type bindings_lst = _mv_313.data.lst;
                        {
                            __auto_type result = SLOP_STR("({ ");
                            __auto_type bindings_items = bindings_lst.items;
                            __auto_type bindings_len = ((int64_t)((bindings_items).len));
                            __auto_type bi = 0;
                            while ((bi < bindings_len)) {
                                __auto_type _mv_314 = ({ __auto_type _lst = bindings_items; size_t _idx = (size_t)bi; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_314.has_value) {
                                    __auto_type binding = _mv_314.value;
                                    {
                                        __auto_type binding_c = expr_transpile_binding_expr(ctx, binding);
                                        result = context_ctx_str3(ctx, result, binding_c, SLOP_STR(" "));
                                    }
                                } else if (!_mv_314.has_value) {
                                }
                                bi = (bi + 1);
                            }
                            {
                                __auto_type i = 2;
                                while ((i < (len - 1))) {
                                    __auto_type _mv_315 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_315.has_value) {
                                        __auto_type body_expr = _mv_315.value;
                                        {
                                            __auto_type body_c = expr_transpile_expr(ctx, body_expr);
                                            result = context_ctx_str3(ctx, result, body_c, SLOP_STR("; "));
                                        }
                                    } else if (!_mv_315.has_value) {
                                    }
                                    i = (i + 1);
                                }
                                __auto_type _mv_316 = ({ __auto_type _lst = items; size_t _idx = (size_t)(len - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_316.has_value) {
                                    __auto_type last_expr = _mv_316.value;
                                    {
                                        __auto_type last_c = expr_transpile_expr(ctx, last_expr);
                                        return context_ctx_str3(ctx, result, last_c, SLOP_STR("; })"));
                                    }
                                } else if (!_mv_316.has_value) {
                                    return context_ctx_str(ctx, result, SLOP_STR("0; })"));
                                }
                            }
                        }
                    }
                    default: {
                        return SLOP_STR("({ (void)0; })");
                    }
                }
            } else if (!_mv_312.has_value) {
                return SLOP_STR("({ (void)0; })");
            }
        }
    }
}

slop_string expr_transpile_binding_expr(context_TranspileContext* ctx, types_SExpr* binding) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((binding != NULL)), "(!= binding nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_317 = (*binding);
        switch (_mv_317.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_317.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 2)) {
                        return SLOP_STR("");
                    } else {
                        {
                            __auto_type has_mut = expr_binding_has_mut(items);
                            __auto_type name_idx = ((has_mut) ? 1 : 0);
                            __auto_type _mv_318 = ({ __auto_type _lst = items; size_t _idx = (size_t)name_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_318.has_value) {
                                __auto_type name_expr = _mv_318.value;
                                __auto_type _mv_319 = (*name_expr);
                                switch (_mv_319.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type name_sym = _mv_319.data.sym;
                                        {
                                            __auto_type var_name = ctype_to_c_name(arena, name_sym.name);
                                            __auto_type has_type = ((has_mut) ? (len >= 4) : (len >= 3));
                                            __auto_type type_idx = (name_idx + 1);
                                            __auto_type init_idx = ((has_mut) ? ((has_type) ? 3 : 2) : ((has_type) ? 2 : 1));
                                            if (has_type) {
                                                __auto_type _mv_320 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_320.has_value) {
                                                    __auto_type type_expr = _mv_320.value;
                                                    {
                                                        __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                        __auto_type _mv_321 = ({ __auto_type _lst = items; size_t _idx = (size_t)init_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                        if (_mv_321.has_value) {
                                                            __auto_type init_expr = _mv_321.value;
                                                            {
                                                                __auto_type init_c = expr_transpile_typed_init(ctx, init_expr, c_type);
                                                                return context_ctx_str5(ctx, c_type, SLOP_STR(" "), context_ctx_str3(ctx, var_name, SLOP_STR(" = "), init_c), SLOP_STR(";"), SLOP_STR(""));
                                                            }
                                                        } else if (!_mv_321.has_value) {
                                                            return context_ctx_str5(ctx, c_type, SLOP_STR(" "), var_name, SLOP_STR(" = {0};"), SLOP_STR(""));
                                                        }
                                                    }
                                                } else if (!_mv_320.has_value) {
                                                    __auto_type _mv_322 = ({ __auto_type _lst = items; size_t _idx = (size_t)init_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_322.has_value) {
                                                        __auto_type init_expr = _mv_322.value;
                                                        {
                                                            __auto_type init_c = expr_transpile_expr(ctx, init_expr);
                                                            return context_ctx_str5(ctx, SLOP_STR("__auto_type "), var_name, SLOP_STR(" = "), init_c, SLOP_STR(";"));
                                                        }
                                                    } else if (!_mv_322.has_value) {
                                                        return context_ctx_str3(ctx, SLOP_STR("__auto_type "), var_name, SLOP_STR(" = 0;"));
                                                    }
                                                }
                                            } else {
                                                __auto_type _mv_323 = ({ __auto_type _lst = items; size_t _idx = (size_t)init_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_323.has_value) {
                                                    __auto_type init_expr = _mv_323.value;
                                                    {
                                                        __auto_type init_c = expr_transpile_expr(ctx, init_expr);
                                                        return context_ctx_str5(ctx, SLOP_STR("__auto_type "), var_name, SLOP_STR(" = "), init_c, SLOP_STR(";"));
                                                    }
                                                } else if (!_mv_323.has_value) {
                                                    return context_ctx_str3(ctx, SLOP_STR("__auto_type "), var_name, SLOP_STR(" = 0;"));
                                                }
                                            }
                                        }
                                    }
                                    default: {
                                        return SLOP_STR("");
                                    }
                                }
                            } else if (!_mv_318.has_value) {
                                return SLOP_STR("");
                            }
                        }
                    }
                }
            }
            default: {
                return SLOP_STR("");
            }
        }
    }
}

uint8_t expr_binding_has_mut(slop_list_types_SExpr_ptr items) {
    if ((((int64_t)((items).len)) < 1)) {
        return 0;
    } else {
        __auto_type _mv_324 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_324.has_value) {
            __auto_type first = _mv_324.value;
            __auto_type _mv_325 = (*first);
            switch (_mv_325.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_325.data.sym;
                    return string_eq(sym.name, SLOP_STR("mut"));
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_324.has_value) {
            return 0;
        }
    }
}

slop_string expr_transpile_typed_init(context_TranspileContext* ctx, types_SExpr* init_expr, slop_string target_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((init_expr != NULL)), "(!= init-expr nil)");
    __auto_type _mv_326 = (*init_expr);
    switch (_mv_326.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_326.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return expr_transpile_expr(ctx, init_expr);
                } else {
                    __auto_type _mv_327 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_327.has_value) {
                        __auto_type head = _mv_327.value;
                        __auto_type _mv_328 = (*head);
                        switch (_mv_328.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_328.data.sym;
                                {
                                    __auto_type op = sym.name;
                                    if (string_eq(op, SLOP_STR("some"))) {
                                        if ((((int64_t)((items).len)) < 2)) {
                                            return expr_transpile_expr(ctx, init_expr);
                                        } else {
                                            __auto_type _mv_329 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_329.has_value) {
                                                __auto_type val_expr = _mv_329.value;
                                                {
                                                    __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                    return context_ctx_str5(ctx, SLOP_STR("("), target_type, SLOP_STR("){.has_value = 1, .value = "), val_c, SLOP_STR("}"));
                                                }
                                            } else if (!_mv_329.has_value) {
                                                return expr_transpile_expr(ctx, init_expr);
                                            }
                                        }
                                    } else if (string_eq(op, SLOP_STR("none"))) {
                                        return context_ctx_str3(ctx, SLOP_STR("("), target_type, SLOP_STR("){.has_value = false}"));
                                    } else {
                                        return expr_transpile_expr(ctx, init_expr);
                                    }
                                }
                            }
                            default: {
                                return expr_transpile_expr(ctx, init_expr);
                            }
                        }
                    } else if (!_mv_327.has_value) {
                        return expr_transpile_expr(ctx, init_expr);
                    }
                }
            }
        }
        default: {
            return expr_transpile_expr(ctx, init_expr);
        }
    }
}

slop_string expr_transpile_while_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 3)) {
            return SLOP_STR("({ (void)0; })");
        } else {
            __auto_type _mv_330 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_330.has_value) {
                __auto_type cond_expr = _mv_330.value;
                {
                    __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                    __auto_type body_str = SLOP_STR("");
                    {
                        __auto_type i = 2;
                        while ((i < len)) {
                            __auto_type _mv_331 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_331.has_value) {
                                __auto_type body_expr = _mv_331.value;
                                {
                                    __auto_type body_c = expr_transpile_expr(ctx, body_expr);
                                    body_str = context_ctx_str3(ctx, body_str, body_c, SLOP_STR("; "));
                                }
                            } else if (!_mv_331.has_value) {
                            }
                            i = (i + 1);
                        }
                    }
                    {
                        __auto_type part1 = context_ctx_str3(ctx, SLOP_STR("({ while ("), cond_c, SLOP_STR(") { "));
                        __auto_type part2 = context_ctx_str(ctx, body_str, SLOP_STR("} 0; })"));
                        return context_ctx_str(ctx, part1, part2);
                    }
                }
            } else if (!_mv_330.has_value) {
                return SLOP_STR("({ (void)0; })");
            }
        }
    }
}

slop_string expr_transpile_do_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len <= 1)) {
            return SLOP_STR("({ (void)0; })");
        } else {
            {
                __auto_type result = SLOP_STR("({ ");
                __auto_type i = 1;
                while ((i < len)) {
                    __auto_type _mv_332 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_332.has_value) {
                        __auto_type expr = _mv_332.value;
                        {
                            __auto_type expr_c = expr_transpile_expr(ctx, expr);
                            __auto_type is_last = (i == (len - 1));
                            result = context_ctx_str3(ctx, result, expr_c, SLOP_STR("; "));
                        }
                    } else if (!_mv_332.has_value) {
                    }
                    i = (i + 1);
                }
                return context_ctx_str(ctx, result, SLOP_STR("})"));
            }
        }
    }
}

slop_string expr_transpile_when_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 2)) {
            return SLOP_STR("({ (void)0; })");
        } else {
            __auto_type _mv_333 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_333.has_value) {
                __auto_type cond_expr = _mv_333.value;
                {
                    __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                    __auto_type body_c = SLOP_STR("({ ");
                    {
                        __auto_type i = 2;
                        while ((i < len)) {
                            __auto_type _mv_334 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_334.has_value) {
                                __auto_type body_expr = _mv_334.value;
                                body_c = context_ctx_str3(ctx, body_c, expr_transpile_expr(ctx, body_expr), SLOP_STR("; "));
                            } else if (!_mv_334.has_value) {
                            }
                            i = (i + 1);
                        }
                    }
                    body_c = context_ctx_str(ctx, body_c, SLOP_STR("0; })"));
                    return context_ctx_str5(ctx, SLOP_STR("(("), cond_c, SLOP_STR(") ? "), body_c, SLOP_STR(" : ({ (void)0; }))"));
                }
            } else if (!_mv_333.has_value) {
                return SLOP_STR("({ (void)0; })");
            }
        }
    }
}

slop_string expr_transpile_set_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if ((len < 3)) {
            return SLOP_STR("({ (void)0; })");
        } else {
            __auto_type _mv_335 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_335.has_value) {
                __auto_type target_expr = _mv_335.value;
                __auto_type _mv_336 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_336.has_value) {
                    __auto_type val_expr = _mv_336.value;
                    {
                        __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                        __auto_type _mv_337 = (*target_expr);
                        switch (_mv_337.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type target_lst = _mv_337.data.lst;
                                {
                                    __auto_type target_items = target_lst.items;
                                    if ((((int64_t)((target_items).len)) < 1)) {
                                        return context_ctx_str5(ctx, SLOP_STR("({ "), expr_transpile_expr(ctx, target_expr), SLOP_STR(" = "), val_c, SLOP_STR("; (void)0; })"));
                                    } else {
                                        __auto_type _mv_338 = ({ __auto_type _lst = target_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_338.has_value) {
                                            __auto_type head = _mv_338.value;
                                            __auto_type _mv_339 = (*head);
                                            switch (_mv_339.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type sym = _mv_339.data.sym;
                                                    {
                                                        __auto_type op = sym.name;
                                                        if (string_eq(op, SLOP_STR("@"))) {
                                                            if ((((int64_t)((target_items).len)) < 3)) {
                                                                return SLOP_STR("({ (void)0; })");
                                                            } else {
                                                                __auto_type _mv_340 = ({ __auto_type _lst = target_items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                if (_mv_340.has_value) {
                                                                    __auto_type arr_expr = _mv_340.value;
                                                                    __auto_type _mv_341 = ({ __auto_type _lst = target_items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                    if (_mv_341.has_value) {
                                                                        __auto_type idx_expr = _mv_341.value;
                                                                        {
                                                                            __auto_type arr_c = expr_transpile_expr(ctx, arr_expr);
                                                                            __auto_type idx_c = expr_transpile_expr(ctx, idx_expr);
                                                                            return context_ctx_str(ctx, SLOP_STR("({ "), context_ctx_str(ctx, arr_c, context_ctx_str(ctx, SLOP_STR("["), context_ctx_str(ctx, idx_c, context_ctx_str(ctx, SLOP_STR("] = "), context_ctx_str(ctx, val_c, SLOP_STR("; (void)0; })")))))));
                                                                        }
                                                                    } else if (!_mv_341.has_value) {
                                                                        return SLOP_STR("({ (void)0; })");
                                                                    }
                                                                } else if (!_mv_340.has_value) {
                                                                    return SLOP_STR("({ (void)0; })");
                                                                }
                                                            }
                                                        } else if (string_eq(op, SLOP_STR("."))) {
                                                            {
                                                                __auto_type target_c = expr_transpile_expr(ctx, target_expr);
                                                                return context_ctx_str5(ctx, SLOP_STR("({ "), target_c, SLOP_STR(" = "), val_c, SLOP_STR("; (void)0; })"));
                                                            }
                                                        } else {
                                                            {
                                                                __auto_type target_c = expr_transpile_expr(ctx, target_expr);
                                                                return context_ctx_str5(ctx, SLOP_STR("({ "), target_c, SLOP_STR(" = "), val_c, SLOP_STR("; (void)0; })"));
                                                            }
                                                        }
                                                    }
                                                }
                                                default: {
                                                    {
                                                        __auto_type target_c = expr_transpile_expr(ctx, target_expr);
                                                        return context_ctx_str5(ctx, SLOP_STR("({ "), target_c, SLOP_STR(" = "), val_c, SLOP_STR("; (void)0; })"));
                                                    }
                                                }
                                            }
                                        } else if (!_mv_338.has_value) {
                                            return SLOP_STR("({ (void)0; })");
                                        }
                                    }
                                }
                            }
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_337.data.sym;
                                {
                                    __auto_type target_c = ctype_to_c_name(arena, sym.name);
                                    return context_ctx_str5(ctx, SLOP_STR("({ "), target_c, SLOP_STR(" = "), val_c, SLOP_STR("; (void)0; })"));
                                }
                            }
                            default: {
                                {
                                    __auto_type target_c = expr_transpile_expr(ctx, target_expr);
                                    return context_ctx_str5(ctx, SLOP_STR("({ "), target_c, SLOP_STR(" = "), val_c, SLOP_STR("; (void)0; })"));
                                }
                            }
                        }
                    }
                } else if (!_mv_336.has_value) {
                    return SLOP_STR("({ (void)0; })");
                }
            } else if (!_mv_335.has_value) {
                return SLOP_STR("({ (void)0; })");
            }
        }
    }
}

slop_string expr_get_arena_for_list_push_expr(context_TranspileContext* ctx, types_SExpr* list_expr, slop_string list_c) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((list_expr != NULL)), "(!= list-expr nil)");
    __auto_type _mv_342 = context_ctx_lookup_var(ctx, SLOP_STR("arena"));
    if (_mv_342.has_value) {
        __auto_type arena_var = _mv_342.value;
        return arena_var.c_name;
    } else if (!_mv_342.has_value) {
        __auto_type _mv_343 = context_ctx_lookup_var(ctx, SLOP_STR("ctx"));
        if (_mv_343.has_value) {
            __auto_type ctx_var = _mv_343.value;
            return context_ctx_str(ctx, ctx_var.c_name, SLOP_STR("->arena"));
        } else if (!_mv_343.has_value) {
            {
                __auto_type arena_from_field = expr_get_arena_from_field_access(ctx, list_expr);
                if ((string_len(arena_from_field) > 0)) {
                    return arena_from_field;
                } else {
                    return SLOP_STR("arena");
                }
            }
        }
    }
}

slop_string expr_get_arena_from_field_access(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_344 = (*expr);
    switch (_mv_344.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_344.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len < 3)) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_345 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_345.has_value) {
                        __auto_type head_expr = _mv_345.value;
                        __auto_type _mv_346 = (*head_expr);
                        switch (_mv_346.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_346.data.sym;
                                if (string_eq(sym.name, SLOP_STR("."))) {
                                    __auto_type _mv_347 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_347.has_value) {
                                        __auto_type base_expr = _mv_347.value;
                                        return expr_get_arena_from_base(ctx, base_expr);
                                    } else if (!_mv_347.has_value) {
                                        return SLOP_STR("");
                                    }
                                } else {
                                    return SLOP_STR("");
                                }
                            }
                            default: {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_345.has_value) {
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

slop_string expr_get_arena_from_base(context_TranspileContext* ctx, types_SExpr* base_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((base_expr != NULL)), "(!= base-expr nil)");
    __auto_type _mv_348 = (*base_expr);
    switch (_mv_348.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_348.data.sym;
            {
                __auto_type var_name = sym.name;
                __auto_type _mv_349 = context_ctx_lookup_var(ctx, var_name);
                if (_mv_349.has_value) {
                    __auto_type entry = _mv_349.value;
                    if (entry.is_pointer) {
                        return context_ctx_str(ctx, entry.c_name, SLOP_STR("->arena"));
                    } else {
                        return context_ctx_str(ctx, entry.c_name, SLOP_STR(".arena"));
                    }
                } else if (!_mv_349.has_value) {
                    {
                        __auto_type arena = (*ctx).arena;
                        __auto_type c_name = ctype_to_c_name(arena, var_name);
                        return context_ctx_str(ctx, c_name, SLOP_STR("->arena"));
                    }
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_348.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 2)) {
                    return SLOP_STR("arena");
                } else {
                    __auto_type _mv_350 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_350.has_value) {
                        __auto_type head_expr = _mv_350.value;
                        __auto_type _mv_351 = (*head_expr);
                        switch (_mv_351.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_351.data.sym;
                                if (string_eq(sym.name, SLOP_STR("deref"))) {
                                    __auto_type _mv_352 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_352.has_value) {
                                        __auto_type ptr_expr = _mv_352.value;
                                        {
                                            __auto_type ptr_c = expr_transpile_expr(ctx, ptr_expr);
                                            return context_ctx_str(ctx, ptr_c, SLOP_STR("->arena"));
                                        }
                                    } else if (!_mv_352.has_value) {
                                        return SLOP_STR("arena");
                                    }
                                } else {
                                    return SLOP_STR("arena");
                                }
                            }
                            default: {
                                return SLOP_STR("arena");
                            }
                        }
                    } else if (!_mv_350.has_value) {
                        return SLOP_STR("arena");
                    }
                }
            }
        }
        default: {
            return SLOP_STR("arena");
        }
    }
}

slop_string expr_get_arena_for_list_push(context_TranspileContext* ctx, slop_string list_c) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return SLOP_STR("arena");
}

uint8_t expr_is_ptr_to_ptr_map(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_353 = (*expr);
    switch (_mv_353.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_353.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_354 = context_ctx_lookup_var(ctx, name);
                if (_mv_354.has_value) {
                    __auto_type entry = _mv_354.value;
                    {
                        __auto_type c_type = entry.c_type;
                        return strlib_ends_with(c_type, SLOP_STR("**"));
                    }
                } else if (!_mv_354.has_value) {
                    return 0;
                }
            }
        }
        default: {
            return 0;
        }
    }
}

slop_string expr_transpile_record_new(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if ((len < 2)) {
            context_ctx_add_error_at(ctx, SLOP_STR("record-new: missing type"), context_list_first_line(items), context_list_first_col(items));
            return SLOP_STR("0");
        } else {
            __auto_type _mv_355 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_355.has_value) {
                __auto_type type_expr = _mv_355.value;
                __auto_type _mv_356 = (*type_expr);
                switch (_mv_356.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type type_sym = _mv_356.data.sym;
                        {
                            __auto_type raw_type_name = type_sym.name;
                            __auto_type type_name = ({ __auto_type _mv = context_ctx_lookup_type(ctx, raw_type_name); _mv.has_value ? ({ __auto_type entry = _mv.value; entry.c_name; }) : (context_ctx_prefix_type(ctx, ctype_to_c_name(arena, raw_type_name))); });
                            return expr_transpile_record_fields(ctx, type_name, items, 2);
                        }
                    }
                    case types_SExpr_lst:
                    {
                        __auto_type type_lst = _mv_356.data.lst;
                        {
                            __auto_type type_items = type_lst.items;
                            if ((((int64_t)((type_items).len)) < 1)) {
                                context_ctx_add_error_at(ctx, SLOP_STR("record-new: invalid inline type"), context_list_first_line(items), context_list_first_col(items));
                                return SLOP_STR("0");
                            } else {
                                __auto_type _mv_357 = ({ __auto_type _lst = type_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_357.has_value) {
                                    __auto_type head = _mv_357.value;
                                    __auto_type _mv_358 = (*head);
                                    switch (_mv_358.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type head_sym = _mv_358.data.sym;
                                            if (string_eq(head_sym.name, SLOP_STR("record"))) {
                                                {
                                                    __auto_type type_name = context_to_c_type_prefixed(ctx, type_expr);
                                                    return expr_transpile_record_fields(ctx, type_name, items, 2);
                                                }
                                            } else {
                                                context_ctx_add_error_at(ctx, SLOP_STR("record-new: expected record keyword"), context_list_first_line(items), context_list_first_col(items));
                                                return SLOP_STR("0");
                                            }
                                        }
                                        default: {
                                            context_ctx_add_error_at(ctx, SLOP_STR("record-new: invalid type head"), context_list_first_line(items), context_list_first_col(items));
                                            return SLOP_STR("0");
                                        }
                                    }
                                } else if (!_mv_357.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("record-new: empty type"), context_list_first_line(items), context_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                            }
                        }
                    }
                    default: {
                        context_ctx_add_error_at(ctx, SLOP_STR("record-new: invalid type"), context_list_first_line(items), context_list_first_col(items));
                        return SLOP_STR("0");
                    }
                }
            } else if (!_mv_355.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("record-new: missing type"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("0");
            }
        }
    }
}

slop_string expr_transpile_record_fields(context_TranspileContext* ctx, slop_string type_name, slop_list_types_SExpr_ptr items, int64_t start_idx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result = context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, type_name, SLOP_STR("){")));
        __auto_type i = start_idx;
        __auto_type first = 1;
        while ((i < len)) {
            __auto_type _mv_359 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_359.has_value) {
                __auto_type field_expr = _mv_359.value;
                __auto_type _mv_360 = (*field_expr);
                switch (_mv_360.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type field_lst = _mv_360.data.lst;
                        {
                            __auto_type field_items = field_lst.items;
                            if ((((int64_t)((field_items).len)) >= 2)) {
                                __auto_type _mv_361 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_361.has_value) {
                                    __auto_type name_expr = _mv_361.value;
                                    __auto_type _mv_362 = (*name_expr);
                                    switch (_mv_362.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type name_sym = _mv_362.data.sym;
                                            __auto_type _mv_363 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_363.has_value) {
                                                __auto_type val_expr = _mv_363.value;
                                                {
                                                    __auto_type field_name = ctype_to_c_name(arena, name_sym.name);
                                                    __auto_type field_val = expr_transpile_expr(ctx, val_expr);
                                                    if (first) {
                                                        result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR("."), context_ctx_str(ctx, field_name, context_ctx_str(ctx, SLOP_STR(" = "), field_val))));
                                                    } else {
                                                        result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR(", ."), context_ctx_str(ctx, field_name, context_ctx_str(ctx, SLOP_STR(" = "), field_val))));
                                                    }
                                                    first = 0;
                                                }
                                            } else if (!_mv_363.has_value) {
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
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_359.has_value) {
            }
            i = (i + 1);
        }
        return context_ctx_str(ctx, result, SLOP_STR("})"));
    }
}

slop_string expr_build_inline_struct_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr type_items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((type_items).len));
        __auto_type result = SLOP_STR("struct { ");
        __auto_type i = 1;
        while ((i < len)) {
            __auto_type _mv_364 = ({ __auto_type _lst = type_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_364.has_value) {
                __auto_type field_expr = _mv_364.value;
                __auto_type _mv_365 = (*field_expr);
                switch (_mv_365.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type field_lst = _mv_365.data.lst;
                        {
                            __auto_type field_items = field_lst.items;
                            if ((((int64_t)((field_items).len)) >= 2)) {
                                __auto_type _mv_366 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_366.has_value) {
                                    __auto_type name_expr = _mv_366.value;
                                    __auto_type _mv_367 = (*name_expr);
                                    switch (_mv_367.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type name_sym = _mv_367.data.sym;
                                            __auto_type _mv_368 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_368.has_value) {
                                                __auto_type type_expr = _mv_368.value;
                                                {
                                                    __auto_type field_name = ctype_to_c_name(arena, name_sym.name);
                                                    __auto_type field_type = context_to_c_type_prefixed(ctx, type_expr);
                                                    result = context_ctx_str(ctx, result, context_ctx_str(ctx, field_type, context_ctx_str(ctx, SLOP_STR(" "), context_ctx_str(ctx, field_name, SLOP_STR("; ")))));
                                                }
                                            } else if (!_mv_368.has_value) {
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_366.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_364.has_value) {
            }
            i = (i + 1);
        }
        return context_ctx_str(ctx, result, SLOP_STR("}"));
    }
}

slop_string expr_transpile_inline_record_fields(context_TranspileContext* ctx, slop_string struct_def, slop_list_types_SExpr_ptr items, int64_t start_idx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result = context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, struct_def, SLOP_STR("){")));
        __auto_type i = start_idx;
        __auto_type first = 1;
        while ((i < len)) {
            __auto_type _mv_369 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_369.has_value) {
                __auto_type field_expr = _mv_369.value;
                __auto_type _mv_370 = (*field_expr);
                switch (_mv_370.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type field_lst = _mv_370.data.lst;
                        {
                            __auto_type field_items = field_lst.items;
                            if ((((int64_t)((field_items).len)) >= 2)) {
                                __auto_type _mv_371 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_371.has_value) {
                                    __auto_type name_expr = _mv_371.value;
                                    __auto_type _mv_372 = (*name_expr);
                                    switch (_mv_372.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type name_sym = _mv_372.data.sym;
                                            __auto_type _mv_373 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_373.has_value) {
                                                __auto_type val_expr = _mv_373.value;
                                                {
                                                    __auto_type field_name = ctype_to_c_name(arena, name_sym.name);
                                                    __auto_type field_val = expr_transpile_expr(ctx, val_expr);
                                                    if (first) {
                                                        result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR("."), context_ctx_str(ctx, field_name, context_ctx_str(ctx, SLOP_STR(" = "), field_val))));
                                                    } else {
                                                        result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR(", ."), context_ctx_str(ctx, field_name, context_ctx_str(ctx, SLOP_STR(" = "), field_val))));
                                                    }
                                                    first = 0;
                                                }
                                            } else if (!_mv_373.has_value) {
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_371.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_369.has_value) {
            }
            i = (i + 1);
        }
        return context_ctx_str(ctx, result, SLOP_STR("})"));
    }
}

slop_string expr_transpile_list_literal(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if ((len < 2)) {
            context_ctx_add_error_at(ctx, SLOP_STR("list: missing type"), context_list_first_line(items), context_list_first_col(items));
            return SLOP_STR("0");
        } else {
            __auto_type _mv_374 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_374.has_value) {
                __auto_type type_expr = _mv_374.value;
                {
                    __auto_type elem_type = context_to_c_type_prefixed(ctx, type_expr);
                    __auto_type elem_count = (len - 2);
                    {
                        __auto_type type_id = ctype_type_to_identifier(arena, elem_type);
                        __auto_type count_str = int_to_string(arena, elem_count);
                        __auto_type result = context_ctx_str(ctx, SLOP_STR("((slop_list_"), context_ctx_str(ctx, type_id, SLOP_STR("){")));
                        __auto_type data_part = context_ctx_str(ctx, SLOP_STR(".len = "), context_ctx_str(ctx, count_str, context_ctx_str(ctx, SLOP_STR(", .cap = "), context_ctx_str(ctx, count_str, context_ctx_str(ctx, SLOP_STR(", .data = ("), context_ctx_str(ctx, elem_type, SLOP_STR("[]){")))))));
                        __auto_type i = 2;
                        __auto_type first = 1;
                        while ((i < len)) {
                            __auto_type _mv_375 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_375.has_value) {
                                __auto_type elem_expr = _mv_375.value;
                                {
                                    __auto_type elem_c = expr_transpile_expr(ctx, elem_expr);
                                    if (first) {
                                        data_part = context_ctx_str(ctx, data_part, elem_c);
                                    } else {
                                        data_part = context_ctx_str(ctx, data_part, context_ctx_str(ctx, SLOP_STR(", "), elem_c));
                                    }
                                    first = 0;
                                }
                            } else if (!_mv_375.has_value) {
                            }
                            i = (i + 1);
                        }
                        return context_ctx_str(ctx, result, context_ctx_str(ctx, data_part, SLOP_STR("}})")));
                    }
                }
            } else if (!_mv_374.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("list: missing type"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("0");
            }
        }
    }
}

slop_string expr_build_struct_key_info(context_TranspileContext* ctx, slop_string c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return context_ctx_str(ctx, SLOP_STR("sizeof("), context_ctx_str(ctx, c_name, context_ctx_str(ctx, SLOP_STR("), slop_hash_"), context_ctx_str(ctx, c_name, context_ctx_str(ctx, SLOP_STR(", slop_eq_"), c_name)))));
}

slop_string expr_get_map_key_c_info(context_TranspileContext* ctx, types_SExpr* key_type_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((key_type_expr != NULL)), "(!= key-type-expr nil)");
    __auto_type _mv_376 = (*key_type_expr);
    switch (_mv_376.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_376.data.sym;
            {
                __auto_type name = sym.name;
                if (string_eq(name, SLOP_STR("String"))) {
                    return SLOP_STR("sizeof(slop_string), slop_hash_string, slop_eq_string");
                } else if ((string_eq(name, SLOP_STR("Int")) || string_eq(name, SLOP_STR("I64")))) {
                    return SLOP_STR("sizeof(int64_t), slop_hash_int, slop_eq_int");
                } else if (string_eq(name, SLOP_STR("I32"))) {
                    return SLOP_STR("sizeof(int32_t), slop_hash_int, slop_eq_int");
                } else if ((string_eq(name, SLOP_STR("Uint")) || string_eq(name, SLOP_STR("U64")))) {
                    return SLOP_STR("sizeof(uint64_t), slop_hash_uint, slop_eq_uint");
                } else if (string_eq(name, SLOP_STR("U32"))) {
                    return SLOP_STR("sizeof(uint32_t), slop_hash_uint, slop_eq_uint");
                } else if (string_eq(name, SLOP_STR("Symbol"))) {
                    return SLOP_STR("sizeof(int64_t), slop_hash_symbol, slop_eq_symbol");
                } else {
                    {
                        __auto_type arena = (*ctx).arena;
                        __auto_type result = expr_get_struct_key_info_by_name(ctx, name);
                        if ((string_len(result) > 0)) {
                            return result;
                        } else {
                            {
                                __auto_type c_name = ctype_to_c_name(arena, name);
                                context_ctx_register_struct_key_type(ctx, c_name);
                                return expr_build_struct_key_info(ctx, c_name);
                            }
                        }
                    }
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_376.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return SLOP_STR("sizeof(void*), slop_hash_ptr, slop_eq_ptr");
                } else {
                    __auto_type _mv_377 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_377.has_value) {
                        __auto_type head = _mv_377.value;
                        __auto_type _mv_378 = (*head);
                        switch (_mv_378.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_378.data.sym;
                                {
                                    __auto_type head_name = sym.name;
                                    if (string_eq(head_name, SLOP_STR("Ptr"))) {
                                        return SLOP_STR("sizeof(void*), slop_hash_ptr, slop_eq_ptr");
                                    } else {
                                        return SLOP_STR("sizeof(slop_string), slop_hash_string, slop_eq_string");
                                    }
                                }
                            }
                            default: {
                                return SLOP_STR("sizeof(slop_string), slop_hash_string, slop_eq_string");
                            }
                        }
                    } else if (!_mv_377.has_value) {
                        return SLOP_STR("sizeof(void*), slop_hash_ptr, slop_eq_ptr");
                    }
                }
            }
        }
        default: {
            return SLOP_STR("sizeof(slop_string), slop_hash_string, slop_eq_string");
        }
    }
}

slop_string expr_get_struct_key_info_by_name(context_TranspileContext* ctx, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    __auto_type _mv_379 = context_ctx_lookup_type(ctx, name);
    if (_mv_379.has_value) {
        __auto_type type_entry = _mv_379.value;
        {
            __auto_type c_name = type_entry.c_name;
            context_ctx_register_struct_key_type(ctx, c_name);
            return expr_build_struct_key_info(ctx, c_name);
        }
    } else if (!_mv_379.has_value) {
        __auto_type _mv_380 = context_ctx_get_module(ctx);
        if (_mv_380.has_value) {
            __auto_type mod = _mv_380.value;
            {
                __auto_type prefixed = context_ctx_str3(ctx, mod, SLOP_STR("_"), name);
                __auto_type _mv_381 = context_ctx_lookup_type(ctx, prefixed);
                if (_mv_381.has_value) {
                    __auto_type type_entry = _mv_381.value;
                    {
                        __auto_type c_name = type_entry.c_name;
                        context_ctx_register_struct_key_type(ctx, c_name);
                        return expr_build_struct_key_info(ctx, c_name);
                    }
                } else if (!_mv_381.has_value) {
                    return SLOP_STR("");
                }
            }
        } else if (!_mv_380.has_value) {
            return SLOP_STR("");
        }
    }
}

slop_string expr_transpile_map_new(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 3)) {
            if ((len < 2)) {
                context_ctx_add_error_at(ctx, SLOP_STR("map-new: missing arena"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("NULL");
            } else {
                __auto_type _mv_382 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_382.has_value) {
                    __auto_type arena_expr = _mv_382.value;
                    {
                        __auto_type arena_c = expr_transpile_expr(ctx, arena_expr);
                        return context_ctx_str(ctx, SLOP_STR("slop_map_new_ptr("), context_ctx_str(ctx, arena_c, SLOP_STR(", 16, sizeof(slop_string), slop_hash_string, slop_eq_string)")));
                    }
                } else if (!_mv_382.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("map-new: missing arena"), context_list_first_line(items), context_list_first_col(items));
                    return SLOP_STR("NULL");
                }
            }
        } else {
            __auto_type _mv_383 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_383.has_value) {
                __auto_type arena_expr = _mv_383.value;
                __auto_type _mv_384 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_384.has_value) {
                    __auto_type key_type_expr = _mv_384.value;
                    {
                        __auto_type arena_c = expr_transpile_expr(ctx, arena_expr);
                        __auto_type key_info = expr_get_map_key_c_info(ctx, key_type_expr);
                        return context_ctx_str(ctx, SLOP_STR("slop_map_new_ptr("), context_ctx_str(ctx, arena_c, context_ctx_str(ctx, SLOP_STR(", 16, "), context_ctx_str(ctx, key_info, SLOP_STR(")")))));
                    }
                } else if (!_mv_384.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("map-new: missing KeyType"), context_list_first_line(items), context_list_first_col(items));
                    return SLOP_STR("NULL");
                }
            } else if (!_mv_383.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("map-new: missing arena"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("NULL");
            }
        }
    }
}

uint8_t expr_is_c_primitive_type(slop_string t) {
    if (string_eq(t, SLOP_STR("int64_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("int32_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("int16_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("int8_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("uint64_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("uint32_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("uint16_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("uint8_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("double"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("float"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("bool"))) {
        return 1;
    } else {
        return 0;
    }
}

slop_string expr_wrap_map_key_as_ptr(context_TranspileContext* ctx, slop_string key_c, types_SExpr* key_expr, types_SExpr* container_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((key_expr != NULL)), "(!= key-expr nil)");
    {
        __auto_type container_key_type = (((container_expr != NULL)) ? ({ __auto_type map_type = expr_infer_map_key_c_type(ctx, container_expr); (((string_len(map_type) > 0)) ? map_type : expr_infer_set_elem_c_type(ctx, container_expr)); }) : SLOP_STR(""));
        __auto_type key_type = (((string_len(container_key_type) > 0)) ? container_key_type : expr_infer_expr_c_type(ctx, key_expr));
        if (string_eq(key_type, SLOP_STR("slop_string"))) {
            return context_ctx_str(ctx, SLOP_STR("&("), context_ctx_str(ctx, key_c, SLOP_STR(")")));
        } else if (strlib_ends_with(key_type, SLOP_STR("*"))) {
            return context_ctx_str(ctx, SLOP_STR("&(void*){"), context_ctx_str(ctx, key_c, SLOP_STR("}")));
        } else if (expr_is_c_primitive_type(key_type)) {
            return context_ctx_str(ctx, SLOP_STR("&("), context_ctx_str(ctx, key_type, context_ctx_str(ctx, SLOP_STR("){"), context_ctx_str(ctx, key_c, SLOP_STR("}")))));
        } else {
            return context_ctx_str(ctx, SLOP_STR("&("), context_ctx_str(ctx, key_c, SLOP_STR(")")));
        }
    }
}

slop_string expr_transpile_map_put(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 4)) {
            context_ctx_add_error_at(ctx, SLOP_STR("map-put: needs map, key, val"), context_list_first_line(items), context_list_first_col(items));
            return SLOP_STR("0");
        } else {
            __auto_type _mv_385 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_385.has_value) {
                __auto_type map_expr = _mv_385.value;
                __auto_type _mv_386 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_386.has_value) {
                    __auto_type key_expr = _mv_386.value;
                    __auto_type _mv_387 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_387.has_value) {
                        __auto_type val_expr = _mv_387.value;
                        {
                            __auto_type map_c = expr_transpile_expr(ctx, map_expr);
                            __auto_type key_c = expr_transpile_expr(ctx, key_expr);
                            __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                            __auto_type key_ptr = expr_wrap_map_key_as_ptr(ctx, key_c, key_expr, map_expr);
                            __auto_type needs_deref = expr_is_ptr_to_ptr_map(ctx, map_expr);
                            if (needs_deref) {
                                {
                                    __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _val = "), val_c);
                                    __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("; void* _vptr = slop_arena_alloc(arena, sizeof(_val)); memcpy(_vptr, &_val, sizeof(_val)); slop_map_put(arena, (*"));
                                    __auto_type s3 = context_ctx_str(ctx, s2, map_c);
                                    __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR("), "));
                                    __auto_type s5 = context_ctx_str(ctx, s4, key_ptr);
                                    __auto_type s6 = context_ctx_str(ctx, s5, SLOP_STR(", _vptr); })"));
                                    return s6;
                                }
                            } else {
                                {
                                    __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _val = "), val_c);
                                    __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("; void* _vptr = slop_arena_alloc(arena, sizeof(_val)); memcpy(_vptr, &_val, sizeof(_val)); slop_map_put(arena, "));
                                    __auto_type s3 = context_ctx_str(ctx, s2, map_c);
                                    __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR(", "));
                                    __auto_type s5 = context_ctx_str(ctx, s4, key_ptr);
                                    __auto_type s6 = context_ctx_str(ctx, s5, SLOP_STR(", _vptr); })"));
                                    return s6;
                                }
                            }
                        }
                    } else if (!_mv_387.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("map-put: missing val"), context_list_first_line(items), context_list_first_col(items));
                        return SLOP_STR("0");
                    }
                } else if (!_mv_386.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("map-put: missing key"), context_list_first_line(items), context_list_first_col(items));
                    return SLOP_STR("0");
                }
            } else if (!_mv_385.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("map-put: missing map"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("0");
            }
        }
    }
}

slop_string expr_transpile_map_get(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type arena = (*ctx).arena;
        if ((len < 3)) {
            context_ctx_add_error_at(ctx, SLOP_STR("map-get: needs map, key"), context_list_first_line(items), context_list_first_col(items));
            return SLOP_STR("NULL");
        } else {
            __auto_type _mv_388 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_388.has_value) {
                __auto_type map_expr = _mv_388.value;
                __auto_type _mv_389 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_389.has_value) {
                    __auto_type key_expr = _mv_389.value;
                    {
                        __auto_type map_c = expr_transpile_expr(ctx, map_expr);
                        __auto_type key_c = expr_transpile_expr(ctx, key_expr);
                        __auto_type key_ptr = expr_wrap_map_key_as_ptr(ctx, key_c, key_expr, map_expr);
                        __auto_type option_type = expr_infer_map_value_option_type(ctx, map_expr);
                        if ((string_len(option_type) > 0)) {
                            {
                                __auto_type inner_type_name = expr_substring_after_prefix(arena, option_type, SLOP_STR("slop_option_"));
                                __auto_type value_c_type = expr_option_type_to_value_c_type(arena, option_type);
                                context_ctx_register_option_type(ctx, inner_type_name, option_type);
                                return context_ctx_str(ctx, SLOP_STR("({ void* _ptr = slop_map_get("), context_ctx_str(ctx, map_c, context_ctx_str(ctx, SLOP_STR(", "), context_ctx_str(ctx, key_ptr, context_ctx_str(ctx, SLOP_STR("); _ptr ? ("), context_ctx_str(ctx, option_type, context_ctx_str(ctx, SLOP_STR("){ .has_value = true, .value = *("), context_ctx_str(ctx, value_c_type, context_ctx_str(ctx, SLOP_STR("*)_ptr } : ("), context_ctx_str(ctx, option_type, SLOP_STR("){ .has_value = false }; })")))))))))));
                            }
                        } else {
                            return context_ctx_str(ctx, SLOP_STR("({ void* _ptr = slop_map_get("), context_ctx_str(ctx, map_c, context_ctx_str(ctx, SLOP_STR(", "), context_ctx_str(ctx, key_ptr, SLOP_STR("); struct { bool has_value; void* value; } _r; if (_ptr) { _r.has_value = true; _r.value = _ptr; } else { _r.has_value = false; } _r; })")))));
                        }
                    }
                } else if (!_mv_389.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("map-get: missing key"), context_list_first_line(items), context_list_first_col(items));
                    return SLOP_STR("NULL");
                }
            } else if (!_mv_388.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("map-get: missing map"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("NULL");
            }
        }
    }
}

slop_string expr_transpile_map_has(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 3)) {
            context_ctx_add_error_at(ctx, SLOP_STR("map-has: needs map, key"), context_list_first_line(items), context_list_first_col(items));
            return SLOP_STR("false");
        } else {
            __auto_type _mv_390 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_390.has_value) {
                __auto_type map_expr = _mv_390.value;
                __auto_type _mv_391 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_391.has_value) {
                    __auto_type key_expr = _mv_391.value;
                    {
                        __auto_type map_c = expr_transpile_expr(ctx, map_expr);
                        __auto_type key_c = expr_transpile_expr(ctx, key_expr);
                        __auto_type key_ptr = expr_wrap_map_key_as_ptr(ctx, key_c, key_expr, map_expr);
                        return context_ctx_str(ctx, SLOP_STR("(slop_map_get("), context_ctx_str(ctx, map_c, context_ctx_str(ctx, SLOP_STR(", "), context_ctx_str(ctx, key_ptr, SLOP_STR(") != NULL)")))));
                    }
                } else if (!_mv_391.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("map-has: missing key"), context_list_first_line(items), context_list_first_col(items));
                    return SLOP_STR("false");
                }
            } else if (!_mv_390.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("map-has: missing map"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("false");
            }
        }
    }
}

slop_string expr_transpile_map_keys(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type arena = (*ctx).arena;
        if ((len < 2)) {
            context_ctx_add_error_at(ctx, SLOP_STR("map-keys: needs map"), context_list_first_line(items), context_list_first_col(items));
            return SLOP_STR("NULL");
        } else {
            __auto_type _mv_392 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_392.has_value) {
                __auto_type map_expr = _mv_392.value;
                {
                    __auto_type map_c = expr_transpile_expr(ctx, map_expr);
                    __auto_type key_c_type = expr_infer_map_key_c_type(ctx, map_expr);
                    __auto_type debug_var_name = expr_get_var_name_from_expr(map_expr);
                    __auto_type debug_slop_type = ({ __auto_type _mv = context_ctx_lookup_var(ctx, debug_var_name); _mv.has_value ? ({ __auto_type entry = _mv.value; entry.slop_type; }) : (SLOP_STR("VAR_NOT_FOUND")); });
                    if ((string_eq(key_c_type, SLOP_STR("slop_string")) || (string_len(key_c_type) == 0))) {
                        return context_ctx_str(ctx, SLOP_STR("/* DEBUG: var="), context_ctx_str(ctx, debug_var_name, context_ctx_str(ctx, SLOP_STR(" slop="), context_ctx_str(ctx, debug_slop_type, context_ctx_str(ctx, SLOP_STR(" key="), context_ctx_str(ctx, key_c_type, context_ctx_str(ctx, SLOP_STR(" */ slop_map_keys(arena, "), context_ctx_str(ctx, map_c, SLOP_STR(")")))))))));
                    } else {
                        {
                            __auto_type list_type = context_ctx_str(ctx, SLOP_STR("slop_list_"), key_c_type);
                            return context_ctx_str(ctx, SLOP_STR("({ slop_set_elements_result _r = slop_set_elements_raw(arena, "), context_ctx_str(ctx, map_c, context_ctx_str(ctx, SLOP_STR("); ("), context_ctx_str(ctx, list_type, context_ctx_str(ctx, SLOP_STR("){.data = ("), context_ctx_str(ctx, key_c_type, context_ctx_str(ctx, SLOP_STR("*)_r.data, .len = _r.len, .cap = _r.cap}; })"), SLOP_STR(""))))))));
                        }
                    }
                }
            } else if (!_mv_392.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("map-keys: missing map"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("NULL");
            }
        }
    }
}

slop_string expr_transpile_set_new(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 3)) {
            context_ctx_add_error_at(ctx, SLOP_STR("set-new: needs arena and ElementType"), context_list_first_line(items), context_list_first_col(items));
            return SLOP_STR("NULL");
        } else {
            __auto_type _mv_393 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_393.has_value) {
                __auto_type arena_expr = _mv_393.value;
                __auto_type _mv_394 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_394.has_value) {
                    __auto_type elem_type_expr = _mv_394.value;
                    {
                        __auto_type arena_c = expr_transpile_expr(ctx, arena_expr);
                        __auto_type elem_info = expr_get_map_key_c_info(ctx, elem_type_expr);
                        return context_ctx_str(ctx, SLOP_STR("slop_map_new_ptr("), context_ctx_str(ctx, arena_c, context_ctx_str(ctx, SLOP_STR(", 16, "), context_ctx_str(ctx, elem_info, SLOP_STR(")")))));
                    }
                } else if (!_mv_394.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("set-new: missing ElementType"), context_list_first_line(items), context_list_first_col(items));
                    return SLOP_STR("NULL");
                }
            } else if (!_mv_393.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("set-new: missing arena"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("NULL");
            }
        }
    }
}

slop_string expr_transpile_set_put(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 3)) {
            context_ctx_add_error_at(ctx, SLOP_STR("set-put: needs set, element"), context_list_first_line(items), context_list_first_col(items));
            return SLOP_STR("0");
        } else {
            __auto_type _mv_395 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_395.has_value) {
                __auto_type set_expr = _mv_395.value;
                __auto_type _mv_396 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_396.has_value) {
                    __auto_type elem_expr = _mv_396.value;
                    {
                        __auto_type set_c = expr_transpile_expr(ctx, set_expr);
                        __auto_type elem_c = expr_transpile_expr(ctx, elem_expr);
                        __auto_type elem_ptr = expr_wrap_map_key_as_ptr(ctx, elem_c, elem_expr, set_expr);
                        return context_ctx_str(ctx, SLOP_STR("({ uint8_t _dummy = 1; slop_map_put(arena, "), context_ctx_str(ctx, set_c, context_ctx_str(ctx, SLOP_STR(", "), context_ctx_str(ctx, elem_ptr, SLOP_STR(", &_dummy); })")))));
                    }
                } else if (!_mv_396.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("set-put: missing element"), context_list_first_line(items), context_list_first_col(items));
                    return SLOP_STR("0");
                }
            } else if (!_mv_395.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("set-put: missing set"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("0");
            }
        }
    }
}

slop_string expr_transpile_set_has(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 3)) {
            context_ctx_add_error_at(ctx, SLOP_STR("set-has: needs set, element"), context_list_first_line(items), context_list_first_col(items));
            return SLOP_STR("false");
        } else {
            __auto_type _mv_397 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_397.has_value) {
                __auto_type set_expr = _mv_397.value;
                __auto_type _mv_398 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_398.has_value) {
                    __auto_type elem_expr = _mv_398.value;
                    {
                        __auto_type set_c = expr_transpile_expr(ctx, set_expr);
                        __auto_type elem_c = expr_transpile_expr(ctx, elem_expr);
                        __auto_type elem_ptr = expr_wrap_map_key_as_ptr(ctx, elem_c, elem_expr, set_expr);
                        return context_ctx_str(ctx, SLOP_STR("(slop_map_get("), context_ctx_str(ctx, set_c, context_ctx_str(ctx, SLOP_STR(", "), context_ctx_str(ctx, elem_ptr, SLOP_STR(") != NULL)")))));
                    }
                } else if (!_mv_398.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("set-has: missing element"), context_list_first_line(items), context_list_first_col(items));
                    return SLOP_STR("false");
                }
            } else if (!_mv_397.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("set-has: missing set"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("false");
            }
        }
    }
}

slop_string expr_transpile_set_remove(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 3)) {
            context_ctx_add_error_at(ctx, SLOP_STR("set-remove: needs set, element"), context_list_first_line(items), context_list_first_col(items));
            return SLOP_STR("0");
        } else {
            __auto_type _mv_399 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_399.has_value) {
                __auto_type set_expr = _mv_399.value;
                __auto_type _mv_400 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_400.has_value) {
                    __auto_type elem_expr = _mv_400.value;
                    {
                        __auto_type set_c = expr_transpile_expr(ctx, set_expr);
                        __auto_type elem_c = expr_transpile_expr(ctx, elem_expr);
                        __auto_type elem_ptr = expr_wrap_map_key_as_ptr(ctx, elem_c, elem_expr, set_expr);
                        return context_ctx_str(ctx, SLOP_STR("slop_map_remove("), context_ctx_str(ctx, set_c, context_ctx_str(ctx, SLOP_STR(", "), context_ctx_str(ctx, elem_ptr, SLOP_STR(")")))));
                    }
                } else if (!_mv_400.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("set-remove: missing element"), context_list_first_line(items), context_list_first_col(items));
                    return SLOP_STR("0");
                }
            } else if (!_mv_399.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("set-remove: missing set"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("0");
            }
        }
    }
}

slop_string expr_transpile_set_elements(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 2)) {
            context_ctx_add_error_at(ctx, SLOP_STR("set-elements: needs set"), context_list_first_line(items), context_list_first_col(items));
            return SLOP_STR("NULL");
        } else {
            __auto_type _mv_401 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_401.has_value) {
                __auto_type set_expr = _mv_401.value;
                {
                    __auto_type set_c = expr_transpile_expr(ctx, set_expr);
                    __auto_type elem_c_type = expr_infer_set_elem_c_type(ctx, set_expr);
                    if ((string_eq(elem_c_type, SLOP_STR("slop_string")) || (string_len(elem_c_type) == 0))) {
                        return context_ctx_str(ctx, SLOP_STR("slop_map_keys(arena, "), context_ctx_str(ctx, set_c, SLOP_STR(")")));
                    } else {
                        {
                            __auto_type list_type = context_ctx_str(ctx, SLOP_STR("slop_list_"), elem_c_type);
                            return context_ctx_str(ctx, SLOP_STR("({ slop_set_elements_result _r = slop_set_elements_raw(arena, "), context_ctx_str(ctx, set_c, context_ctx_str(ctx, SLOP_STR("); ("), context_ctx_str(ctx, list_type, context_ctx_str(ctx, SLOP_STR("){.data = ("), context_ctx_str(ctx, elem_c_type, context_ctx_str(ctx, SLOP_STR("*)_r.data, .len = _r.len, .cap = _r.cap}; })"), SLOP_STR(""))))))));
                        }
                    }
                }
            } else if (!_mv_401.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("set-elements: missing set"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("NULL");
            }
        }
    }
}

slop_string expr_transpile_set_literal(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if ((len < 2)) {
            context_ctx_add_error_at(ctx, SLOP_STR("set: needs at least Type"), context_list_first_line(items), context_list_first_col(items));
            return SLOP_STR("NULL");
        } else {
            __auto_type _mv_402 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_402.has_value) {
                __auto_type type_expr = _mv_402.value;
                {
                    __auto_type elem_info = expr_get_map_key_c_info(ctx, type_expr);
                    __auto_type num_elems = (len - 2);
                    __auto_type init_cap = (((num_elems > 16)) ? num_elems : 16);
                    __auto_type result = context_ctx_str(ctx, SLOP_STR("({ slop_map* _s = slop_map_new_ptr(arena, "), context_ctx_str(ctx, int_to_string(arena, init_cap), context_ctx_str(ctx, SLOP_STR(", "), context_ctx_str(ctx, elem_info, SLOP_STR("); ")))));
                    {
                        __auto_type i = 2;
                        while ((i < len)) {
                            __auto_type _mv_403 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_403.has_value) {
                                __auto_type elem_expr = _mv_403.value;
                                {
                                    __auto_type elem_c = expr_transpile_expr(ctx, elem_expr);
                                    __auto_type elem_ptr = expr_wrap_map_key_as_ptr(ctx, elem_c, elem_expr, NULL);
                                    result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR("slop_map_put(arena, _s, "), context_ctx_str(ctx, elem_ptr, SLOP_STR(", &(uint8_t){1}); "))));
                                }
                            } else if (!_mv_403.has_value) {
                            }
                            i = (i + 1);
                        }
                    }
                    return context_ctx_str(ctx, result, SLOP_STR("_s; })"));
                }
            } else if (!_mv_402.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("set: missing type"), context_list_first_line(items), context_list_first_col(items));
                return SLOP_STR("NULL");
            }
        }
    }
}

slop_string expr_transpile_for_as_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if ((len < 2)) {
            return SLOP_STR("({ /* for: need binding */ 0; })");
        } else {
            __auto_type _mv_404 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_404.has_value) {
                __auto_type binding_expr = _mv_404.value;
                __auto_type _mv_405 = (*binding_expr);
                switch (_mv_405.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type binding_lst = _mv_405.data.lst;
                        {
                            __auto_type binding_items = binding_lst.items;
                            __auto_type binding_len = ((int64_t)((binding_items).len));
                            if ((binding_len < 3)) {
                                return SLOP_STR("({ /* for: binding needs (var start end) */ 0; })");
                            } else {
                                __auto_type _mv_406 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_406.has_value) {
                                    __auto_type var_expr = _mv_406.value;
                                    __auto_type _mv_407 = (*var_expr);
                                    switch (_mv_407.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type var_sym = _mv_407.data.sym;
                                            {
                                                __auto_type var_name = ctype_to_c_name(arena, var_sym.name);
                                                __auto_type _mv_408 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_408.has_value) {
                                                    __auto_type start_expr = _mv_408.value;
                                                    __auto_type _mv_409 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_409.has_value) {
                                                        __auto_type end_expr = _mv_409.value;
                                                        {
                                                            __auto_type start_c = expr_transpile_expr(ctx, start_expr);
                                                            __auto_type end_c = expr_transpile_expr(ctx, end_expr);
                                                            __auto_type result = context_ctx_str5(ctx, SLOP_STR("({ for (int64_t "), var_name, SLOP_STR(" = "), start_c, context_ctx_str5(ctx, SLOP_STR("; "), var_name, SLOP_STR(" < "), end_c, context_ctx_str3(ctx, SLOP_STR("; "), var_name, SLOP_STR("++) { "))));
                                                            context_ctx_push_scope(ctx);
                                                            context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, SLOP_STR("int64_t"), SLOP_STR(""), 0, 0});
                                                            {
                                                                __auto_type i = 2;
                                                                while ((i < len)) {
                                                                    __auto_type _mv_410 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                    if (_mv_410.has_value) {
                                                                        __auto_type body_expr = _mv_410.value;
                                                                        {
                                                                            __auto_type body_c = expr_transpile_expr(ctx, body_expr);
                                                                            result = context_ctx_str3(ctx, result, body_c, SLOP_STR("; "));
                                                                        }
                                                                    } else if (!_mv_410.has_value) {
                                                                    }
                                                                    i = (i + 1);
                                                                }
                                                            }
                                                            context_ctx_pop_scope(ctx);
                                                            return context_ctx_str(ctx, result, SLOP_STR("} 0; })"));
                                                        }
                                                    } else if (!_mv_409.has_value) {
                                                        return SLOP_STR("({ /* for: missing end */ 0; })");
                                                    }
                                                } else if (!_mv_408.has_value) {
                                                    return SLOP_STR("({ /* for: missing start */ 0; })");
                                                }
                                            }
                                        }
                                        default: {
                                            return SLOP_STR("({ /* for: var must be symbol */ 0; })");
                                        }
                                    }
                                } else if (!_mv_406.has_value) {
                                    return SLOP_STR("({ /* for: missing var */ 0; })");
                                }
                            }
                        }
                    }
                    default: {
                        return SLOP_STR("({ /* for: binding must be list */ 0; })");
                    }
                }
            } else if (!_mv_404.has_value) {
                return SLOP_STR("({ /* for: missing binding */ 0; })");
            }
        }
    }
}

slop_string expr_transpile_for_each_as_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if ((len < 2)) {
            return SLOP_STR("({ /* for-each: need binding */ 0; })");
        } else {
            __auto_type _mv_411 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_411.has_value) {
                __auto_type binding_expr = _mv_411.value;
                __auto_type _mv_412 = (*binding_expr);
                switch (_mv_412.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type binding_lst = _mv_412.data.lst;
                        {
                            __auto_type binding_items = binding_lst.items;
                            __auto_type binding_len = ((int64_t)((binding_items).len));
                            if ((binding_len < 2)) {
                                return SLOP_STR("({ /* for-each: binding needs (var coll) */ 0; })");
                            } else {
                                __auto_type _mv_413 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_413.has_value) {
                                    __auto_type var_expr = _mv_413.value;
                                    __auto_type _mv_414 = (*var_expr);
                                    switch (_mv_414.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type var_sym = _mv_414.data.sym;
                                            {
                                                __auto_type var_name = ctype_to_c_name(arena, var_sym.name);
                                                __auto_type _mv_415 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_415.has_value) {
                                                    __auto_type coll_expr = _mv_415.value;
                                                    {
                                                        __auto_type coll_c = expr_transpile_expr(ctx, coll_expr);
                                                        __auto_type elem_slop_type = expr_infer_collection_element_slop_type(ctx, coll_expr);
                                                        __auto_type result = context_ctx_str3(ctx, SLOP_STR("({ for (size_t _i = 0; _i < "), coll_c, context_ctx_str5(ctx, SLOP_STR(".len; _i++) { __auto_type "), var_name, SLOP_STR(" = "), coll_c, SLOP_STR(".data[_i]; ")));
                                                        context_ctx_push_scope(ctx);
                                                        context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, SLOP_STR("auto"), elem_slop_type, 0, 0});
                                                        {
                                                            __auto_type i = 2;
                                                            while ((i < len)) {
                                                                __auto_type _mv_416 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                if (_mv_416.has_value) {
                                                                    __auto_type body_expr = _mv_416.value;
                                                                    {
                                                                        __auto_type body_c = expr_transpile_expr(ctx, body_expr);
                                                                        result = context_ctx_str3(ctx, result, body_c, SLOP_STR("; "));
                                                                    }
                                                                } else if (!_mv_416.has_value) {
                                                                }
                                                                i = (i + 1);
                                                            }
                                                        }
                                                        context_ctx_pop_scope(ctx);
                                                        return context_ctx_str(ctx, result, SLOP_STR("} 0; })"));
                                                    }
                                                } else if (!_mv_415.has_value) {
                                                    return SLOP_STR("({ /* for-each: missing collection */ 0; })");
                                                }
                                            }
                                        }
                                        default: {
                                            return SLOP_STR("({ /* for-each: var must be symbol */ 0; })");
                                        }
                                    }
                                } else if (!_mv_413.has_value) {
                                    return SLOP_STR("({ /* for-each: missing var */ 0; })");
                                }
                            }
                        }
                    }
                    default: {
                        return SLOP_STR("({ /* for-each: binding must be list */ 0; })");
                    }
                }
            } else if (!_mv_411.has_value) {
                return SLOP_STR("({ /* for-each: missing binding */ 0; })");
            }
        }
    }
}

slop_string expr_extract_first_type_arg(slop_arena* arena, slop_string slop_type, int64_t start) {
    {
        __auto_type len = ((int64_t)(string_len(slop_type)));
        __auto_type depth = 0;
        __auto_type end_pos = start;
        __auto_type found = 0;
        while (((end_pos < len) && !(found))) {
            {
                __auto_type c = strlib_char_at(slop_type, ((int64_t)(end_pos)));
                if ((c == 40)) {
                    depth = (depth + 1);
                    end_pos = (end_pos + 1);
                } else if ((c == 41)) {
                    if ((depth == 0)) {
                        found = 1;
                    } else {
                        depth = (depth - 1);
                        end_pos = (end_pos + 1);
                    }
                } else if (((c == 32) && (depth == 0))) {
                    found = 1;
                } else {
                    end_pos = (end_pos + 1);
                }
            }
        }
        if ((end_pos > start)) {
            return strlib_substring(arena, slop_type, ((int64_t)(start)), ((int64_t)((end_pos - start))));
        } else {
            return SLOP_STR("");
        }
    }
}

slop_string expr_extract_second_type_arg(slop_arena* arena, slop_string slop_type, int64_t start) {
    {
        __auto_type first_arg = expr_extract_first_type_arg(arena, slop_type, start);
        __auto_type first_len = string_len(first_arg);
        if ((first_len == 0)) {
            return SLOP_STR("");
        } else {
            return expr_extract_first_type_arg(arena, slop_type, (start + (((int64_t)(first_len)) + 1)));
        }
    }
}

slop_string expr_infer_result_ok_slop_type(context_TranspileContext* ctx, types_SExpr* scrutinee) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((scrutinee != NULL)), "(!= scrutinee nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_417 = (*scrutinee);
        switch (_mv_417.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_417.data.sym;
                __auto_type _mv_418 = context_ctx_lookup_var(ctx, sym.name);
                if (_mv_418.has_value) {
                    __auto_type var_entry = _mv_418.value;
                    {
                        __auto_type slop_type = var_entry.slop_type;
                        if (strlib_starts_with(slop_type, SLOP_STR("(Result "))) {
                            return expr_extract_first_type_arg(arena, slop_type, 8);
                        } else {
                            return SLOP_STR("");
                        }
                    }
                } else if (!_mv_418.has_value) {
                    return SLOP_STR("");
                }
            }
            default: {
                return SLOP_STR("");
            }
        }
    }
}

slop_string expr_infer_result_err_slop_type(context_TranspileContext* ctx, types_SExpr* scrutinee) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((scrutinee != NULL)), "(!= scrutinee nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_419 = (*scrutinee);
        switch (_mv_419.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_419.data.sym;
                __auto_type _mv_420 = context_ctx_lookup_var(ctx, sym.name);
                if (_mv_420.has_value) {
                    __auto_type var_entry = _mv_420.value;
                    {
                        __auto_type slop_type = var_entry.slop_type;
                        if (strlib_starts_with(slop_type, SLOP_STR("(Result "))) {
                            return expr_extract_second_type_arg(arena, slop_type, 8);
                        } else {
                            return SLOP_STR("");
                        }
                    }
                } else if (!_mv_420.has_value) {
                    return SLOP_STR("");
                }
            }
            default: {
                return SLOP_STR("");
            }
        }
    }
}

slop_string expr_infer_collection_element_slop_type(context_TranspileContext* ctx, types_SExpr* coll_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((coll_expr != NULL)), "(!= coll-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_421 = (*coll_expr);
        switch (_mv_421.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_421.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) < 1)) {
                        return SLOP_STR("");
                    } else {
                        __auto_type _mv_422 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_422.has_value) {
                            __auto_type head = _mv_422.value;
                            __auto_type _mv_423 = (*head);
                            switch (_mv_423.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_423.data.sym;
                                    {
                                        __auto_type op = sym.name;
                                        if (string_eq(op, SLOP_STR("map-keys"))) {
                                            if ((((int64_t)((items).len)) < 2)) {
                                                return SLOP_STR("");
                                            } else {
                                                __auto_type _mv_424 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_424.has_value) {
                                                    __auto_type map_expr = _mv_424.value;
                                                    {
                                                        __auto_type map_slop_type = expr_infer_expr_slop_type(ctx, map_expr);
                                                        if ((string_len(map_slop_type) > 0)) {
                                                            {
                                                                __auto_type resolved = expr_resolve_type_alias_for_map(ctx, map_slop_type);
                                                                return expr_extract_map_key_from_slop_type(arena, resolved);
                                                            }
                                                        } else {
                                                            return SLOP_STR("");
                                                        }
                                                    }
                                                } else if (!_mv_424.has_value) {
                                                    return SLOP_STR("");
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("set-elements"))) {
                                            if ((((int64_t)((items).len)) < 2)) {
                                                return SLOP_STR("");
                                            } else {
                                                __auto_type _mv_425 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_425.has_value) {
                                                    __auto_type set_expr = _mv_425.value;
                                                    {
                                                        __auto_type set_slop_type = expr_infer_expr_slop_type(ctx, set_expr);
                                                        if ((string_len(set_slop_type) > 0)) {
                                                            {
                                                                __auto_type resolved = expr_resolve_type_alias_for_map(ctx, set_slop_type);
                                                                return expr_extract_set_elem_from_slop_type(arena, resolved);
                                                            }
                                                        } else {
                                                            return SLOP_STR("");
                                                        }
                                                    }
                                                } else if (!_mv_425.has_value) {
                                                    return SLOP_STR("");
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("map-values"))) {
                                            if ((((int64_t)((items).len)) < 2)) {
                                                return SLOP_STR("");
                                            } else {
                                                __auto_type _mv_426 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_426.has_value) {
                                                    __auto_type map_expr = _mv_426.value;
                                                    {
                                                        __auto_type map_slop_type = expr_infer_expr_slop_type(ctx, map_expr);
                                                        if ((string_len(map_slop_type) > 0)) {
                                                            {
                                                                __auto_type resolved = expr_resolve_type_alias_for_map(ctx, map_slop_type);
                                                                return expr_extract_map_value_from_slop_type(arena, resolved);
                                                            }
                                                        } else {
                                                            return SLOP_STR("");
                                                        }
                                                    }
                                                } else if (!_mv_426.has_value) {
                                                    return SLOP_STR("");
                                                }
                                            }
                                        } else {
                                            return expr_infer_elem_from_type(ctx, coll_expr);
                                        }
                                    }
                                }
                                default: {
                                    return expr_infer_elem_from_type(ctx, coll_expr);
                                }
                            }
                        } else if (!_mv_422.has_value) {
                            return SLOP_STR("");
                        }
                    }
                }
            }
            default: {
                return expr_infer_elem_from_type(ctx, coll_expr);
            }
        }
    }
}

slop_string expr_infer_elem_from_type(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type slop_type = expr_infer_expr_slop_type(ctx, expr);
        if ((string_len(slop_type) == 0)) {
            return SLOP_STR("");
        } else {
            {
                __auto_type resolved_type = expr_resolve_type_alias_for_map(ctx, slop_type);
                if (strlib_starts_with(resolved_type, SLOP_STR("(List "))) {
                    {
                        __auto_type elem_len = ((string_len(resolved_type) - 6) - 1);
                        if ((elem_len > 0)) {
                            return strlib_substring(arena, resolved_type, 6, ((int64_t)(elem_len)));
                        } else {
                            return SLOP_STR("");
                        }
                    }
                } else if (strlib_starts_with(resolved_type, SLOP_STR("(Set "))) {
                    return expr_extract_set_elem_from_slop_type(arena, resolved_type);
                } else if (strlib_starts_with(resolved_type, SLOP_STR("(Map "))) {
                    return expr_extract_map_key_from_slop_type(arena, resolved_type);
                } else {
                    return SLOP_STR("");
                }
            }
        }
    }
}

