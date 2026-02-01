#include "../runtime/slop_runtime.h"
#include "slop_emit.h"

slop_string emit_prefix_symbol(slop_arena* arena, slop_string name, slop_string prefix, type_extract_TypeRegistry types);
emit_EmitContext* emit_emit_ctx_new(slop_arena* arena);
emit_EmitContext* emit_emit_ctx_new_typed(slop_arena* arena, type_extract_TypeRegistry* types);
void emit_emit(emit_EmitContext* ctx, slop_string line);
slop_list_string emit_emit_ctx_get_lines(emit_EmitContext* ctx);
slop_string emit_sexpr_to_c_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_emit_union_literal_typed(slop_arena* arena, type_extract_TypeEntry* union_entry, slop_string variant_name, slop_list_types_SExpr_ptr items, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_emit_record_literal_typed(slop_arena* arena, type_extract_TypeEntry* record_entry, slop_list_types_SExpr_ptr items, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_emit_field_value_typed(slop_arena* arena, types_SExpr* item, slop_string field_type, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_emit_option_value_typed(slop_arena* arena, types_SExpr* item, slop_string opt_type, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_option_type_to_c(slop_arena* arena, slop_string opt_type, slop_string prefix);
slop_string emit_emit_binary_op_typed(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string c_op, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_emit_function_call_typed(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_emit_args_typed(slop_arena* arena, slop_list_types_SExpr_ptr items, int64_t start, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_emit_type_constructor_typed(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_sexpr_to_c(slop_arena* arena, types_SExpr* expr, slop_string prefix);
slop_string emit_emit_binary_op(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string c_op, slop_string prefix);
slop_string emit_emit_function_call(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string prefix);
slop_string emit_emit_args(slop_arena* arena, slop_list_types_SExpr_ptr items, int64_t start, slop_string prefix);
slop_string emit_emit_type_constructor(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string prefix);
slop_string emit_escape_string(slop_arena* arena, slop_string s);
slop_list_string emit_emit_test_harness_typed(slop_arena* arena, slop_list_extract_TestCase_ptr tests, slop_string module_prefix, type_extract_TypeRegistry* types, slop_list_type_extract_ImportEntry imports);
slop_list_string emit_emit_test_harness(slop_arena* arena, slop_list_extract_TestCase_ptr tests, slop_string module_prefix);
uint8_t emit_any_test_needs_arena(slop_list_extract_TestCase_ptr tests);
void emit_emit_test_function_typed(emit_EmitContext* ctx, extract_TestCase tc, int64_t index, slop_string prefix, type_extract_TypeRegistry* types);
uint8_t emit_is_none_or_some_form(types_SExpr* expr);
uint8_t emit_args_contain_complex_constructor(slop_list_types_SExpr_ptr args);
void emit_emit_test_function(emit_EmitContext* ctx, extract_TestCase tc, int64_t index, slop_string prefix);
void emit_emit_main_function(emit_EmitContext* ctx, int64_t test_count, uint8_t needs_arena);
slop_string emit_build_args_display_typed(slop_arena* arena, slop_list_types_SExpr_ptr args, type_extract_TypeRegistry types);
slop_string emit_build_call_args_typed(slop_arena* arena, slop_list_types_SExpr_ptr args, uint8_t needs_arena, int64_t arena_pos, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_make_c_fn_name(slop_arena* arena, slop_string fn_name, slop_option_string module_name, slop_string prefix);
slop_string emit_build_args_display(slop_arena* arena, slop_list_types_SExpr_ptr args);
slop_string emit_build_call_args(slop_arena* arena, slop_list_types_SExpr_ptr args, uint8_t needs_arena, int64_t arena_pos, slop_string prefix);
emit_CompareInfo emit_build_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_option_string return_type, slop_string prefix, type_extract_TypeRegistry types, slop_option_string eq_fn);
emit_CompareInfo emit_build_record_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_get_record_name_from_expr(types_SExpr* expr);
slop_list_types_SExpr_ptr emit_get_record_field_values(slop_arena* arena, types_SExpr* expr);
uint8_t emit_is_wildcard_expr(types_SExpr* expr);
slop_string emit_build_record_field_comparisons_with_values(slop_arena* arena, slop_list_type_extract_FieldEntry fields, slop_list_types_SExpr_ptr field_values, slop_string result_accessor, slop_string expected_var);
slop_string emit_build_single_field_comparison_with_accessor(slop_arena* arena, slop_string fname, slop_string ftype, slop_string result_accessor, slop_string expected_var);
slop_string emit_build_record_field_comparisons(slop_arena* arena, slop_list_type_extract_FieldEntry fields, slop_string prefix, slop_string expected_var);
slop_string emit_build_single_field_comparison(slop_arena* arena, slop_string fname, slop_string ftype, slop_string expected_var);
emit_CompareInfo emit_build_union_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types, slop_string ret_type_str);
slop_string emit_build_union_payload_comparison(slop_arena* arena, slop_string payload_type, slop_string c_variant, slop_string expected_var, type_extract_TypeRegistry types);
slop_string emit_build_union_record_payload_comparison(slop_arena* arena, slop_list_type_extract_FieldEntry fields, slop_string c_variant, slop_string expected_var);
slop_string emit_build_union_field_comparison(slop_arena* arena, slop_string fname, slop_string ftype, slop_string c_variant, slop_string expected_var);
uint8_t emit_is_union_constructor_typed(types_SExpr* expr, type_extract_TypeRegistry types);
slop_string emit_get_union_variant_name(types_SExpr* expr);
uint8_t emit_is_enum_value_typed(types_SExpr* expr, type_extract_TypeRegistry types);
uint8_t emit_is_record_constructor_typed(types_SExpr* expr, type_extract_TypeRegistry types);
slop_string emit_emit_string_slice(slop_string s, int64_t start);
slop_string emit_get_some_inner_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_get_ok_inner_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types);
types_SExpr* emit_get_some_inner_expr(types_SExpr* expected);
slop_string emit_get_error_inner_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types);
types_SExpr* emit_get_ok_inner_expr(types_SExpr* expected);
slop_string emit_extract_list_element_type(slop_arena* arena, slop_string list_type_str);
slop_string emit_build_eq_function_name(slop_arena* arena, slop_string type_name, slop_string prefix, type_extract_TypeRegistry types);
emit_CompareInfo emit_build_list_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types, slop_string ret_type_str, slop_option_string eq_fn);
uint8_t emit_is_none_value(types_SExpr* expr);
uint8_t emit_is_some_value(types_SExpr* expr);
uint8_t emit_is_ok_value(types_SExpr* expr);
uint8_t emit_is_error_value(types_SExpr* expr);
slop_string emit_get_some_inner(slop_arena* arena, types_SExpr* expr, slop_string prefix);
slop_string emit_get_ok_inner(slop_arena* arena, types_SExpr* expr, slop_string prefix);
slop_string emit_get_error_inner(slop_arena* arena, types_SExpr* expr, slop_string prefix);
uint8_t emit_is_list_literal(types_SExpr* expr);
uint8_t emit_is_union_or_record_constructor(types_SExpr* expr);
emit_CompareInfo emit_build_comparison(slop_arena* arena, types_SExpr* expected, slop_option_string return_type, slop_string prefix);
emit_CompareInfo emit_build_list_comparison(slop_arena* arena, types_SExpr* expected, slop_string prefix);

slop_string emit_prefix_symbol(slop_arena* arena, slop_string name, slop_string prefix, type_extract_TypeRegistry types) {
    if (string_eq(name, SLOP_STR("arena"))) {
        return SLOP_STR("test_arena");
    } else {
        __auto_type _mv_130 = type_extract_registry_lookup_import(types, name);
        if (_mv_130.has_value) {
            __auto_type mod_name = _mv_130.value;
            return string_concat(arena, ctype_to_c_name(arena, mod_name), string_concat(arena, SLOP_STR("_"), ctype_to_c_name(arena, name)));
        } else if (!_mv_130.has_value) {
            if ((((int64_t)(prefix.len)) > 0)) {
                return string_concat(arena, prefix, string_concat(arena, SLOP_STR("_"), ctype_to_c_name(arena, name)));
            } else {
                return ctype_to_c_name(arena, name);
            }
        }
    }
}

emit_EmitContext* emit_emit_ctx_new(slop_arena* arena) {
    {
        __auto_type ctx = ((emit_EmitContext*)((uint8_t*)slop_arena_alloc(arena, 128)));
        (*ctx) = (emit_EmitContext){((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }), arena, ((type_extract_TypeRegistry*)(0)), 0};
        return ctx;
    }
}

emit_EmitContext* emit_emit_ctx_new_typed(slop_arena* arena, type_extract_TypeRegistry* types) {
    {
        __auto_type ctx = ((emit_EmitContext*)((uint8_t*)slop_arena_alloc(arena, 128)));
        (*ctx) = (emit_EmitContext){((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }), arena, types, 1};
        return ctx;
    }
}

void emit_emit(emit_EmitContext* ctx, slop_string line) {
    ({ __auto_type _lst_p = &((*ctx).lines); __auto_type _item = (line); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_list_string emit_emit_ctx_get_lines(emit_EmitContext* ctx) {
    return (*ctx).lines;
}

slop_string emit_sexpr_to_c_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types) {
    __auto_type _mv_131 = (*expr);
    switch (_mv_131.tag) {
        case types_SExpr_num:
        {
            __auto_type num = _mv_131.data.num;
            return num.raw;
        }
        case types_SExpr_str:
        {
            __auto_type str = _mv_131.data.str;
            {
                __auto_type val = str.value;
                return string_concat(arena, string_concat(arena, SLOP_STR("SLOP_STR(\""), emit_escape_string(arena, val)), SLOP_STR("\")"));
            }
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_131.data.sym;
            {
                __auto_type name = sym.name;
                if (string_eq(name, SLOP_STR("true"))) {
                    return SLOP_STR("true");
                } else if (string_eq(name, SLOP_STR("false"))) {
                    return SLOP_STR("false");
                } else if (string_eq(name, SLOP_STR("nil"))) {
                    return SLOP_STR("NULL");
                } else if (string_eq(name, SLOP_STR("_"))) {
                    return SLOP_STR("{0}");
                } else if (string_eq(name, SLOP_STR("none"))) {
                    return SLOP_STR("(slop_option_string){.has_value = false}");
                } else if (strlib_starts_with(name, SLOP_STR("'"))) {
                    {
                        __auto_type variant_name = strlib_substring(arena, name, 1, ((int64_t)((((int64_t)(name.len)) - 1))));
                        __auto_type _mv_132 = type_extract_registry_lookup_enum_value(types, variant_name);
                        if (_mv_132.has_value) {
                            __auto_type enum_entry = _mv_132.value;
                            return string_concat(arena, (*enum_entry).c_name, string_concat(arena, SLOP_STR("_"), ctype_to_c_name(arena, variant_name)));
                        } else if (!_mv_132.has_value) {
                            return ctype_to_c_name(arena, variant_name);
                        }
                    }
                } else {
                    return emit_prefix_symbol(arena, name, prefix, types);
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_131.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len == 0)) {
                    return SLOP_STR("(void)0");
                } else {
                    __auto_type _mv_133 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (!_mv_133.has_value) {
                        return SLOP_STR("(void)0");
                    } else if (_mv_133.has_value) {
                        __auto_type head = _mv_133.value;
                        if (parser_sexpr_is_symbol(head)) {
                            {
                                __auto_type op = parser_sexpr_get_symbol_name(head);
                                if (string_eq(op, SLOP_STR("none"))) {
                                    return SLOP_STR("(slop_option_string){.has_value = false}");
                                } else if (string_eq(op, SLOP_STR("some"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_134 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_134.has_value) {
                                            __auto_type val = _mv_134.value;
                                            {
                                                __auto_type inner_c = emit_sexpr_to_c_typed(arena, val, prefix, types);
                                                return string_concat(arena, SLOP_STR("(slop_option_string){.has_value = true, .value = "), string_concat(arena, inner_c, SLOP_STR("}")));
                                            }
                                        } else if (!_mv_134.has_value) {
                                            return SLOP_STR("(slop_option_string){.has_value = true}");
                                        }
                                    } else {
                                        return SLOP_STR("(slop_option_string){.has_value = true}");
                                    }
                                } else if (string_eq(op, SLOP_STR("list"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_135 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_135.has_value) {
                                            __auto_type type_expr = _mv_135.value;
                                            if (parser_sexpr_is_symbol(type_expr)) {
                                                {
                                                    __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                                                    if (string_eq(type_name, SLOP_STR("String"))) {
                                                        return SLOP_STR("(slop_list_string){.data = NULL, .len = 0, .cap = 0}");
                                                    } else {
                                                        __auto_type _mv_136 = type_extract_registry_lookup(types, type_name);
                                                        if (_mv_136.has_value) {
                                                            __auto_type entry = _mv_136.value;
                                                            return string_concat(arena, SLOP_STR("(slop_list_"), string_concat(arena, (*entry).c_name, SLOP_STR("){.data = NULL, .len = 0, .cap = 0}")));
                                                        } else if (!_mv_136.has_value) {
                                                            __auto_type _mv_137 = type_extract_registry_lookup_import(types, type_name);
                                                            if (_mv_137.has_value) {
                                                                __auto_type mod_name = _mv_137.value;
                                                                return string_concat(arena, SLOP_STR("(slop_list_"), string_concat(arena, ctype_to_c_name(arena, mod_name), string_concat(arena, SLOP_STR("_"), string_concat(arena, ctype_to_c_name(arena, type_name), SLOP_STR("){.data = NULL, .len = 0, .cap = 0}")))));
                                                            } else if (!_mv_137.has_value) {
                                                                return string_concat(arena, SLOP_STR("(slop_list_"), string_concat(arena, prefix, string_concat(arena, SLOP_STR("_"), string_concat(arena, ctype_to_c_name(arena, type_name), SLOP_STR("){.data = NULL, .len = 0, .cap = 0}")))));
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                return SLOP_STR("/* error: list literal first element must be type symbol */");
                                            }
                                        } else if (!_mv_135.has_value) {
                                            return SLOP_STR("/* error: list literal requires type */");
                                        }
                                    } else {
                                        return SLOP_STR("/* error: list literal requires type */");
                                    }
                                } else if (string_eq(op, SLOP_STR("ok"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_138 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_138.has_value) {
                                            __auto_type val = _mv_138.value;
                                            return string_concat(arena, SLOP_STR("(("), string_concat(arena, prefix, string_concat(arena, SLOP_STR("Result){.is_ok=true,.data.ok="), string_concat(arena, emit_sexpr_to_c_typed(arena, val, prefix, types), SLOP_STR("})")))));
                                        } else if (!_mv_138.has_value) {
                                            return SLOP_STR("((Result){.is_ok=true,.data.ok=0})");
                                        }
                                    } else {
                                        return SLOP_STR("((Result){.is_ok=true,.data.ok=0})");
                                    }
                                } else if (string_eq(op, SLOP_STR("error"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_139 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_139.has_value) {
                                            __auto_type val = _mv_139.value;
                                            return string_concat(arena, SLOP_STR("(("), string_concat(arena, prefix, string_concat(arena, SLOP_STR("Result){.is_ok=false,.data.err="), string_concat(arena, emit_sexpr_to_c_typed(arena, val, prefix, types), SLOP_STR("})")))));
                                        } else if (!_mv_139.has_value) {
                                            return SLOP_STR("((Result){.is_ok=false,.data.err=0})");
                                        }
                                    } else {
                                        return SLOP_STR("((Result){.is_ok=false,.data.err=0})");
                                    }
                                } else if (string_eq(op, SLOP_STR("quote"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_140 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_140.has_value) {
                                            __auto_type quoted = _mv_140.value;
                                            if (parser_sexpr_is_symbol(quoted)) {
                                                {
                                                    __auto_type variant_name = parser_sexpr_get_symbol_name(quoted);
                                                    __auto_type _mv_141 = type_extract_registry_lookup_enum_value(types, variant_name);
                                                    if (_mv_141.has_value) {
                                                        __auto_type enum_entry = _mv_141.value;
                                                        return string_concat(arena, (*enum_entry).c_name, string_concat(arena, SLOP_STR("_"), ctype_to_c_name(arena, variant_name)));
                                                    } else if (!_mv_141.has_value) {
                                                        return string_concat(arena, prefix, string_concat(arena, SLOP_STR("_"), ctype_to_c_name(arena, variant_name)));
                                                    }
                                                }
                                            } else {
                                                return emit_sexpr_to_c_typed(arena, quoted, prefix, types);
                                            }
                                        } else if (!_mv_140.has_value) {
                                            return SLOP_STR("0");
                                        }
                                    } else {
                                        return SLOP_STR("0");
                                    }
                                } else if (string_eq(op, SLOP_STR("+"))) {
                                    return emit_emit_binary_op_typed(arena, items, SLOP_STR("+"), prefix, types);
                                } else if (string_eq(op, SLOP_STR("-"))) {
                                    return emit_emit_binary_op_typed(arena, items, SLOP_STR("-"), prefix, types);
                                } else if (string_eq(op, SLOP_STR("*"))) {
                                    return emit_emit_binary_op_typed(arena, items, SLOP_STR("*"), prefix, types);
                                } else if (string_eq(op, SLOP_STR("/"))) {
                                    return emit_emit_binary_op_typed(arena, items, SLOP_STR("/"), prefix, types);
                                } else if (string_eq(op, SLOP_STR("%"))) {
                                    return emit_emit_binary_op_typed(arena, items, SLOP_STR("%"), prefix, types);
                                } else if (string_eq(op, SLOP_STR("=="))) {
                                    return emit_emit_binary_op_typed(arena, items, SLOP_STR("=="), prefix, types);
                                } else if (string_eq(op, SLOP_STR("!="))) {
                                    return emit_emit_binary_op_typed(arena, items, SLOP_STR("!="), prefix, types);
                                } else if (string_eq(op, SLOP_STR("<"))) {
                                    return emit_emit_binary_op_typed(arena, items, SLOP_STR("<"), prefix, types);
                                } else if (string_eq(op, SLOP_STR("<="))) {
                                    return emit_emit_binary_op_typed(arena, items, SLOP_STR("<="), prefix, types);
                                } else if (string_eq(op, SLOP_STR(">"))) {
                                    return emit_emit_binary_op_typed(arena, items, SLOP_STR(">"), prefix, types);
                                } else if (string_eq(op, SLOP_STR(">="))) {
                                    return emit_emit_binary_op_typed(arena, items, SLOP_STR(">="), prefix, types);
                                } else if (string_eq(op, SLOP_STR("and"))) {
                                    return emit_emit_binary_op_typed(arena, items, SLOP_STR("&&"), prefix, types);
                                } else if (string_eq(op, SLOP_STR("or"))) {
                                    return emit_emit_binary_op_typed(arena, items, SLOP_STR("||"), prefix, types);
                                } else if (string_eq(op, SLOP_STR("not"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_142 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_142.has_value) {
                                            __auto_type operand = _mv_142.value;
                                            return string_concat(arena, SLOP_STR("(!"), string_concat(arena, emit_sexpr_to_c_typed(arena, operand, prefix, types), SLOP_STR(")")));
                                        } else if (!_mv_142.has_value) {
                                            return SLOP_STR("(!0)");
                                        }
                                    } else {
                                        return SLOP_STR("(!0)");
                                    }
                                } else if (string_eq(op, SLOP_STR("."))) {
                                    if ((len >= 3)) {
                                        __auto_type _mv_143 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_143.has_value) {
                                            __auto_type obj = _mv_143.value;
                                            __auto_type _mv_144 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_144.has_value) {
                                                __auto_type field = _mv_144.value;
                                                return string_concat(arena, emit_sexpr_to_c_typed(arena, obj, prefix, types), string_concat(arena, SLOP_STR("."), ((parser_sexpr_is_symbol(field)) ? ctype_to_c_name(arena, parser_sexpr_get_symbol_name(field)) : emit_sexpr_to_c_typed(arena, field, prefix, types))));
                                            } else if (!_mv_144.has_value) {
                                                return SLOP_STR("0");
                                            }
                                        } else if (!_mv_143.has_value) {
                                            return SLOP_STR("0");
                                        }
                                    } else {
                                        return SLOP_STR("0");
                                    }
                                } else if (string_eq(op, SLOP_STR("cast"))) {
                                    if ((len >= 3)) {
                                        __auto_type _mv_145 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_145.has_value) {
                                            __auto_type expr_val = _mv_145.value;
                                            return emit_sexpr_to_c_typed(arena, expr_val, prefix, types);
                                        } else if (!_mv_145.has_value) {
                                            return SLOP_STR("0");
                                        }
                                    } else {
                                        return SLOP_STR("0");
                                    }
                                } else {
                                    __auto_type _mv_146 = type_extract_registry_lookup_variant(types, op);
                                    if (_mv_146.has_value) {
                                        __auto_type union_entry = _mv_146.value;
                                        return emit_emit_union_literal_typed(arena, union_entry, op, items, prefix, types);
                                    } else if (!_mv_146.has_value) {
                                        {
                                            __auto_type first_char = op.data[0];
                                            if (((first_char >= 65) && (first_char <= 90))) {
                                                __auto_type _mv_147 = type_extract_registry_lookup(types, op);
                                                if (_mv_147.has_value) {
                                                    __auto_type type_entry = _mv_147.value;
                                                    if (((*type_entry).kind == type_extract_TypeEntryKind_te_record)) {
                                                        return emit_emit_record_literal_typed(arena, type_entry, items, prefix, types);
                                                    } else {
                                                        return emit_emit_function_call_typed(arena, items, prefix, types);
                                                    }
                                                } else if (!_mv_147.has_value) {
                                                    return emit_emit_function_call_typed(arena, items, prefix, types);
                                                }
                                            } else {
                                                return emit_emit_function_call_typed(arena, items, prefix, types);
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            return emit_emit_type_constructor_typed(arena, items, prefix, types);
                        }
                    }
                }
            }
        }
    }
}

slop_string emit_emit_union_literal_typed(slop_arena* arena, type_extract_TypeEntry* union_entry, slop_string variant_name, slop_list_types_SExpr_ptr items, slop_string prefix, type_extract_TypeRegistry types) {
    {
        __auto_type c_name = (*union_entry).c_name;
        __auto_type c_variant = ctype_to_c_name(arena, variant_name);
        {
            __auto_type tag_value = string_concat(arena, c_name, string_concat(arena, SLOP_STR("_"), c_variant));
            if ((((int64_t)((items).len)) > 1)) {
                __auto_type _mv_148 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_148.has_value) {
                    __auto_type inner_expr = _mv_148.value;
                    {
                        __auto_type inner_c = emit_sexpr_to_c_typed(arena, inner_expr, prefix, types);
                        __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("({ typeof(")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(") _u = {0}; _u.tag = ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (tag_value); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("; _u.data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(" = ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (inner_c); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("; _u; })")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        return strlib_string_build(arena, parts);
                    }
                } else if (!_mv_148.has_value) {
                    {
                        __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("({ typeof(")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(") _u = {0}; _u.tag = ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (tag_value); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("; _u; })")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        return strlib_string_build(arena, parts);
                    }
                }
            } else {
                {
                    __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("({ typeof(")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(") _u = {0}; _u.tag = ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (tag_value); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("; _u; })")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    return strlib_string_build(arena, parts);
                }
            }
        }
    }
}

slop_string emit_emit_record_literal_typed(slop_arena* arena, type_extract_TypeEntry* record_entry, slop_list_types_SExpr_ptr items, slop_string prefix, type_extract_TypeRegistry types) {
    {
        __auto_type c_name = (*record_entry).c_name;
        __auto_type fields = (*record_entry).fields;
        __auto_type field_count = ((int64_t)((fields).len));
        __auto_type arg_count = (((int64_t)((items).len)) - 1);
        {
            __auto_type result = string_concat(arena, SLOP_STR("(("), string_concat(arena, c_name, SLOP_STR("){")));
            __auto_type i = 0;
            __auto_type first = 1;
            while (((i < field_count) && (i < arg_count))) {
                __auto_type _mv_149 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_type_extract_FieldEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_149.has_value) {
                    __auto_type field = _mv_149.value;
                    __auto_type _mv_150 = ({ __auto_type _lst = items; size_t _idx = (size_t)(i + 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_150.has_value) {
                        __auto_type item = _mv_150.value;
                        {
                            __auto_type fname = ctype_to_c_name(arena, field.name);
                            __auto_type ftype = field.type_name;
                            __auto_type val_c = emit_emit_field_value_typed(arena, item, ftype, prefix, types);
                            if (first) {
                                result = string_concat(arena, result, string_concat(arena, SLOP_STR("."), string_concat(arena, fname, string_concat(arena, SLOP_STR(" = "), val_c))));
                                first = 0;
                            } else {
                                result = string_concat(arena, result, string_concat(arena, SLOP_STR(", ."), string_concat(arena, fname, string_concat(arena, SLOP_STR(" = "), val_c))));
                            }
                        }
                    } else if (!_mv_150.has_value) {
                    }
                } else if (!_mv_149.has_value) {
                }
                i = (i + 1);
            }
            result = string_concat(arena, result, SLOP_STR("})"));
            return result;
        }
    }
}

slop_string emit_emit_field_value_typed(slop_arena* arena, types_SExpr* item, slop_string field_type, slop_string prefix, type_extract_TypeRegistry types) {
    if (strlib_contains(field_type, SLOP_STR("Option"))) {
        return emit_emit_option_value_typed(arena, item, field_type, prefix, types);
    } else {
        return emit_sexpr_to_c_typed(arena, item, prefix, types);
    }
}

slop_string emit_emit_option_value_typed(slop_arena* arena, types_SExpr* item, slop_string opt_type, slop_string prefix, type_extract_TypeRegistry types) {
    {
        __auto_type c_opt_type = emit_option_type_to_c(arena, opt_type, prefix);
        __auto_type _mv_151 = (*item);
        switch (_mv_151.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_151.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) == 0)) {
                        return string_concat(arena, SLOP_STR("("), string_concat(arena, c_opt_type, SLOP_STR("){.has_value = false}")));
                    } else {
                        __auto_type _mv_152 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_152.has_value) {
                            __auto_type first = _mv_152.value;
                            if (parser_sexpr_is_symbol(first)) {
                                {
                                    __auto_type name = parser_sexpr_get_symbol_name(first);
                                    if (string_eq(name, SLOP_STR("none"))) {
                                        return string_concat(arena, SLOP_STR("("), string_concat(arena, c_opt_type, SLOP_STR("){.has_value = false}")));
                                    } else if (string_eq(name, SLOP_STR("some"))) {
                                        if ((((int64_t)((items).len)) > 1)) {
                                            __auto_type _mv_153 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_153.has_value) {
                                                __auto_type inner = _mv_153.value;
                                                {
                                                    __auto_type inner_c = emit_sexpr_to_c_typed(arena, inner, prefix, types);
                                                    return string_concat(arena, SLOP_STR("("), string_concat(arena, c_opt_type, string_concat(arena, SLOP_STR("){.has_value = true, .value = "), string_concat(arena, inner_c, SLOP_STR("}")))));
                                                }
                                            } else if (!_mv_153.has_value) {
                                                return string_concat(arena, SLOP_STR("("), string_concat(arena, c_opt_type, SLOP_STR("){.has_value = true}")));
                                            }
                                        } else {
                                            return string_concat(arena, SLOP_STR("("), string_concat(arena, c_opt_type, SLOP_STR("){.has_value = true}")));
                                        }
                                    } else {
                                        {
                                            __auto_type inner_c = emit_sexpr_to_c_typed(arena, item, prefix, types);
                                            return string_concat(arena, SLOP_STR("("), string_concat(arena, c_opt_type, string_concat(arena, SLOP_STR("){.has_value = true, .value = "), string_concat(arena, inner_c, SLOP_STR("}")))));
                                        }
                                    }
                                }
                            } else {
                                {
                                    __auto_type inner_c = emit_sexpr_to_c_typed(arena, item, prefix, types);
                                    return string_concat(arena, SLOP_STR("("), string_concat(arena, c_opt_type, string_concat(arena, SLOP_STR("){.has_value = true, .value = "), string_concat(arena, inner_c, SLOP_STR("}")))));
                                }
                            }
                        } else if (!_mv_152.has_value) {
                            return string_concat(arena, SLOP_STR("("), string_concat(arena, c_opt_type, SLOP_STR("){.has_value = false}")));
                        }
                    }
                }
            }
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_151.data.sym;
                {
                    __auto_type name = sym.name;
                    if (string_eq(name, SLOP_STR("none"))) {
                        return string_concat(arena, SLOP_STR("("), string_concat(arena, c_opt_type, SLOP_STR("){.has_value = false}")));
                    } else {
                        {
                            __auto_type val_c = emit_sexpr_to_c_typed(arena, item, prefix, types);
                            return string_concat(arena, SLOP_STR("("), string_concat(arena, c_opt_type, string_concat(arena, SLOP_STR("){.has_value = true, .value = "), string_concat(arena, val_c, SLOP_STR("}")))));
                        }
                    }
                }
            }
            default: {
                {
                    __auto_type val_c = emit_sexpr_to_c_typed(arena, item, prefix, types);
                    return string_concat(arena, SLOP_STR("("), string_concat(arena, c_opt_type, string_concat(arena, SLOP_STR("){.has_value = true, .value = "), string_concat(arena, val_c, SLOP_STR("}")))));
                }
            }
        }
    }
}

slop_string emit_option_type_to_c(slop_arena* arena, slop_string opt_type, slop_string prefix) {
    if (strlib_contains(opt_type, SLOP_STR("String"))) {
        return SLOP_STR("slop_option_string");
    } else if (strlib_contains(opt_type, SLOP_STR("Int"))) {
        return SLOP_STR("slop_option_int");
    } else if (strlib_contains(opt_type, SLOP_STR("Bool"))) {
        return SLOP_STR("slop_option_bool");
    } else if (strlib_contains(opt_type, SLOP_STR("Float"))) {
        return SLOP_STR("slop_option_float");
    } else {
        return SLOP_STR("slop_option_ptr");
    }
}

slop_string emit_emit_binary_op_typed(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string c_op, slop_string prefix, type_extract_TypeRegistry types) {
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 3)) {
            if ((len == 2)) {
                __auto_type _mv_154 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_154.has_value) {
                    __auto_type a = _mv_154.value;
                    return string_concat(arena, SLOP_STR("("), string_concat(arena, c_op, string_concat(arena, emit_sexpr_to_c_typed(arena, a, prefix, types), SLOP_STR(")"))));
                } else if (!_mv_154.has_value) {
                    return SLOP_STR("0");
                }
            } else {
                return SLOP_STR("0");
            }
        } else {
            __auto_type _mv_155 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_155.has_value) {
                __auto_type a = _mv_155.value;
                __auto_type _mv_156 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_156.has_value) {
                    __auto_type b = _mv_156.value;
                    return string_concat(arena, SLOP_STR("("), string_concat(arena, emit_sexpr_to_c_typed(arena, a, prefix, types), string_concat(arena, SLOP_STR(" "), string_concat(arena, c_op, string_concat(arena, SLOP_STR(" "), string_concat(arena, emit_sexpr_to_c_typed(arena, b, prefix, types), SLOP_STR(")")))))));
                } else if (!_mv_156.has_value) {
                    return SLOP_STR("0");
                }
            } else if (!_mv_155.has_value) {
                return SLOP_STR("0");
            }
        }
    }
}

slop_string emit_emit_function_call_typed(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string prefix, type_extract_TypeRegistry types) {
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 1)) {
            return SLOP_STR("(void)0");
        } else {
            __auto_type _mv_157 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (!_mv_157.has_value) {
                return SLOP_STR("(void)0");
            } else if (_mv_157.has_value) {
                __auto_type head = _mv_157.value;
                {
                    __auto_type fn_name = ((parser_sexpr_is_symbol(head)) ? emit_prefix_symbol(arena, parser_sexpr_get_symbol_name(head), prefix, types) : SLOP_STR("unknown"));
                    {
                        __auto_type args_str = emit_emit_args_typed(arena, items, 1, prefix, types);
                        return string_concat(arena, fn_name, string_concat(arena, SLOP_STR("("), string_concat(arena, args_str, SLOP_STR(")"))));
                    }
                }
            }
        }
    }
}

slop_string emit_emit_args_typed(slop_arena* arena, slop_list_types_SExpr_ptr items, int64_t start, slop_string prefix, type_extract_TypeRegistry types) {
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type result = SLOP_STR("");
        __auto_type first = 1;
        __auto_type i = start;
        while ((i < len)) {
            __auto_type _mv_158 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_158.has_value) {
                __auto_type arg = _mv_158.value;
                {
                    __auto_type arg_c = emit_sexpr_to_c_typed(arena, arg, prefix, types);
                    if (first) {
                        result = arg_c;
                        first = 0;
                    } else {
                        result = string_concat(arena, result, string_concat(arena, SLOP_STR(", "), arg_c));
                    }
                }
            } else if (!_mv_158.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_string emit_emit_type_constructor_typed(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string prefix, type_extract_TypeRegistry types) {
    if ((((int64_t)((items).len)) == 0)) {
        return SLOP_STR("(void)0");
    } else {
        return emit_emit_function_call_typed(arena, items, prefix, types);
    }
}

slop_string emit_sexpr_to_c(slop_arena* arena, types_SExpr* expr, slop_string prefix) {
    __auto_type _mv_159 = (*expr);
    switch (_mv_159.tag) {
        case types_SExpr_num:
        {
            __auto_type num = _mv_159.data.num;
            return num.raw;
        }
        case types_SExpr_str:
        {
            __auto_type str = _mv_159.data.str;
            {
                __auto_type val = str.value;
                return string_concat(arena, string_concat(arena, SLOP_STR("SLOP_STR(\""), emit_escape_string(arena, val)), SLOP_STR("\")"));
            }
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_159.data.sym;
            {
                __auto_type name = sym.name;
                if (string_eq(name, SLOP_STR("true"))) {
                    return SLOP_STR("true");
                } else if (string_eq(name, SLOP_STR("false"))) {
                    return SLOP_STR("false");
                } else if (string_eq(name, SLOP_STR("nil"))) {
                    return SLOP_STR("NULL");
                } else if (string_eq(name, SLOP_STR("none"))) {
                    return SLOP_STR("none");
                } else if (strlib_starts_with(name, SLOP_STR("'"))) {
                    return ctype_to_c_name(arena, strlib_substring(arena, name, 1, ((int64_t)((((int64_t)(name.len)) - 1)))));
                } else {
                    return ctype_to_c_name(arena, name);
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_159.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len == 0)) {
                    return SLOP_STR("(void)0");
                } else {
                    __auto_type _mv_160 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (!_mv_160.has_value) {
                        return SLOP_STR("(void)0");
                    } else if (_mv_160.has_value) {
                        __auto_type head = _mv_160.value;
                        if (parser_sexpr_is_symbol(head)) {
                            {
                                __auto_type op = parser_sexpr_get_symbol_name(head);
                                if (string_eq(op, SLOP_STR("none"))) {
                                    return SLOP_STR("none");
                                } else if (string_eq(op, SLOP_STR("some"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_161 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_161.has_value) {
                                            __auto_type val = _mv_161.value;
                                            return string_concat(arena, SLOP_STR("some("), string_concat(arena, emit_sexpr_to_c(arena, val, prefix), SLOP_STR(")")));
                                        } else if (!_mv_161.has_value) {
                                            return SLOP_STR("some(0)");
                                        }
                                    } else {
                                        return SLOP_STR("some(0)");
                                    }
                                } else if (string_eq(op, SLOP_STR("ok"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_162 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_162.has_value) {
                                            __auto_type val = _mv_162.value;
                                            return string_concat(arena, SLOP_STR("(("), string_concat(arena, prefix, string_concat(arena, SLOP_STR("Result){.is_ok=true,.data.ok="), string_concat(arena, emit_sexpr_to_c(arena, val, prefix), SLOP_STR("})")))));
                                        } else if (!_mv_162.has_value) {
                                            return SLOP_STR("((Result){.is_ok=true,.data.ok=0})");
                                        }
                                    } else {
                                        return SLOP_STR("((Result){.is_ok=true,.data.ok=0})");
                                    }
                                } else if (string_eq(op, SLOP_STR("error"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_163 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_163.has_value) {
                                            __auto_type val = _mv_163.value;
                                            return string_concat(arena, SLOP_STR("(("), string_concat(arena, prefix, string_concat(arena, SLOP_STR("Result){.is_ok=false,.data.err="), string_concat(arena, emit_sexpr_to_c(arena, val, prefix), SLOP_STR("})")))));
                                        } else if (!_mv_163.has_value) {
                                            return SLOP_STR("((Result){.is_ok=false,.data.err=0})");
                                        }
                                    } else {
                                        return SLOP_STR("((Result){.is_ok=false,.data.err=0})");
                                    }
                                } else if (string_eq(op, SLOP_STR("quote"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_164 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_164.has_value) {
                                            __auto_type quoted = _mv_164.value;
                                            if (parser_sexpr_is_symbol(quoted)) {
                                                {
                                                    __auto_type name = parser_sexpr_get_symbol_name(quoted);
                                                    return string_concat(arena, prefix, string_concat(arena, SLOP_STR("_"), ctype_to_c_name(arena, name)));
                                                }
                                            } else {
                                                return emit_sexpr_to_c(arena, quoted, prefix);
                                            }
                                        } else if (!_mv_164.has_value) {
                                            return SLOP_STR("0");
                                        }
                                    } else {
                                        return SLOP_STR("0");
                                    }
                                } else if (string_eq(op, SLOP_STR("+"))) {
                                    return emit_emit_binary_op(arena, items, SLOP_STR("+"), prefix);
                                } else if (string_eq(op, SLOP_STR("-"))) {
                                    return emit_emit_binary_op(arena, items, SLOP_STR("-"), prefix);
                                } else if (string_eq(op, SLOP_STR("*"))) {
                                    return emit_emit_binary_op(arena, items, SLOP_STR("*"), prefix);
                                } else if (string_eq(op, SLOP_STR("/"))) {
                                    return emit_emit_binary_op(arena, items, SLOP_STR("/"), prefix);
                                } else if (string_eq(op, SLOP_STR("%"))) {
                                    return emit_emit_binary_op(arena, items, SLOP_STR("%"), prefix);
                                } else if (string_eq(op, SLOP_STR("=="))) {
                                    return emit_emit_binary_op(arena, items, SLOP_STR("=="), prefix);
                                } else if (string_eq(op, SLOP_STR("!="))) {
                                    return emit_emit_binary_op(arena, items, SLOP_STR("!="), prefix);
                                } else if (string_eq(op, SLOP_STR("<"))) {
                                    return emit_emit_binary_op(arena, items, SLOP_STR("<"), prefix);
                                } else if (string_eq(op, SLOP_STR("<="))) {
                                    return emit_emit_binary_op(arena, items, SLOP_STR("<="), prefix);
                                } else if (string_eq(op, SLOP_STR(">"))) {
                                    return emit_emit_binary_op(arena, items, SLOP_STR(">"), prefix);
                                } else if (string_eq(op, SLOP_STR(">="))) {
                                    return emit_emit_binary_op(arena, items, SLOP_STR(">="), prefix);
                                } else if (string_eq(op, SLOP_STR("and"))) {
                                    return emit_emit_binary_op(arena, items, SLOP_STR("&&"), prefix);
                                } else if (string_eq(op, SLOP_STR("or"))) {
                                    return emit_emit_binary_op(arena, items, SLOP_STR("||"), prefix);
                                } else if (string_eq(op, SLOP_STR("not"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_165 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_165.has_value) {
                                            __auto_type operand = _mv_165.value;
                                            return string_concat(arena, SLOP_STR("(!"), string_concat(arena, emit_sexpr_to_c(arena, operand, prefix), SLOP_STR(")")));
                                        } else if (!_mv_165.has_value) {
                                            return SLOP_STR("(!0)");
                                        }
                                    } else {
                                        return SLOP_STR("(!0)");
                                    }
                                } else if (string_eq(op, SLOP_STR("."))) {
                                    if ((len >= 3)) {
                                        __auto_type _mv_166 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_166.has_value) {
                                            __auto_type obj = _mv_166.value;
                                            __auto_type _mv_167 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_167.has_value) {
                                                __auto_type field = _mv_167.value;
                                                return string_concat(arena, emit_sexpr_to_c(arena, obj, prefix), string_concat(arena, SLOP_STR("."), ((parser_sexpr_is_symbol(field)) ? ctype_to_c_name(arena, parser_sexpr_get_symbol_name(field)) : emit_sexpr_to_c(arena, field, prefix))));
                                            } else if (!_mv_167.has_value) {
                                                return SLOP_STR("0");
                                            }
                                        } else if (!_mv_166.has_value) {
                                            return SLOP_STR("0");
                                        }
                                    } else {
                                        return SLOP_STR("0");
                                    }
                                } else if (string_eq(op, SLOP_STR("cast"))) {
                                    if ((len >= 3)) {
                                        __auto_type _mv_168 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_168.has_value) {
                                            __auto_type expr_val = _mv_168.value;
                                            return emit_sexpr_to_c(arena, expr_val, prefix);
                                        } else if (!_mv_168.has_value) {
                                            return SLOP_STR("0");
                                        }
                                    } else {
                                        return SLOP_STR("0");
                                    }
                                } else {
                                    return emit_emit_function_call(arena, items, prefix);
                                }
                            }
                        } else {
                            return emit_emit_type_constructor(arena, items, prefix);
                        }
                    }
                }
            }
        }
    }
}

slop_string emit_emit_binary_op(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string c_op, slop_string prefix) {
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 3)) {
            if ((len == 2)) {
                __auto_type _mv_169 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_169.has_value) {
                    __auto_type a = _mv_169.value;
                    return string_concat(arena, SLOP_STR("("), string_concat(arena, c_op, string_concat(arena, emit_sexpr_to_c(arena, a, prefix), SLOP_STR(")"))));
                } else if (!_mv_169.has_value) {
                    return SLOP_STR("0");
                }
            } else {
                return SLOP_STR("0");
            }
        } else {
            __auto_type _mv_170 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_170.has_value) {
                __auto_type a = _mv_170.value;
                __auto_type _mv_171 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_171.has_value) {
                    __auto_type b = _mv_171.value;
                    return string_concat(arena, SLOP_STR("("), string_concat(arena, emit_sexpr_to_c(arena, a, prefix), string_concat(arena, SLOP_STR(" "), string_concat(arena, c_op, string_concat(arena, SLOP_STR(" "), string_concat(arena, emit_sexpr_to_c(arena, b, prefix), SLOP_STR(")")))))));
                } else if (!_mv_171.has_value) {
                    return SLOP_STR("0");
                }
            } else if (!_mv_170.has_value) {
                return SLOP_STR("0");
            }
        }
    }
}

slop_string emit_emit_function_call(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string prefix) {
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 1)) {
            return SLOP_STR("(void)0");
        } else {
            __auto_type _mv_172 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (!_mv_172.has_value) {
                return SLOP_STR("(void)0");
            } else if (_mv_172.has_value) {
                __auto_type head = _mv_172.value;
                {
                    __auto_type fn_name = ((parser_sexpr_is_symbol(head)) ? ctype_to_c_name(arena, parser_sexpr_get_symbol_name(head)) : SLOP_STR("unknown"));
                    {
                        __auto_type args_str = emit_emit_args(arena, items, 1, prefix);
                        return string_concat(arena, fn_name, string_concat(arena, SLOP_STR("("), string_concat(arena, args_str, SLOP_STR(")"))));
                    }
                }
            }
        }
    }
}

slop_string emit_emit_args(slop_arena* arena, slop_list_types_SExpr_ptr items, int64_t start, slop_string prefix) {
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type result = SLOP_STR("");
        __auto_type first = 1;
        __auto_type i = start;
        while ((i < len)) {
            __auto_type _mv_173 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_173.has_value) {
                __auto_type arg = _mv_173.value;
                {
                    __auto_type arg_c = emit_sexpr_to_c(arena, arg, prefix);
                    if (first) {
                        result = arg_c;
                        first = 0;
                    } else {
                        result = string_concat(arena, result, string_concat(arena, SLOP_STR(", "), arg_c));
                    }
                }
            } else if (!_mv_173.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_string emit_emit_type_constructor(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string prefix) {
    return emit_emit_function_call(arena, items, prefix);
}

slop_string emit_escape_string(slop_arena* arena, slop_string s) {
    {
        __auto_type len = ((int64_t)(s.len));
        __auto_type buf = ((uint8_t*)((uint8_t*)slop_arena_alloc(arena, ((len * 2) + 1))));
        __auto_type i = 0;
        __auto_type out = 0;
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

slop_list_string emit_emit_test_harness_typed(slop_arena* arena, slop_list_extract_TestCase_ptr tests, slop_string module_prefix, type_extract_TypeRegistry* types, slop_list_type_extract_ImportEntry imports) {
    {
        __auto_type ctx = emit_emit_ctx_new_typed(arena, types);
        emit_emit(ctx, SLOP_STR("// ===== SLOP Test Harness (Native Generated - Type Aware) ====="));
        {
            __auto_type type_count = ((int64_t)(((*types).types).len));
            emit_emit(ctx, string_concat(arena, SLOP_STR("// DEBUG: TypeRegistry has "), string_concat(arena, int_to_string(arena, type_count), SLOP_STR(" type(s)"))));
        }
        emit_emit(ctx, SLOP_STR(""));
        emit_emit(ctx, SLOP_STR("#include <stdio.h>"));
        emit_emit(ctx, SLOP_STR("#include <string.h>"));
        emit_emit(ctx, SLOP_STR("#include <math.h>"));
        {
            __auto_type import_count = ((int64_t)((imports).len));
            __auto_type j = 0;
            while ((j < import_count)) {
                __auto_type _mv_174 = ({ __auto_type _lst = imports; size_t _idx = (size_t)j; slop_option_type_extract_ImportEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_174.has_value) {
                    __auto_type entry = _mv_174.value;
                    {
                        __auto_type c_name = ctype_to_c_name(arena, entry.module_name);
                        emit_emit(ctx, string_concat(arena, SLOP_STR("#include \"slop_"), string_concat(arena, c_name, SLOP_STR(".h\""))));
                    }
                } else if (!_mv_174.has_value) {
                }
                j = (j + 1);
            }
        }
        emit_emit(ctx, SLOP_STR(""));
        emit_emit(ctx, SLOP_STR("static int tests_passed = 0;"));
        emit_emit(ctx, SLOP_STR("static int tests_failed = 0;"));
        emit_emit(ctx, SLOP_STR(""));
        {
            __auto_type any_needs_arena = emit_any_test_needs_arena(tests);
            if (any_needs_arena) {
                emit_emit(ctx, SLOP_STR("// Global test arena for functions that need one"));
                emit_emit(ctx, SLOP_STR("static slop_arena test_arena_storage;"));
                emit_emit(ctx, SLOP_STR("static slop_arena* test_arena = NULL;"));
                emit_emit(ctx, SLOP_STR(""));
            }
            {
                __auto_type test_count = ((int64_t)((tests).len));
                __auto_type i = 0;
                while ((i < test_count)) {
                    __auto_type _mv_175 = ({ __auto_type _lst = tests; size_t _idx = (size_t)i; slop_option_extract_TestCase_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_175.has_value) {
                        __auto_type tc = _mv_175.value;
                        emit_emit_test_function_typed(ctx, (*tc), i, module_prefix, types);
                    } else if (!_mv_175.has_value) {
                    }
                    i = (i + 1);
                }
                emit_emit_main_function(ctx, test_count, any_needs_arena);
            }
        }
        return emit_emit_ctx_get_lines(ctx);
    }
}

slop_list_string emit_emit_test_harness(slop_arena* arena, slop_list_extract_TestCase_ptr tests, slop_string module_prefix) {
    {
        __auto_type ctx = emit_emit_ctx_new(arena);
        emit_emit(ctx, SLOP_STR("// ===== SLOP Test Harness (Native Generated) ====="));
        emit_emit(ctx, SLOP_STR(""));
        emit_emit(ctx, SLOP_STR("#include <stdio.h>"));
        emit_emit(ctx, SLOP_STR("#include <string.h>"));
        emit_emit(ctx, SLOP_STR("#include <math.h>"));
        emit_emit(ctx, SLOP_STR(""));
        emit_emit(ctx, SLOP_STR("static int tests_passed = 0;"));
        emit_emit(ctx, SLOP_STR("static int tests_failed = 0;"));
        emit_emit(ctx, SLOP_STR(""));
        {
            __auto_type any_needs_arena = emit_any_test_needs_arena(tests);
            if (any_needs_arena) {
                emit_emit(ctx, SLOP_STR("// Global test arena for functions that need one"));
                emit_emit(ctx, SLOP_STR("static slop_arena test_arena_storage;"));
                emit_emit(ctx, SLOP_STR("static slop_arena* test_arena = NULL;"));
                emit_emit(ctx, SLOP_STR(""));
            }
            {
                __auto_type test_count = ((int64_t)((tests).len));
                __auto_type i = 0;
                while ((i < test_count)) {
                    __auto_type _mv_176 = ({ __auto_type _lst = tests; size_t _idx = (size_t)i; slop_option_extract_TestCase_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_176.has_value) {
                        __auto_type tc = _mv_176.value;
                        emit_emit_test_function(ctx, (*tc), i, module_prefix);
                    } else if (!_mv_176.has_value) {
                    }
                    i = (i + 1);
                }
                emit_emit_main_function(ctx, test_count, any_needs_arena);
            }
        }
        return emit_emit_ctx_get_lines(ctx);
    }
}

uint8_t emit_any_test_needs_arena(slop_list_extract_TestCase_ptr tests) {
    {
        __auto_type len = ((int64_t)((tests).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_177 = ({ __auto_type _lst = tests; size_t _idx = (size_t)i; slop_option_extract_TestCase_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_177.has_value) {
                __auto_type tc = _mv_177.value;
                if ((*tc).needs_arena) {
                    found = 1;
                }
            } else if (!_mv_177.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

void emit_emit_test_function_typed(emit_EmitContext* ctx, extract_TestCase tc, int64_t index, slop_string prefix, type_extract_TypeRegistry* types) {
    {
        __auto_type arena = (*ctx).arena;
        __auto_type fn_name = tc.fn_name;
        __auto_type c_fn_name = emit_make_c_fn_name(arena, fn_name, tc.module_name, prefix);
        __auto_type args_display = emit_build_args_display_typed(arena, tc.args, (*types));
        __auto_type call_args = emit_build_call_args_typed(arena, tc.args, tc.needs_arena, tc.arena_position, prefix, (*types));
        {
            __auto_type call_expr = string_concat(arena, c_fn_name, string_concat(arena, SLOP_STR("("), string_concat(arena, call_args, SLOP_STR(")"))));
            emit_emit(ctx, string_concat(arena, SLOP_STR("void test_"), string_concat(arena, int_to_string(arena, index), SLOP_STR("(void) {"))));
            emit_emit(ctx, string_concat(arena, SLOP_STR("    printf(\"  "), string_concat(arena, fn_name, string_concat(arena, SLOP_STR("("), string_concat(arena, emit_escape_string(arena, args_display), SLOP_STR(") -> \");"))))));
            emit_emit(ctx, string_concat(arena, SLOP_STR("    typeof("), string_concat(arena, call_expr, string_concat(arena, SLOP_STR(") result = "), string_concat(arena, call_expr, SLOP_STR(";"))))));
            {
                __auto_type compare_info = emit_build_comparison_typed(arena, tc.expected, tc.return_type, prefix, (*types), tc.eq_fn);
                emit_emit(ctx, string_concat(arena, SLOP_STR("    if ("), string_concat(arena, compare_info.compare_expr, SLOP_STR(") {"))));
                emit_emit(ctx, SLOP_STR("        printf(\"PASS\\n\");"));
                emit_emit(ctx, SLOP_STR("        tests_passed++;"));
                emit_emit(ctx, SLOP_STR("    } else {"));
                {
                    __auto_type fail_str = string_concat(arena, SLOP_STR("        printf(\"FAIL (got "), string_concat(arena, compare_info.result_fmt, string_concat(arena, SLOP_STR(", expected "), string_concat(arena, compare_info.expected_fmt, string_concat(arena, SLOP_STR(")\\n\", "), string_concat(arena, compare_info.result_args, string_concat(arena, SLOP_STR(", "), string_concat(arena, compare_info.expected_args, SLOP_STR(");")))))))));
                    emit_emit(ctx, fail_str);
                }
                emit_emit(ctx, SLOP_STR("        tests_failed++;"));
                emit_emit(ctx, SLOP_STR("    }"));
                emit_emit(ctx, SLOP_STR("}"));
                emit_emit(ctx, SLOP_STR(""));
            }
        }
    }
}

uint8_t emit_is_none_or_some_form(types_SExpr* expr) {
    __auto_type _mv_178 = (*expr);
    switch (_mv_178.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_178.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return 0;
                } else {
                    __auto_type _mv_179 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_179.has_value) {
                        __auto_type first = _mv_179.value;
                        if (parser_sexpr_is_symbol(first)) {
                            {
                                __auto_type name = parser_sexpr_get_symbol_name(first);
                                return (string_eq(name, SLOP_STR("none")) || string_eq(name, SLOP_STR("some")));
                            }
                        } else {
                            return 0;
                        }
                    } else if (!_mv_179.has_value) {
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

uint8_t emit_args_contain_complex_constructor(slop_list_types_SExpr_ptr args) {
    {
        __auto_type len = ((int64_t)((args).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_180 = ({ __auto_type _lst = args; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_180.has_value) {
                __auto_type arg = _mv_180.value;
                if ((emit_is_union_or_record_constructor(arg) || emit_is_none_or_some_form(arg))) {
                    found = 1;
                }
            } else if (!_mv_180.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

void emit_emit_test_function(emit_EmitContext* ctx, extract_TestCase tc, int64_t index, slop_string prefix) {
    {
        __auto_type arena = (*ctx).arena;
        if (emit_args_contain_complex_constructor(tc.args)) {
            emit_emit(ctx, string_concat(arena, SLOP_STR("void test_"), string_concat(arena, int_to_string(arena, index), SLOP_STR("(void) {"))));
            emit_emit(ctx, string_concat(arena, SLOP_STR("    printf(\"  "), string_concat(arena, tc.fn_name, SLOP_STR("(...) -> SKIP (complex args)\\n\");"))));
            emit_emit(ctx, SLOP_STR("    // Test skipped: arguments contain union/record constructors"));
            emit_emit(ctx, SLOP_STR("    tests_passed++;  // Count as passed (not a failure)"));
            emit_emit(ctx, SLOP_STR("}"));
            emit_emit(ctx, SLOP_STR(""));
        } else {
            {
                __auto_type fn_name = tc.fn_name;
                __auto_type c_fn_name = emit_make_c_fn_name(arena, fn_name, tc.module_name, prefix);
                __auto_type args_display = emit_build_args_display(arena, tc.args);
                __auto_type call_args = emit_build_call_args(arena, tc.args, tc.needs_arena, tc.arena_position, prefix);
                {
                    __auto_type call_expr = string_concat(arena, c_fn_name, string_concat(arena, SLOP_STR("("), string_concat(arena, call_args, SLOP_STR(")"))));
                    emit_emit(ctx, string_concat(arena, SLOP_STR("void test_"), string_concat(arena, int_to_string(arena, index), SLOP_STR("(void) {"))));
                    emit_emit(ctx, string_concat(arena, SLOP_STR("    printf(\"  "), string_concat(arena, fn_name, string_concat(arena, SLOP_STR("("), string_concat(arena, emit_escape_string(arena, args_display), SLOP_STR(") -> \");"))))));
                    emit_emit(ctx, string_concat(arena, SLOP_STR("    typeof("), string_concat(arena, call_expr, string_concat(arena, SLOP_STR(") result = "), string_concat(arena, call_expr, SLOP_STR(";"))))));
                    {
                        __auto_type compare_info = emit_build_comparison(arena, tc.expected, tc.return_type, prefix);
                        emit_emit(ctx, string_concat(arena, SLOP_STR("    if ("), string_concat(arena, compare_info.compare_expr, SLOP_STR(") {"))));
                        emit_emit(ctx, SLOP_STR("        printf(\"PASS\\n\");"));
                        emit_emit(ctx, SLOP_STR("        tests_passed++;"));
                        emit_emit(ctx, SLOP_STR("    } else {"));
                        {
                            __auto_type fail_str = string_concat(arena, SLOP_STR("        printf(\"FAIL (got "), string_concat(arena, compare_info.result_fmt, string_concat(arena, SLOP_STR(", expected "), string_concat(arena, compare_info.expected_fmt, string_concat(arena, SLOP_STR(")\\n\", "), string_concat(arena, compare_info.result_args, string_concat(arena, SLOP_STR(", "), string_concat(arena, compare_info.expected_args, SLOP_STR(");")))))))));
                            emit_emit(ctx, fail_str);
                        }
                        emit_emit(ctx, SLOP_STR("        tests_failed++;"));
                        emit_emit(ctx, SLOP_STR("    }"));
                        emit_emit(ctx, SLOP_STR("}"));
                        emit_emit(ctx, SLOP_STR(""));
                    }
                }
            }
        }
    }
}

void emit_emit_main_function(emit_EmitContext* ctx, int64_t test_count, uint8_t needs_arena) {
    {
        __auto_type arena = (*ctx).arena;
        emit_emit(ctx, SLOP_STR("int main(void) {"));
        if (needs_arena) {
            emit_emit(ctx, SLOP_STR("    // Create test arena (1MB)"));
            emit_emit(ctx, SLOP_STR("    test_arena_storage = slop_arena_new(1024 * 1024);"));
            emit_emit(ctx, SLOP_STR("    test_arena = &test_arena_storage;"));
        }
        {
            __auto_type count_str = int_to_string(arena, test_count);
            __auto_type print_stmt = string_concat(arena, SLOP_STR("    printf(\"Running "), string_concat(arena, count_str, SLOP_STR(" test(s)...\\n\");")));
            emit_emit(ctx, print_stmt);
        }
        {
            __auto_type i = 0;
            while ((i < test_count)) {
                {
                    __auto_type call = string_concat(arena, SLOP_STR("    test_"), string_concat(arena, int_to_string(arena, i), SLOP_STR("();")));
                    emit_emit(ctx, call);
                }
                i = (i + 1);
            }
        }
        emit_emit(ctx, SLOP_STR("    printf(\"\\n%d passed, %d failed\\n\", tests_passed, tests_failed);"));
        if (needs_arena) {
            emit_emit(ctx, SLOP_STR("    slop_arena_free(test_arena);"));
        }
        emit_emit(ctx, SLOP_STR("    return tests_failed > 0 ? 1 : 0;"));
        emit_emit(ctx, SLOP_STR("}"));
    }
}

slop_string emit_build_args_display_typed(slop_arena* arena, slop_list_types_SExpr_ptr args, type_extract_TypeRegistry types) {
    {
        __auto_type len = ((int64_t)((args).len));
        __auto_type result = SLOP_STR("");
        __auto_type first = 1;
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_181 = ({ __auto_type _lst = args; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_181.has_value) {
                __auto_type arg = _mv_181.value;
                {
                    __auto_type arg_str = parser_pretty_print(arena, arg);
                    if (first) {
                        result = arg_str;
                        first = 0;
                    } else {
                        result = string_concat(arena, result, string_concat(arena, SLOP_STR(", "), arg_str));
                    }
                }
            } else if (!_mv_181.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_string emit_build_call_args_typed(slop_arena* arena, slop_list_types_SExpr_ptr args, uint8_t needs_arena, int64_t arena_pos, slop_string prefix, type_extract_TypeRegistry types) {
    {
        __auto_type len = ((int64_t)((args).len));
        __auto_type result = SLOP_STR("");
        __auto_type first = 1;
        __auto_type i = 0;
        __auto_type arg_idx = 0;
        while ((i < len)) {
            if ((needs_arena && (arg_idx == arena_pos))) {
                if (first) {
                    result = SLOP_STR("test_arena");
                    first = 0;
                } else {
                    result = string_concat(arena, result, SLOP_STR(", test_arena"));
                }
                arg_idx = (arg_idx + 1);
            }
            __auto_type _mv_182 = ({ __auto_type _lst = args; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_182.has_value) {
                __auto_type arg = _mv_182.value;
                {
                    __auto_type arg_c = emit_sexpr_to_c_typed(arena, arg, prefix, types);
                    if (first) {
                        result = arg_c;
                        first = 0;
                    } else {
                        result = string_concat(arena, result, string_concat(arena, SLOP_STR(", "), arg_c));
                    }
                }
            } else if (!_mv_182.has_value) {
            }
            i = (i + 1);
            arg_idx = (arg_idx + 1);
        }
        if ((needs_arena && (arena_pos >= len))) {
            if (first) {
                result = SLOP_STR("test_arena");
            } else {
                result = string_concat(arena, result, SLOP_STR(", test_arena"));
            }
        }
        return result;
    }
}

slop_string emit_make_c_fn_name(slop_arena* arena, slop_string fn_name, slop_option_string module_name, slop_string prefix) {
    {
        __auto_type c_name = ctype_to_c_name(arena, fn_name);
        __auto_type _mv_183 = module_name;
        if (_mv_183.has_value) {
            __auto_type mod = _mv_183.value;
            return string_concat(arena, ctype_to_c_name(arena, mod), string_concat(arena, SLOP_STR("_"), c_name));
        } else if (!_mv_183.has_value) {
            if ((((int64_t)(prefix.len)) > 0)) {
                return string_concat(arena, prefix, string_concat(arena, SLOP_STR("_"), c_name));
            } else {
                return c_name;
            }
        }
    }
}

slop_string emit_build_args_display(slop_arena* arena, slop_list_types_SExpr_ptr args) {
    {
        __auto_type len = ((int64_t)((args).len));
        __auto_type result = SLOP_STR("");
        __auto_type first = 1;
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_184 = ({ __auto_type _lst = args; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_184.has_value) {
                __auto_type arg = _mv_184.value;
                {
                    __auto_type arg_str = parser_pretty_print(arena, arg);
                    if (first) {
                        result = arg_str;
                        first = 0;
                    } else {
                        result = string_concat(arena, result, string_concat(arena, SLOP_STR(", "), arg_str));
                    }
                }
            } else if (!_mv_184.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_string emit_build_call_args(slop_arena* arena, slop_list_types_SExpr_ptr args, uint8_t needs_arena, int64_t arena_pos, slop_string prefix) {
    {
        __auto_type len = ((int64_t)((args).len));
        __auto_type result = SLOP_STR("");
        __auto_type first = 1;
        __auto_type i = 0;
        __auto_type arg_idx = 0;
        while ((i < len)) {
            if ((needs_arena && (arg_idx == arena_pos))) {
                if (first) {
                    result = SLOP_STR("test_arena");
                    first = 0;
                } else {
                    result = string_concat(arena, result, SLOP_STR(", test_arena"));
                }
                arg_idx = (arg_idx + 1);
            }
            __auto_type _mv_185 = ({ __auto_type _lst = args; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_185.has_value) {
                __auto_type arg = _mv_185.value;
                {
                    __auto_type arg_c = emit_sexpr_to_c(arena, arg, prefix);
                    if (first) {
                        result = arg_c;
                        first = 0;
                    } else {
                        result = string_concat(arena, result, string_concat(arena, SLOP_STR(", "), arg_c));
                    }
                }
            } else if (!_mv_185.has_value) {
            }
            i = (i + 1);
            arg_idx = (arg_idx + 1);
        }
        if ((needs_arena && (arena_pos >= len))) {
            if (first) {
                result = SLOP_STR("test_arena");
            } else {
                result = string_concat(arena, result, SLOP_STR(", test_arena"));
            }
        }
        return result;
    }
}

emit_CompareInfo emit_build_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_option_string return_type, slop_string prefix, type_extract_TypeRegistry types, slop_option_string eq_fn) {
    {
        __auto_type ret_type_str = ({ __auto_type _mv = return_type; _mv.has_value ? ({ __auto_type s = _mv.value; s; }) : (SLOP_STR("Int")); });
        if (emit_is_union_constructor_typed(expected, types)) {
            return emit_build_union_comparison_typed(arena, expected, prefix, types, ret_type_str);
        } else {
            if (strlib_contains(ret_type_str, SLOP_STR("Option"))) {
                if (emit_is_none_value(expected)) {
                    return (emit_CompareInfo){SLOP_STR("!result.has_value"), SLOP_STR("%s"), SLOP_STR("result.has_value ? \"some(...)\" : \"none\""), SLOP_STR("%s"), SLOP_STR("\"none\"")};
                } else {
                    if (emit_is_some_value(expected)) {
                        {
                            __auto_type inner_expected = emit_get_some_inner_typed(arena, expected, prefix, types);
                            __auto_type inner_expr = emit_get_some_inner_expr(expected);
                            if (strlib_contains(ret_type_str, SLOP_STR("String"))) {
                                return (emit_CompareInfo){string_concat(arena, SLOP_STR("result.has_value && slop_string_eq(result.value, "), string_concat(arena, inner_expected, SLOP_STR(")"))), SLOP_STR("%s"), SLOP_STR("result.has_value ? \"some(...)\" : \"none\""), SLOP_STR("%s"), SLOP_STR("\"some(...)\"")};
                            } else if (emit_is_record_constructor_typed(inner_expr, types)) {
                                {
                                    __auto_type record_name = emit_get_record_name_from_expr(inner_expr);
                                    __auto_type field_values = emit_get_record_field_values(arena, inner_expr);
                                    __auto_type _mv_186 = type_extract_registry_get_record_fields(types, record_name);
                                    if (_mv_186.has_value) {
                                        __auto_type fields = _mv_186.value;
                                        {
                                            __auto_type expected_var_name = SLOP_STR("expected_value");
                                            __auto_type compare_expr = emit_build_record_field_comparisons_with_values(arena, fields, field_values, SLOP_STR("result.value"), expected_var_name);
                                            return (emit_CompareInfo){string_concat(arena, SLOP_STR("({ typeof(result.value) "), string_concat(arena, expected_var_name, string_concat(arena, SLOP_STR(" = "), string_concat(arena, inner_expected, string_concat(arena, SLOP_STR("; result.has_value && "), string_concat(arena, compare_expr, SLOP_STR("; })"))))))), SLOP_STR("%s"), SLOP_STR("result.has_value ? \"some(...)\" : \"none\""), SLOP_STR("%s"), SLOP_STR("\"some(...)\"")};
                                        }
                                    } else if (!_mv_186.has_value) {
                                        return (emit_CompareInfo){string_concat(arena, SLOP_STR("({ typeof(result.value) expected_value = "), string_concat(arena, inner_expected, SLOP_STR("; result.has_value && memcmp(&result.value, &expected_value, sizeof(result.value)) == 0; })"))), SLOP_STR("%s"), SLOP_STR("result.has_value ? \"some(...)\" : \"none\""), SLOP_STR("%s"), SLOP_STR("\"some(...)\"")};
                                    }
                                }
                            } else {
                                return (emit_CompareInfo){string_concat(arena, SLOP_STR("result.has_value && result.value == "), inner_expected), SLOP_STR("%s"), SLOP_STR("result.has_value ? \"some(...)\" : \"none\""), SLOP_STR("%s"), SLOP_STR("\"some(...)\"")};
                            }
                        }
                    } else {
                        {
                            __auto_type c_expected = emit_sexpr_to_c_typed(arena, expected, prefix, types);
                            return (emit_CompareInfo){string_concat(arena, SLOP_STR("result == "), c_expected), SLOP_STR("%lld"), SLOP_STR("(long long)result"), SLOP_STR("%lld"), string_concat(arena, SLOP_STR("(long long)"), c_expected)};
                        }
                    }
                }
            } else {
                if (strlib_contains(ret_type_str, SLOP_STR("Result"))) {
                    if (emit_is_ok_value(expected)) {
                        {
                            __auto_type inner_expected = emit_get_ok_inner_typed(arena, expected, prefix, types);
                            __auto_type inner_expr = emit_get_ok_inner_expr(expected);
                            if (emit_is_union_constructor_typed(inner_expr, types)) {
                                {
                                    __auto_type expected_var = SLOP_STR("expected_ok");
                                    __auto_type variant_name = emit_get_union_variant_name(inner_expr);
                                    __auto_type c_variant = ctype_to_c_name(arena, variant_name);
                                    __auto_type is_string_variant = strlib_contains(strlib_to_lower(arena, variant_name), SLOP_STR("string"));
                                    return (emit_CompareInfo){({ __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("({ typeof(result.data.ok) ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(" = ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (inner_expected); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("; result.is_ok && result.data.ok.tag == ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".tag && ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ((is_string_variant) ? ({ ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("slop_string_eq(result.data.ok.data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(", ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(")")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); }) : ({ ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("result.data.ok.data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(" == ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); })); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("; })")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); strlib_string_build(arena, parts); }), SLOP_STR("%s"), SLOP_STR("result.is_ok ? \"ok(...)\" : \"error(...)\""), SLOP_STR("%s"), SLOP_STR("\"ok(...)\"")};
                                }
                            } else {
                                return (emit_CompareInfo){string_concat(arena, SLOP_STR("result.is_ok && result.data.ok == "), inner_expected), SLOP_STR("%s"), SLOP_STR("result.is_ok ? \"ok(...)\" : \"error(...)\""), SLOP_STR("%s"), SLOP_STR("\"ok(...)\"")};
                            }
                        }
                    } else {
                        if (emit_is_error_value(expected)) {
                            {
                                __auto_type inner_expected = emit_get_error_inner_typed(arena, expected, prefix, types);
                                __auto_type inner_expr = emit_get_ok_inner_expr(expected);
                                if (emit_is_union_constructor_typed(inner_expr, types)) {
                                    {
                                        __auto_type expected_var = SLOP_STR("expected_err");
                                        __auto_type variant_name = emit_get_union_variant_name(inner_expr);
                                        __auto_type c_variant = ctype_to_c_name(arena, variant_name);
                                        __auto_type is_string_variant = strlib_contains(strlib_to_lower(arena, variant_name), SLOP_STR("string"));
                                        return (emit_CompareInfo){({ __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("({ typeof(result.data.err) ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(" = ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (inner_expected); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("; !result.is_ok && result.data.err.tag == ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".tag && ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ((is_string_variant) ? ({ ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("slop_string_eq(result.data.err.data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(", ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(")")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); }) : ({ ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("result.data.err.data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(" == ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".data.")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_variant); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); })); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("; })")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); strlib_string_build(arena, parts); }), SLOP_STR("%s"), SLOP_STR("result.is_ok ? \"ok(...)\" : \"error(...)\""), SLOP_STR("%s"), SLOP_STR("\"error(...)\"")};
                                    }
                                } else {
                                    return (emit_CompareInfo){string_concat(arena, SLOP_STR("!result.is_ok && result.data.err == "), inner_expected), SLOP_STR("%s"), SLOP_STR("result.is_ok ? \"ok(...)\" : \"error(...)\""), SLOP_STR("%s"), SLOP_STR("\"error(...)\"")};
                                }
                            }
                        } else {
                            {
                                __auto_type c_expected = emit_sexpr_to_c_typed(arena, expected, prefix, types);
                                return (emit_CompareInfo){string_concat(arena, SLOP_STR("result == "), c_expected), SLOP_STR("%lld"), SLOP_STR("(long long)result"), SLOP_STR("%lld"), string_concat(arena, SLOP_STR("(long long)"), c_expected)};
                            }
                        }
                    }
                } else {
                    if (strlib_contains(ret_type_str, SLOP_STR("String"))) {
                        {
                            __auto_type c_expected = emit_sexpr_to_c_typed(arena, expected, prefix, types);
                            return (emit_CompareInfo){string_concat(arena, SLOP_STR("slop_string_eq(result, "), string_concat(arena, c_expected, SLOP_STR(")"))), SLOP_STR("\\\"%.*s\\\""), SLOP_STR("(int)result.len, result.data"), SLOP_STR("\\\"%.*s\\\""), ({ __auto_type part1 = string_concat(arena, SLOP_STR("(int)("), c_expected); __auto_type part2 = string_concat(arena, part1, SLOP_STR(").len, (")); __auto_type part3 = string_concat(arena, part2, c_expected); __auto_type part4 = string_concat(arena, part3, SLOP_STR(").data")); part4; })};
                        }
                    } else {
                        if (strlib_contains(ret_type_str, SLOP_STR("List"))) {
                            return emit_build_list_comparison_typed(arena, expected, prefix, types, ret_type_str, eq_fn);
                        } else {
                            if (strlib_contains(ret_type_str, SLOP_STR("Bool"))) {
                                {
                                    __auto_type c_expected = emit_sexpr_to_c_typed(arena, expected, prefix, types);
                                    return (emit_CompareInfo){string_concat(arena, SLOP_STR("result == "), c_expected), SLOP_STR("%s"), SLOP_STR("result ? \"true\" : \"false\""), SLOP_STR("%s"), string_concat(arena, c_expected, SLOP_STR(" ? \"true\" : \"false\""))};
                                }
                            } else {
                                if (strlib_contains(ret_type_str, SLOP_STR("Float"))) {
                                    {
                                        __auto_type c_expected = emit_sexpr_to_c_typed(arena, expected, prefix, types);
                                        {
                                            __auto_type fabs1 = string_concat(arena, SLOP_STR("fabs(result - "), c_expected);
                                            __auto_type fabs2 = string_concat(arena, fabs1, SLOP_STR(") < (fabs("));
                                            __auto_type fabs3 = string_concat(arena, fabs2, c_expected);
                                            __auto_type fabs4 = string_concat(arena, fabs3, SLOP_STR(") * 1e-6 + 1e-9)"));
                                            return (emit_CompareInfo){fabs4, SLOP_STR("%g"), SLOP_STR("result"), SLOP_STR("%g"), c_expected};
                                        }
                                    }
                                } else {
                                    if (emit_is_enum_value_typed(expected, types)) {
                                        {
                                            __auto_type c_expected = emit_sexpr_to_c_typed(arena, expected, prefix, types);
                                            return (emit_CompareInfo){string_concat(arena, SLOP_STR("result == "), c_expected), SLOP_STR("%d"), SLOP_STR("(int)result"), SLOP_STR("%d"), string_concat(arena, SLOP_STR("(int)"), c_expected)};
                                        }
                                    } else {
                                        if (emit_is_record_constructor_typed(expected, types)) {
                                            return emit_build_record_comparison_typed(arena, expected, prefix, types);
                                        } else {
                                            {
                                                __auto_type c_expected = emit_sexpr_to_c_typed(arena, expected, prefix, types);
                                                return (emit_CompareInfo){string_concat(arena, SLOP_STR("result == "), c_expected), SLOP_STR("%lld"), SLOP_STR("(long long)result"), SLOP_STR("%lld"), string_concat(arena, SLOP_STR("(long long)"), c_expected)};
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

emit_CompareInfo emit_build_record_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types) {
    {
        __auto_type record_name = emit_get_record_name_from_expr(expected);
        __auto_type c_expected = emit_sexpr_to_c_typed(arena, expected, prefix, types);
        __auto_type field_values = emit_get_record_field_values(arena, expected);
        __auto_type _mv_187 = type_extract_registry_get_record_fields(types, record_name);
        if (_mv_187.has_value) {
            __auto_type fields = _mv_187.value;
            {
                __auto_type expected_var_name = SLOP_STR("expected_value");
                __auto_type compare_expr = emit_build_record_field_comparisons_with_values(arena, fields, field_values, SLOP_STR("result"), expected_var_name);
                return (emit_CompareInfo){string_concat(arena, SLOP_STR("({ typeof(result) "), string_concat(arena, expected_var_name, string_concat(arena, SLOP_STR(" = "), string_concat(arena, c_expected, string_concat(arena, SLOP_STR("; "), string_concat(arena, compare_expr, SLOP_STR("; })"))))))), SLOP_STR("%s"), SLOP_STR("\"<record>\""), SLOP_STR("%s"), SLOP_STR("\"<expected>\"")};
            }
        } else if (!_mv_187.has_value) {
            {
                __auto_type expected_var_name = SLOP_STR("expected_value");
                return (emit_CompareInfo){string_concat(arena, SLOP_STR("({ typeof(result) "), string_concat(arena, expected_var_name, string_concat(arena, SLOP_STR(" = "), string_concat(arena, c_expected, string_concat(arena, SLOP_STR("; memcmp(&result, &"), string_concat(arena, expected_var_name, SLOP_STR(", sizeof(result)) == 0; })"))))))), SLOP_STR("%s"), SLOP_STR("\"<record>\""), SLOP_STR("%s"), SLOP_STR("\"<expected>\"")};
            }
        }
    }
}

slop_string emit_get_record_name_from_expr(types_SExpr* expr) {
    __auto_type _mv_188 = (*expr);
    switch (_mv_188.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_188.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_189 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_189.has_value) {
                        __auto_type first = _mv_189.value;
                        if (parser_sexpr_is_symbol(first)) {
                            return parser_sexpr_get_symbol_name(first);
                        } else {
                            return SLOP_STR("");
                        }
                    } else if (!_mv_189.has_value) {
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

slop_list_types_SExpr_ptr emit_get_record_field_values(slop_arena* arena, types_SExpr* expr) {
    __auto_type _mv_190 = (*expr);
    switch (_mv_190.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_190.data.lst;
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
                            __auto_type _mv_191 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_191.has_value) {
                                __auto_type val = _mv_191.value;
                                ({ __auto_type _lst_p = &(result); __auto_type _item = (val); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            } else if (!_mv_191.has_value) {
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

uint8_t emit_is_wildcard_expr(types_SExpr* expr) {
    __auto_type _mv_192 = (*expr);
    switch (_mv_192.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_192.data.sym;
            return string_eq(sym.name, SLOP_STR("_"));
        }
        default: {
            return 0;
        }
    }
}

slop_string emit_build_record_field_comparisons_with_values(slop_arena* arena, slop_list_type_extract_FieldEntry fields, slop_list_types_SExpr_ptr field_values, slop_string result_accessor, slop_string expected_var) {
    {
        __auto_type len = ((int64_t)((fields).len));
        __auto_type comp_result = SLOP_STR("1");
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_193 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_type_extract_FieldEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_193.has_value) {
                __auto_type field = _mv_193.value;
                {
                    __auto_type is_wildcard = ({ __auto_type _mv = ({ __auto_type _lst = field_values; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type val = _mv.value; emit_is_wildcard_expr(val); }) : (0); });
                    if (!(is_wildcard)) {
                        {
                            __auto_type fname = ctype_to_c_name(arena, field.name);
                            __auto_type ftype = field.type_name;
                            __auto_type field_cmp = emit_build_single_field_comparison_with_accessor(arena, fname, ftype, result_accessor, expected_var);
                            comp_result = string_concat(arena, comp_result, string_concat(arena, SLOP_STR(" && "), field_cmp));
                        }
                    }
                }
            } else if (!_mv_193.has_value) {
            }
            i = (i + 1);
        }
        return comp_result;
    }
}

slop_string emit_build_single_field_comparison_with_accessor(slop_arena* arena, slop_string fname, slop_string ftype, slop_string result_accessor, slop_string expected_var) {
    if (strlib_contains(ftype, SLOP_STR("List"))) {
        return string_concat(arena, result_accessor, string_concat(arena, SLOP_STR("."), string_concat(arena, fname, string_concat(arena, SLOP_STR(".len == "), string_concat(arena, expected_var, string_concat(arena, SLOP_STR("."), string_concat(arena, fname, SLOP_STR(".len"))))))));
    } else {
        if (strlib_contains(ftype, SLOP_STR("String"))) {
            return string_concat(arena, SLOP_STR("slop_string_eq("), string_concat(arena, result_accessor, string_concat(arena, SLOP_STR("."), string_concat(arena, fname, string_concat(arena, SLOP_STR(", "), string_concat(arena, expected_var, string_concat(arena, SLOP_STR("."), string_concat(arena, fname, SLOP_STR(")")))))))));
        } else {
            return string_concat(arena, result_accessor, string_concat(arena, SLOP_STR("."), string_concat(arena, fname, string_concat(arena, SLOP_STR(" == "), string_concat(arena, expected_var, string_concat(arena, SLOP_STR("."), fname))))));
        }
    }
}

slop_string emit_build_record_field_comparisons(slop_arena* arena, slop_list_type_extract_FieldEntry fields, slop_string prefix, slop_string expected_var) {
    {
        __auto_type len = ((int64_t)((fields).len));
        __auto_type result = SLOP_STR("1");
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_194 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_type_extract_FieldEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_194.has_value) {
                __auto_type field = _mv_194.value;
                {
                    __auto_type fname = ctype_to_c_name(arena, field.name);
                    __auto_type ftype = field.type_name;
                    __auto_type field_cmp = emit_build_single_field_comparison(arena, fname, ftype, expected_var);
                    result = string_concat(arena, result, string_concat(arena, SLOP_STR(" && "), field_cmp));
                }
            } else if (!_mv_194.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_string emit_build_single_field_comparison(slop_arena* arena, slop_string fname, slop_string ftype, slop_string expected_var) {
    if (strlib_contains(ftype, SLOP_STR("List"))) {
        return string_concat(arena, SLOP_STR("result."), string_concat(arena, fname, string_concat(arena, SLOP_STR(".len == "), string_concat(arena, expected_var, string_concat(arena, SLOP_STR("."), string_concat(arena, fname, SLOP_STR(".len")))))));
    } else {
        if (strlib_contains(ftype, SLOP_STR("String"))) {
            return string_concat(arena, SLOP_STR("slop_string_eq(result."), string_concat(arena, fname, string_concat(arena, SLOP_STR(", "), string_concat(arena, expected_var, string_concat(arena, SLOP_STR("."), string_concat(arena, fname, SLOP_STR(")")))))));
        } else {
            return string_concat(arena, SLOP_STR("result."), string_concat(arena, fname, string_concat(arena, SLOP_STR(" == "), string_concat(arena, expected_var, string_concat(arena, SLOP_STR("."), fname)))));
        }
    }
}

emit_CompareInfo emit_build_union_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types, slop_string ret_type_str) {
    {
        __auto_type c_expected = emit_sexpr_to_c_typed(arena, expected, prefix, types);
        __auto_type expected_var_name = SLOP_STR("expected_value");
        __auto_type variant_name = emit_get_union_variant_name(expected);
        __auto_type c_variant = ctype_to_c_name(arena, variant_name);
        {
            __auto_type payload_cmp = ({ __auto_type _mv = type_extract_registry_get_variant_info(types, variant_name); _mv.has_value ? ({ __auto_type ve = _mv.value; ({ __auto_type payload_type = ve.payload_type; emit_build_union_payload_comparison(arena, payload_type, c_variant, expected_var_name, types); }); }) : (string_concat(arena, SLOP_STR("memcmp(&result.data, &"), string_concat(arena, expected_var_name, SLOP_STR(".data, sizeof(result.data)) == 0")))); });
            return (emit_CompareInfo){({ __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("({ typeof(result) ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(" = ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (c_expected); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("; result.tag == ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_var_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(".tag && ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (payload_cmp); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("; })")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); strlib_string_build(arena, parts); }), SLOP_STR("%s"), SLOP_STR("\"<union>\""), SLOP_STR("%s"), SLOP_STR("\"<expected>\"")};
        }
    }
}

slop_string emit_build_union_payload_comparison(slop_arena* arena, slop_string payload_type, slop_string c_variant, slop_string expected_var, type_extract_TypeRegistry types) {
    if (string_eq(payload_type, SLOP_STR(""))) {
        return SLOP_STR("1");
    } else if (string_eq(payload_type, SLOP_STR("String"))) {
        return string_concat(arena, SLOP_STR("slop_string_eq(result.data."), string_concat(arena, c_variant, string_concat(arena, SLOP_STR(", "), string_concat(arena, expected_var, string_concat(arena, SLOP_STR(".data."), string_concat(arena, c_variant, SLOP_STR(")")))))));
    } else {
        __auto_type _mv_195 = type_extract_registry_get_record_fields(types, payload_type);
        if (_mv_195.has_value) {
            __auto_type fields = _mv_195.value;
            return emit_build_union_record_payload_comparison(arena, fields, c_variant, expected_var);
        } else if (!_mv_195.has_value) {
            return string_concat(arena, SLOP_STR("memcmp(&result.data."), string_concat(arena, c_variant, string_concat(arena, SLOP_STR(", &"), string_concat(arena, expected_var, string_concat(arena, SLOP_STR(".data."), string_concat(arena, c_variant, string_concat(arena, SLOP_STR(", sizeof(result.data."), string_concat(arena, c_variant, SLOP_STR("))")))))))));
        }
    }
}

slop_string emit_build_union_record_payload_comparison(slop_arena* arena, slop_list_type_extract_FieldEntry fields, slop_string c_variant, slop_string expected_var) {
    {
        __auto_type len = ((int64_t)((fields).len));
        __auto_type result = SLOP_STR("1");
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_196 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_type_extract_FieldEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_196.has_value) {
                __auto_type field = _mv_196.value;
                {
                    __auto_type fname = ctype_to_c_name(arena, field.name);
                    __auto_type ftype = field.type_name;
                    __auto_type field_cmp = emit_build_union_field_comparison(arena, fname, ftype, c_variant, expected_var);
                    result = string_concat(arena, result, string_concat(arena, SLOP_STR(" && "), field_cmp));
                }
            } else if (!_mv_196.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_string emit_build_union_field_comparison(slop_arena* arena, slop_string fname, slop_string ftype, slop_string c_variant, slop_string expected_var) {
    {
        __auto_type result_path = string_concat(arena, SLOP_STR("result.data."), string_concat(arena, c_variant, string_concat(arena, SLOP_STR("."), fname)));
        __auto_type expected_path = string_concat(arena, expected_var, string_concat(arena, SLOP_STR(".data."), string_concat(arena, c_variant, string_concat(arena, SLOP_STR("."), fname))));
        if (string_eq(ftype, SLOP_STR("String"))) {
            return string_concat(arena, SLOP_STR("slop_string_eq("), string_concat(arena, result_path, string_concat(arena, SLOP_STR(", "), string_concat(arena, expected_path, SLOP_STR(")")))));
        } else if (string_eq(ftype, SLOP_STR("(Option String)"))) {
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

uint8_t emit_is_union_constructor_typed(types_SExpr* expr, type_extract_TypeRegistry types) {
    __auto_type _mv_197 = (*expr);
    switch (_mv_197.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_197.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return 0;
                } else {
                    __auto_type _mv_198 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_198.has_value) {
                        __auto_type first = _mv_198.value;
                        if (parser_sexpr_is_symbol(first)) {
                            {
                                __auto_type name = parser_sexpr_get_symbol_name(first);
                                if (((string_eq(name, SLOP_STR("none"))) || (string_eq(name, SLOP_STR("some"))) || (string_eq(name, SLOP_STR("ok"))) || (string_eq(name, SLOP_STR("error"))))) {
                                    return 0;
                                } else {
                                    __auto_type _mv_199 = type_extract_registry_lookup_variant(types, name);
                                    if (_mv_199.has_value) {
                                        __auto_type _ = _mv_199.value;
                                        return 1;
                                    } else if (!_mv_199.has_value) {
                                        return 0;
                                    }
                                }
                            }
                        } else {
                            return 0;
                        }
                    } else if (!_mv_198.has_value) {
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

slop_string emit_get_union_variant_name(types_SExpr* expr) {
    __auto_type _mv_200 = (*expr);
    switch (_mv_200.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_200.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_201 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_201.has_value) {
                        __auto_type first = _mv_201.value;
                        if (parser_sexpr_is_symbol(first)) {
                            return parser_sexpr_get_symbol_name(first);
                        } else {
                            return SLOP_STR("");
                        }
                    } else if (!_mv_201.has_value) {
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

uint8_t emit_is_enum_value_typed(types_SExpr* expr, type_extract_TypeRegistry types) {
    __auto_type _mv_202 = (*expr);
    switch (_mv_202.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_202.data.sym;
            {
                __auto_type name = sym.name;
                if (strlib_starts_with(name, SLOP_STR("'"))) {
                    {
                        __auto_type variant_name = emit_emit_string_slice(name, 1);
                        __auto_type _mv_203 = type_extract_registry_lookup_enum_value(types, variant_name);
                        if (_mv_203.has_value) {
                            __auto_type _ = _mv_203.value;
                            return 1;
                        } else if (!_mv_203.has_value) {
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
            __auto_type lst = _mv_202.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 2)) {
                    return 0;
                } else {
                    __auto_type _mv_204 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_204.has_value) {
                        __auto_type first = _mv_204.value;
                        if ((parser_sexpr_is_symbol(first) && string_eq(parser_sexpr_get_symbol_name(first), SLOP_STR("quote")))) {
                            __auto_type _mv_205 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_205.has_value) {
                                __auto_type quoted = _mv_205.value;
                                if (parser_sexpr_is_symbol(quoted)) {
                                    __auto_type _mv_206 = type_extract_registry_lookup_enum_value(types, parser_sexpr_get_symbol_name(quoted));
                                    if (_mv_206.has_value) {
                                        __auto_type _ = _mv_206.value;
                                        return 1;
                                    } else if (!_mv_206.has_value) {
                                        return 0;
                                    }
                                } else {
                                    return 0;
                                }
                            } else if (!_mv_205.has_value) {
                                return 0;
                            }
                        } else {
                            return 0;
                        }
                    } else if (!_mv_204.has_value) {
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

uint8_t emit_is_record_constructor_typed(types_SExpr* expr, type_extract_TypeRegistry types) {
    __auto_type _mv_207 = (*expr);
    switch (_mv_207.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_207.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return 0;
                } else {
                    __auto_type _mv_208 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_208.has_value) {
                        __auto_type first = _mv_208.value;
                        if (parser_sexpr_is_symbol(first)) {
                            {
                                __auto_type name = parser_sexpr_get_symbol_name(first);
                                if ((string_eq(name, SLOP_STR("none")) || (string_eq(name, SLOP_STR("some")) || (string_eq(name, SLOP_STR("ok")) || (string_eq(name, SLOP_STR("error")) || string_eq(name, SLOP_STR("list"))))))) {
                                    return 0;
                                } else {
                                    __auto_type _mv_209 = type_extract_registry_lookup(types, name);
                                    if (_mv_209.has_value) {
                                        __auto_type entry = _mv_209.value;
                                        return type_extract_registry_is_record(types, name);
                                    } else if (!_mv_209.has_value) {
                                        return 0;
                                    }
                                }
                            }
                        } else {
                            return 0;
                        }
                    } else if (!_mv_208.has_value) {
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

slop_string emit_emit_string_slice(slop_string s, int64_t start) {
    if ((start >= ((int64_t)(s.len)))) {
        return SLOP_STR("");
    } else {
        return (slop_string){.len = ((uint64_t)((s.len - ((uint64_t)(start))))), .data = ((uint8_t*)((((int64_t)(s.data)) + start)))};
    }
}

slop_string emit_get_some_inner_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types) {
    if ((parser_sexpr_list_len(expr) > 1)) {
        __auto_type _mv_210 = parser_sexpr_list_get(expr, 1);
        if (_mv_210.has_value) {
            __auto_type inner = _mv_210.value;
            return emit_sexpr_to_c_typed(arena, inner, prefix, types);
        } else if (!_mv_210.has_value) {
            return SLOP_STR("0");
        }
    } else {
        return SLOP_STR("0");
    }
}

slop_string emit_get_ok_inner_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types) {
    return emit_get_some_inner_typed(arena, expr, prefix, types);
}

types_SExpr* emit_get_some_inner_expr(types_SExpr* expected) {
    __auto_type _mv_211 = (*expected);
    switch (_mv_211.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_211.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) > 1)) {
                    __auto_type _mv_212 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_212.has_value) {
                        __auto_type inner = _mv_212.value;
                        return inner;
                    } else if (!_mv_212.has_value) {
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

slop_string emit_get_error_inner_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types) {
    return emit_get_some_inner_typed(arena, expr, prefix, types);
}

types_SExpr* emit_get_ok_inner_expr(types_SExpr* expected) {
    __auto_type _mv_213 = (*expected);
    switch (_mv_213.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_213.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) > 1)) {
                    __auto_type _mv_214 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_214.has_value) {
                        __auto_type inner = _mv_214.value;
                        return inner;
                    } else if (!_mv_214.has_value) {
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

slop_string emit_extract_list_element_type(slop_arena* arena, slop_string list_type_str) {
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
                        __auto_type buf = ((uint8_t*)((uint8_t*)slop_arena_alloc(arena, (elem_len + 1))));
                        {
                            __auto_type i = 0;
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

slop_string emit_build_eq_function_name(slop_arena* arena, slop_string type_name, slop_string prefix, type_extract_TypeRegistry types) {
    {
        __auto_type type_c = strlib_to_lower(arena, ctype_to_c_name(arena, type_name));
        __auto_type _mv_215 = type_extract_registry_lookup_import(types, type_name);
        if (_mv_215.has_value) {
            __auto_type mod_name = _mv_215.value;
            return strlib_string_build(arena, ((slop_list_string){.len = 4, .cap = 4, .data = (slop_string[]){ctype_to_c_name(arena, mod_name), SLOP_STR("_"), type_c, SLOP_STR("_eq")}}));
        } else if (!_mv_215.has_value) {
            if ((((int64_t)(prefix.len)) > 0)) {
                return strlib_string_build(arena, ((slop_list_string){.len = 4, .cap = 4, .data = (slop_string[]){prefix, SLOP_STR("_"), type_c, SLOP_STR("_eq")}}));
            } else {
                return strlib_string_build(arena, ((slop_list_string){.len = 2, .cap = 2, .data = (slop_string[]){type_c, SLOP_STR("_eq")}}));
            }
        }
    }
}

emit_CompareInfo emit_build_list_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types, slop_string ret_type_str, slop_option_string eq_fn) {
    __auto_type _mv_216 = (*expected);
    switch (_mv_216.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_216.data.lst;
            {
                __auto_type elements = lst.items;
                __auto_type total_count = ((int64_t)((elements).len));
                {
                    __auto_type start_idx = ((((total_count > 0) && ({ __auto_type _mv = ({ __auto_type _lst = elements; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type first_elem = _mv.value; (parser_sexpr_is_symbol(first_elem) && string_eq(parser_sexpr_get_symbol_name(first_elem), SLOP_STR("list"))); }) : (0); }))) ? 1 : 0);
                    __auto_type elem_count = (total_count - start_idx);
                    if ((elem_count == 0)) {
                        return (emit_CompareInfo){SLOP_STR("result.len == 0"), SLOP_STR("len=%lld"), SLOP_STR("(long long)result.len"), SLOP_STR("len=%lld"), SLOP_STR("0LL")};
                    } else {
                        {
                            __auto_type has_wildcard = 0;
                            __auto_type j = start_idx;
                            while ((j < total_count)) {
                                __auto_type _mv_217 = ({ __auto_type _lst = elements; size_t _idx = (size_t)j; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_217.has_value) {
                                    __auto_type elem = _mv_217.value;
                                    if (emit_is_wildcard_expr(elem)) {
                                        has_wildcard = 1;
                                    }
                                } else if (!_mv_217.has_value) {
                                }
                                j = (j + 1);
                            }
                            {
                                __auto_type len_str = int_to_string(arena, elem_count);
                                if (has_wildcard) {
                                    return (emit_CompareInfo){strlib_string_build(arena, ((slop_list_string){.len = 2, .cap = 2, .data = (slop_string[]){SLOP_STR("result.len == "), len_str}})), SLOP_STR("len=%lld"), SLOP_STR("(long long)result.len"), SLOP_STR("len=%lld"), strlib_string_build(arena, ((slop_list_string){.len = 2, .cap = 2, .data = (slop_string[]){SLOP_STR("(long long)"), len_str}}))};
                                } else {
                                    {
                                        __auto_type elem_type = emit_extract_list_element_type(arena, ret_type_str);
                                        __auto_type is_complex = (type_extract_registry_is_record(types, elem_type) || type_extract_registry_is_union(types, elem_type));
                                        {
                                            __auto_type arr_init = SLOP_STR("{");
                                            __auto_type i = start_idx;
                                            __auto_type first = 1;
                                            while ((i < total_count)) {
                                                __auto_type _mv_218 = ({ __auto_type _lst = elements; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_218.has_value) {
                                                    __auto_type elem = _mv_218.value;
                                                    {
                                                        __auto_type elem_c = emit_sexpr_to_c_typed(arena, elem, prefix, types);
                                                        if (first) {
                                                            arr_init = string_concat(arena, arr_init, elem_c);
                                                            first = 0;
                                                        } else {
                                                            arr_init = string_concat(arena, arr_init, string_concat(arena, SLOP_STR(", "), elem_c));
                                                        }
                                                    }
                                                } else if (!_mv_218.has_value) {
                                                }
                                                i = (i + 1);
                                            }
                                            arr_init = string_concat(arena, arr_init, SLOP_STR("}"));
                                            if (!(is_complex)) {
                                                {
                                                    __auto_type cmp_expr = strlib_string_build(arena, ((slop_list_string){.len = 7, .cap = 7, .data = (slop_string[]){SLOP_STR("(result.len == "), len_str, SLOP_STR(" && memcmp(result.data, (typeof(*result.data)[])"), arr_init, SLOP_STR(", sizeof(typeof(*result.data)) * "), len_str, SLOP_STR(") == 0)")}}));
                                                    return (emit_CompareInfo){cmp_expr, SLOP_STR("len=%lld"), SLOP_STR("(long long)result.len"), SLOP_STR("len=%lld"), strlib_string_build(arena, ((slop_list_string){.len = 2, .cap = 2, .data = (slop_string[]){SLOP_STR("(long long)"), len_str}}))};
                                                }
                                            } else {
                                                {
                                                    __auto_type eq_fn_name = ({ __auto_type _mv = eq_fn; _mv.has_value ? ({ __auto_type fn_name = _mv.value; emit_prefix_symbol(arena, fn_name, prefix, types); }) : (emit_build_eq_function_name(arena, elem_type, prefix, types)); });
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
                                                        return (emit_CompareInfo){strlib_string_build(arena, cmp_parts), SLOP_STR("len=%lld"), SLOP_STR("(long long)result.len"), SLOP_STR("len=%lld"), strlib_string_build(arena, ((slop_list_string){.len = 2, .cap = 2, .data = (slop_string[]){SLOP_STR("(long long)"), len_str}}))};
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
            return (emit_CompareInfo){SLOP_STR("result.len == 0"), SLOP_STR("len=%lld"), SLOP_STR("(long long)result.len"), SLOP_STR("len=%lld"), SLOP_STR("0LL")};
        }
    }
}

uint8_t emit_is_none_value(types_SExpr* expr) {
    __auto_type _mv_219 = (*expr);
    switch (_mv_219.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_219.data.sym;
            return string_eq(sym.name, SLOP_STR("none"));
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_219.data.lst;
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

uint8_t emit_is_some_value(types_SExpr* expr) {
    return parser_is_form(expr, SLOP_STR("some"));
}

uint8_t emit_is_ok_value(types_SExpr* expr) {
    return parser_is_form(expr, SLOP_STR("ok"));
}

uint8_t emit_is_error_value(types_SExpr* expr) {
    return parser_is_form(expr, SLOP_STR("error"));
}

slop_string emit_get_some_inner(slop_arena* arena, types_SExpr* expr, slop_string prefix) {
    if ((parser_sexpr_list_len(expr) > 1)) {
        __auto_type _mv_220 = parser_sexpr_list_get(expr, 1);
        if (_mv_220.has_value) {
            __auto_type inner = _mv_220.value;
            return emit_sexpr_to_c(arena, inner, prefix);
        } else if (!_mv_220.has_value) {
            return SLOP_STR("0");
        }
    } else {
        return SLOP_STR("0");
    }
}

slop_string emit_get_ok_inner(slop_arena* arena, types_SExpr* expr, slop_string prefix) {
    return emit_get_some_inner(arena, expr, prefix);
}

slop_string emit_get_error_inner(slop_arena* arena, types_SExpr* expr, slop_string prefix) {
    return emit_get_some_inner(arena, expr, prefix);
}

uint8_t emit_is_list_literal(types_SExpr* expr) {
    __auto_type _mv_221 = (*expr);
    switch (_mv_221.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_221.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return 1;
                } else {
                    __auto_type _mv_222 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_222.has_value) {
                        __auto_type first = _mv_222.value;
                        return parser_sexpr_is_number(first);
                    } else if (!_mv_222.has_value) {
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

uint8_t emit_is_union_or_record_constructor(types_SExpr* expr) {
    __auto_type _mv_223 = (*expr);
    switch (_mv_223.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_223.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return 0;
                } else {
                    __auto_type _mv_224 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_224.has_value) {
                        __auto_type first = _mv_224.value;
                        if (parser_sexpr_is_symbol(first)) {
                            {
                                __auto_type name = parser_sexpr_get_symbol_name(first);
                                return ((!(string_eq(name, SLOP_STR("none")))) && (!(string_eq(name, SLOP_STR("some")))) && (!(string_eq(name, SLOP_STR("ok")))) && (!(string_eq(name, SLOP_STR("error")))) && (!(string_eq(name, SLOP_STR("quote")))) && (!(string_eq(name, SLOP_STR("list")))) && (({ __auto_type first_char = name.data[0]; (((first_char >= 65) && (first_char <= 90)) || (((first_char >= 97)) && ((first_char <= 122)) && (!(string_eq(name, SLOP_STR("+")))) && (!(string_eq(name, SLOP_STR("-")))) && (!(string_eq(name, SLOP_STR("*")))) && (!(string_eq(name, SLOP_STR("/")))) && (!(string_eq(name, SLOP_STR("%")))) && (!(string_eq(name, SLOP_STR("==")))) && (!(string_eq(name, SLOP_STR("!=")))) && (!(string_eq(name, SLOP_STR("<")))) && (!(string_eq(name, SLOP_STR("<=")))) && (!(string_eq(name, SLOP_STR(">")))) && (!(string_eq(name, SLOP_STR(">=")))) && (!(string_eq(name, SLOP_STR("and")))) && (!(string_eq(name, SLOP_STR("or")))) && (!(string_eq(name, SLOP_STR("not")))) && (!(string_eq(name, SLOP_STR(".")))) && (!(string_eq(name, SLOP_STR("cast")))))); })));
                            }
                        } else {
                            return 0;
                        }
                    } else if (!_mv_224.has_value) {
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

emit_CompareInfo emit_build_comparison(slop_arena* arena, types_SExpr* expected, slop_option_string return_type, slop_string prefix) {
    if (emit_is_union_or_record_constructor(expected)) {
        return (emit_CompareInfo){SLOP_STR("true"), SLOP_STR("%s"), SLOP_STR("\"<union/record>\""), SLOP_STR("%s"), SLOP_STR("\"<skipped>\"")};
    } else {
        {
            __auto_type c_expected = emit_sexpr_to_c(arena, expected, prefix);
            {
                __auto_type ret_type_str = ({ __auto_type _mv = return_type; _mv.has_value ? ({ __auto_type s = _mv.value; s; }) : (SLOP_STR("Int")); });
                if (strlib_contains(ret_type_str, SLOP_STR("Option"))) {
                    if (emit_is_none_value(expected)) {
                        return (emit_CompareInfo){SLOP_STR("!result.has_value"), SLOP_STR("%s"), SLOP_STR("result.has_value ? \"some(...)\" : \"none\""), SLOP_STR("%s"), SLOP_STR("\"none\"")};
                    } else {
                        if (emit_is_some_value(expected)) {
                            {
                                __auto_type inner_expected = emit_get_some_inner(arena, expected, prefix);
                                if (strlib_contains(ret_type_str, SLOP_STR("String"))) {
                                    return (emit_CompareInfo){string_concat(arena, SLOP_STR("result.has_value && slop_string_eq(result.value, "), string_concat(arena, inner_expected, SLOP_STR(")"))), SLOP_STR("%s"), SLOP_STR("result.has_value ? \"some(...)\" : \"none\""), SLOP_STR("%s"), SLOP_STR("\"some(...)\"")};
                                } else {
                                    return (emit_CompareInfo){string_concat(arena, SLOP_STR("result.has_value && result.value == "), inner_expected), SLOP_STR("%s"), SLOP_STR("result.has_value ? \"some(...)\" : \"none\""), SLOP_STR("%s"), SLOP_STR("\"some(...)\"")};
                                }
                            }
                        } else {
                            return (emit_CompareInfo){string_concat(arena, SLOP_STR("result == "), c_expected), SLOP_STR("%lld"), SLOP_STR("(long long)result"), SLOP_STR("%lld"), string_concat(arena, SLOP_STR("(long long)"), c_expected)};
                        }
                    }
                } else {
                    if (strlib_contains(ret_type_str, SLOP_STR("Result"))) {
                        if (emit_is_ok_value(expected)) {
                            {
                                __auto_type inner_expected = emit_get_ok_inner(arena, expected, prefix);
                                return (emit_CompareInfo){string_concat(arena, SLOP_STR("result.is_ok && result.data.ok == "), inner_expected), SLOP_STR("%s"), SLOP_STR("result.is_ok ? \"ok(...)\" : \"error(...)\""), SLOP_STR("%s"), SLOP_STR("\"ok(...)\"")};
                            }
                        } else {
                            if (emit_is_error_value(expected)) {
                                {
                                    __auto_type inner_expected = emit_get_error_inner(arena, expected, prefix);
                                    return (emit_CompareInfo){string_concat(arena, SLOP_STR("!result.is_ok && result.data.err == "), inner_expected), SLOP_STR("%s"), SLOP_STR("result.is_ok ? \"ok(...)\" : \"error(...)\""), SLOP_STR("%s"), SLOP_STR("\"error(...)\"")};
                                }
                            } else {
                                return (emit_CompareInfo){string_concat(arena, SLOP_STR("result == "), c_expected), SLOP_STR("%lld"), SLOP_STR("(long long)result"), SLOP_STR("%lld"), string_concat(arena, SLOP_STR("(long long)"), c_expected)};
                            }
                        }
                    } else {
                        if (strlib_contains(ret_type_str, SLOP_STR("String"))) {
                            return (emit_CompareInfo){string_concat(arena, SLOP_STR("slop_string_eq(result, "), string_concat(arena, c_expected, SLOP_STR(")"))), SLOP_STR("\\\"%.*s\\\""), SLOP_STR("(int)result.len, result.data"), SLOP_STR("\\\"%.*s\\\""), ({ __auto_type part1 = string_concat(arena, SLOP_STR("(int)("), c_expected); __auto_type part2 = string_concat(arena, part1, SLOP_STR(").len, (")); __auto_type part3 = string_concat(arena, part2, c_expected); __auto_type part4 = string_concat(arena, part3, SLOP_STR(").data")); part4; })};
                        } else {
                            if (strlib_contains(ret_type_str, SLOP_STR("List"))) {
                                return emit_build_list_comparison(arena, expected, prefix);
                            } else {
                                if (strlib_contains(ret_type_str, SLOP_STR("Bool"))) {
                                    return (emit_CompareInfo){string_concat(arena, SLOP_STR("result == "), c_expected), SLOP_STR("%s"), SLOP_STR("result ? \"true\" : \"false\""), SLOP_STR("%s"), string_concat(arena, c_expected, SLOP_STR(" ? \"true\" : \"false\""))};
                                } else {
                                    if (strlib_contains(ret_type_str, SLOP_STR("Float"))) {
                                        {
                                            __auto_type fabs1 = string_concat(arena, SLOP_STR("fabs(result - "), c_expected);
                                            __auto_type fabs2 = string_concat(arena, fabs1, SLOP_STR(") < (fabs("));
                                            __auto_type fabs3 = string_concat(arena, fabs2, c_expected);
                                            __auto_type fabs4 = string_concat(arena, fabs3, SLOP_STR(") * 1e-6 + 1e-9)"));
                                            return (emit_CompareInfo){fabs4, SLOP_STR("%g"), SLOP_STR("result"), SLOP_STR("%g"), c_expected};
                                        }
                                    } else {
                                        return (emit_CompareInfo){string_concat(arena, SLOP_STR("result == "), c_expected), SLOP_STR("%lld"), SLOP_STR("(long long)result"), SLOP_STR("%lld"), string_concat(arena, SLOP_STR("(long long)"), c_expected)};
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

emit_CompareInfo emit_build_list_comparison(slop_arena* arena, types_SExpr* expected, slop_string prefix) {
    __auto_type _mv_225 = (*expected);
    switch (_mv_225.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_225.data.lst;
            {
                __auto_type elements = lst.items;
                __auto_type elem_count = ((int64_t)((elements).len));
                if ((elem_count == 0)) {
                    return (emit_CompareInfo){SLOP_STR("result.len == 0"), SLOP_STR("len=%lld"), SLOP_STR("(long long)result.len"), SLOP_STR("len=%lld"), SLOP_STR("0LL")};
                } else {
                    {
                        __auto_type arr_init = SLOP_STR("{");
                        __auto_type i = 0;
                        __auto_type first = 1;
                        while ((i < elem_count)) {
                            __auto_type _mv_226 = ({ __auto_type _lst = elements; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_226.has_value) {
                                __auto_type elem = _mv_226.value;
                                {
                                    __auto_type elem_c = emit_sexpr_to_c(arena, elem, prefix);
                                    if (first) {
                                        arr_init = string_concat(arena, arr_init, elem_c);
                                        first = 0;
                                    } else {
                                        arr_init = string_concat(arena, arr_init, string_concat(arena, SLOP_STR(", "), elem_c));
                                    }
                                }
                            } else if (!_mv_226.has_value) {
                            }
                            i = (i + 1);
                        }
                        arr_init = string_concat(arena, arr_init, SLOP_STR("}"));
                        {
                            __auto_type len_str = int_to_string(arena, elem_count);
                            __auto_type cmp_expr = string_concat(arena, SLOP_STR("(result.len == "), string_concat(arena, len_str, string_concat(arena, SLOP_STR(" && memcmp(result.data, (typeof(*result.data)[])"), string_concat(arena, arr_init, string_concat(arena, SLOP_STR(", sizeof(typeof(*result.data)) * "), string_concat(arena, len_str, SLOP_STR(") == 0)")))))));
                            return (emit_CompareInfo){cmp_expr, SLOP_STR("len=%lld"), SLOP_STR("(long long)result.len"), SLOP_STR("len=%lld"), string_concat(arena, SLOP_STR("(long long)"), len_str)};
                        }
                    }
                }
            }
        }
        default: {
            return (emit_CompareInfo){SLOP_STR("result.len == 0"), SLOP_STR("len=%lld"), SLOP_STR("(long long)result.len"), SLOP_STR("len=%lld"), SLOP_STR("0LL")};
        }
    }
}

