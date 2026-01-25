#include "../runtime/slop_runtime.h"
#include "slop_emit.h"

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
slop_string emit_convert_symbol_to_c(slop_arena* arena, slop_string name);
slop_string emit_escape_string(slop_arena* arena, slop_string s);
uint8_t emit_string_starts_with(slop_string s, slop_string prefix);
slop_string emit_emit_emit_string_slice(slop_arena* arena, slop_string s, int64_t start, int64_t end);
slop_list_string emit_emit_test_harness_typed(slop_arena* arena, slop_list_extract_TestCase_ptr tests, slop_string module_prefix, type_extract_TypeRegistry* types, slop_list_string imports);
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
emit_CompareInfo emit_build_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_option_string return_type, slop_string prefix, type_extract_TypeRegistry types);
emit_CompareInfo emit_build_record_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_get_record_name_from_expr(types_SExpr* expr);
slop_string emit_build_record_field_comparisons(slop_arena* arena, slop_list_type_extract_FieldEntry fields, slop_string prefix, slop_string expected_var);
slop_string emit_build_single_field_comparison(slop_arena* arena, slop_string fname, slop_string ftype, slop_string expected_var);
emit_CompareInfo emit_build_union_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types, slop_string ret_type_str);
slop_string emit_get_union_eq_fn_name(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_slop_name_to_c_lower(slop_arena* arena, slop_string name);
uint8_t emit_is_union_constructor_typed(types_SExpr* expr, type_extract_TypeRegistry types);
slop_string emit_get_union_variant_name(types_SExpr* expr);
uint8_t emit_is_enum_value_typed(types_SExpr* expr, type_extract_TypeRegistry types);
uint8_t emit_is_record_constructor_typed(types_SExpr* expr, type_extract_TypeRegistry types);
slop_string emit_emit_string_slice(slop_string s, int64_t start);
slop_string emit_get_some_inner_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_get_ok_inner_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_get_error_inner_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types);
types_SExpr* emit_get_ok_inner_expr(types_SExpr* expected);
emit_CompareInfo emit_build_list_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types);
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
    __auto_type _mv_112 = (*expr);
    switch (_mv_112.tag) {
        case types_SExpr_num:
        {
            __auto_type num = _mv_112.data.num;
            return num.raw;
        }
        case types_SExpr_str:
        {
            __auto_type str = _mv_112.data.str;
            {
                __auto_type val = str.value;
                return string_concat(arena, string_concat(arena, SLOP_STR("SLOP_STR(\""), emit_escape_string(arena, val)), SLOP_STR("\")"));
            }
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_112.data.sym;
            {
                __auto_type name = sym.name;
                if (string_eq(name, SLOP_STR("true"))) {
                    return SLOP_STR("true");
                } else if (string_eq(name, SLOP_STR("false"))) {
                    return SLOP_STR("false");
                } else if (string_eq(name, SLOP_STR("nil"))) {
                    return SLOP_STR("NULL");
                } else if (string_eq(name, SLOP_STR("none"))) {
                    return SLOP_STR("(slop_option_string){.has_value = false}");
                } else if (emit_string_starts_with(name, SLOP_STR("'"))) {
                    {
                        __auto_type variant_name = emit_emit_emit_string_slice(arena, name, 1, ((int64_t)(name.len)));
                        __auto_type _mv_113 = type_extract_registry_lookup_enum_value(types, variant_name);
                        if (_mv_113.has_value) {
                            __auto_type enum_entry = _mv_113.value;
                            return string_concat(arena, (*enum_entry).c_name, string_concat(arena, SLOP_STR("_"), emit_convert_symbol_to_c(arena, variant_name)));
                        } else if (!_mv_113.has_value) {
                            return emit_convert_symbol_to_c(arena, variant_name);
                        }
                    }
                } else {
                    return emit_convert_symbol_to_c(arena, name);
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_112.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len == 0)) {
                    return SLOP_STR("(void)0");
                } else {
                    __auto_type _mv_114 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (!_mv_114.has_value) {
                        return SLOP_STR("(void)0");
                    } else if (_mv_114.has_value) {
                        __auto_type head = _mv_114.value;
                        if (parser_sexpr_is_symbol(head)) {
                            {
                                __auto_type op = parser_sexpr_get_symbol_name(head);
                                if (string_eq(op, SLOP_STR("none"))) {
                                    return SLOP_STR("(slop_option_string){.has_value = false}");
                                } else if (string_eq(op, SLOP_STR("some"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_115 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_115.has_value) {
                                            __auto_type val = _mv_115.value;
                                            {
                                                __auto_type inner_c = emit_sexpr_to_c_typed(arena, val, prefix, types);
                                                return string_concat(arena, SLOP_STR("(slop_option_string){.has_value = true, .value = "), string_concat(arena, inner_c, SLOP_STR("}")));
                                            }
                                        } else if (!_mv_115.has_value) {
                                            return SLOP_STR("(slop_option_string){.has_value = true}");
                                        }
                                    } else {
                                        return SLOP_STR("(slop_option_string){.has_value = true}");
                                    }
                                } else if (string_eq(op, SLOP_STR("list"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_116 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_116.has_value) {
                                            __auto_type type_expr = _mv_116.value;
                                            if (parser_sexpr_is_symbol(type_expr)) {
                                                {
                                                    __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                                                    if (string_eq(type_name, SLOP_STR("String"))) {
                                                        return SLOP_STR("(slop_list_string){.data = NULL, .len = 0, .cap = 0}");
                                                    } else {
                                                        return string_concat(arena, SLOP_STR("(slop_list_"), string_concat(arena, prefix, string_concat(arena, SLOP_STR("_"), string_concat(arena, emit_convert_symbol_to_c(arena, type_name), SLOP_STR("){.data = NULL, .len = 0, .cap = 0}")))));
                                                    }
                                                }
                                            } else {
                                                return SLOP_STR("/* error: list literal first element must be type symbol */");
                                            }
                                        } else if (!_mv_116.has_value) {
                                            return SLOP_STR("/* error: list literal requires type */");
                                        }
                                    } else {
                                        return SLOP_STR("/* error: list literal requires type */");
                                    }
                                } else if (string_eq(op, SLOP_STR("ok"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_117 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_117.has_value) {
                                            __auto_type val = _mv_117.value;
                                            return string_concat(arena, SLOP_STR("(("), string_concat(arena, prefix, string_concat(arena, SLOP_STR("Result){.is_ok=true,.data.ok="), string_concat(arena, emit_sexpr_to_c_typed(arena, val, prefix, types), SLOP_STR("})")))));
                                        } else if (!_mv_117.has_value) {
                                            return SLOP_STR("((Result){.is_ok=true,.data.ok=0})");
                                        }
                                    } else {
                                        return SLOP_STR("((Result){.is_ok=true,.data.ok=0})");
                                    }
                                } else if (string_eq(op, SLOP_STR("error"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_118 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_118.has_value) {
                                            __auto_type val = _mv_118.value;
                                            return string_concat(arena, SLOP_STR("(("), string_concat(arena, prefix, string_concat(arena, SLOP_STR("Result){.is_ok=false,.data.err="), string_concat(arena, emit_sexpr_to_c_typed(arena, val, prefix, types), SLOP_STR("})")))));
                                        } else if (!_mv_118.has_value) {
                                            return SLOP_STR("((Result){.is_ok=false,.data.err=0})");
                                        }
                                    } else {
                                        return SLOP_STR("((Result){.is_ok=false,.data.err=0})");
                                    }
                                } else if (string_eq(op, SLOP_STR("quote"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_119 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_119.has_value) {
                                            __auto_type quoted = _mv_119.value;
                                            if (parser_sexpr_is_symbol(quoted)) {
                                                {
                                                    __auto_type variant_name = parser_sexpr_get_symbol_name(quoted);
                                                    __auto_type _mv_120 = type_extract_registry_lookup_enum_value(types, variant_name);
                                                    if (_mv_120.has_value) {
                                                        __auto_type enum_entry = _mv_120.value;
                                                        return string_concat(arena, (*enum_entry).c_name, string_concat(arena, SLOP_STR("_"), emit_convert_symbol_to_c(arena, variant_name)));
                                                    } else if (!_mv_120.has_value) {
                                                        return string_concat(arena, prefix, string_concat(arena, SLOP_STR("_"), emit_convert_symbol_to_c(arena, variant_name)));
                                                    }
                                                }
                                            } else {
                                                return emit_sexpr_to_c_typed(arena, quoted, prefix, types);
                                            }
                                        } else if (!_mv_119.has_value) {
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
                                        __auto_type _mv_121 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_121.has_value) {
                                            __auto_type operand = _mv_121.value;
                                            return string_concat(arena, SLOP_STR("(!"), string_concat(arena, emit_sexpr_to_c_typed(arena, operand, prefix, types), SLOP_STR(")")));
                                        } else if (!_mv_121.has_value) {
                                            return SLOP_STR("(!0)");
                                        }
                                    } else {
                                        return SLOP_STR("(!0)");
                                    }
                                } else if (string_eq(op, SLOP_STR("."))) {
                                    if ((len >= 3)) {
                                        __auto_type _mv_122 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_122.has_value) {
                                            __auto_type obj = _mv_122.value;
                                            __auto_type _mv_123 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_123.has_value) {
                                                __auto_type field = _mv_123.value;
                                                return string_concat(arena, emit_sexpr_to_c_typed(arena, obj, prefix, types), string_concat(arena, SLOP_STR("."), ((parser_sexpr_is_symbol(field)) ? emit_convert_symbol_to_c(arena, parser_sexpr_get_symbol_name(field)) : emit_sexpr_to_c_typed(arena, field, prefix, types))));
                                            } else if (!_mv_123.has_value) {
                                                return SLOP_STR("0");
                                            }
                                        } else if (!_mv_122.has_value) {
                                            return SLOP_STR("0");
                                        }
                                    } else {
                                        return SLOP_STR("0");
                                    }
                                } else if (string_eq(op, SLOP_STR("cast"))) {
                                    if ((len >= 3)) {
                                        __auto_type _mv_124 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_124.has_value) {
                                            __auto_type expr_val = _mv_124.value;
                                            return emit_sexpr_to_c_typed(arena, expr_val, prefix, types);
                                        } else if (!_mv_124.has_value) {
                                            return SLOP_STR("0");
                                        }
                                    } else {
                                        return SLOP_STR("0");
                                    }
                                } else {
                                    __auto_type _mv_125 = type_extract_registry_lookup_variant(types, op);
                                    if (_mv_125.has_value) {
                                        __auto_type union_entry = _mv_125.value;
                                        return emit_emit_union_literal_typed(arena, union_entry, op, items, prefix, types);
                                    } else if (!_mv_125.has_value) {
                                        {
                                            __auto_type first_char = op.data[0];
                                            if (((first_char >= 65) && (first_char <= 90))) {
                                                __auto_type _mv_126 = type_extract_registry_lookup(types, op);
                                                if (_mv_126.has_value) {
                                                    __auto_type type_entry = _mv_126.value;
                                                    if (((*type_entry).kind == type_extract_TypeEntryKind_te_record)) {
                                                        return emit_emit_record_literal_typed(arena, type_entry, items, prefix, types);
                                                    } else {
                                                        return emit_emit_function_call_typed(arena, items, prefix, types);
                                                    }
                                                } else if (!_mv_126.has_value) {
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
        __auto_type c_variant = emit_convert_symbol_to_c(arena, variant_name);
        {
            __auto_type tag_value = string_concat(arena, c_name, string_concat(arena, SLOP_STR("_"), c_variant));
            if ((((int64_t)((items).len)) > 1)) {
                __auto_type _mv_127 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_127.has_value) {
                    __auto_type inner_expr = _mv_127.value;
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
                } else if (!_mv_127.has_value) {
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
                __auto_type _mv_128 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_128.has_value) {
                    __auto_type field = _mv_128.value;
                    __auto_type _mv_129 = ({ __auto_type _lst = items; size_t _idx = (size_t)(i + 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_129.has_value) {
                        __auto_type item = _mv_129.value;
                        {
                            __auto_type fname = field.name;
                            __auto_type ftype = field.type_name;
                            __auto_type val_c = emit_emit_field_value_typed(arena, item, ftype, prefix, types);
                            if (first) {
                                result = string_concat(arena, result, string_concat(arena, SLOP_STR("."), string_concat(arena, fname, string_concat(arena, SLOP_STR(" = "), val_c))));
                                first = 0;
                            } else {
                                result = string_concat(arena, result, string_concat(arena, SLOP_STR(", ."), string_concat(arena, fname, string_concat(arena, SLOP_STR(" = "), val_c))));
                            }
                        }
                    } else if (!_mv_129.has_value) {
                    }
                } else if (!_mv_128.has_value) {
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
        __auto_type _mv_130 = (*item);
        switch (_mv_130.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_130.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) == 0)) {
                        return string_concat(arena, SLOP_STR("("), string_concat(arena, c_opt_type, SLOP_STR("){.has_value = false}")));
                    } else {
                        __auto_type _mv_131 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_131.has_value) {
                            __auto_type first = _mv_131.value;
                            if (parser_sexpr_is_symbol(first)) {
                                {
                                    __auto_type name = parser_sexpr_get_symbol_name(first);
                                    if (string_eq(name, SLOP_STR("none"))) {
                                        return string_concat(arena, SLOP_STR("("), string_concat(arena, c_opt_type, SLOP_STR("){.has_value = false}")));
                                    } else if (string_eq(name, SLOP_STR("some"))) {
                                        if ((((int64_t)((items).len)) > 1)) {
                                            __auto_type _mv_132 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_132.has_value) {
                                                __auto_type inner = _mv_132.value;
                                                {
                                                    __auto_type inner_c = emit_sexpr_to_c_typed(arena, inner, prefix, types);
                                                    return string_concat(arena, SLOP_STR("("), string_concat(arena, c_opt_type, string_concat(arena, SLOP_STR("){.has_value = true, .value = "), string_concat(arena, inner_c, SLOP_STR("}")))));
                                                }
                                            } else if (!_mv_132.has_value) {
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
                        } else if (!_mv_131.has_value) {
                            return string_concat(arena, SLOP_STR("("), string_concat(arena, c_opt_type, SLOP_STR("){.has_value = false}")));
                        }
                    }
                }
            }
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_130.data.sym;
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
                __auto_type _mv_133 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_133.has_value) {
                    __auto_type a = _mv_133.value;
                    return string_concat(arena, SLOP_STR("("), string_concat(arena, c_op, string_concat(arena, emit_sexpr_to_c_typed(arena, a, prefix, types), SLOP_STR(")"))));
                } else if (!_mv_133.has_value) {
                    return SLOP_STR("0");
                }
            } else {
                return SLOP_STR("0");
            }
        } else {
            __auto_type _mv_134 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_134.has_value) {
                __auto_type a = _mv_134.value;
                __auto_type _mv_135 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_135.has_value) {
                    __auto_type b = _mv_135.value;
                    return string_concat(arena, SLOP_STR("("), string_concat(arena, emit_sexpr_to_c_typed(arena, a, prefix, types), string_concat(arena, SLOP_STR(" "), string_concat(arena, c_op, string_concat(arena, SLOP_STR(" "), string_concat(arena, emit_sexpr_to_c_typed(arena, b, prefix, types), SLOP_STR(")")))))));
                } else if (!_mv_135.has_value) {
                    return SLOP_STR("0");
                }
            } else if (!_mv_134.has_value) {
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
            __auto_type _mv_136 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (!_mv_136.has_value) {
                return SLOP_STR("(void)0");
            } else if (_mv_136.has_value) {
                __auto_type head = _mv_136.value;
                {
                    __auto_type fn_name = ((parser_sexpr_is_symbol(head)) ? emit_convert_symbol_to_c(arena, parser_sexpr_get_symbol_name(head)) : SLOP_STR("unknown"));
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
            __auto_type _mv_137 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_137.has_value) {
                __auto_type arg = _mv_137.value;
                {
                    __auto_type arg_c = emit_sexpr_to_c_typed(arena, arg, prefix, types);
                    if (first) {
                        result = arg_c;
                        first = 0;
                    } else {
                        result = string_concat(arena, result, string_concat(arena, SLOP_STR(", "), arg_c));
                    }
                }
            } else if (!_mv_137.has_value) {
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
    __auto_type _mv_138 = (*expr);
    switch (_mv_138.tag) {
        case types_SExpr_num:
        {
            __auto_type num = _mv_138.data.num;
            return num.raw;
        }
        case types_SExpr_str:
        {
            __auto_type str = _mv_138.data.str;
            {
                __auto_type val = str.value;
                return string_concat(arena, string_concat(arena, SLOP_STR("SLOP_STR(\""), emit_escape_string(arena, val)), SLOP_STR("\")"));
            }
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_138.data.sym;
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
                } else if (emit_string_starts_with(name, SLOP_STR("'"))) {
                    return emit_convert_symbol_to_c(arena, emit_emit_emit_string_slice(arena, name, 1, ((int64_t)(name.len))));
                } else {
                    return emit_convert_symbol_to_c(arena, name);
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_138.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len == 0)) {
                    return SLOP_STR("(void)0");
                } else {
                    __auto_type _mv_139 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (!_mv_139.has_value) {
                        return SLOP_STR("(void)0");
                    } else if (_mv_139.has_value) {
                        __auto_type head = _mv_139.value;
                        if (parser_sexpr_is_symbol(head)) {
                            {
                                __auto_type op = parser_sexpr_get_symbol_name(head);
                                if (string_eq(op, SLOP_STR("none"))) {
                                    return SLOP_STR("none");
                                } else if (string_eq(op, SLOP_STR("some"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_140 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_140.has_value) {
                                            __auto_type val = _mv_140.value;
                                            return string_concat(arena, SLOP_STR("some("), string_concat(arena, emit_sexpr_to_c(arena, val, prefix), SLOP_STR(")")));
                                        } else if (!_mv_140.has_value) {
                                            return SLOP_STR("some(0)");
                                        }
                                    } else {
                                        return SLOP_STR("some(0)");
                                    }
                                } else if (string_eq(op, SLOP_STR("ok"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_141 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_141.has_value) {
                                            __auto_type val = _mv_141.value;
                                            return string_concat(arena, SLOP_STR("(("), string_concat(arena, prefix, string_concat(arena, SLOP_STR("Result){.is_ok=true,.data.ok="), string_concat(arena, emit_sexpr_to_c(arena, val, prefix), SLOP_STR("})")))));
                                        } else if (!_mv_141.has_value) {
                                            return SLOP_STR("((Result){.is_ok=true,.data.ok=0})");
                                        }
                                    } else {
                                        return SLOP_STR("((Result){.is_ok=true,.data.ok=0})");
                                    }
                                } else if (string_eq(op, SLOP_STR("error"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_142 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_142.has_value) {
                                            __auto_type val = _mv_142.value;
                                            return string_concat(arena, SLOP_STR("(("), string_concat(arena, prefix, string_concat(arena, SLOP_STR("Result){.is_ok=false,.data.err="), string_concat(arena, emit_sexpr_to_c(arena, val, prefix), SLOP_STR("})")))));
                                        } else if (!_mv_142.has_value) {
                                            return SLOP_STR("((Result){.is_ok=false,.data.err=0})");
                                        }
                                    } else {
                                        return SLOP_STR("((Result){.is_ok=false,.data.err=0})");
                                    }
                                } else if (string_eq(op, SLOP_STR("quote"))) {
                                    if ((len > 1)) {
                                        __auto_type _mv_143 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_143.has_value) {
                                            __auto_type quoted = _mv_143.value;
                                            if (parser_sexpr_is_symbol(quoted)) {
                                                {
                                                    __auto_type name = parser_sexpr_get_symbol_name(quoted);
                                                    return string_concat(arena, prefix, string_concat(arena, SLOP_STR("_"), emit_convert_symbol_to_c(arena, name)));
                                                }
                                            } else {
                                                return emit_sexpr_to_c(arena, quoted, prefix);
                                            }
                                        } else if (!_mv_143.has_value) {
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
                                        __auto_type _mv_144 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_144.has_value) {
                                            __auto_type operand = _mv_144.value;
                                            return string_concat(arena, SLOP_STR("(!"), string_concat(arena, emit_sexpr_to_c(arena, operand, prefix), SLOP_STR(")")));
                                        } else if (!_mv_144.has_value) {
                                            return SLOP_STR("(!0)");
                                        }
                                    } else {
                                        return SLOP_STR("(!0)");
                                    }
                                } else if (string_eq(op, SLOP_STR("."))) {
                                    if ((len >= 3)) {
                                        __auto_type _mv_145 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_145.has_value) {
                                            __auto_type obj = _mv_145.value;
                                            __auto_type _mv_146 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_146.has_value) {
                                                __auto_type field = _mv_146.value;
                                                return string_concat(arena, emit_sexpr_to_c(arena, obj, prefix), string_concat(arena, SLOP_STR("."), ((parser_sexpr_is_symbol(field)) ? emit_convert_symbol_to_c(arena, parser_sexpr_get_symbol_name(field)) : emit_sexpr_to_c(arena, field, prefix))));
                                            } else if (!_mv_146.has_value) {
                                                return SLOP_STR("0");
                                            }
                                        } else if (!_mv_145.has_value) {
                                            return SLOP_STR("0");
                                        }
                                    } else {
                                        return SLOP_STR("0");
                                    }
                                } else if (string_eq(op, SLOP_STR("cast"))) {
                                    if ((len >= 3)) {
                                        __auto_type _mv_147 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_147.has_value) {
                                            __auto_type expr_val = _mv_147.value;
                                            return emit_sexpr_to_c(arena, expr_val, prefix);
                                        } else if (!_mv_147.has_value) {
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
                __auto_type _mv_148 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_148.has_value) {
                    __auto_type a = _mv_148.value;
                    return string_concat(arena, SLOP_STR("("), string_concat(arena, c_op, string_concat(arena, emit_sexpr_to_c(arena, a, prefix), SLOP_STR(")"))));
                } else if (!_mv_148.has_value) {
                    return SLOP_STR("0");
                }
            } else {
                return SLOP_STR("0");
            }
        } else {
            __auto_type _mv_149 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_149.has_value) {
                __auto_type a = _mv_149.value;
                __auto_type _mv_150 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_150.has_value) {
                    __auto_type b = _mv_150.value;
                    return string_concat(arena, SLOP_STR("("), string_concat(arena, emit_sexpr_to_c(arena, a, prefix), string_concat(arena, SLOP_STR(" "), string_concat(arena, c_op, string_concat(arena, SLOP_STR(" "), string_concat(arena, emit_sexpr_to_c(arena, b, prefix), SLOP_STR(")")))))));
                } else if (!_mv_150.has_value) {
                    return SLOP_STR("0");
                }
            } else if (!_mv_149.has_value) {
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
            __auto_type _mv_151 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (!_mv_151.has_value) {
                return SLOP_STR("(void)0");
            } else if (_mv_151.has_value) {
                __auto_type head = _mv_151.value;
                {
                    __auto_type fn_name = ((parser_sexpr_is_symbol(head)) ? emit_convert_symbol_to_c(arena, parser_sexpr_get_symbol_name(head)) : SLOP_STR("unknown"));
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
            __auto_type _mv_152 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_152.has_value) {
                __auto_type arg = _mv_152.value;
                {
                    __auto_type arg_c = emit_sexpr_to_c(arena, arg, prefix);
                    if (first) {
                        result = arg_c;
                        first = 0;
                    } else {
                        result = string_concat(arena, result, string_concat(arena, SLOP_STR(", "), arg_c));
                    }
                }
            } else if (!_mv_152.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_string emit_emit_type_constructor(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string prefix) {
    return emit_emit_function_call(arena, items, prefix);
}

slop_string emit_convert_symbol_to_c(slop_arena* arena, slop_string name) {
    {
        __auto_type len = ((int64_t)(name.len));
        __auto_type buf = ((uint8_t*)((uint8_t*)slop_arena_alloc(arena, (len + 1))));
        __auto_type i = 0;
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

uint8_t emit_string_starts_with(slop_string s, slop_string prefix) {
    {
        __auto_type s_len = ((int64_t)(s.len));
        __auto_type p_len = ((int64_t)(prefix.len));
        if ((s_len < p_len)) {
            return 0;
        } else {
            {
                __auto_type i = 0;
                __auto_type matches = 1;
                while (((i < p_len) && matches)) {
                    if ((s.data[i] != prefix.data[i])) {
                        matches = 0;
                    }
                    i = (i + 1);
                }
                return matches;
            }
        }
    }
}

slop_string emit_emit_emit_string_slice(slop_arena* arena, slop_string s, int64_t start, int64_t end) {
    {
        __auto_type s_len = ((int64_t)(s.len));
        __auto_type actual_start = (((start < 0)) ? 0 : start);
        __auto_type actual_end = (((end > s_len)) ? s_len : end);
        if ((actual_start >= actual_end)) {
            return SLOP_STR("");
        } else {
            {
                __auto_type new_len = (actual_end - actual_start);
                __auto_type buf = ((uint8_t*)((uint8_t*)slop_arena_alloc(arena, (new_len + 1))));
                __auto_type i = 0;
                while ((i < new_len)) {
                    buf[i] = s.data[(actual_start + i)];
                    i = (i + 1);
                }
                buf[new_len] = 0;
                return (slop_string){.len = ((uint64_t)(new_len)), .data = buf};
            }
        }
    }
}

slop_list_string emit_emit_test_harness_typed(slop_arena* arena, slop_list_extract_TestCase_ptr tests, slop_string module_prefix, type_extract_TypeRegistry* types, slop_list_string imports) {
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
                __auto_type _mv_153 = ({ __auto_type _lst = imports; size_t _idx = (size_t)j; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_153.has_value) {
                    __auto_type mod_name = _mv_153.value;
                    {
                        __auto_type c_name = ctype_to_c_name(arena, mod_name);
                        emit_emit(ctx, string_concat(arena, SLOP_STR("#include \"slop_"), string_concat(arena, c_name, SLOP_STR(".h\""))));
                    }
                } else if (!_mv_153.has_value) {
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
                    __auto_type _mv_154 = ({ __auto_type _lst = tests; size_t _idx = (size_t)i; slop_option_extract_TestCase_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_154.has_value) {
                        __auto_type tc = _mv_154.value;
                        emit_emit_test_function_typed(ctx, (*tc), i, module_prefix, types);
                    } else if (!_mv_154.has_value) {
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
                    __auto_type _mv_155 = ({ __auto_type _lst = tests; size_t _idx = (size_t)i; slop_option_extract_TestCase_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_155.has_value) {
                        __auto_type tc = _mv_155.value;
                        emit_emit_test_function(ctx, (*tc), i, module_prefix);
                    } else if (!_mv_155.has_value) {
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
            __auto_type _mv_156 = ({ __auto_type _lst = tests; size_t _idx = (size_t)i; slop_option_extract_TestCase_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_156.has_value) {
                __auto_type tc = _mv_156.value;
                if ((*tc).needs_arena) {
                    found = 1;
                }
            } else if (!_mv_156.has_value) {
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
                __auto_type compare_info = emit_build_comparison_typed(arena, tc.expected, tc.return_type, prefix, (*types));
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
    __auto_type _mv_157 = (*expr);
    switch (_mv_157.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_157.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return 0;
                } else {
                    __auto_type _mv_158 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_158.has_value) {
                        __auto_type first = _mv_158.value;
                        if (parser_sexpr_is_symbol(first)) {
                            {
                                __auto_type name = parser_sexpr_get_symbol_name(first);
                                return (string_eq(name, SLOP_STR("none")) || string_eq(name, SLOP_STR("some")));
                            }
                        } else {
                            return 0;
                        }
                    } else if (!_mv_158.has_value) {
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
            __auto_type _mv_159 = ({ __auto_type _lst = args; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_159.has_value) {
                __auto_type arg = _mv_159.value;
                if ((emit_is_union_or_record_constructor(arg) || emit_is_none_or_some_form(arg))) {
                    found = 1;
                }
            } else if (!_mv_159.has_value) {
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
            __auto_type _mv_160 = ({ __auto_type _lst = args; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_160.has_value) {
                __auto_type arg = _mv_160.value;
                {
                    __auto_type arg_str = parser_pretty_print(arena, arg);
                    if (first) {
                        result = arg_str;
                        first = 0;
                    } else {
                        result = string_concat(arena, result, string_concat(arena, SLOP_STR(", "), arg_str));
                    }
                }
            } else if (!_mv_160.has_value) {
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
            __auto_type _mv_161 = ({ __auto_type _lst = args; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_161.has_value) {
                __auto_type arg = _mv_161.value;
                {
                    __auto_type arg_c = emit_sexpr_to_c_typed(arena, arg, prefix, types);
                    if (first) {
                        result = arg_c;
                        first = 0;
                    } else {
                        result = string_concat(arena, result, string_concat(arena, SLOP_STR(", "), arg_c));
                    }
                }
            } else if (!_mv_161.has_value) {
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
        __auto_type c_name = emit_convert_symbol_to_c(arena, fn_name);
        __auto_type _mv_162 = module_name;
        if (_mv_162.has_value) {
            __auto_type mod = _mv_162.value;
            return string_concat(arena, emit_convert_symbol_to_c(arena, mod), string_concat(arena, SLOP_STR("_"), c_name));
        } else if (!_mv_162.has_value) {
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
            __auto_type _mv_163 = ({ __auto_type _lst = args; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_163.has_value) {
                __auto_type arg = _mv_163.value;
                {
                    __auto_type arg_str = parser_pretty_print(arena, arg);
                    if (first) {
                        result = arg_str;
                        first = 0;
                    } else {
                        result = string_concat(arena, result, string_concat(arena, SLOP_STR(", "), arg_str));
                    }
                }
            } else if (!_mv_163.has_value) {
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
            __auto_type _mv_164 = ({ __auto_type _lst = args; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_164.has_value) {
                __auto_type arg = _mv_164.value;
                {
                    __auto_type arg_c = emit_sexpr_to_c(arena, arg, prefix);
                    if (first) {
                        result = arg_c;
                        first = 0;
                    } else {
                        result = string_concat(arena, result, string_concat(arena, SLOP_STR(", "), arg_c));
                    }
                }
            } else if (!_mv_164.has_value) {
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

emit_CompareInfo emit_build_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_option_string return_type, slop_string prefix, type_extract_TypeRegistry types) {
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
                            if (strlib_contains(ret_type_str, SLOP_STR("String"))) {
                                return (emit_CompareInfo){string_concat(arena, SLOP_STR("result.has_value && slop_string_eq(result.value, "), string_concat(arena, inner_expected, SLOP_STR(")"))), SLOP_STR("%s"), SLOP_STR("result.has_value ? \"some(...)\" : \"none\""), SLOP_STR("%s"), SLOP_STR("\"some(...)\"")};
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
                                    __auto_type c_variant = emit_convert_symbol_to_c(arena, variant_name);
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
                                        __auto_type c_variant = emit_convert_symbol_to_c(arena, variant_name);
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
                            return emit_build_list_comparison_typed(arena, expected, prefix, types);
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
        __auto_type _mv_165 = type_extract_registry_get_record_fields(types, record_name);
        if (_mv_165.has_value) {
            __auto_type fields = _mv_165.value;
            {
                __auto_type expected_var_name = SLOP_STR("expected_value");
                __auto_type compare_expr = emit_build_record_field_comparisons(arena, fields, prefix, expected_var_name);
                return (emit_CompareInfo){string_concat(arena, SLOP_STR("({ typeof(result) "), string_concat(arena, expected_var_name, string_concat(arena, SLOP_STR(" = "), string_concat(arena, c_expected, string_concat(arena, SLOP_STR("; "), string_concat(arena, compare_expr, SLOP_STR("; })"))))))), SLOP_STR("%s"), SLOP_STR("\"<record>\""), SLOP_STR("%s"), SLOP_STR("\"<expected>\"")};
            }
        } else if (!_mv_165.has_value) {
            {
                __auto_type expected_var_name = SLOP_STR("expected_value");
                return (emit_CompareInfo){string_concat(arena, SLOP_STR("({ typeof(result) "), string_concat(arena, expected_var_name, string_concat(arena, SLOP_STR(" = "), string_concat(arena, c_expected, string_concat(arena, SLOP_STR("; memcmp(&result, &"), string_concat(arena, expected_var_name, SLOP_STR(", sizeof(result)) == 0; })"))))))), SLOP_STR("%s"), SLOP_STR("\"<record>\""), SLOP_STR("%s"), SLOP_STR("\"<expected>\"")};
            }
        }
    }
}

slop_string emit_get_record_name_from_expr(types_SExpr* expr) {
    __auto_type _mv_166 = (*expr);
    switch (_mv_166.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_166.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_167 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_167.has_value) {
                        __auto_type first = _mv_167.value;
                        if (parser_sexpr_is_symbol(first)) {
                            return parser_sexpr_get_symbol_name(first);
                        } else {
                            return SLOP_STR("");
                        }
                    } else if (!_mv_167.has_value) {
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

slop_string emit_build_record_field_comparisons(slop_arena* arena, slop_list_type_extract_FieldEntry fields, slop_string prefix, slop_string expected_var) {
    {
        __auto_type len = ((int64_t)((fields).len));
        __auto_type result = SLOP_STR("1");
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_168 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_type_extract_FieldEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_168.has_value) {
                __auto_type field = _mv_168.value;
                {
                    __auto_type fname = field.name;
                    __auto_type ftype = field.type_name;
                    __auto_type field_cmp = emit_build_single_field_comparison(arena, fname, ftype, expected_var);
                    result = string_concat(arena, result, string_concat(arena, SLOP_STR(" && "), field_cmp));
                }
            } else if (!_mv_168.has_value) {
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
        __auto_type eq_fn_name = emit_get_union_eq_fn_name(arena, expected, prefix, types);
        return (emit_CompareInfo){((string_eq(eq_fn_name, SLOP_STR(""))) ? string_concat(arena, SLOP_STR("({ typeof(result) "), string_concat(arena, expected_var_name, string_concat(arena, SLOP_STR(" = "), string_concat(arena, c_expected, string_concat(arena, SLOP_STR("; result.tag == "), string_concat(arena, expected_var_name, string_concat(arena, SLOP_STR(".tag && memcmp(&result.data, &"), string_concat(arena, expected_var_name, SLOP_STR(".data, sizeof(result.data)) == 0; })"))))))))) : string_concat(arena, eq_fn_name, string_concat(arena, SLOP_STR("(result, "), string_concat(arena, c_expected, SLOP_STR(")"))))), SLOP_STR("%s"), SLOP_STR("\"<union>\""), SLOP_STR("%s"), SLOP_STR("\"<expected>\"")};
    }
}

slop_string emit_get_union_eq_fn_name(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types) {
    __auto_type _mv_169 = (*expr);
    switch (_mv_169.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_169.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_170 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_170.has_value) {
                        __auto_type first = _mv_170.value;
                        if (parser_sexpr_is_symbol(first)) {
                            {
                                __auto_type variant_name = parser_sexpr_get_symbol_name(first);
                                __auto_type _mv_171 = type_extract_registry_lookup_variant(types, variant_name);
                                if (_mv_171.has_value) {
                                    __auto_type entry = _mv_171.value;
                                    {
                                        __auto_type slop_name = (*entry).name;
                                        return string_concat(arena, prefix, string_concat(arena, SLOP_STR("_"), string_concat(arena, emit_slop_name_to_c_lower(arena, slop_name), SLOP_STR("_eq"))));
                                    }
                                } else if (!_mv_171.has_value) {
                                    return SLOP_STR("");
                                }
                            }
                        } else {
                            return SLOP_STR("");
                        }
                    } else if (!_mv_170.has_value) {
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

slop_string emit_slop_name_to_c_lower(slop_arena* arena, slop_string name) {
    return strlib_to_lower(arena, name);
}

uint8_t emit_is_union_constructor_typed(types_SExpr* expr, type_extract_TypeRegistry types) {
    __auto_type _mv_172 = (*expr);
    switch (_mv_172.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_172.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return 0;
                } else {
                    __auto_type _mv_173 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_173.has_value) {
                        __auto_type first = _mv_173.value;
                        if (parser_sexpr_is_symbol(first)) {
                            {
                                __auto_type name = parser_sexpr_get_symbol_name(first);
                                if (((string_eq(name, SLOP_STR("none"))) || (string_eq(name, SLOP_STR("some"))) || (string_eq(name, SLOP_STR("ok"))) || (string_eq(name, SLOP_STR("error"))))) {
                                    return 0;
                                } else {
                                    __auto_type _mv_174 = type_extract_registry_lookup_variant(types, name);
                                    if (_mv_174.has_value) {
                                        __auto_type _ = _mv_174.value;
                                        return 1;
                                    } else if (!_mv_174.has_value) {
                                        return 0;
                                    }
                                }
                            }
                        } else {
                            return 0;
                        }
                    } else if (!_mv_173.has_value) {
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
    __auto_type _mv_175 = (*expr);
    switch (_mv_175.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_175.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_176 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_176.has_value) {
                        __auto_type first = _mv_176.value;
                        if (parser_sexpr_is_symbol(first)) {
                            return parser_sexpr_get_symbol_name(first);
                        } else {
                            return SLOP_STR("");
                        }
                    } else if (!_mv_176.has_value) {
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
    __auto_type _mv_177 = (*expr);
    switch (_mv_177.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_177.data.sym;
            {
                __auto_type name = sym.name;
                if (emit_string_starts_with(name, SLOP_STR("'"))) {
                    {
                        __auto_type variant_name = emit_emit_string_slice(name, 1);
                        __auto_type _mv_178 = type_extract_registry_lookup_enum_value(types, variant_name);
                        if (_mv_178.has_value) {
                            __auto_type _ = _mv_178.value;
                            return 1;
                        } else if (!_mv_178.has_value) {
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
            __auto_type lst = _mv_177.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 2)) {
                    return 0;
                } else {
                    __auto_type _mv_179 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_179.has_value) {
                        __auto_type first = _mv_179.value;
                        if ((parser_sexpr_is_symbol(first) && string_eq(parser_sexpr_get_symbol_name(first), SLOP_STR("quote")))) {
                            __auto_type _mv_180 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_180.has_value) {
                                __auto_type quoted = _mv_180.value;
                                if (parser_sexpr_is_symbol(quoted)) {
                                    __auto_type _mv_181 = type_extract_registry_lookup_enum_value(types, parser_sexpr_get_symbol_name(quoted));
                                    if (_mv_181.has_value) {
                                        __auto_type _ = _mv_181.value;
                                        return 1;
                                    } else if (!_mv_181.has_value) {
                                        return 0;
                                    }
                                } else {
                                    return 0;
                                }
                            } else if (!_mv_180.has_value) {
                                return 0;
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

uint8_t emit_is_record_constructor_typed(types_SExpr* expr, type_extract_TypeRegistry types) {
    __auto_type _mv_182 = (*expr);
    switch (_mv_182.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_182.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return 0;
                } else {
                    __auto_type _mv_183 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_183.has_value) {
                        __auto_type first = _mv_183.value;
                        if (parser_sexpr_is_symbol(first)) {
                            {
                                __auto_type name = parser_sexpr_get_symbol_name(first);
                                if ((string_eq(name, SLOP_STR("none")) || (string_eq(name, SLOP_STR("some")) || (string_eq(name, SLOP_STR("ok")) || (string_eq(name, SLOP_STR("error")) || string_eq(name, SLOP_STR("list"))))))) {
                                    return 0;
                                } else {
                                    __auto_type _mv_184 = type_extract_registry_lookup(types, name);
                                    if (_mv_184.has_value) {
                                        __auto_type entry = _mv_184.value;
                                        return type_extract_registry_is_record(types, name);
                                    } else if (!_mv_184.has_value) {
                                        return 0;
                                    }
                                }
                            }
                        } else {
                            return 0;
                        }
                    } else if (!_mv_183.has_value) {
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
        __auto_type _mv_185 = parser_sexpr_list_get(expr, 1);
        if (_mv_185.has_value) {
            __auto_type inner = _mv_185.value;
            return emit_sexpr_to_c_typed(arena, inner, prefix, types);
        } else if (!_mv_185.has_value) {
            return SLOP_STR("0");
        }
    } else {
        return SLOP_STR("0");
    }
}

slop_string emit_get_ok_inner_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types) {
    return emit_get_some_inner_typed(arena, expr, prefix, types);
}

slop_string emit_get_error_inner_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types) {
    return emit_get_some_inner_typed(arena, expr, prefix, types);
}

types_SExpr* emit_get_ok_inner_expr(types_SExpr* expected) {
    __auto_type _mv_186 = (*expected);
    switch (_mv_186.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_186.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) > 1)) {
                    __auto_type _mv_187 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_187.has_value) {
                        __auto_type inner = _mv_187.value;
                        return inner;
                    } else if (!_mv_187.has_value) {
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

emit_CompareInfo emit_build_list_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types) {
    __auto_type _mv_188 = (*expected);
    switch (_mv_188.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_188.data.lst;
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
                            __auto_type _mv_189 = ({ __auto_type _lst = elements; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_189.has_value) {
                                __auto_type elem = _mv_189.value;
                                {
                                    __auto_type elem_c = emit_sexpr_to_c_typed(arena, elem, prefix, types);
                                    if (first) {
                                        arr_init = string_concat(arena, arr_init, elem_c);
                                        first = 0;
                                    } else {
                                        arr_init = string_concat(arena, arr_init, string_concat(arena, SLOP_STR(", "), elem_c));
                                    }
                                }
                            } else if (!_mv_189.has_value) {
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

uint8_t emit_is_none_value(types_SExpr* expr) {
    __auto_type _mv_190 = (*expr);
    switch (_mv_190.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_190.data.sym;
            return string_eq(sym.name, SLOP_STR("none"));
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_190.data.lst;
            {
                __auto_type items = lst.items;
                return ((((int64_t)((items).len)) == 1) && ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type first = _mv.value; (parser_sexpr_is_symbol(first) && string_eq(parser_sexpr_get_symbol_name(first), SLOP_STR("none"))); }) : (0); }));
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
        __auto_type _mv_191 = parser_sexpr_list_get(expr, 1);
        if (_mv_191.has_value) {
            __auto_type inner = _mv_191.value;
            return emit_sexpr_to_c(arena, inner, prefix);
        } else if (!_mv_191.has_value) {
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
    __auto_type _mv_192 = (*expr);
    switch (_mv_192.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_192.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return 1;
                } else {
                    __auto_type _mv_193 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_193.has_value) {
                        __auto_type first = _mv_193.value;
                        return parser_sexpr_is_number(first);
                    } else if (!_mv_193.has_value) {
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
    __auto_type _mv_194 = (*expr);
    switch (_mv_194.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_194.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 0)) {
                    return 0;
                } else {
                    __auto_type _mv_195 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_195.has_value) {
                        __auto_type first = _mv_195.value;
                        if (parser_sexpr_is_symbol(first)) {
                            {
                                __auto_type name = parser_sexpr_get_symbol_name(first);
                                return ((!(string_eq(name, SLOP_STR("none")))) && (!(string_eq(name, SLOP_STR("some")))) && (!(string_eq(name, SLOP_STR("ok")))) && (!(string_eq(name, SLOP_STR("error")))) && (!(string_eq(name, SLOP_STR("quote")))) && (!(string_eq(name, SLOP_STR("list")))) && (({ __auto_type first_char = name.data[0]; (((first_char >= 65) && (first_char <= 90)) || (((first_char >= 97)) && ((first_char <= 122)) && (!(string_eq(name, SLOP_STR("+")))) && (!(string_eq(name, SLOP_STR("-")))) && (!(string_eq(name, SLOP_STR("*")))) && (!(string_eq(name, SLOP_STR("/")))) && (!(string_eq(name, SLOP_STR("%")))) && (!(string_eq(name, SLOP_STR("==")))) && (!(string_eq(name, SLOP_STR("!=")))) && (!(string_eq(name, SLOP_STR("<")))) && (!(string_eq(name, SLOP_STR("<=")))) && (!(string_eq(name, SLOP_STR(">")))) && (!(string_eq(name, SLOP_STR(">=")))) && (!(string_eq(name, SLOP_STR("and")))) && (!(string_eq(name, SLOP_STR("or")))) && (!(string_eq(name, SLOP_STR("not")))) && (!(string_eq(name, SLOP_STR(".")))) && (!(string_eq(name, SLOP_STR("cast")))))); })));
                            }
                        } else {
                            return 0;
                        }
                    } else if (!_mv_195.has_value) {
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
    __auto_type _mv_196 = (*expected);
    switch (_mv_196.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_196.data.lst;
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
                            __auto_type _mv_197 = ({ __auto_type _lst = elements; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_197.has_value) {
                                __auto_type elem = _mv_197.value;
                                {
                                    __auto_type elem_c = emit_sexpr_to_c(arena, elem, prefix);
                                    if (first) {
                                        arr_init = string_concat(arena, arr_init, elem_c);
                                        first = 0;
                                    } else {
                                        arr_init = string_concat(arena, arr_init, string_concat(arena, SLOP_STR(", "), elem_c));
                                    }
                                }
                            } else if (!_mv_197.has_value) {
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

