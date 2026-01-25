#include "../runtime/slop_runtime.h"
#include "slop_defn.h"

uint8_t defn_is_type_form(types_SExpr* expr);
uint8_t defn_is_function_form(types_SExpr* expr);
uint8_t defn_is_const_form(types_SExpr* expr);
uint8_t defn_is_ffi_form(types_SExpr* expr);
uint8_t defn_is_ffi_struct_form(types_SExpr* expr);
uint8_t defn_is_pointer_type_expr(types_SExpr* type_expr);
void defn_transpile_const(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_exported);
void defn_emit_const_def(context_TranspileContext* ctx, slop_string c_name, types_SExpr* type_expr, types_SExpr* value_expr, uint8_t is_exported);
slop_string defn_get_type_name_str(types_SExpr* type_expr);
uint8_t defn_is_int_type(slop_string type_name);
slop_string defn_eval_const_value(context_TranspileContext* ctx, types_SExpr* expr);
void defn_transpile_ffi(context_TranspileContext* ctx, types_SExpr* expr);
void defn_transpile_ffi_struct(context_TranspileContext* ctx, types_SExpr* expr);
uint8_t defn_is_string_expr(slop_list_types_SExpr_ptr items, int64_t idx);
uint8_t defn_ends_with_t(slop_string name);
void defn_transpile_type(context_TranspileContext* ctx, types_SExpr* expr);
void defn_dispatch_type_def(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, types_SExpr* type_def);
uint8_t defn_has_payload_variants(slop_list_types_SExpr_ptr items);
void defn_transpile_record(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, types_SExpr* expr);
void defn_emit_record_fields(context_TranspileContext* ctx, slop_string raw_type_name, slop_string qualified_type_name, slop_list_types_SExpr_ptr items, int64_t start_idx);
void defn_emit_record_field(context_TranspileContext* ctx, slop_string raw_type_name, slop_string qualified_type_name, types_SExpr* field);
void defn_transpile_enum(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, types_SExpr* expr);
void defn_emit_enum_values(context_TranspileContext* ctx, slop_string type_name, slop_list_types_SExpr_ptr items, int64_t start_idx, int64_t len);
void defn_transpile_union(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, types_SExpr* expr);
void defn_emit_union_variants(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start_idx);
void defn_emit_tag_constants(context_TranspileContext* ctx, slop_string type_name, slop_list_types_SExpr_ptr items, int64_t start_idx);
void defn_transpile_type_alias(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, types_SExpr* type_expr);
uint8_t defn_is_array_type(types_SExpr* type_expr);
void defn_emit_array_typedef(context_TranspileContext* ctx, slop_string qualified_name, types_SExpr* type_expr);
slop_string defn_get_number_as_string(types_SExpr* expr);
uint8_t defn_is_range_type(types_SExpr* type_expr);
types_RangeBounds defn_parse_range_bounds(types_SExpr* type_expr);
int64_t defn_string_to_int(slop_string s);
slop_string defn_select_smallest_c_type(int64_t min_val, int64_t max_val, uint8_t has_min, uint8_t has_max);
void defn_emit_range_typedef(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, types_SExpr* type_expr);
void defn_transpile_function(context_TranspileContext* ctx, types_SExpr* expr);
void defn_emit_function_def(context_TranspileContext* ctx, slop_string raw_name, slop_string fn_name, types_SExpr* params_expr, slop_list_types_SExpr_ptr items, uint8_t is_public_api);
void defn_bind_params_to_scope(context_TranspileContext* ctx, types_SExpr* params_expr);
void defn_bind_single_param(context_TranspileContext* ctx, types_SExpr* param);
uint8_t defn_is_pointer_type(types_SExpr* type_expr);
slop_list_context_FuncParamType_ptr defn_collect_param_types(context_TranspileContext* ctx, types_SExpr* params_expr);
slop_string defn_get_param_c_type(context_TranspileContext* ctx, types_SExpr* param);
void defn_emit_forward_declaration(context_TranspileContext* ctx, types_SExpr* expr);
slop_string defn_get_return_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
uint8_t defn_is_spec_form(types_SExpr* expr);
slop_string defn_extract_spec_return_type(context_TranspileContext* ctx, types_SExpr* spec_expr);
slop_option_string defn_get_result_type_name(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_option_string defn_extract_result_type_name(context_TranspileContext* ctx, types_SExpr* spec_expr);
slop_option_string defn_check_result_type(context_TranspileContext* ctx, types_SExpr* type_expr);
slop_string defn_build_result_name(slop_arena* arena, slop_string ok_type, slop_string err_type);
slop_string defn_build_param_str(context_TranspileContext* ctx, types_SExpr* params_expr);
slop_string defn_build_single_param(context_TranspileContext* ctx, types_SExpr* param);
uint8_t defn_is_param_mode(slop_list_types_SExpr_ptr items);
uint8_t defn_is_fn_type(types_SExpr* type_expr);
slop_string defn_emit_fn_param_type(context_TranspileContext* ctx, types_SExpr* type_expr, slop_string param_name);
slop_string defn_build_fn_args_str_for_param(context_TranspileContext* ctx, types_SExpr* args_expr);
void defn_emit_function_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
uint8_t defn_is_c_name_attr(types_SExpr* expr);
uint8_t defn_is_last_body_item(slop_list_types_SExpr_ptr items, int64_t current_i);
uint8_t defn_is_c_name_attr_at(slop_list_types_SExpr_ptr items, int64_t idx);
int64_t defn_find_body_start(slop_list_types_SExpr_ptr items);
uint8_t defn_is_annotation(types_SExpr* expr);
uint8_t defn_is_pre_form(types_SExpr* expr);
uint8_t defn_is_post_form(types_SExpr* expr);
uint8_t defn_is_assume_form(types_SExpr* expr);
slop_option_types_SExpr_ptr defn_get_annotation_condition(types_SExpr* expr);
slop_list_types_SExpr_ptr defn_collect_preconditions(slop_arena* arena, slop_list_types_SExpr_ptr items);
slop_list_types_SExpr_ptr defn_collect_postconditions(slop_arena* arena, slop_list_types_SExpr_ptr items);
slop_list_types_SExpr_ptr defn_collect_assumptions(slop_arena* arena, slop_list_types_SExpr_ptr items);
uint8_t defn_has_postconditions(slop_list_types_SExpr_ptr items);
void defn_emit_preconditions(context_TranspileContext* ctx, slop_list_types_SExpr_ptr preconditions);
void defn_emit_postconditions(context_TranspileContext* ctx, slop_list_types_SExpr_ptr postconditions);
void defn_emit_assumptions(context_TranspileContext* ctx, slop_list_types_SExpr_ptr assumptions);
slop_string defn_escape_for_c_string(slop_arena* arena, slop_string s);

uint8_t defn_is_type_form(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_685 = (*expr);
    switch (_mv_685.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_685.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_686 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_686.has_value) {
                        __auto_type head = _mv_686.value;
                        __auto_type _mv_687 = (*head);
                        switch (_mv_687.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_687.data.sym;
                                return string_eq(sym.name, SLOP_STR("type"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_686.has_value) {
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

uint8_t defn_is_function_form(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_688 = (*expr);
    switch (_mv_688.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_688.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_689 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_689.has_value) {
                        __auto_type head = _mv_689.value;
                        __auto_type _mv_690 = (*head);
                        switch (_mv_690.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_690.data.sym;
                                return string_eq(sym.name, SLOP_STR("fn"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_689.has_value) {
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

uint8_t defn_is_const_form(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_691 = (*expr);
    switch (_mv_691.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_691.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_692 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_692.has_value) {
                        __auto_type head = _mv_692.value;
                        __auto_type _mv_693 = (*head);
                        switch (_mv_693.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_693.data.sym;
                                return string_eq(sym.name, SLOP_STR("const"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_692.has_value) {
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

uint8_t defn_is_ffi_form(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_694 = (*expr);
    switch (_mv_694.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_694.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_695 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_695.has_value) {
                        __auto_type head = _mv_695.value;
                        __auto_type _mv_696 = (*head);
                        switch (_mv_696.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_696.data.sym;
                                return string_eq(sym.name, SLOP_STR("ffi"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_695.has_value) {
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

uint8_t defn_is_ffi_struct_form(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_697 = (*expr);
    switch (_mv_697.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_697.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_698 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_698.has_value) {
                        __auto_type head = _mv_698.value;
                        __auto_type _mv_699 = (*head);
                        switch (_mv_699.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_699.data.sym;
                                return string_eq(sym.name, SLOP_STR("ffi-struct"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_698.has_value) {
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

uint8_t defn_is_pointer_type_expr(types_SExpr* type_expr) {
    __auto_type _mv_700 = (*type_expr);
    switch (_mv_700.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_700.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_701 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_701.has_value) {
                        __auto_type head = _mv_701.value;
                        __auto_type _mv_702 = (*head);
                        switch (_mv_702.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_702.data.sym;
                                return (string_eq(sym.name, SLOP_STR("Ptr")) || string_eq(sym.name, SLOP_STR("ScopedPtr")));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_701.has_value) {
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

void defn_transpile_const(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_exported) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_703 = (*expr);
        switch (_mv_703.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_703.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 4)) {
                        context_ctx_fail(ctx, SLOP_STR("invalid const: need name, type, value"));
                    } else {
                        __auto_type _mv_704 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_704.has_value) {
                            __auto_type name_expr = _mv_704.value;
                            __auto_type _mv_705 = (*name_expr);
                            switch (_mv_705.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_705.data.sym;
                                    {
                                        __auto_type raw_name = name_sym.name;
                                        __auto_type base_name = ctype_to_c_name(arena, raw_name);
                                        __auto_type c_name = context_ctx_prefix_type(ctx, base_name);
                                        context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, SLOP_STR("auto"), SLOP_STR(""), 0, 0});
                                        __auto_type _mv_706 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_706.has_value) {
                                            __auto_type type_expr = _mv_706.value;
                                            __auto_type _mv_707 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_707.has_value) {
                                                __auto_type value_expr = _mv_707.value;
                                                defn_emit_const_def(ctx, c_name, type_expr, value_expr, is_exported);
                                            } else if (!_mv_707.has_value) {
                                                context_ctx_fail(ctx, SLOP_STR("missing const value"));
                                            }
                                        } else if (!_mv_706.has_value) {
                                            context_ctx_fail(ctx, SLOP_STR("missing const type"));
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    context_ctx_fail(ctx, SLOP_STR("const name must be symbol"));
                                    break;
                                }
                            }
                        } else if (!_mv_704.has_value) {
                            context_ctx_fail(ctx, SLOP_STR("missing const name"));
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_fail(ctx, SLOP_STR("invalid const form"));
                break;
            }
        }
    }
}

void defn_emit_const_def(context_TranspileContext* ctx, slop_string c_name, types_SExpr* type_expr, types_SExpr* value_expr, uint8_t is_exported) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    SLOP_PRE(((value_expr != NULL)), "(!= value-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
        __auto_type type_name = defn_get_type_name_str(type_expr);
        if (defn_is_int_type(type_name)) {
            if (!(is_exported)) {
                {
                    __auto_type value_c = defn_eval_const_value(ctx, value_expr);
                    context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("#define "), c_name, SLOP_STR(" ("), context_ctx_str(ctx, value_c, SLOP_STR(")"))));
                }
            }
        } else {
            {
                __auto_type storage = ((is_exported) ? SLOP_STR("const ") : SLOP_STR("static const "));
                if (string_eq(type_name, SLOP_STR("String"))) {
                    __auto_type _mv_708 = (*value_expr);
                    switch (_mv_708.tag) {
                        case types_SExpr_str:
                        {
                            __auto_type str = _mv_708.data.str;
                            context_ctx_emit(ctx, context_ctx_str5(ctx, storage, c_type, SLOP_STR(" "), c_name, context_ctx_str3(ctx, SLOP_STR(" = SLOP_STR(\""), str.value, SLOP_STR("\");"))));
                            break;
                        }
                        default: {
                            {
                                __auto_type value_c = defn_eval_const_value(ctx, value_expr);
                                context_ctx_emit(ctx, context_ctx_str5(ctx, storage, c_type, SLOP_STR(" "), c_name, context_ctx_str3(ctx, SLOP_STR(" = "), value_c, SLOP_STR(";"))));
                            }
                            break;
                        }
                    }
                } else {
                    {
                        __auto_type value_c = defn_eval_const_value(ctx, value_expr);
                        context_ctx_emit(ctx, context_ctx_str5(ctx, storage, c_type, SLOP_STR(" "), c_name, context_ctx_str3(ctx, SLOP_STR(" = "), value_c, SLOP_STR(";"))));
                    }
                }
            }
        }
    }
}

slop_string defn_get_type_name_str(types_SExpr* type_expr) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_709 = (*type_expr);
    switch (_mv_709.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_709.data.sym;
            return sym.name;
        }
        default: {
            return SLOP_STR("");
        }
    }
}

uint8_t defn_is_int_type(slop_string type_name) {
    return ((string_eq(type_name, SLOP_STR("Int"))) || (string_eq(type_name, SLOP_STR("I8"))) || (string_eq(type_name, SLOP_STR("I16"))) || (string_eq(type_name, SLOP_STR("I32"))) || (string_eq(type_name, SLOP_STR("I64"))) || (string_eq(type_name, SLOP_STR("U8"))) || (string_eq(type_name, SLOP_STR("U16"))) || (string_eq(type_name, SLOP_STR("U32"))) || (string_eq(type_name, SLOP_STR("U64"))));
}

slop_string defn_eval_const_value(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_710 = (*expr);
        switch (_mv_710.tag) {
            case types_SExpr_num:
            {
                __auto_type num = _mv_710.data.num;
                return num.raw;
            }
            case types_SExpr_str:
            {
                __auto_type str = _mv_710.data.str;
                return context_ctx_str3(ctx, SLOP_STR("\""), str.value, SLOP_STR("\""));
            }
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_710.data.sym;
                return ctype_to_c_name(arena, sym.name);
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_710.data.lst;
                return expr_transpile_expr(ctx, expr);
            }
        }
    }
}

void defn_transpile_ffi(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
}

void defn_transpile_ffi_struct(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_711 = (*expr);
        switch (_mv_711.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_711.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    {
                        __auto_type name_idx = ((((len >= 2) && defn_is_string_expr(items, 1))) ? 2 : 1);
                        if ((len >= (name_idx + 1))) {
                            __auto_type _mv_712 = ({ __auto_type _lst = items; size_t _idx = (size_t)name_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_712.has_value) {
                                __auto_type name_expr = _mv_712.value;
                                __auto_type _mv_713 = (*name_expr);
                                switch (_mv_713.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_713.data.sym;
                                        {
                                            __auto_type type_name = sym.name;
                                            __auto_type c_name = ctype_to_c_name(arena, type_name);
                                            {
                                                __auto_type actual_c_name = ((defn_ends_with_t(type_name)) ? c_name : context_ctx_str(ctx, SLOP_STR("struct "), c_name));
                                                context_ctx_register_type(ctx, (context_TypeEntry){type_name, c_name, actual_c_name, 0, 1, 0});
                                            }
                                        }
                                        break;
                                    }
                                    default: {
                                        break;
                                    }
                                }
                            } else if (!_mv_712.has_value) {
                            }
                        }
                    }
                }
                break;
            }
            default: {
                break;
            }
        }
    }
}

uint8_t defn_is_string_expr(slop_list_types_SExpr_ptr items, int64_t idx) {
    __auto_type _mv_714 = ({ __auto_type _lst = items; size_t _idx = (size_t)idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
    if (_mv_714.has_value) {
        __auto_type item = _mv_714.value;
        __auto_type _mv_715 = (*item);
        switch (_mv_715.tag) {
            case types_SExpr_str:
            {
                __auto_type _ = _mv_715.data.str;
                return 1;
            }
            default: {
                return 0;
            }
        }
    } else if (!_mv_714.has_value) {
        return 0;
    }
}

uint8_t defn_ends_with_t(slop_string name) {
    return strlib_ends_with(name, SLOP_STR("_t"));
}

void defn_transpile_type(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_716 = (*expr);
        switch (_mv_716.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_716.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 3)) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid type: need name and definition"), context_sexpr_line(expr), context_sexpr_col(expr));
                    } else {
                        __auto_type _mv_717 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_717.has_value) {
                            __auto_type name_expr = _mv_717.value;
                            __auto_type _mv_718 = (*name_expr);
                            switch (_mv_718.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_718.data.sym;
                                    {
                                        __auto_type raw_name = name_sym.name;
                                        __auto_type base_name = ctype_to_c_name(arena, raw_name);
                                        __auto_type qualified_name = ((context_ctx_prefixing_enabled(ctx)) ? ({ __auto_type _mv = context_ctx_get_module(ctx); _mv.has_value ? ({ __auto_type mod_name = _mv.value; context_ctx_str(ctx, ctype_to_c_name(arena, mod_name), context_ctx_str(ctx, SLOP_STR("_"), base_name)); }) : (base_name); }) : base_name);
                                        __auto_type _mv_719 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_719.has_value) {
                                            __auto_type type_def = _mv_719.value;
                                            defn_dispatch_type_def(ctx, raw_name, qualified_name, type_def);
                                        } else if (!_mv_719.has_value) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("missing type definition"), context_sexpr_line(name_expr), context_sexpr_col(name_expr));
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    context_ctx_add_error_at(ctx, SLOP_STR("type name must be symbol"), context_sexpr_line(name_expr), context_sexpr_col(name_expr));
                                    break;
                                }
                            }
                        } else if (!_mv_717.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing type name"), context_sexpr_line(expr), context_sexpr_col(expr));
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid type form"), context_sexpr_line(expr), context_sexpr_col(expr));
                break;
            }
        }
    }
}

void defn_dispatch_type_def(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    __auto_type _mv_720 = (*type_def);
    switch (_mv_720.tag) {
        case types_SExpr_lst:
        {
            __auto_type def_lst = _mv_720.data.lst;
            {
                __auto_type items = def_lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    context_ctx_add_error_at(ctx, SLOP_STR("empty type definition"), context_sexpr_line(type_def), context_sexpr_col(type_def));
                } else {
                    __auto_type _mv_721 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_721.has_value) {
                        __auto_type head = _mv_721.value;
                        __auto_type _mv_722 = (*head);
                        switch (_mv_722.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_722.data.sym;
                                {
                                    __auto_type kind = sym.name;
                                    if (string_eq(kind, SLOP_STR("record"))) {
                                        defn_transpile_record(ctx, raw_name, qualified_name, type_def);
                                    } else if (string_eq(kind, SLOP_STR("enum"))) {
                                        if (defn_has_payload_variants(items)) {
                                            defn_transpile_union(ctx, raw_name, qualified_name, type_def);
                                        } else {
                                            defn_transpile_enum(ctx, raw_name, qualified_name, type_def);
                                        }
                                    } else if (string_eq(kind, SLOP_STR("union"))) {
                                        defn_transpile_union(ctx, raw_name, qualified_name, type_def);
                                    } else {
                                        defn_transpile_type_alias(ctx, raw_name, qualified_name, type_def);
                                    }
                                }
                                break;
                            }
                            default: {
                                context_ctx_add_error_at(ctx, SLOP_STR("invalid type definition head"), context_sexpr_line(head), context_sexpr_col(head));
                                break;
                            }
                        }
                    } else if (!_mv_721.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("empty type definition"), context_sexpr_line(type_def), context_sexpr_col(type_def));
                    }
                }
            }
            break;
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_720.data.sym;
            defn_transpile_type_alias(ctx, raw_name, qualified_name, type_def);
            break;
        }
        default: {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid type definition form"), context_sexpr_line(type_def), context_sexpr_col(type_def));
            break;
        }
    }
}

uint8_t defn_has_payload_variants(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 1;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_723 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_723.has_value) {
                __auto_type item = _mv_723.value;
                __auto_type _mv_724 = (*item);
                switch (_mv_724.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type _ = _mv_724.data.lst;
                        found = 1;
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_723.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

void defn_transpile_record(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_725 = (*expr);
        switch (_mv_725.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_725.data.lst;
                {
                    __auto_type items = lst.items;
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("struct "), qualified_name, SLOP_STR(" {")));
                    defn_emit_record_fields(ctx, raw_name, qualified_name, items, 1);
                    context_ctx_emit(ctx, SLOP_STR("};"));
                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("typedef struct "), qualified_name, SLOP_STR(" "), qualified_name, SLOP_STR(";")));
                    context_ctx_emit(ctx, SLOP_STR(""));
                    context_ctx_register_type(ctx, (context_TypeEntry){raw_name, qualified_name, qualified_name, 0, 1, 0});
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid record form"), context_sexpr_line(expr), context_sexpr_col(expr));
                break;
            }
        }
    }
}

void defn_emit_record_fields(context_TranspileContext* ctx, slop_string raw_type_name, slop_string qualified_type_name, slop_list_types_SExpr_ptr items, int64_t start_idx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start_idx;
        while ((i < len)) {
            __auto_type _mv_726 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_726.has_value) {
                __auto_type field_expr = _mv_726.value;
                defn_emit_record_field(ctx, raw_type_name, qualified_type_name, field_expr);
            } else if (!_mv_726.has_value) {
            }
            i = (i + 1);
        }
    }
}

void defn_emit_record_field(context_TranspileContext* ctx, slop_string raw_type_name, slop_string qualified_type_name, types_SExpr* field) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((field != NULL)), "(!= field nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_727 = (*field);
        switch (_mv_727.tag) {
            case types_SExpr_lst:
            {
                __auto_type field_lst = _mv_727.data.lst;
                {
                    __auto_type items = field_lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 2)) {
                        context_ctx_emit(ctx, SLOP_STR("    /* invalid field */"));
                    } else {
                        __auto_type _mv_728 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_728.has_value) {
                            __auto_type name_expr = _mv_728.value;
                            __auto_type _mv_729 = (*name_expr);
                            switch (_mv_729.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_729.data.sym;
                                    __auto_type _mv_730 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_730.has_value) {
                                        __auto_type type_expr = _mv_730.value;
                                        {
                                            __auto_type raw_field_name = name_sym.name;
                                            __auto_type field_name = ctype_to_c_name(arena, raw_field_name);
                                            __auto_type field_type = context_to_c_type_prefixed(ctx, type_expr);
                                            __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                                            __auto_type is_ptr = expr_is_pointer_type_expr(type_expr);
                                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("    "), field_type, SLOP_STR(" "), field_name, SLOP_STR(";")));
                                            context_ctx_register_field_type(ctx, raw_type_name, raw_field_name, field_type, slop_type_str, is_ptr);
                                            context_ctx_register_field_type(ctx, qualified_type_name, raw_field_name, field_type, slop_type_str, is_ptr);
                                        }
                                    } else if (!_mv_730.has_value) {
                                        context_ctx_emit(ctx, SLOP_STR("    /* missing field type */"));
                                    }
                                    break;
                                }
                                default: {
                                    context_ctx_emit(ctx, SLOP_STR("    /* field name must be symbol */"));
                                    break;
                                }
                            }
                        } else if (!_mv_728.has_value) {
                            context_ctx_emit(ctx, SLOP_STR("    /* missing field name */"));
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_emit(ctx, SLOP_STR("    /* field must be a list */"));
                break;
            }
        }
    }
}

void defn_transpile_enum(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_731 = (*expr);
        switch (_mv_731.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_731.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    context_ctx_emit(ctx, SLOP_STR("typedef enum {"));
                    defn_emit_enum_values(ctx, qualified_name, items, 1, len);
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("} "), qualified_name, SLOP_STR(";")));
                    context_ctx_emit(ctx, SLOP_STR(""));
                    context_ctx_register_type(ctx, (context_TypeEntry){raw_name, qualified_name, qualified_name, 1, 0, 0});
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid enum form"), context_sexpr_line(expr), context_sexpr_col(expr));
                break;
            }
        }
    }
}

void defn_emit_enum_values(context_TranspileContext* ctx, slop_string type_name, slop_list_types_SExpr_ptr items, int64_t start_idx, int64_t len) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type i = start_idx;
        while ((i < len)) {
            __auto_type _mv_732 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_732.has_value) {
                __auto_type val_expr = _mv_732.value;
                __auto_type _mv_733 = (*val_expr);
                switch (_mv_733.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_733.data.sym;
                        {
                            __auto_type val_name = ctype_to_c_name(arena, sym.name);
                            __auto_type full_name = context_ctx_str3(ctx, type_name, SLOP_STR("_"), val_name);
                            __auto_type is_last = (i == (len - 1));
                            if (is_last) {
                                context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("    "), full_name));
                            } else {
                                context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("    "), full_name, SLOP_STR(",")));
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_732.has_value) {
            }
            i = (i + 1);
        }
    }
}

void defn_transpile_union(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_734 = (*expr);
        switch (_mv_734.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_734.data.lst;
                {
                    __auto_type items = lst.items;
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("struct "), qualified_name, SLOP_STR(" {")));
                    context_ctx_emit(ctx, SLOP_STR("    uint8_t tag;"));
                    context_ctx_emit(ctx, SLOP_STR("    union {"));
                    defn_emit_union_variants(ctx, items, 1);
                    context_ctx_emit(ctx, SLOP_STR("    } data;"));
                    context_ctx_emit(ctx, SLOP_STR("};"));
                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("typedef struct "), qualified_name, SLOP_STR(" "), qualified_name, SLOP_STR(";")));
                    context_ctx_emit(ctx, SLOP_STR(""));
                    defn_emit_tag_constants(ctx, qualified_name, items, 1);
                    context_ctx_emit(ctx, SLOP_STR(""));
                    context_ctx_register_type(ctx, (context_TypeEntry){raw_name, qualified_name, qualified_name, 0, 0, 1});
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid union form"), context_sexpr_line(expr), context_sexpr_col(expr));
                break;
            }
        }
    }
}

void defn_emit_union_variants(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start_idx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start_idx;
        while ((i < len)) {
            __auto_type _mv_735 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_735.has_value) {
                __auto_type variant_expr = _mv_735.value;
                __auto_type _mv_736 = (*variant_expr);
                switch (_mv_736.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type var_lst = _mv_736.data.lst;
                        {
                            __auto_type var_items = var_lst.items;
                            __auto_type var_len = ((int64_t)((var_items).len));
                            if ((var_len >= 1)) {
                                __auto_type _mv_737 = ({ __auto_type _lst = var_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_737.has_value) {
                                    __auto_type tag_expr = _mv_737.value;
                                    __auto_type _mv_738 = (*tag_expr);
                                    switch (_mv_738.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type tag_sym = _mv_738.data.sym;
                                            {
                                                __auto_type tag_name = tag_sym.name;
                                                if ((var_len >= 2)) {
                                                    __auto_type _mv_739 = ({ __auto_type _lst = var_items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_739.has_value) {
                                                        __auto_type type_expr = _mv_739.value;
                                                        {
                                                            __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("        "), c_type, SLOP_STR(" "), tag_name, SLOP_STR(";")));
                                                        }
                                                    } else if (!_mv_739.has_value) {
                                                    }
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_737.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_735.has_value) {
            }
            i = (i + 1);
        }
    }
}

void defn_emit_tag_constants(context_TranspileContext* ctx, slop_string type_name, slop_list_types_SExpr_ptr items, int64_t start_idx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start_idx;
        __auto_type tag_idx = 0;
        while ((i < len)) {
            __auto_type _mv_740 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_740.has_value) {
                __auto_type variant_expr = _mv_740.value;
                __auto_type _mv_741 = (*variant_expr);
                switch (_mv_741.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type var_lst = _mv_741.data.lst;
                        {
                            __auto_type var_items = var_lst.items;
                            if ((((int64_t)((var_items).len)) >= 1)) {
                                __auto_type _mv_742 = ({ __auto_type _lst = var_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_742.has_value) {
                                    __auto_type tag_expr = _mv_742.value;
                                    __auto_type _mv_743 = (*tag_expr);
                                    switch (_mv_743.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type tag_sym = _mv_743.data.sym;
                                            {
                                                __auto_type tag_name = tag_sym.name;
                                                __auto_type define_name = context_ctx_str4(ctx, type_name, SLOP_STR("_"), tag_name, SLOP_STR("_TAG"));
                                                context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("#define "), define_name, SLOP_STR(" "), int_to_string(arena, tag_idx)));
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_742.has_value) {
                                }
                            }
                            tag_idx = (tag_idx + 1);
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_740.has_value) {
            }
            i = (i + 1);
        }
    }
}

void defn_transpile_type_alias(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, types_SExpr* type_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (defn_is_array_type(type_expr)) {
            defn_emit_array_typedef(ctx, qualified_name, type_expr);
        } else if (defn_is_range_type(type_expr)) {
            defn_emit_range_typedef(ctx, raw_name, qualified_name, type_expr);
        } else {
            {
                __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("typedef "), c_type, SLOP_STR(" "), qualified_name, SLOP_STR(";")));
                context_ctx_emit(ctx, SLOP_STR(""));
                context_ctx_register_type(ctx, (context_TypeEntry){raw_name, qualified_name, c_type, 0, 0, 0});
                if ((strlib_starts_with(slop_type_str, SLOP_STR("(Map ")) || strlib_starts_with(slop_type_str, SLOP_STR("(Set ")))) {
                    context_ctx_register_type_alias(ctx, raw_name, slop_type_str);
                }
            }
        }
    }
}

uint8_t defn_is_array_type(types_SExpr* type_expr) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_744 = (*type_expr);
    switch (_mv_744.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_744.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_745 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_745.has_value) {
                        __auto_type head = _mv_745.value;
                        __auto_type _mv_746 = (*head);
                        switch (_mv_746.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_746.data.sym;
                                return string_eq(sym.name, SLOP_STR("Array"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_745.has_value) {
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

void defn_emit_array_typedef(context_TranspileContext* ctx, slop_string qualified_name, types_SExpr* type_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_747 = (*type_expr);
        switch (_mv_747.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_747.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 3)) {
                        context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("typedef void* "), context_ctx_str(ctx, qualified_name, SLOP_STR(";"))));
                    } else {
                        __auto_type _mv_748 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_748.has_value) {
                            __auto_type elem_type_expr = _mv_748.value;
                            __auto_type _mv_749 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_749.has_value) {
                                __auto_type size_expr = _mv_749.value;
                                {
                                    __auto_type elem_c_type = context_to_c_type_prefixed(ctx, elem_type_expr);
                                    __auto_type size_str = defn_get_number_as_string(size_expr);
                                    context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("typedef "), context_ctx_str(ctx, elem_c_type, context_ctx_str(ctx, SLOP_STR(" "), context_ctx_str(ctx, qualified_name, context_ctx_str3(ctx, SLOP_STR("["), size_str, SLOP_STR("];")))))));
                                    context_ctx_emit(ctx, SLOP_STR(""));
                                    {
                                        __auto_type ptr_type = context_ctx_str(ctx, elem_c_type, SLOP_STR("*"));
                                        context_ctx_register_type(ctx, (context_TypeEntry){qualified_name, qualified_name, ptr_type, 0, 0, 0});
                                    }
                                }
                            } else if (!_mv_749.has_value) {
                                context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("typedef void* "), context_ctx_str(ctx, qualified_name, SLOP_STR(";"))));
                            }
                        } else if (!_mv_748.has_value) {
                            context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("typedef void* "), context_ctx_str(ctx, qualified_name, SLOP_STR(";"))));
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("typedef void* "), context_ctx_str(ctx, qualified_name, SLOP_STR(";"))));
                break;
            }
        }
    }
}

slop_string defn_get_number_as_string(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_750 = (*expr);
    switch (_mv_750.tag) {
        case types_SExpr_num:
        {
            __auto_type num = _mv_750.data.num;
            return num.raw;
        }
        default: {
            return SLOP_STR("0");
        }
    }
}

uint8_t defn_is_range_type(types_SExpr* type_expr) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_751 = (*type_expr);
    switch (_mv_751.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_751.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type found_dots = 0;
                __auto_type i = 0;
                while (((i < len) && !(found_dots))) {
                    __auto_type _mv_752 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_752.has_value) {
                        __auto_type item = _mv_752.value;
                        __auto_type _mv_753 = (*item);
                        switch (_mv_753.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_753.data.sym;
                                if (string_eq(sym.name, SLOP_STR(".."))) {
                                    found_dots = 1;
                                }
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_752.has_value) {
                    }
                    i = (i + 1);
                }
                return found_dots;
            }
        }
        default: {
            return 0;
        }
    }
}

types_RangeBounds defn_parse_range_bounds(types_SExpr* type_expr) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    {
        __auto_type min_val = 0;
        __auto_type max_val = 0;
        __auto_type has_min = 0;
        __auto_type has_max = 0;
        __auto_type found_dots = 0;
        __auto_type _mv_754 = (*type_expr);
        switch (_mv_754.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_754.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    __auto_type i = 1;
                    while ((i < len)) {
                        __auto_type _mv_755 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_755.has_value) {
                            __auto_type item = _mv_755.value;
                            __auto_type _mv_756 = (*item);
                            switch (_mv_756.tag) {
                                case types_SExpr_num:
                                {
                                    __auto_type num = _mv_756.data.num;
                                    if (!(found_dots)) {
                                        min_val = defn_string_to_int(num.raw);
                                        has_min = 1;
                                    } else {
                                        max_val = defn_string_to_int(num.raw);
                                        has_max = 1;
                                    }
                                    break;
                                }
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_756.data.sym;
                                    if (string_eq(sym.name, SLOP_STR(".."))) {
                                        found_dots = 1;
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_755.has_value) {
                        }
                        i = (i + 1);
                    }
                }
                break;
            }
            default: {
                break;
            }
        }
        return (types_RangeBounds){has_min, has_max, ((int64_t)(min_val)), ((int64_t)(max_val))};
    }
}

int64_t defn_string_to_int(slop_string s) {
    {
        __auto_type len = ((int64_t)(string_len(s)));
        __auto_type result = 0;
        __auto_type i = 0;
        __auto_type negative = 0;
        if (((len > 0) && (s.data[0] == 45))) {
            negative = 1;
            i = 1;
        }
        while ((i < len)) {
            {
                __auto_type c = s.data[i];
                if (((c >= 48) && (c <= 57))) {
                    result = ((result * 10) + (((int64_t)(c)) - 48));
                }
            }
            i = (i + 1);
        }
        if (negative) {
            return (0 - result);
        } else {
            return result;
        }
    }
}

slop_string defn_select_smallest_c_type(int64_t min_val, int64_t max_val, uint8_t has_min, uint8_t has_max) {
    if ((has_min && has_max)) {
        if (((min_val >= 0) && (max_val <= 255))) {
            return SLOP_STR("uint8_t");
        } else if (((min_val >= 0) && (max_val <= 65535))) {
            return SLOP_STR("uint16_t");
        } else if (((min_val >= (0 - 128)) && (max_val <= 127))) {
            return SLOP_STR("int8_t");
        } else if (((min_val >= (0 - 32768)) && (max_val <= 32767))) {
            return SLOP_STR("int16_t");
        } else {
            return SLOP_STR("int64_t");
        }
    } else {
        return SLOP_STR("int64_t");
    }
}

void defn_emit_range_typedef(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, types_SExpr* type_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        types_RangeBounds bounds = defn_parse_range_bounds(type_expr);
        int64_t min_val = bounds.min_val;
        int64_t max_val = bounds.max_val;
        uint8_t has_min = bounds.has_min;
        uint8_t has_max = bounds.has_max;
        __auto_type c_type = defn_select_smallest_c_type(min_val, max_val, has_min, has_max);
        context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("typedef "), c_type, SLOP_STR(" "), qualified_name, SLOP_STR(";")));
        context_ctx_emit(ctx, SLOP_STR(""));
        context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("static inline "), qualified_name, SLOP_STR(" "), qualified_name, SLOP_STR("_new(int64_t v) {")));
        context_ctx_indent(ctx);
        if ((has_min && has_max)) {
            {
                __auto_type min_str = int_to_string(arena, min_val);
                __auto_type max_str = int_to_string(arena, max_val);
                context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("SLOP_PRE(v >= "), context_ctx_str(ctx, min_str, context_ctx_str(ctx, SLOP_STR(" && v <= "), context_ctx_str(ctx, max_str, context_ctx_str(ctx, SLOP_STR(", \""), context_ctx_str(ctx, qualified_name, context_ctx_str(ctx, SLOP_STR(" in range "), context_ctx_str(ctx, min_str, context_ctx_str(ctx, SLOP_STR(".."), context_ctx_str(ctx, max_str, SLOP_STR("\");"))))))))))));
            }
        } else if (has_min) {
            {
                __auto_type min_str = int_to_string(arena, min_val);
                context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("SLOP_PRE(v >= "), context_ctx_str(ctx, min_str, context_ctx_str(ctx, SLOP_STR(", \""), context_ctx_str(ctx, qualified_name, context_ctx_str(ctx, SLOP_STR(" >= "), context_ctx_str(ctx, min_str, SLOP_STR("\");"))))))));
            }
        } else if (has_max) {
            {
                __auto_type max_str = int_to_string(arena, max_val);
                context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("SLOP_PRE(v <= "), context_ctx_str(ctx, max_str, context_ctx_str(ctx, SLOP_STR(", \""), context_ctx_str(ctx, qualified_name, context_ctx_str(ctx, SLOP_STR(" <= "), context_ctx_str(ctx, max_str, SLOP_STR("\");"))))))));
            }
        } else {
        }
        context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("return ("), context_ctx_str(ctx, qualified_name, SLOP_STR(")v;"))));
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
        context_ctx_emit(ctx, SLOP_STR(""));
        context_ctx_register_type(ctx, (context_TypeEntry){raw_name, qualified_name, c_type, 0, 0, 0});
    }
}

void defn_transpile_function(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_757 = (*expr);
        switch (_mv_757.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_757.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 3)) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid fn: need name and params"), context_sexpr_line(expr), context_sexpr_col(expr));
                    } else {
                        __auto_type _mv_758 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_758.has_value) {
                            __auto_type name_expr = _mv_758.value;
                            __auto_type _mv_759 = (*name_expr);
                            switch (_mv_759.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_759.data.sym;
                                    {
                                        __auto_type raw_name = name_sym.name;
                                        __auto_type base_name = ctype_to_c_name(arena, raw_name);
                                        __auto_type mangled_name = ((string_eq(base_name, SLOP_STR("main"))) ? base_name : context_ctx_prefix_type(ctx, base_name));
                                        __auto_type fn_name = context_extract_fn_c_name(arena, items, mangled_name);
                                        __auto_type is_public_api = !(string_eq(fn_name, mangled_name));
                                        __auto_type _mv_760 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_760.has_value) {
                                            __auto_type params_expr = _mv_760.value;
                                            defn_emit_function_def(ctx, raw_name, fn_name, params_expr, items, is_public_api);
                                        } else if (!_mv_760.has_value) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("missing params"), context_sexpr_line(name_expr), context_sexpr_col(name_expr));
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    context_ctx_add_error_at(ctx, SLOP_STR("function name must be symbol"), context_sexpr_line(name_expr), context_sexpr_col(name_expr));
                                    break;
                                }
                            }
                        } else if (!_mv_758.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing function name"), context_sexpr_line(expr), context_sexpr_col(expr));
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid fn form"), context_sexpr_line(expr), context_sexpr_col(expr));
                break;
            }
        }
    }
}

void defn_emit_function_def(context_TranspileContext* ctx, slop_string raw_name, slop_string fn_name, types_SExpr* params_expr, slop_list_types_SExpr_ptr items, uint8_t is_public_api) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((params_expr != NULL)), "(!= params-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result_type_opt = defn_get_result_type_name(ctx, items);
        __auto_type raw_return = defn_get_return_type(ctx, items);
        __auto_type preconditions = defn_collect_preconditions(arena, items);
        __auto_type postconditions = defn_collect_postconditions(arena, items);
        __auto_type assumptions = defn_collect_assumptions(arena, items);
        {
            slop_string return_type = ({ __auto_type _mv = result_type_opt; _mv.has_value ? ({ __auto_type result_name = _mv.value; result_name; }) : (raw_return); });
            __auto_type actual_return = ((string_eq(fn_name, SLOP_STR("main"))) ? SLOP_STR("int") : return_type);
            __auto_type param_str = defn_build_param_str(ctx, params_expr);
            __auto_type has_post = ((((int64_t)((postconditions).len)) > 0) || (((int64_t)((assumptions).len)) > 0));
            __auto_type needs_retval = (has_post && !(string_eq(actual_return, SLOP_STR("void"))));
            context_ctx_set_current_return_type(ctx, actual_return);
            __auto_type _mv_761 = result_type_opt;
            if (_mv_761.has_value) {
                __auto_type result_name = _mv_761.value;
                context_ctx_set_current_result_type(ctx, result_name);
            } else if (!_mv_761.has_value) {
                context_ctx_clear_current_result_type(ctx);
            }
            context_ctx_emit(ctx, context_ctx_str5(ctx, actual_return, SLOP_STR(" "), fn_name, SLOP_STR("("), context_ctx_str(ctx, ((string_eq(param_str, SLOP_STR(""))) ? SLOP_STR("void") : param_str), SLOP_STR(") {"))));
            context_ctx_indent(ctx);
            context_ctx_push_scope(ctx);
            defn_bind_params_to_scope(ctx, params_expr);
            defn_emit_preconditions(ctx, preconditions);
            if (needs_retval) {
                context_ctx_emit(ctx, context_ctx_str(ctx, actual_return, SLOP_STR(" _retval;")));
            }
            if (needs_retval) {
                context_ctx_set_capture_retval(ctx, 1);
            }
            defn_emit_function_body(ctx, items);
            if (needs_retval) {
                context_ctx_set_capture_retval(ctx, 0);
            }
            defn_emit_postconditions(ctx, postconditions);
            defn_emit_assumptions(ctx, assumptions);
            if (needs_retval) {
                context_ctx_emit(ctx, SLOP_STR("return _retval;"));
            }
            context_ctx_pop_scope(ctx);
            context_ctx_dedent(ctx);
            context_ctx_emit(ctx, SLOP_STR("}"));
            context_ctx_emit(ctx, SLOP_STR(""));
            {
                __auto_type param_types = defn_collect_param_types(ctx, params_expr);
                context_ctx_register_func(ctx, (context_FuncEntry){raw_name, fn_name, actual_return, 0, string_eq(actual_return, SLOP_STR("slop_string")), param_types});
            }
            context_ctx_clear_current_result_type(ctx);
            context_ctx_clear_current_return_type(ctx);
        }
    }
}

void defn_bind_params_to_scope(context_TranspileContext* ctx, types_SExpr* params_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((params_expr != NULL)), "(!= params-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_762 = (*params_expr);
        switch (_mv_762.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_762.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    __auto_type i = 0;
                    while ((i < len)) {
                        __auto_type _mv_763 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_763.has_value) {
                            __auto_type param = _mv_763.value;
                            defn_bind_single_param(ctx, param);
                        } else if (!_mv_763.has_value) {
                        }
                        i = (i + 1);
                    }
                }
                break;
            }
            default: {
                break;
            }
        }
    }
}

void defn_bind_single_param(context_TranspileContext* ctx, types_SExpr* param) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((param != NULL)), "(!= param nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_764 = (*param);
        switch (_mv_764.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_764.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len >= 2)) {
                        {
                            __auto_type has_mode = ((len >= 3) && defn_is_param_mode(items));
                            __auto_type name_idx = ((has_mode) ? 1 : 0);
                            __auto_type type_idx = ((has_mode) ? 2 : 1);
                            __auto_type _mv_765 = ({ __auto_type _lst = items; size_t _idx = (size_t)name_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_765.has_value) {
                                __auto_type name_expr = _mv_765.value;
                                __auto_type _mv_766 = (*name_expr);
                                switch (_mv_766.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type name_sym = _mv_766.data.sym;
                                        __auto_type _mv_767 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_767.has_value) {
                                            __auto_type type_expr = _mv_767.value;
                                            {
                                                __auto_type param_name = name_sym.name;
                                                __auto_type c_name = ctype_to_c_name(arena, param_name);
                                                __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                                                __auto_type is_ptr = defn_is_pointer_type(type_expr);
                                                context_ctx_bind_var(ctx, (context_VarEntry){param_name, c_name, c_type, slop_type_str, is_ptr, 0});
                                            }
                                        } else if (!_mv_767.has_value) {
                                        }
                                        break;
                                    }
                                    default: {
                                        break;
                                    }
                                }
                            } else if (!_mv_765.has_value) {
                            }
                        }
                    }
                }
                break;
            }
            default: {
                break;
            }
        }
    }
}

uint8_t defn_is_pointer_type(types_SExpr* type_expr) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_768 = (*type_expr);
    switch (_mv_768.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_768.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_769 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_769.has_value) {
                        __auto_type head = _mv_769.value;
                        __auto_type _mv_770 = (*head);
                        switch (_mv_770.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_770.data.sym;
                                return string_eq(sym.name, SLOP_STR("Ptr"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_769.has_value) {
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

slop_list_context_FuncParamType_ptr defn_collect_param_types(context_TranspileContext* ctx, types_SExpr* params_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((params_expr != NULL)), "(!= params-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type result = ((slop_list_context_FuncParamType_ptr){ .data = (context_FuncParamType**)slop_arena_alloc(arena, 16 * sizeof(context_FuncParamType*)), .len = 0, .cap = 16 });
        __auto_type _mv_771 = (*params_expr);
        switch (_mv_771.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_771.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    __auto_type i = 0;
                    while ((i < len)) {
                        __auto_type _mv_772 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_772.has_value) {
                            __auto_type param = _mv_772.value;
                            {
                                __auto_type c_type = defn_get_param_c_type(ctx, param);
                                __auto_type param_info = ((context_FuncParamType*)((uint8_t*)slop_arena_alloc(arena, 64)));
                                (*param_info).c_type = c_type;
                                ({ __auto_type _lst_p = &(result); __auto_type _item = (param_info); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            }
                        } else if (!_mv_772.has_value) {
                        }
                        i = (i + 1);
                    }
                }
                break;
            }
            default: {
                break;
            }
        }
        return result;
    }
}

slop_string defn_get_param_c_type(context_TranspileContext* ctx, types_SExpr* param) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((param != NULL)), "(!= param nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_773 = (*param);
        switch (_mv_773.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_773.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 2)) {
                        return SLOP_STR("void*");
                    } else {
                        {
                            __auto_type has_mode = ((len >= 3) && defn_is_param_mode(items));
                            __auto_type type_idx = ((has_mode) ? 2 : 1);
                            __auto_type _mv_774 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_774.has_value) {
                                __auto_type type_expr = _mv_774.value;
                                return context_to_c_type_prefixed(ctx, type_expr);
                            } else if (!_mv_774.has_value) {
                                return SLOP_STR("void*");
                            }
                        }
                    }
                }
            }
            default: {
                return SLOP_STR("void*");
            }
        }
    }
}

void defn_emit_forward_declaration(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_775 = (*expr);
        switch (_mv_775.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_775.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len >= 3)) {
                        __auto_type _mv_776 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_776.has_value) {
                            __auto_type name_expr = _mv_776.value;
                            __auto_type _mv_777 = (*name_expr);
                            switch (_mv_777.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_777.data.sym;
                                    {
                                        __auto_type raw_name = name_sym.name;
                                        __auto_type base_name = ctype_to_c_name(arena, raw_name);
                                        __auto_type mangled_name = context_ctx_prefix_type(ctx, base_name);
                                        __auto_type fn_name = context_extract_fn_c_name(arena, items, mangled_name);
                                        __auto_type _mv_778 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_778.has_value) {
                                            __auto_type params_expr = _mv_778.value;
                                            {
                                                __auto_type result_type_opt = defn_get_result_type_name(ctx, items);
                                                __auto_type raw_return = defn_get_return_type(ctx, items);
                                                {
                                                    slop_string return_type = ({ __auto_type _mv = result_type_opt; _mv.has_value ? ({ __auto_type result_name = _mv.value; result_name; }) : (raw_return); });
                                                    __auto_type actual_return = ((string_eq(base_name, SLOP_STR("main"))) ? SLOP_STR("int") : return_type);
                                                    __auto_type param_str = defn_build_param_str(ctx, params_expr);
                                                    context_ctx_emit(ctx, context_ctx_str5(ctx, actual_return, SLOP_STR(" "), fn_name, SLOP_STR("("), context_ctx_str(ctx, ((string_eq(param_str, SLOP_STR(""))) ? SLOP_STR("void") : param_str), SLOP_STR(");"))));
                                                }
                                            }
                                        } else if (!_mv_778.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_776.has_value) {
                        }
                    }
                }
                break;
            }
            default: {
                break;
            }
        }
    }
}

slop_string defn_get_return_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 3;
        __auto_type result = SLOP_STR("void");
        while ((i < len)) {
            __auto_type _mv_779 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_779.has_value) {
                __auto_type item = _mv_779.value;
                if (defn_is_spec_form(item)) {
                    result = defn_extract_spec_return_type(ctx, item);
                }
            } else if (!_mv_779.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

uint8_t defn_is_spec_form(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_780 = (*expr);
    switch (_mv_780.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_780.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_781 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_781.has_value) {
                        __auto_type head = _mv_781.value;
                        __auto_type _mv_782 = (*head);
                        switch (_mv_782.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_782.data.sym;
                                return string_eq(sym.name, SLOP_STR("@spec"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_781.has_value) {
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

slop_string defn_extract_spec_return_type(context_TranspileContext* ctx, types_SExpr* spec_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((spec_expr != NULL)), "(!= spec-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_783 = (*spec_expr);
        switch (_mv_783.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_783.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) < 2)) {
                        return SLOP_STR("void");
                    } else {
                        __auto_type _mv_784 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_784.has_value) {
                            __auto_type spec_body = _mv_784.value;
                            __auto_type _mv_785 = (*spec_body);
                            switch (_mv_785.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type body_lst = _mv_785.data.lst;
                                    {
                                        __auto_type body_items = body_lst.items;
                                        __auto_type body_len = ((int64_t)((body_items).len));
                                        if ((body_len < 1)) {
                                            return SLOP_STR("void");
                                        } else {
                                            __auto_type _mv_786 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_786.has_value) {
                                                __auto_type ret_type = _mv_786.value;
                                                return context_to_c_type_prefixed(ctx, ret_type);
                                            } else if (!_mv_786.has_value) {
                                                return SLOP_STR("void");
                                            }
                                        }
                                    }
                                }
                                default: {
                                    return SLOP_STR("void");
                                }
                            }
                        } else if (!_mv_784.has_value) {
                            return SLOP_STR("void");
                        }
                    }
                }
            }
            default: {
                return SLOP_STR("void");
            }
        }
    }
}

slop_option_string defn_get_result_type_name(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 3;
        slop_option_string result = (slop_option_string){.has_value = false};
        while (((i < len) && ({ __auto_type _mv = result; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); }))) {
            __auto_type _mv_787 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_787.has_value) {
                __auto_type item = _mv_787.value;
                if (defn_is_spec_form(item)) {
                    result = defn_extract_result_type_name(ctx, item);
                }
            } else if (!_mv_787.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_option_string defn_extract_result_type_name(context_TranspileContext* ctx, types_SExpr* spec_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((spec_expr != NULL)), "(!= spec-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_788 = (*spec_expr);
        switch (_mv_788.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_788.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) < 2)) {
                        return (slop_option_string){.has_value = false};
                    } else {
                        __auto_type _mv_789 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_789.has_value) {
                            __auto_type spec_body = _mv_789.value;
                            __auto_type _mv_790 = (*spec_body);
                            switch (_mv_790.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type body_lst = _mv_790.data.lst;
                                    {
                                        __auto_type body_items = body_lst.items;
                                        __auto_type body_len = ((int64_t)((body_items).len));
                                        if ((body_len < 1)) {
                                            return (slop_option_string){.has_value = false};
                                        } else {
                                            __auto_type _mv_791 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_791.has_value) {
                                                __auto_type ret_type = _mv_791.value;
                                                return defn_check_result_type(ctx, ret_type);
                                            } else if (!_mv_791.has_value) {
                                                return (slop_option_string){.has_value = false};
                                            }
                                        }
                                    }
                                }
                                default: {
                                    return (slop_option_string){.has_value = false};
                                }
                            }
                        } else if (!_mv_789.has_value) {
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
}

slop_option_string defn_check_result_type(context_TranspileContext* ctx, types_SExpr* type_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_792 = (*type_expr);
        switch (_mv_792.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_792.data.sym;
                {
                    __auto_type type_name = sym.name;
                    __auto_type _mv_793 = context_ctx_lookup_result_type_alias(ctx, type_name);
                    if (_mv_793.has_value) {
                        __auto_type alias_result = _mv_793.value;
                        return (slop_option_string){.has_value = 1, .value = alias_result};
                    } else if (!_mv_793.has_value) {
                        __auto_type _mv_794 = context_ctx_lookup_type(ctx, type_name);
                        if (_mv_794.has_value) {
                            __auto_type entry = _mv_794.value;
                            return (slop_option_string){.has_value = 1, .value = entry.c_name};
                        } else if (!_mv_794.has_value) {
                            return (slop_option_string){.has_value = false};
                        }
                    }
                }
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_792.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) < 3)) {
                        return (slop_option_string){.has_value = false};
                    } else {
                        __auto_type _mv_795 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_795.has_value) {
                            __auto_type head = _mv_795.value;
                            __auto_type _mv_796 = (*head);
                            switch (_mv_796.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_796.data.sym;
                                    if (string_eq(sym.name, SLOP_STR("Result"))) {
                                        __auto_type _mv_797 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_797.has_value) {
                                            __auto_type ok_type_expr = _mv_797.value;
                                            __auto_type _mv_798 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_798.has_value) {
                                                __auto_type err_type_expr = _mv_798.value;
                                                {
                                                    __auto_type ok_c_type = context_to_c_type_prefixed(ctx, ok_type_expr);
                                                    __auto_type err_c_type = context_to_c_type_prefixed(ctx, err_type_expr);
                                                    __auto_type result_name = defn_build_result_name(arena, ok_c_type, err_c_type);
                                                    return (slop_option_string){.has_value = 1, .value = result_name};
                                                }
                                            } else if (!_mv_798.has_value) {
                                                return (slop_option_string){.has_value = false};
                                            }
                                        } else if (!_mv_797.has_value) {
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
                        } else if (!_mv_795.has_value) {
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
}

slop_string defn_build_result_name(slop_arena* arena, slop_string ok_type, slop_string err_type) {
    {
        __auto_type ok_id = ctype_type_to_identifier(arena, ok_type);
        __auto_type err_id = ctype_type_to_identifier(arena, err_type);
        return string_concat(arena, string_concat(arena, string_concat(arena, SLOP_STR("slop_result_"), ok_id), SLOP_STR("_")), err_id);
    }
}

slop_string defn_build_param_str(context_TranspileContext* ctx, types_SExpr* params_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((params_expr != NULL)), "(!= params-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_799 = (*params_expr);
        switch (_mv_799.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_799.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    __auto_type result = SLOP_STR("");
                    __auto_type i = 0;
                    while ((i < len)) {
                        __auto_type _mv_800 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_800.has_value) {
                            __auto_type param = _mv_800.value;
                            {
                                __auto_type param_str = defn_build_single_param(ctx, param);
                                if (string_eq(result, SLOP_STR(""))) {
                                    result = param_str;
                                } else {
                                    result = context_ctx_str3(ctx, result, SLOP_STR(", "), param_str);
                                }
                            }
                        } else if (!_mv_800.has_value) {
                        }
                        i = (i + 1);
                    }
                    return result;
                }
            }
            default: {
                return SLOP_STR("");
            }
        }
    }
}

slop_string defn_build_single_param(context_TranspileContext* ctx, types_SExpr* param) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((param != NULL)), "(!= param nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_801 = (*param);
        switch (_mv_801.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_801.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 2)) {
                        return SLOP_STR("/* invalid param */");
                    } else {
                        {
                            __auto_type has_mode = ((len >= 3) && defn_is_param_mode(items));
                            __auto_type name_idx = ((((len >= 3) && defn_is_param_mode(items))) ? 1 : 0);
                            __auto_type type_idx = ((((len >= 3) && defn_is_param_mode(items))) ? 2 : 1);
                            __auto_type _mv_802 = ({ __auto_type _lst = items; size_t _idx = (size_t)name_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_802.has_value) {
                                __auto_type name_expr = _mv_802.value;
                                __auto_type _mv_803 = (*name_expr);
                                switch (_mv_803.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type name_sym = _mv_803.data.sym;
                                        __auto_type _mv_804 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_804.has_value) {
                                            __auto_type type_expr = _mv_804.value;
                                            {
                                                __auto_type param_name = ctype_to_c_name(arena, name_sym.name);
                                                if (defn_is_fn_type(type_expr)) {
                                                    return defn_emit_fn_param_type(ctx, type_expr, param_name);
                                                } else {
                                                    {
                                                        __auto_type param_type = context_to_c_type_prefixed(ctx, type_expr);
                                                        return context_ctx_str3(ctx, param_type, SLOP_STR(" "), param_name);
                                                    }
                                                }
                                            }
                                        } else if (!_mv_804.has_value) {
                                            return SLOP_STR("/* missing param type */");
                                        }
                                    }
                                    default: {
                                        return SLOP_STR("/* param name must be symbol */");
                                    }
                                }
                            } else if (!_mv_802.has_value) {
                                return SLOP_STR("/* missing param name */");
                            }
                        }
                    }
                }
            }
            default: {
                return SLOP_STR("/* param must be a list */");
            }
        }
    }
}

uint8_t defn_is_param_mode(slop_list_types_SExpr_ptr items) {
    if ((((int64_t)((items).len)) < 1)) {
        return 0;
    } else {
        __auto_type _mv_805 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_805.has_value) {
            __auto_type first = _mv_805.value;
            __auto_type _mv_806 = (*first);
            switch (_mv_806.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_806.data.sym;
                    {
                        __auto_type name = sym.name;
                        return ((string_eq(name, SLOP_STR("in"))) || (string_eq(name, SLOP_STR("out"))) || (string_eq(name, SLOP_STR("mut"))));
                    }
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_805.has_value) {
            return 0;
        }
    }
}

uint8_t defn_is_fn_type(types_SExpr* type_expr) {
    __auto_type _mv_807 = (*type_expr);
    switch (_mv_807.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_807.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_808 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_808.has_value) {
                        __auto_type first = _mv_808.value;
                        __auto_type _mv_809 = (*first);
                        switch (_mv_809.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_809.data.sym;
                                return string_eq(sym.name, SLOP_STR("Fn"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_808.has_value) {
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

slop_string defn_emit_fn_param_type(context_TranspileContext* ctx, types_SExpr* type_expr, slop_string param_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_810 = (*type_expr);
        switch (_mv_810.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_810.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 2)) {
                        return context_ctx_str(ctx, SLOP_STR("void* "), param_name);
                    } else {
                        {
                            __auto_type ret_type = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)(len - 1); struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type ret = _mv.value; context_to_c_type_prefixed(ctx, ret); }) : (SLOP_STR("void")); });
                            if ((len == 2)) {
                                return context_ctx_str(ctx, context_ctx_str(ctx, ret_type, SLOP_STR("(*")), context_ctx_str(ctx, param_name, SLOP_STR(")(void)")));
                            } else {
                                __auto_type _mv_811 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_811.has_value) {
                                    __auto_type args_expr = _mv_811.value;
                                    {
                                        __auto_type args_str = defn_build_fn_args_str_for_param(ctx, args_expr);
                                        return context_ctx_str(ctx, context_ctx_str(ctx, ret_type, SLOP_STR("(*")), context_ctx_str(ctx, param_name, context_ctx_str(ctx, SLOP_STR(")"), args_str)));
                                    }
                                } else if (!_mv_811.has_value) {
                                    return context_ctx_str(ctx, context_ctx_str(ctx, ret_type, SLOP_STR("(*")), context_ctx_str(ctx, param_name, SLOP_STR(")(void)")));
                                }
                            }
                        }
                    }
                }
            }
            default: {
                return context_ctx_str(ctx, SLOP_STR("void* "), param_name);
            }
        }
    }
}

slop_string defn_build_fn_args_str_for_param(context_TranspileContext* ctx, types_SExpr* args_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_812 = (*args_expr);
        switch (_mv_812.tag) {
            case types_SExpr_lst:
            {
                __auto_type args_list = _mv_812.data.lst;
                {
                    __auto_type arg_items = args_list.items;
                    __auto_type arg_count = ((int64_t)((arg_items).len));
                    if ((arg_count == 0)) {
                        return SLOP_STR("(void)");
                    } else {
                        {
                            __auto_type result = SLOP_STR("(");
                            __auto_type i = 0;
                            while ((i < arg_count)) {
                                __auto_type _mv_813 = ({ __auto_type _lst = arg_items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_813.has_value) {
                                    __auto_type arg_expr = _mv_813.value;
                                    {
                                        __auto_type arg_type = context_to_c_type_prefixed(ctx, arg_expr);
                                        if ((i > 0)) {
                                            result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR(", "), arg_type));
                                        } else {
                                            result = context_ctx_str(ctx, result, arg_type);
                                        }
                                    }
                                } else if (!_mv_813.has_value) {
                                    /* empty list */;
                                }
                                i = (i + 1);
                            }
                            return context_ctx_str(ctx, result, SLOP_STR(")"));
                        }
                    }
                }
            }
            default: {
                return SLOP_STR("(void)");
            }
        }
    }
}

void defn_emit_function_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type is_void_fn = ({ __auto_type _mv = context_ctx_get_current_return_type(ctx); _mv.has_value ? ({ __auto_type ret_type = _mv.value; string_eq(ret_type, SLOP_STR("void")); }) : (1); });
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 3;
        __auto_type body_start = defn_find_body_start(items);
        i = body_start;
        while ((i < len)) {
            __auto_type _mv_814 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_814.has_value) {
                __auto_type item = _mv_814.value;
                if (defn_is_c_name_attr(item)) {
                    i = (i + 1);
                } else {
                    {
                        __auto_type is_last = defn_is_last_body_item(items, i);
                        __auto_type is_return = (is_last && !(is_void_fn));
                        if (!(defn_is_annotation(item))) {
                            stmt_transpile_stmt(ctx, item, is_return);
                        }
                    }
                }
            } else if (!_mv_814.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t defn_is_c_name_attr(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_815 = (*expr);
    switch (_mv_815.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_815.data.sym;
            return string_eq(sym.name, SLOP_STR(":c-name"));
        }
        default: {
            return 0;
        }
    }
}

uint8_t defn_is_last_body_item(slop_list_types_SExpr_ptr items, int64_t current_i) {
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = (current_i + 1);
        __auto_type found_body = 0;
        while (((i < len) && !(found_body))) {
            __auto_type _mv_816 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_816.has_value) {
                __auto_type item = _mv_816.value;
                if ((defn_is_annotation(item) || defn_is_c_name_attr(item))) {
                    i = (i + 1);
                } else {
                    if (((i > 0) && defn_is_c_name_attr_at(items, (i - 1)))) {
                        i = (i + 1);
                    } else {
                        found_body = 1;
                    }
                }
            } else if (!_mv_816.has_value) {
                i = (i + 1);
            }
        }
        return !(found_body);
    }
}

uint8_t defn_is_c_name_attr_at(slop_list_types_SExpr_ptr items, int64_t idx) {
    __auto_type _mv_817 = ({ __auto_type _lst = items; size_t _idx = (size_t)idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
    if (_mv_817.has_value) {
        __auto_type item = _mv_817.value;
        return defn_is_c_name_attr(item);
    } else if (!_mv_817.has_value) {
        return 0;
    }
}

int64_t defn_find_body_start(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 3;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_818 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_818.has_value) {
                __auto_type item = _mv_818.value;
                if (defn_is_annotation(item)) {
                    i = (i + 1);
                } else {
                    found = 1;
                }
            } else if (!_mv_818.has_value) {
                found = 1;
            }
        }
        return i;
    }
}

uint8_t defn_is_annotation(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_819 = (*expr);
    switch (_mv_819.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_819.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_820 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_820.has_value) {
                        __auto_type head = _mv_820.value;
                        __auto_type _mv_821 = (*head);
                        switch (_mv_821.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_821.data.sym;
                                {
                                    __auto_type name = sym.name;
                                    return ((string_eq(name, SLOP_STR("@intent"))) || (string_eq(name, SLOP_STR("@spec"))) || (string_eq(name, SLOP_STR("@pre"))) || (string_eq(name, SLOP_STR("@post"))) || (string_eq(name, SLOP_STR("@assume"))) || (string_eq(name, SLOP_STR("@alloc"))) || (string_eq(name, SLOP_STR("@example"))) || (string_eq(name, SLOP_STR("@pure"))));
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_820.has_value) {
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

uint8_t defn_is_pre_form(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_822 = (*expr);
    switch (_mv_822.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_822.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_823 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_823.has_value) {
                        __auto_type head = _mv_823.value;
                        __auto_type _mv_824 = (*head);
                        switch (_mv_824.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_824.data.sym;
                                return string_eq(sym.name, SLOP_STR("@pre"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_823.has_value) {
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

uint8_t defn_is_post_form(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_825 = (*expr);
    switch (_mv_825.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_825.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_826 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_826.has_value) {
                        __auto_type head = _mv_826.value;
                        __auto_type _mv_827 = (*head);
                        switch (_mv_827.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_827.data.sym;
                                return string_eq(sym.name, SLOP_STR("@post"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_826.has_value) {
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

uint8_t defn_is_assume_form(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_828 = (*expr);
    switch (_mv_828.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_828.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_829 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_829.has_value) {
                        __auto_type head = _mv_829.value;
                        __auto_type _mv_830 = (*head);
                        switch (_mv_830.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_830.data.sym;
                                return string_eq(sym.name, SLOP_STR("@assume"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_829.has_value) {
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

slop_option_types_SExpr_ptr defn_get_annotation_condition(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        slop_option_types_SExpr_ptr result = (slop_option_types_SExpr_ptr){.has_value = false};
        __auto_type _mv_831 = (*expr);
        switch (_mv_831.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_831.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 2)) {
                        __auto_type _mv_832 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_832.has_value) {
                            __auto_type val = _mv_832.value;
                            result = (slop_option_types_SExpr_ptr){.has_value = 1, .value = val};
                        } else if (!_mv_832.has_value) {
                        }
                    }
                }
                break;
            }
            default: {
                break;
            }
        }
        return result;
    }
}

slop_list_types_SExpr_ptr defn_collect_preconditions(slop_arena* arena, slop_list_types_SExpr_ptr items) {
    {
        __auto_type result = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 3;
        while ((i < len)) {
            __auto_type _mv_833 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_833.has_value) {
                __auto_type item = _mv_833.value;
                if (defn_is_pre_form(item)) {
                    __auto_type _mv_834 = defn_get_annotation_condition(item);
                    if (_mv_834.has_value) {
                        __auto_type cond = _mv_834.value;
                        ({ __auto_type _lst_p = &(result); __auto_type _item = (cond); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    } else if (!_mv_834.has_value) {
                    }
                }
            } else if (!_mv_833.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_list_types_SExpr_ptr defn_collect_postconditions(slop_arena* arena, slop_list_types_SExpr_ptr items) {
    {
        __auto_type result = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 3;
        while ((i < len)) {
            __auto_type _mv_835 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_835.has_value) {
                __auto_type item = _mv_835.value;
                if (defn_is_post_form(item)) {
                    __auto_type _mv_836 = defn_get_annotation_condition(item);
                    if (_mv_836.has_value) {
                        __auto_type cond = _mv_836.value;
                        ({ __auto_type _lst_p = &(result); __auto_type _item = (cond); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    } else if (!_mv_836.has_value) {
                    }
                }
            } else if (!_mv_835.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_list_types_SExpr_ptr defn_collect_assumptions(slop_arena* arena, slop_list_types_SExpr_ptr items) {
    {
        __auto_type result = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 3;
        while ((i < len)) {
            __auto_type _mv_837 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_837.has_value) {
                __auto_type item = _mv_837.value;
                if (defn_is_assume_form(item)) {
                    __auto_type _mv_838 = defn_get_annotation_condition(item);
                    if (_mv_838.has_value) {
                        __auto_type cond = _mv_838.value;
                        ({ __auto_type _lst_p = &(result); __auto_type _item = (cond); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    } else if (!_mv_838.has_value) {
                    }
                }
            } else if (!_mv_837.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

uint8_t defn_has_postconditions(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 3;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_839 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_839.has_value) {
                __auto_type item = _mv_839.value;
                if ((defn_is_post_form(item) || defn_is_assume_form(item))) {
                    found = 1;
                }
            } else if (!_mv_839.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

void defn_emit_preconditions(context_TranspileContext* ctx, slop_list_types_SExpr_ptr preconditions) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((preconditions).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_840 = ({ __auto_type _lst = preconditions; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_840.has_value) {
                __auto_type cond_expr = _mv_840.value;
                {
                    __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                    __auto_type expr_str = parser_pretty_print(arena, cond_expr);
                    __auto_type escaped_str = defn_escape_for_c_string(arena, expr_str);
                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("SLOP_PRE(("), cond_c, SLOP_STR("), \""), escaped_str, SLOP_STR("\");")));
                }
            } else if (!_mv_840.has_value) {
            }
            i = (i + 1);
        }
    }
}

void defn_emit_postconditions(context_TranspileContext* ctx, slop_list_types_SExpr_ptr postconditions) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((postconditions).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_841 = ({ __auto_type _lst = postconditions; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_841.has_value) {
                __auto_type cond_expr = _mv_841.value;
                {
                    __auto_type cond_c_raw = expr_transpile_expr(ctx, cond_expr);
                    __auto_type cond_c = strlib_replace(arena, strlib_replace(arena, cond_c_raw, SLOP_STR("_result"), SLOP_STR("_retval")), SLOP_STR("$result"), SLOP_STR("_retval"));
                    __auto_type expr_str = parser_pretty_print(arena, cond_expr);
                    __auto_type escaped_str = defn_escape_for_c_string(arena, expr_str);
                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("SLOP_POST(("), cond_c, SLOP_STR("), \""), escaped_str, SLOP_STR("\");")));
                }
            } else if (!_mv_841.has_value) {
            }
            i = (i + 1);
        }
    }
}

void defn_emit_assumptions(context_TranspileContext* ctx, slop_list_types_SExpr_ptr assumptions) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((assumptions).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_842 = ({ __auto_type _lst = assumptions; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_842.has_value) {
                __auto_type cond_expr = _mv_842.value;
                {
                    __auto_type cond_c_raw = expr_transpile_expr(ctx, cond_expr);
                    __auto_type cond_c = strlib_replace(arena, strlib_replace(arena, cond_c_raw, SLOP_STR("_result"), SLOP_STR("_retval")), SLOP_STR("$result"), SLOP_STR("_retval"));
                    __auto_type expr_str = parser_pretty_print(arena, cond_expr);
                    __auto_type escaped_str = defn_escape_for_c_string(arena, expr_str);
                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("SLOP_POST(("), cond_c, SLOP_STR("), \""), escaped_str, SLOP_STR("\");")));
                }
            } else if (!_mv_842.has_value) {
            }
            i = (i + 1);
        }
    }
}

slop_string defn_escape_for_c_string(slop_arena* arena, slop_string s) {
    {
        __auto_type len = ((int64_t)(s.len));
        __auto_type buf = ((uint8_t*)((uint8_t*)slop_arena_alloc(arena, ((len * 2) + 1))));
        __auto_type out_idx = 0;
        __auto_type in_idx = 0;
        while ((in_idx < len)) {
            {
                __auto_type c = s.data[in_idx];
                if ((c == 92)) {
                    buf[out_idx] = 92;
                    out_idx = (out_idx + 1);
                    buf[out_idx] = 92;
                    out_idx = (out_idx + 1);
                } else if ((c == 34)) {
                    buf[out_idx] = 92;
                    out_idx = (out_idx + 1);
                    buf[out_idx] = 34;
                    out_idx = (out_idx + 1);
                } else if ((c == 10)) {
                    buf[out_idx] = 92;
                    out_idx = (out_idx + 1);
                    buf[out_idx] = 110;
                    out_idx = (out_idx + 1);
                } else if ((c == 9)) {
                    buf[out_idx] = 92;
                    out_idx = (out_idx + 1);
                    buf[out_idx] = 116;
                    out_idx = (out_idx + 1);
                } else {
                    buf[out_idx] = c;
                    out_idx = (out_idx + 1);
                }
            }
            in_idx = (in_idx + 1);
        }
        buf[out_idx] = 0;
        return (slop_string){.len = ((uint64_t)(out_idx)), .data = buf};
    }
}

