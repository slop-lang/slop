#include "../runtime/slop_runtime.h"
#include "slop_defn.h"

uint8_t defn_is_type_form(types_SExpr* expr);
uint8_t defn_is_function_form(types_SExpr* expr);
uint8_t defn_is_const_form(types_SExpr* expr);
uint8_t defn_is_ffi_form(types_SExpr* expr);
uint8_t defn_is_ffi_struct_form(types_SExpr* expr);
uint8_t defn_has_generic_annotation(slop_list_types_SExpr_ptr items);
uint8_t defn_is_pointer_type_expr(types_SExpr* type_expr);
void defn_transpile_const(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_exported);
void defn_emit_const_def(context_TranspileContext* ctx, slop_string c_name, types_SExpr* type_expr, types_SExpr* value_expr, uint8_t is_exported);
slop_string defn_get_type_name_str(types_SExpr* type_expr);
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
void defn_register_union_variant_fields(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, slop_list_types_SExpr_ptr items, int64_t start_idx);
void defn_transpile_type_alias(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, types_SExpr* type_expr);
uint8_t defn_is_generic_type_alias(slop_string s);
uint8_t defn_is_array_type(types_SExpr* type_expr);
void defn_emit_array_typedef(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, types_SExpr* type_expr);
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
slop_string defn_extract_spec_slop_return_type(context_TranspileContext* ctx, types_SExpr* spec_expr);
slop_string defn_get_slop_return_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_option_string defn_get_result_type_name(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_option_string defn_extract_result_type_name(context_TranspileContext* ctx, types_SExpr* spec_expr);
slop_option_string defn_check_result_type(context_TranspileContext* ctx, types_SExpr* type_expr);
slop_string defn_build_result_name(slop_arena* arena, slop_string ok_type, slop_string err_type);
slop_string defn_build_param_str(context_TranspileContext* ctx, types_SExpr* params_expr);
slop_string defn_build_single_param(context_TranspileContext* ctx, types_SExpr* param);
uint8_t defn_is_param_mode(slop_list_types_SExpr_ptr items);
slop_string defn_param_mode_word(slop_list_types_SExpr_ptr items);
void defn_check_param_mode(context_TranspileContext* ctx, slop_string mode, slop_string name, slop_string slop_type, types_SExpr* at);
uint8_t defn_is_container_slop_type(context_TranspileContext* ctx, slop_string slop_type);
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
uint8_t defn_is_verification_only_expr(types_SExpr* expr);
uint8_t defn_is_doc_form(types_SExpr* expr);
slop_option_string defn_get_doc_string(types_SExpr* expr);
slop_option_string defn_collect_doc_string(slop_arena* arena, slop_list_types_SExpr_ptr items);
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
    __auto_type _mv_1095 = (*expr);
    switch (_mv_1095.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1095.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1096 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1096.has_value) {
                        __auto_type head = _mv_1096.value;
                        __auto_type _mv_1097 = (*head);
                        switch (_mv_1097.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1097.data.sym;
                                return string_eq(sym.name, SLOP_STR("type"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1096.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
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
    __auto_type _mv_1098 = (*expr);
    switch (_mv_1098.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1098.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1099 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1099.has_value) {
                        __auto_type head = _mv_1099.value;
                        __auto_type _mv_1100 = (*head);
                        switch (_mv_1100.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1100.data.sym;
                                return string_eq(sym.name, SLOP_STR("fn"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1099.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
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
    __auto_type _mv_1101 = (*expr);
    switch (_mv_1101.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1101.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1102 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1102.has_value) {
                        __auto_type head = _mv_1102.value;
                        __auto_type _mv_1103 = (*head);
                        switch (_mv_1103.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1103.data.sym;
                                return string_eq(sym.name, SLOP_STR("const"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1102.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
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
    __auto_type _mv_1104 = (*expr);
    switch (_mv_1104.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1104.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1105 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1105.has_value) {
                        __auto_type head = _mv_1105.value;
                        __auto_type _mv_1106 = (*head);
                        switch (_mv_1106.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1106.data.sym;
                                return string_eq(sym.name, SLOP_STR("ffi"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1105.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
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
    __auto_type _mv_1107 = (*expr);
    switch (_mv_1107.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1107.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1108 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1108.has_value) {
                        __auto_type head = _mv_1108.value;
                        __auto_type _mv_1109 = (*head);
                        switch (_mv_1109.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1109.data.sym;
                                return string_eq(sym.name, SLOP_STR("ffi-struct"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1108.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        default: {
            return 0;
        }
    }
}

uint8_t defn_has_generic_annotation(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 0;
        uint8_t found = 0;
        while ((i < len) && !(found)) {
            __auto_type _mv_1110 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1110.has_value) {
                __auto_type item = _mv_1110.value;
                __auto_type _mv_1111 = (*item);
                switch (_mv_1111.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type lst = _mv_1111.data.lst;
                        {
                            __auto_type sub_items = lst.items;
                            if (((int64_t)((sub_items).len)) > 0) {
                                __auto_type _mv_1112 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1112.has_value) {
                                    __auto_type head = _mv_1112.value;
                                    __auto_type _mv_1113 = (*head);
                                    switch (_mv_1113.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_1113.data.sym;
                                            if (string_eq(sym.name, SLOP_STR("@generic"))) {
                                                found = 1;
                                            } else {
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_1112.has_value) {
                                }
                            } else {
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1110.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

uint8_t defn_is_pointer_type_expr(types_SExpr* type_expr) {
    __auto_type _mv_1114 = (*type_expr);
    switch (_mv_1114.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1114.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1115 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1115.has_value) {
                        __auto_type head = _mv_1115.value;
                        __auto_type _mv_1116 = (*head);
                        switch (_mv_1116.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1116.data.sym;
                                return (string_eq(sym.name, SLOP_STR("Ptr")) || string_eq(sym.name, SLOP_STR("ScopedPtr")));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1115.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
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
        __auto_type _mv_1117 = (*expr);
        switch (_mv_1117.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1117.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len < 4) {
                        context_ctx_fail(ctx, SLOP_STR("invalid const: need name, type, value"));
                    } else {
                        __auto_type _mv_1118 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1118.has_value) {
                            __auto_type name_expr = _mv_1118.value;
                            __auto_type _mv_1119 = (*name_expr);
                            switch (_mv_1119.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_1119.data.sym;
                                    {
                                        __auto_type raw_name = name_sym.name;
                                        __auto_type base_name = ctype_to_c_name(arena, raw_name);
                                        __auto_type c_name = context_ctx_prefix_type(ctx, base_name);
                                        __auto_type _mv_1120 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1120.has_value) {
                                            __auto_type type_expr = _mv_1120.value;
                                            {
                                                __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                                                context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, SLOP_STR("auto"), slop_type_str, 0, 0, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_const});
                                                __auto_type _mv_1121 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1121.has_value) {
                                                    __auto_type value_expr = _mv_1121.value;
                                                    defn_emit_const_def(ctx, c_name, type_expr, value_expr, is_exported);
                                                } else if (!_mv_1121.has_value) {
                                                    context_ctx_fail(ctx, SLOP_STR("missing const value"));
                                                }
                                            }
                                        } else if (!_mv_1120.has_value) {
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
                        } else if (!_mv_1118.has_value) {
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
        if (ctype_is_int_type(type_name)) {
            if (!(is_exported)) {
                {
                    __auto_type value_c = defn_eval_const_value(ctx, value_expr);
                    context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("#define "), c_name, SLOP_STR(" ("), context_ctx_str(ctx, value_c, SLOP_STR(")"))));
                }
            }
        } else {
            {
                __auto_type storage = ((is_exported) ? SLOP_STR("const ") : SLOP_STR("static const "));
                if (string_eq(context_ctx_resolve_plain_type_alias(ctx, type_name), SLOP_STR("String"))) {
                    __auto_type _mv_1122 = (*value_expr);
                    switch (_mv_1122.tag) {
                        case types_SExpr_str:
                        {
                            __auto_type str = _mv_1122.data.str;
                            context_ctx_emit(ctx, context_ctx_str5(ctx, storage, c_type, SLOP_STR(" "), c_name, context_ctx_str3(ctx, SLOP_STR(" = SLOP_STR(\""), expr_escape_c_string(ctx, str.value), SLOP_STR("\");"))));
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
    __auto_type _mv_1123 = (*type_expr);
    switch (_mv_1123.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1123.data.sym;
            return sym.name;
        }
        default: {
            return SLOP_STR("");
        }
    }
}

slop_string defn_eval_const_value(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1124 = (*expr);
        switch (_mv_1124.tag) {
            case types_SExpr_num:
            {
                __auto_type num = _mv_1124.data.num;
                return num.raw;
            }
            case types_SExpr_str:
            {
                __auto_type str = _mv_1124.data.str;
                return context_ctx_str3(ctx, SLOP_STR("\""), expr_escape_c_string(ctx, str.value), SLOP_STR("\""));
            }
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_1124.data.sym;
                return ctype_to_c_name(arena, sym.name);
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1124.data.lst;
                return expr_transpile_expr(ctx, expr);
            }
        }
        SLOP_UNREACHABLE();
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
        __auto_type _mv_1125 = (*expr);
        switch (_mv_1125.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1125.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    {
                        __auto_type name_idx = ((((len >= 2) && defn_is_string_expr(items, 1))) ? 2 : 1);
                        if (len >= (name_idx + 1)) {
                            __auto_type _mv_1126 = ({ __auto_type _lst = items; size_t _idx = (size_t)name_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1126.has_value) {
                                __auto_type name_expr = _mv_1126.value;
                                __auto_type _mv_1127 = (*name_expr);
                                switch (_mv_1127.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1127.data.sym;
                                        {
                                            __auto_type type_name = sym.name;
                                            __auto_type c_name = ctype_to_c_name(arena, type_name);
                                            {
                                                __auto_type actual_c_name = ((defn_ends_with_t(type_name)) ? c_name : context_ctx_str(ctx, SLOP_STR("struct "), c_name));
                                                context_ctx_register_type(ctx, (context_TypeEntry){type_name, c_name, actual_c_name, 0, 1, 0, context_ctx_current_module_name(ctx), SLOP_STR("")});
                                            }
                                        }
                                        break;
                                    }
                                    default: {
                                        break;
                                    }
                                }
                            } else if (!_mv_1126.has_value) {
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
    __auto_type _mv_1128 = ({ __auto_type _lst = items; size_t _idx = (size_t)idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
    if (_mv_1128.has_value) {
        __auto_type item = _mv_1128.value;
        __auto_type _mv_1129 = (*item);
        switch (_mv_1129.tag) {
            case types_SExpr_str:
            {
                __auto_type _ = _mv_1129.data.str;
                return 1;
            }
            default: {
                return 0;
            }
        }
    } else if (!_mv_1128.has_value) {
        return 0;
    }
    SLOP_UNREACHABLE();
}

uint8_t defn_ends_with_t(slop_string name) {
    return strlib_ends_with(name, SLOP_STR("_t"));
}

void defn_transpile_type(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1130 = (*expr);
        switch (_mv_1130.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1130.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len < 3) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid type: need name and definition"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    } else {
                        __auto_type _mv_1131 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1131.has_value) {
                            __auto_type name_expr = _mv_1131.value;
                            __auto_type _mv_1132 = (*name_expr);
                            switch (_mv_1132.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_1132.data.sym;
                                    {
                                        __auto_type raw_name = name_sym.name;
                                        __auto_type base_name = ctype_to_c_name(arena, raw_name);
                                        __auto_type qualified_name = ((context_ctx_prefixing_enabled(ctx)) ? ({ __auto_type _mv = context_ctx_get_module(ctx); _mv.has_value ? ({ __auto_type mod_name = _mv.value; context_ctx_str(ctx, ctype_to_c_name(arena, mod_name), context_ctx_str(ctx, SLOP_STR("_"), base_name)); }) : (base_name); }) : base_name);
                                        __auto_type _mv_1133 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1133.has_value) {
                                            __auto_type type_def = _mv_1133.value;
                                            defn_dispatch_type_def(ctx, raw_name, qualified_name, type_def);
                                        } else if (!_mv_1133.has_value) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("missing type definition"), context_ctx_sexpr_line(name_expr), context_ctx_sexpr_col(name_expr));
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    context_ctx_add_error_at(ctx, SLOP_STR("type name must be symbol"), context_ctx_sexpr_line(name_expr), context_ctx_sexpr_col(name_expr));
                                    break;
                                }
                            }
                        } else if (!_mv_1131.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing type name"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid type form"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                break;
            }
        }
    }
}

void defn_dispatch_type_def(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    __auto_type _mv_1134 = (*type_def);
    switch (_mv_1134.tag) {
        case types_SExpr_lst:
        {
            __auto_type def_lst = _mv_1134.data.lst;
            {
                __auto_type items = def_lst.items;
                if (((int64_t)((items).len)) < 1) {
                    context_ctx_add_error_at(ctx, SLOP_STR("empty type definition"), context_ctx_sexpr_line(type_def), context_ctx_sexpr_col(type_def));
                } else {
                    __auto_type _mv_1135 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1135.has_value) {
                        __auto_type head = _mv_1135.value;
                        __auto_type _mv_1136 = (*head);
                        switch (_mv_1136.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1136.data.sym;
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
                                context_ctx_add_error_at(ctx, SLOP_STR("invalid type definition head"), context_ctx_sexpr_line(head), context_ctx_sexpr_col(head));
                                break;
                            }
                        }
                    } else if (!_mv_1135.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("empty type definition"), context_ctx_sexpr_line(type_def), context_ctx_sexpr_col(type_def));
                    }
                }
            }
            break;
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1134.data.sym;
            defn_transpile_type_alias(ctx, raw_name, qualified_name, type_def);
            break;
        }
        default: {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid type definition form"), context_ctx_sexpr_line(type_def), context_ctx_sexpr_col(type_def));
            break;
        }
    }
}

uint8_t defn_has_payload_variants(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 1;
        uint8_t found = 0;
        while ((i < len) && !(found)) {
            __auto_type _mv_1137 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1137.has_value) {
                __auto_type item = _mv_1137.value;
                __auto_type _mv_1138 = (*item);
                switch (_mv_1138.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type _ = _mv_1138.data.lst;
                        found = 1;
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1137.has_value) {
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
        __auto_type _mv_1139 = (*expr);
        switch (_mv_1139.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1139.data.lst;
                {
                    __auto_type items = lst.items;
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("struct "), qualified_name, SLOP_STR(" {")));
                    defn_emit_record_fields(ctx, raw_name, qualified_name, items, 1);
                    context_ctx_emit(ctx, SLOP_STR("};"));
                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("typedef struct "), qualified_name, SLOP_STR(" "), qualified_name, SLOP_STR(";")));
                    context_ctx_emit(ctx, SLOP_STR(""));
                    context_ctx_register_type(ctx, (context_TypeEntry){raw_name, qualified_name, qualified_name, 0, 1, 0, context_ctx_current_module_name(ctx), SLOP_STR("")});
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid record form"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
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
        int64_t i = start_idx;
        while (i < len) {
            __auto_type _mv_1140 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1140.has_value) {
                __auto_type field_expr = _mv_1140.value;
                defn_emit_record_field(ctx, raw_type_name, qualified_type_name, field_expr);
            } else if (!_mv_1140.has_value) {
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
        __auto_type _mv_1141 = (*field);
        switch (_mv_1141.tag) {
            case types_SExpr_lst:
            {
                __auto_type field_lst = _mv_1141.data.lst;
                {
                    __auto_type items = field_lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len < 2) {
                        context_ctx_emit(ctx, SLOP_STR("    /* invalid field */"));
                    } else {
                        __auto_type _mv_1142 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1142.has_value) {
                            __auto_type name_expr = _mv_1142.value;
                            __auto_type _mv_1143 = (*name_expr);
                            switch (_mv_1143.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_1143.data.sym;
                                    __auto_type _mv_1144 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_1144.has_value) {
                                        __auto_type type_expr = _mv_1144.value;
                                        {
                                            __auto_type raw_field_name = name_sym.name;
                                            __auto_type field_name = ctype_to_c_name(arena, raw_field_name);
                                            __auto_type field_type = context_to_c_type_prefixed(ctx, type_expr);
                                            __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                                            __auto_type is_ptr = defn_is_pointer_type_expr(type_expr);
                                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("    "), field_type, SLOP_STR(" "), field_name, SLOP_STR(";")));
                                            context_ctx_register_field_type(ctx, qualified_type_name, raw_field_name, field_type, slop_type_str, is_ptr);
                                        }
                                    } else if (!_mv_1144.has_value) {
                                        context_ctx_emit(ctx, SLOP_STR("    /* missing field type */"));
                                    }
                                    break;
                                }
                                default: {
                                    context_ctx_emit(ctx, SLOP_STR("    /* field name must be symbol */"));
                                    break;
                                }
                            }
                        } else if (!_mv_1142.has_value) {
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
        __auto_type _mv_1145 = (*expr);
        switch (_mv_1145.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1145.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    context_ctx_emit(ctx, SLOP_STR("typedef enum {"));
                    defn_emit_enum_values(ctx, qualified_name, items, 1, len);
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("} "), qualified_name, SLOP_STR(";")));
                    context_ctx_emit(ctx, SLOP_STR(""));
                    context_ctx_register_type(ctx, (context_TypeEntry){raw_name, qualified_name, qualified_name, 1, 0, 0, context_ctx_current_module_name(ctx), SLOP_STR("")});
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid enum form"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                break;
            }
        }
    }
}

void defn_emit_enum_values(context_TranspileContext* ctx, slop_string type_name, slop_list_types_SExpr_ptr items, int64_t start_idx, int64_t len) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        int64_t i = start_idx;
        while (i < len) {
            __auto_type _mv_1146 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1146.has_value) {
                __auto_type val_expr = _mv_1146.value;
                __auto_type _mv_1147 = (*val_expr);
                switch (_mv_1147.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_1147.data.sym;
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
            } else if (!_mv_1146.has_value) {
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
        __auto_type _mv_1148 = (*expr);
        switch (_mv_1148.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1148.data.lst;
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
                    context_ctx_register_type(ctx, (context_TypeEntry){raw_name, qualified_name, qualified_name, 0, 0, 1, context_ctx_current_module_name(ctx), SLOP_STR("")});
                    defn_register_union_variant_fields(ctx, raw_name, qualified_name, items, 1);
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid union form"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
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
        int64_t i = start_idx;
        while (i < len) {
            __auto_type _mv_1149 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1149.has_value) {
                __auto_type variant_expr = _mv_1149.value;
                __auto_type _mv_1150 = (*variant_expr);
                switch (_mv_1150.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type var_lst = _mv_1150.data.lst;
                        {
                            __auto_type var_items = var_lst.items;
                            __auto_type var_len = ((int64_t)((var_items).len));
                            if (var_len >= 1) {
                                __auto_type _mv_1151 = ({ __auto_type _lst = var_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1151.has_value) {
                                    __auto_type tag_expr = _mv_1151.value;
                                    __auto_type _mv_1152 = (*tag_expr);
                                    switch (_mv_1152.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type tag_sym = _mv_1152.data.sym;
                                            {
                                                __auto_type tag_name = tag_sym.name;
                                                __auto_type c_tag = ctype_to_c_name(arena, tag_name);
                                                if (var_len == 2) {
                                                    __auto_type _mv_1153 = ({ __auto_type _lst = var_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_1153.has_value) {
                                                        __auto_type type_expr = _mv_1153.value;
                                                        {
                                                            __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                            {
                                                                __auto_type actual_type = ((string_eq(c_type, SLOP_STR("void"))) ? SLOP_STR("int") : c_type);
                                                                context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("        "), actual_type, SLOP_STR(" "), c_tag, SLOP_STR(";")));
                                                            }
                                                        }
                                                    } else if (!_mv_1153.has_value) {
                                                    }
                                                } else if (var_len >= 3) {
                                                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("        struct { "), SLOP_STR(""), SLOP_STR("")));
                                                    for (int64_t fi = 1; fi < var_len; fi++) {
                                                        __auto_type _mv_1154 = ({ __auto_type _lst = var_items; size_t _idx = (size_t)fi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                        if (_mv_1154.has_value) {
                                                            __auto_type type_expr = _mv_1154.value;
                                                            {
                                                                __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                                {
                                                                    __auto_type actual_type = ((string_eq(c_type, SLOP_STR("void"))) ? SLOP_STR("int") : c_type);
                                                                    __auto_type field_name = context_ctx_str(ctx, SLOP_STR("f"), int_to_string(arena, (fi - 1)));
                                                                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("            "), actual_type, SLOP_STR(" "), field_name, SLOP_STR(";")));
                                                                }
                                                            }
                                                        } else if (!_mv_1154.has_value) {
                                                        }
                                                    }
                                                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("        } "), c_tag, SLOP_STR(";")));
                                                } else {
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_1151.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1149.has_value) {
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
        int64_t i = start_idx;
        int64_t tag_idx = 0;
        while (i < len) {
            __auto_type _mv_1155 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1155.has_value) {
                __auto_type variant_expr = _mv_1155.value;
                __auto_type _mv_1156 = (*variant_expr);
                switch (_mv_1156.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type var_lst = _mv_1156.data.lst;
                        {
                            __auto_type var_items = var_lst.items;
                            if (((int64_t)((var_items).len)) >= 1) {
                                __auto_type _mv_1157 = ({ __auto_type _lst = var_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1157.has_value) {
                                    __auto_type tag_expr = _mv_1157.value;
                                    __auto_type _mv_1158 = (*tag_expr);
                                    switch (_mv_1158.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type tag_sym = _mv_1158.data.sym;
                                            {
                                                __auto_type tag_name = tag_sym.name;
                                                __auto_type define_name = context_ctx_str4(ctx, type_name, SLOP_STR("_"), ctype_to_c_name(arena, tag_name), SLOP_STR("_TAG"));
                                                context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("#define "), define_name, SLOP_STR(" "), int_to_string(arena, tag_idx)));
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_1157.has_value) {
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
            } else if (!_mv_1155.has_value) {
            }
            i = (i + 1);
        }
    }
}

void defn_register_union_variant_fields(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, slop_list_types_SExpr_ptr items, int64_t start_idx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        int64_t i = start_idx;
        while (i < len) {
            __auto_type _mv_1159 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1159.has_value) {
                __auto_type variant_expr = _mv_1159.value;
                __auto_type _mv_1160 = (*variant_expr);
                switch (_mv_1160.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type var_lst = _mv_1160.data.lst;
                        {
                            __auto_type var_items = var_lst.items;
                            __auto_type var_len = ((int64_t)((var_items).len));
                            if (var_len >= 2) {
                                __auto_type _mv_1161 = ({ __auto_type _lst = var_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1161.has_value) {
                                    __auto_type tag_expr = _mv_1161.value;
                                    __auto_type _mv_1162 = (*tag_expr);
                                    switch (_mv_1162.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type tag_sym = _mv_1162.data.sym;
                                            {
                                                __auto_type tag_name = tag_sym.name;
                                                if (var_len == 2) {
                                                    __auto_type _mv_1163 = ({ __auto_type _lst = var_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_1163.has_value) {
                                                        __auto_type type_expr = _mv_1163.value;
                                                        {
                                                            __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                            __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                                                            __auto_type is_ptr = defn_is_pointer_type_expr(type_expr);
                                                            context_ctx_register_field_type(ctx, qualified_name, tag_name, c_type, slop_type_str, is_ptr);
                                                        }
                                                    } else if (!_mv_1163.has_value) {
                                                    }
                                                } else if (var_len >= 3) {
                                                    {
                                                        __auto_type count_key = context_ctx_str3(ctx, tag_name, SLOP_STR("__count"), SLOP_STR(""));
                                                        __auto_type count_str = int_to_string(arena, (var_len - 1));
                                                        context_ctx_register_field_type(ctx, qualified_name, count_key, count_str, SLOP_STR(""), 0);
                                                    }
                                                    for (int64_t fi = 1; fi < var_len; fi++) {
                                                        __auto_type _mv_1164 = ({ __auto_type _lst = var_items; size_t _idx = (size_t)fi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                        if (_mv_1164.has_value) {
                                                            __auto_type type_expr = _mv_1164.value;
                                                            {
                                                                __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                                __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                                                                __auto_type is_ptr = defn_is_pointer_type_expr(type_expr);
                                                                __auto_type field_key = context_ctx_str3(ctx, tag_name, SLOP_STR("__"), int_to_string(arena, (fi - 1)));
                                                                context_ctx_register_field_type(ctx, qualified_name, field_key, c_type, slop_type_str, is_ptr);
                                                            }
                                                        } else if (!_mv_1164.has_value) {
                                                        }
                                                    }
                                                    __auto_type _mv_1165 = ({ __auto_type _lst = var_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_1165.has_value) {
                                                        __auto_type type_expr = _mv_1165.value;
                                                        {
                                                            __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                            __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                                                            __auto_type is_ptr = defn_is_pointer_type_expr(type_expr);
                                                            context_ctx_register_field_type(ctx, qualified_name, tag_name, c_type, slop_type_str, is_ptr);
                                                        }
                                                    } else if (!_mv_1165.has_value) {
                                                    }
                                                } else {
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_1161.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1159.has_value) {
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
            defn_emit_array_typedef(ctx, raw_name, qualified_name, type_expr);
        } else if (defn_is_range_type(type_expr)) {
            defn_emit_range_typedef(ctx, raw_name, qualified_name, type_expr);
        } else {
            {
                __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("typedef "), c_type, SLOP_STR(" "), qualified_name, SLOP_STR(";")));
                context_ctx_emit(ctx, SLOP_STR(""));
                context_ctx_register_type(ctx, (context_TypeEntry){raw_name, qualified_name, c_type, 0, 0, 0, context_ctx_current_module_name(ctx), SLOP_STR("")});
                if (defn_is_generic_type_alias(slop_type_str)) {
                    context_ctx_register_type_alias(ctx, raw_name, slop_type_str);
                }
            }
        }
    }
}

uint8_t defn_is_generic_type_alias(slop_string s) {
    return (strlib_starts_with(s, SLOP_STR("(Map ")) || (strlib_starts_with(s, SLOP_STR("(Set ")) || (strlib_starts_with(s, SLOP_STR("(Result ")) || strlib_starts_with(s, SLOP_STR("(Option ")))));
}

uint8_t defn_is_array_type(types_SExpr* type_expr) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_1166 = (*type_expr);
    switch (_mv_1166.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1166.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1167 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1167.has_value) {
                        __auto_type head = _mv_1167.value;
                        __auto_type _mv_1168 = (*head);
                        switch (_mv_1168.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1168.data.sym;
                                return string_eq(sym.name, SLOP_STR("Array"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1167.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        default: {
            return 0;
        }
    }
}

void defn_emit_array_typedef(context_TranspileContext* ctx, slop_string raw_name, slop_string qualified_name, types_SExpr* type_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1169 = (*type_expr);
        switch (_mv_1169.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1169.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len < 3) {
                        context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("typedef void* "), context_ctx_str(ctx, qualified_name, SLOP_STR(";"))));
                    } else {
                        __auto_type _mv_1170 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1170.has_value) {
                            __auto_type elem_type_expr = _mv_1170.value;
                            __auto_type _mv_1171 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1171.has_value) {
                                __auto_type size_expr = _mv_1171.value;
                                {
                                    __auto_type elem_c_type = context_to_c_type_prefixed(ctx, elem_type_expr);
                                    __auto_type size_str = defn_get_number_as_string(size_expr);
                                    context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("typedef "), context_ctx_str(ctx, elem_c_type, context_ctx_str(ctx, SLOP_STR(" "), context_ctx_str(ctx, qualified_name, context_ctx_str3(ctx, SLOP_STR("["), size_str, SLOP_STR("];")))))));
                                    context_ctx_emit(ctx, SLOP_STR(""));
                                    {
                                        __auto_type ptr_type = context_ctx_str(ctx, elem_c_type, SLOP_STR("*"));
                                        context_ctx_register_type(ctx, (context_TypeEntry){raw_name, qualified_name, ptr_type, 0, 0, 0, context_ctx_current_module_name(ctx), SLOP_STR("")});
                                    }
                                }
                            } else if (!_mv_1171.has_value) {
                                context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("typedef void* "), context_ctx_str(ctx, qualified_name, SLOP_STR(";"))));
                            }
                        } else if (!_mv_1170.has_value) {
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
    __auto_type _mv_1172 = (*expr);
    switch (_mv_1172.tag) {
        case types_SExpr_num:
        {
            __auto_type num = _mv_1172.data.num;
            return num.raw;
        }
        default: {
            return SLOP_STR("0");
        }
    }
}

uint8_t defn_is_range_type(types_SExpr* type_expr) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_1173 = (*type_expr);
    switch (_mv_1173.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1173.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                uint8_t found_dots = 0;
                int64_t i = 0;
                while ((i < len) && !(found_dots)) {
                    __auto_type _mv_1174 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1174.has_value) {
                        __auto_type item = _mv_1174.value;
                        __auto_type _mv_1175 = (*item);
                        switch (_mv_1175.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1175.data.sym;
                                if (string_eq(sym.name, SLOP_STR(".."))) {
                                    found_dots = 1;
                                }
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_1174.has_value) {
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
        int64_t min_val = 0;
        int64_t max_val = 0;
        uint8_t has_min = 0;
        uint8_t has_max = 0;
        uint8_t found_dots = 0;
        __auto_type _mv_1176 = (*type_expr);
        switch (_mv_1176.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1176.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    int64_t i = 1;
                    while (i < len) {
                        __auto_type _mv_1177 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1177.has_value) {
                            __auto_type item = _mv_1177.value;
                            __auto_type _mv_1178 = (*item);
                            switch (_mv_1178.tag) {
                                case types_SExpr_num:
                                {
                                    __auto_type num = _mv_1178.data.num;
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
                                    __auto_type sym = _mv_1178.data.sym;
                                    if (string_eq(sym.name, SLOP_STR(".."))) {
                                        found_dots = 1;
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1177.has_value) {
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
        int64_t result = 0;
        int64_t i = 0;
        uint8_t negative = 0;
        if ((len > 0) && (s.data[0] == 45)) {
            negative = 1;
            i = 1;
        }
        while (i < len) {
            {
                __auto_type c = s.data[i];
                if ((c >= 48) && (c <= 57)) {
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
    if (has_min && has_max) {
        if ((min_val >= 0) && (max_val <= 255)) {
            return SLOP_STR("uint8_t");
        } else if ((min_val >= 0) && (max_val <= 65535)) {
            return SLOP_STR("uint16_t");
        } else if ((min_val >= (0 - 128)) && (max_val <= 127)) {
            return SLOP_STR("int8_t");
        } else if ((min_val >= (0 - 32768)) && (max_val <= 32767)) {
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
        context_ctx_emit(ctx, strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 15 * sizeof(slop_string)), .len = 15, .cap = 15, .arena = arena }; _ll.data[0] = SLOP_STR("return SLOP_RANGE("); _ll.data[1] = qualified_name; _ll.data[2] = SLOP_STR(", v, "); _ll.data[3] = ((has_min) ? SLOP_STR("1") : SLOP_STR("0")); _ll.data[4] = SLOP_STR(", "); _ll.data[5] = ((has_max) ? SLOP_STR("1") : SLOP_STR("0")); _ll.data[6] = SLOP_STR(", "); _ll.data[7] = ((has_min) ? int_to_string(arena, min_val) : SLOP_STR("0")); _ll.data[8] = SLOP_STR(", "); _ll.data[9] = ((has_max) ? int_to_string(arena, max_val) : SLOP_STR("0")); _ll.data[10] = SLOP_STR(", \""); _ll.data[11] = raw_name; _ll.data[12] = SLOP_STR(" "); _ll.data[13] = parser_pretty_print(arena, type_expr); _ll.data[14] = SLOP_STR("\");"); _ll; })));
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
        context_ctx_emit(ctx, SLOP_STR(""));
        context_ctx_register_type(ctx, (context_TypeEntry){raw_name, qualified_name, c_type, 0, 0, 0, context_ctx_current_module_name(ctx), SLOP_STR("")});
        context_ctx_register_type_alias(ctx, raw_name, parser_pretty_print(arena, type_expr));
    }
}

void defn_transpile_function(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    context_ctx_set_pos(ctx, expr);
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1179 = (*expr);
        switch (_mv_1179.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1179.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len < 3) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid fn: need name and params"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    } else {
                        __auto_type _mv_1180 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1180.has_value) {
                            __auto_type name_expr = _mv_1180.value;
                            __auto_type _mv_1181 = (*name_expr);
                            switch (_mv_1181.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_1181.data.sym;
                                    {
                                        __auto_type raw_name = name_sym.name;
                                        __auto_type base_name = ctype_to_c_name(arena, raw_name);
                                        __auto_type mangled_name = ((string_eq(base_name, SLOP_STR("main"))) ? base_name : context_ctx_prefix_type(ctx, base_name));
                                        __auto_type base_fn_name = context_extract_fn_c_name(arena, items, mangled_name);
                                        __auto_type fn_name = base_fn_name;
                                        __auto_type is_public_api = !(string_eq(base_fn_name, mangled_name));
                                        __auto_type _mv_1182 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1182.has_value) {
                                            __auto_type params_expr = _mv_1182.value;
                                            defn_emit_function_def(ctx, raw_name, fn_name, params_expr, items, is_public_api);
                                        } else if (!_mv_1182.has_value) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("missing params"), context_ctx_sexpr_line(name_expr), context_ctx_sexpr_col(name_expr));
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    context_ctx_add_error_at(ctx, SLOP_STR("function name must be symbol"), context_ctx_sexpr_line(name_expr), context_ctx_sexpr_col(name_expr));
                                    break;
                                }
                            }
                        } else if (!_mv_1180.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing function name"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid fn form"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
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
        __auto_type doc_string = defn_collect_doc_string(arena, items);
        {
            slop_string return_type = ({ __auto_type _mv = result_type_opt; _mv.has_value ? ({ __auto_type result_name = _mv.value; result_name; }) : (raw_return); });
            __auto_type actual_return = ((string_eq(fn_name, SLOP_STR("main"))) ? SLOP_STR("int") : return_type);
            __auto_type param_str = ((string_eq(fn_name, SLOP_STR("main"))) ? SLOP_STR("int argc, char** _c_argv") : defn_build_param_str(ctx, params_expr));
            __auto_type has_post = ((((int64_t)((postconditions).len)) > 0) || (((int64_t)((assumptions).len)) > 0));
            __auto_type needs_retval = (has_post && !(string_eq(actual_return, SLOP_STR("void"))));
            context_ctx_set_current_return_type(ctx, actual_return);
            context_ctx_set_current_return_slop_type(ctx, defn_get_slop_return_type(ctx, items));
            __auto_type _mv_1183 = result_type_opt;
            if (_mv_1183.has_value) {
                __auto_type result_name = _mv_1183.value;
                context_ctx_set_current_result_type(ctx, result_name);
            } else if (!_mv_1183.has_value) {
                context_ctx_clear_current_result_type(ctx);
            }
            __auto_type _mv_1184 = doc_string;
            if (_mv_1184.has_value) {
                __auto_type doc = _mv_1184.value;
                context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("/* "), doc, SLOP_STR(" */")));
            } else if (!_mv_1184.has_value) {
            }
            context_ctx_emit(ctx, context_ctx_str5(ctx, actual_return, SLOP_STR(" "), fn_name, SLOP_STR("("), context_ctx_str(ctx, ((string_eq(param_str, SLOP_STR(""))) ? SLOP_STR("void") : param_str), SLOP_STR(") {"))));
            context_ctx_indent(ctx);
            context_ctx_push_scope(ctx);
            defn_bind_params_to_scope(ctx, params_expr);
            if (string_eq(fn_name, SLOP_STR("main"))) {
                context_ctx_emit(ctx, SLOP_STR("uint8_t** argv = (uint8_t**)_c_argv;"));
            }
            defn_emit_preconditions(ctx, preconditions);
            if (needs_retval) {
                context_ctx_emit(ctx, context_ctx_str(ctx, actual_return, SLOP_STR(" _retval = {0};")));
                context_ctx_bind_var(ctx, (context_VarEntry){SLOP_STR("$result"), SLOP_STR("_retval"), actual_return, defn_get_slop_return_type(ctx, items), strlib_ends_with(actual_return, SLOP_STR("*")), 0, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_bound});
            }
            if (needs_retval) {
                context_ctx_set_capture_retval(ctx, 1);
            }
            if (has_post) {
                context_ctx_set_post_exit(ctx, 1);
            }
            context_ctx_set_current_fn_c_name(ctx, fn_name);
            defn_emit_function_body(ctx, items);
            context_ctx_clear_current_fn_c_name(ctx);
            if (needs_retval) {
                context_ctx_set_capture_retval(ctx, 0);
            }
            if (has_post) {
                context_ctx_set_post_exit(ctx, 0);
                if (context_ctx_post_exit_used(ctx)) {
                    context_ctx_emit(ctx, SLOP_STR("_slop_post: ;"));
                }
            }
            context_ctx_set_current_return_slop_type(ctx, SLOP_STR(""));
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
                __auto_type slop_ret_type = defn_get_slop_return_type(ctx, items);
                __auto_type empty_type_params = ((slop_list_string){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
                slop_option_types_SExpr_ptr no_source = (slop_option_types_SExpr_ptr){.has_value = false};
                context_ctx_register_func(ctx, (context_FuncEntry){raw_name, fn_name, actual_return, slop_ret_type, strlib_ends_with(actual_return, SLOP_STR("*")), string_eq(actual_return, SLOP_STR("slop_string")), param_types, 0, empty_type_params, no_source, context_ctx_current_module_name(ctx), SLOP_STR("")});
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
        __auto_type _mv_1185 = (*params_expr);
        switch (_mv_1185.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1185.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    int64_t i = 0;
                    while (i < len) {
                        __auto_type _mv_1186 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1186.has_value) {
                            __auto_type param = _mv_1186.value;
                            defn_bind_single_param(ctx, param);
                        } else if (!_mv_1186.has_value) {
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
        __auto_type _mv_1187 = (*param);
        switch (_mv_1187.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1187.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len >= 2) {
                        {
                            __auto_type has_mode = defn_is_param_mode(items);
                            __auto_type mode = ((has_mode) ? defn_param_mode_word(items) : SLOP_STR("in"));
                            __auto_type name_idx = ((has_mode) ? 1 : 0);
                            __auto_type type_idx = ((has_mode) ? 2 : 1);
                            __auto_type _mv_1188 = ({ __auto_type _lst = items; size_t _idx = (size_t)name_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1188.has_value) {
                                __auto_type name_expr = _mv_1188.value;
                                __auto_type _mv_1189 = (*name_expr);
                                switch (_mv_1189.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type name_sym = _mv_1189.data.sym;
                                        __auto_type _mv_1190 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1190.has_value) {
                                            __auto_type type_expr = _mv_1190.value;
                                            {
                                                __auto_type param_name = name_sym.name;
                                                __auto_type c_name = ctype_to_c_name(arena, param_name);
                                                __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                                                __auto_type is_ptr = defn_is_pointer_type(type_expr);
                                                __auto_type is_closure = defn_is_fn_type(type_expr);
                                                defn_check_param_mode(ctx, mode, param_name, slop_type_str, name_expr);
                                                context_ctx_bind_var(ctx, (context_VarEntry){param_name, c_name, c_type, slop_type_str, is_ptr, string_eq(mode, SLOP_STR("mut")), is_closure, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_param});
                                            }
                                        } else if (!_mv_1190.has_value) {
                                        }
                                        break;
                                    }
                                    default: {
                                        break;
                                    }
                                }
                            } else if (!_mv_1188.has_value) {
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
    __auto_type _mv_1191 = (*type_expr);
    switch (_mv_1191.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1191.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1192 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1192.has_value) {
                        __auto_type head = _mv_1192.value;
                        __auto_type _mv_1193 = (*head);
                        switch (_mv_1193.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1193.data.sym;
                                return string_eq(sym.name, SLOP_STR("Ptr"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1192.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
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
        __auto_type result = ((slop_list_context_FuncParamType_ptr){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
        __auto_type _mv_1194 = (*params_expr);
        switch (_mv_1194.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1194.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    int64_t i = 0;
                    while (i < len) {
                        __auto_type _mv_1195 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1195.has_value) {
                            __auto_type param = _mv_1195.value;
                            {
                                __auto_type c_type = defn_get_param_c_type(ctx, param);
                                __auto_type param_info = ((context_FuncParamType*)(({ __auto_type _alloc = (context_FuncParamType*)slop_arena_alloc(arena, sizeof(context_FuncParamType)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
                                (*param_info).c_type = c_type;
                                (*param_info).slop_type = ctype_param_slop_type_string(arena, param);
                                ({ __auto_type _lst_p = &(result); __auto_type _item = (param_info); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            }
                        } else if (!_mv_1195.has_value) {
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
        __auto_type _mv_1196 = (*param);
        switch (_mv_1196.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1196.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len < 2) {
                        return SLOP_STR("void*");
                    } else {
                        {
                            __auto_type has_mode = ((len >= 3) && defn_is_param_mode(items));
                            __auto_type type_idx = ((has_mode) ? 2 : 1);
                            __auto_type _mv_1197 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1197.has_value) {
                                __auto_type type_expr = _mv_1197.value;
                                return context_to_c_type_prefixed(ctx, type_expr);
                            } else if (!_mv_1197.has_value) {
                                return SLOP_STR("void*");
                            }
                            SLOP_UNREACHABLE();
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
        __auto_type _mv_1198 = (*expr);
        switch (_mv_1198.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1198.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len >= 3) {
                        __auto_type _mv_1199 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1199.has_value) {
                            __auto_type name_expr = _mv_1199.value;
                            __auto_type _mv_1200 = (*name_expr);
                            switch (_mv_1200.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_1200.data.sym;
                                    {
                                        __auto_type raw_name = name_sym.name;
                                        __auto_type base_name = ctype_to_c_name(arena, raw_name);
                                        __auto_type mangled_name = context_ctx_prefix_type(ctx, base_name);
                                        __auto_type fn_name = context_extract_fn_c_name(arena, items, mangled_name);
                                        __auto_type _mv_1201 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1201.has_value) {
                                            __auto_type params_expr = _mv_1201.value;
                                            {
                                                __auto_type result_type_opt = defn_get_result_type_name(ctx, items);
                                                __auto_type raw_return = defn_get_return_type(ctx, items);
                                                {
                                                    slop_string return_type = ({ __auto_type _mv = result_type_opt; _mv.has_value ? ({ __auto_type result_name = _mv.value; result_name; }) : (raw_return); });
                                                    __auto_type actual_return = ((string_eq(base_name, SLOP_STR("main"))) ? SLOP_STR("int") : return_type);
                                                    __auto_type param_str = ((string_eq(base_name, SLOP_STR("main"))) ? SLOP_STR("int argc, char** _c_argv") : defn_build_param_str(ctx, params_expr));
                                                    context_ctx_emit(ctx, context_ctx_str5(ctx, actual_return, SLOP_STR(" "), fn_name, SLOP_STR("("), context_ctx_str(ctx, ((string_eq(param_str, SLOP_STR(""))) ? SLOP_STR("void") : param_str), SLOP_STR(");"))));
                                                }
                                            }
                                        } else if (!_mv_1201.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1199.has_value) {
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
        int64_t i = 3;
        __auto_type result = SLOP_STR("void");
        while (i < len) {
            __auto_type _mv_1202 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1202.has_value) {
                __auto_type item = _mv_1202.value;
                if (defn_is_spec_form(item)) {
                    result = defn_extract_spec_return_type(ctx, item);
                }
            } else if (!_mv_1202.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

uint8_t defn_is_spec_form(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_1203 = (*expr);
    switch (_mv_1203.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1203.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1204 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1204.has_value) {
                        __auto_type head = _mv_1204.value;
                        __auto_type _mv_1205 = (*head);
                        switch (_mv_1205.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1205.data.sym;
                                return string_eq(sym.name, SLOP_STR("@spec"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1204.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
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
        __auto_type _mv_1206 = (*spec_expr);
        switch (_mv_1206.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1206.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) < 2) {
                        return SLOP_STR("void");
                    } else {
                        __auto_type _mv_1207 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1207.has_value) {
                            __auto_type spec_body = _mv_1207.value;
                            __auto_type _mv_1208 = (*spec_body);
                            switch (_mv_1208.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type body_lst = _mv_1208.data.lst;
                                    {
                                        __auto_type body_items = body_lst.items;
                                        __auto_type body_len = ((int64_t)((body_items).len));
                                        if (body_len < 1) {
                                            return SLOP_STR("void");
                                        } else {
                                            __auto_type _mv_1209 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1209.has_value) {
                                                __auto_type ret_type = _mv_1209.value;
                                                return context_to_c_type_prefixed(ctx, ret_type);
                                            } else if (!_mv_1209.has_value) {
                                                return SLOP_STR("void");
                                            }
                                            SLOP_UNREACHABLE();
                                        }
                                    }
                                }
                                default: {
                                    return SLOP_STR("void");
                                }
                            }
                        } else if (!_mv_1207.has_value) {
                            return SLOP_STR("void");
                        }
                        SLOP_UNREACHABLE();
                    }
                }
            }
            default: {
                return SLOP_STR("void");
            }
        }
    }
}

slop_string defn_extract_spec_slop_return_type(context_TranspileContext* ctx, types_SExpr* spec_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((spec_expr != NULL)), "(!= spec-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1210 = (*spec_expr);
        switch (_mv_1210.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1210.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) < 2) {
                        return SLOP_STR("");
                    } else {
                        __auto_type _mv_1211 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1211.has_value) {
                            __auto_type spec_body = _mv_1211.value;
                            __auto_type _mv_1212 = (*spec_body);
                            switch (_mv_1212.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type body_lst = _mv_1212.data.lst;
                                    {
                                        __auto_type body_items = body_lst.items;
                                        __auto_type body_len = ((int64_t)((body_items).len));
                                        if (body_len < 1) {
                                            return SLOP_STR("");
                                        } else {
                                            __auto_type _mv_1213 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1213.has_value) {
                                                __auto_type ret_type = _mv_1213.value;
                                                return parser_pretty_print(arena, ret_type);
                                            } else if (!_mv_1213.has_value) {
                                                return SLOP_STR("");
                                            }
                                            SLOP_UNREACHABLE();
                                        }
                                    }
                                }
                                default: {
                                    return SLOP_STR("");
                                }
                            }
                        } else if (!_mv_1211.has_value) {
                            return SLOP_STR("");
                        }
                        SLOP_UNREACHABLE();
                    }
                }
            }
            default: {
                return SLOP_STR("");
            }
        }
    }
}

slop_string defn_get_slop_return_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 3;
        __auto_type result = SLOP_STR("");
        while (i < len) {
            __auto_type _mv_1214 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1214.has_value) {
                __auto_type item = _mv_1214.value;
                if (defn_is_spec_form(item)) {
                    result = defn_extract_spec_slop_return_type(ctx, item);
                }
            } else if (!_mv_1214.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_option_string defn_get_result_type_name(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 3;
        slop_option_string result = (slop_option_string){.has_value = false};
        while ((i < len) && ({ __auto_type _mv = result; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); })) {
            __auto_type _mv_1215 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1215.has_value) {
                __auto_type item = _mv_1215.value;
                if (defn_is_spec_form(item)) {
                    result = defn_extract_result_type_name(ctx, item);
                }
            } else if (!_mv_1215.has_value) {
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
        __auto_type _mv_1216 = (*spec_expr);
        switch (_mv_1216.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1216.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) < 2) {
                        return (slop_option_string){.has_value = false};
                    } else {
                        __auto_type _mv_1217 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1217.has_value) {
                            __auto_type spec_body = _mv_1217.value;
                            __auto_type _mv_1218 = (*spec_body);
                            switch (_mv_1218.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type body_lst = _mv_1218.data.lst;
                                    {
                                        __auto_type body_items = body_lst.items;
                                        __auto_type body_len = ((int64_t)((body_items).len));
                                        if (body_len < 1) {
                                            return (slop_option_string){.has_value = false};
                                        } else {
                                            __auto_type _mv_1219 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1219.has_value) {
                                                __auto_type ret_type = _mv_1219.value;
                                                return defn_check_result_type(ctx, ret_type);
                                            } else if (!_mv_1219.has_value) {
                                                return (slop_option_string){.has_value = false};
                                            }
                                            SLOP_UNREACHABLE();
                                        }
                                    }
                                }
                                default: {
                                    return (slop_option_string){.has_value = false};
                                }
                            }
                        } else if (!_mv_1217.has_value) {
                            return (slop_option_string){.has_value = false};
                        }
                        SLOP_UNREACHABLE();
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
        __auto_type _mv_1220 = (*type_expr);
        switch (_mv_1220.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_1220.data.sym;
                {
                    __auto_type type_name = sym.name;
                    __auto_type _mv_1221 = context_ctx_lookup_result_type_alias(ctx, type_name);
                    if (_mv_1221.has_value) {
                        __auto_type alias_result = _mv_1221.value;
                        return (slop_option_string){.has_value = 1, .value = alias_result};
                    } else if (!_mv_1221.has_value) {
                        __auto_type _mv_1222 = context_ctx_lookup_type(ctx, type_name);
                        if (_mv_1222.has_value) {
                            __auto_type entry = _mv_1222.value;
                            return (slop_option_string){.has_value = 1, .value = entry.c_name};
                        } else if (!_mv_1222.has_value) {
                            return (slop_option_string){.has_value = false};
                        }
                        SLOP_UNREACHABLE();
                    }
                    SLOP_UNREACHABLE();
                }
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1220.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) < 3) {
                        return (slop_option_string){.has_value = false};
                    } else {
                        __auto_type _mv_1223 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1223.has_value) {
                            __auto_type head = _mv_1223.value;
                            __auto_type _mv_1224 = (*head);
                            switch (_mv_1224.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_1224.data.sym;
                                    if (string_eq(sym.name, SLOP_STR("Result"))) {
                                        __auto_type _mv_1225 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1225.has_value) {
                                            __auto_type ok_type_expr = _mv_1225.value;
                                            __auto_type _mv_1226 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1226.has_value) {
                                                __auto_type err_type_expr = _mv_1226.value;
                                                {
                                                    __auto_type ok_c_type = context_to_c_type_prefixed(ctx, ok_type_expr);
                                                    __auto_type err_c_type = context_to_c_type_prefixed(ctx, err_type_expr);
                                                    __auto_type result_name = defn_build_result_name(arena, ok_c_type, err_c_type);
                                                    return (slop_option_string){.has_value = 1, .value = result_name};
                                                }
                                            } else if (!_mv_1226.has_value) {
                                                return (slop_option_string){.has_value = false};
                                            }
                                            SLOP_UNREACHABLE();
                                        } else if (!_mv_1225.has_value) {
                                            return (slop_option_string){.has_value = false};
                                        }
                                        SLOP_UNREACHABLE();
                                    } else {
                                        return (slop_option_string){.has_value = false};
                                    }
                                }
                                default: {
                                    return (slop_option_string){.has_value = false};
                                }
                            }
                        } else if (!_mv_1223.has_value) {
                            return (slop_option_string){.has_value = false};
                        }
                        SLOP_UNREACHABLE();
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
        __auto_type _mv_1227 = (*params_expr);
        switch (_mv_1227.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1227.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    __auto_type result = SLOP_STR("");
                    int64_t i = 0;
                    while (i < len) {
                        __auto_type _mv_1228 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1228.has_value) {
                            __auto_type param = _mv_1228.value;
                            {
                                __auto_type param_str = defn_build_single_param(ctx, param);
                                if (string_eq(result, SLOP_STR(""))) {
                                    result = param_str;
                                } else {
                                    result = context_ctx_str3(ctx, result, SLOP_STR(", "), param_str);
                                }
                            }
                        } else if (!_mv_1228.has_value) {
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
        __auto_type _mv_1229 = (*param);
        switch (_mv_1229.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1229.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len < 2) {
                        return SLOP_STR("/* invalid param */");
                    } else {
                        {
                            __auto_type has_mode = ((len >= 3) && defn_is_param_mode(items));
                            __auto_type name_idx = ((((len >= 3) && defn_is_param_mode(items))) ? 1 : 0);
                            __auto_type type_idx = ((((len >= 3) && defn_is_param_mode(items))) ? 2 : 1);
                            __auto_type _mv_1230 = ({ __auto_type _lst = items; size_t _idx = (size_t)name_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1230.has_value) {
                                __auto_type name_expr = _mv_1230.value;
                                __auto_type _mv_1231 = (*name_expr);
                                switch (_mv_1231.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type name_sym = _mv_1231.data.sym;
                                        __auto_type _mv_1232 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1232.has_value) {
                                            __auto_type type_expr = _mv_1232.value;
                                            {
                                                __auto_type param_name = ctype_to_c_name(arena, name_sym.name);
                                                {
                                                    __auto_type param_type = context_to_c_type_prefixed(ctx, type_expr);
                                                    return context_ctx_str3(ctx, param_type, SLOP_STR(" "), param_name);
                                                }
                                            }
                                        } else if (!_mv_1232.has_value) {
                                            return SLOP_STR("/* missing param type */");
                                        }
                                        SLOP_UNREACHABLE();
                                    }
                                    default: {
                                        return SLOP_STR("/* param name must be symbol */");
                                    }
                                }
                            } else if (!_mv_1230.has_value) {
                                return SLOP_STR("/* missing param name */");
                            }
                            SLOP_UNREACHABLE();
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
    return (((int64_t)((items).len)) >= 3);
}

slop_string defn_param_mode_word(slop_list_types_SExpr_ptr items) {
    __auto_type _mv_1233 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
    if (_mv_1233.has_value) {
        __auto_type first = _mv_1233.value;
        __auto_type _mv_1234 = (*first);
        switch (_mv_1234.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_1234.data.sym;
                return sym.name;
            }
            default: {
                return SLOP_STR("");
            }
        }
    } else if (!_mv_1233.has_value) {
        return SLOP_STR("");
    }
    SLOP_UNREACHABLE();
}

void defn_check_param_mode(context_TranspileContext* ctx, slop_string mode, slop_string name, slop_string slop_type, types_SExpr* at) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (!((string_eq(mode, SLOP_STR("in")) || (string_eq(mode, SLOP_STR("mut")) && !(defn_is_container_slop_type(ctx, slop_type)))))) {
        context_ctx_add_error_at(ctx, types_param_mode_error_message((*ctx).arena, mode, name), context_ctx_sexpr_line(at), context_ctx_sexpr_col(at));
    }
}

uint8_t defn_is_container_slop_type(context_TranspileContext* ctx, slop_string slop_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type t = slop_type;
        int64_t steps = 0;
        while ((steps < 8) && !(strlib_starts_with(t, SLOP_STR("(")))) {
            {
                __auto_type resolved = expr_resolve_type_alias(ctx, t);
                if (string_eq(resolved, t)) {
                    steps = 8;
                } else {
                    t = resolved;
                }
            }
            steps = (steps + 1);
        }
        return ((strlib_starts_with(t, SLOP_STR("(List "))) || (strlib_starts_with(t, SLOP_STR("(Map "))) || (strlib_starts_with(t, SLOP_STR("(Set "))));
    }
}

uint8_t defn_is_fn_type(types_SExpr* type_expr) {
    __auto_type _mv_1235 = (*type_expr);
    switch (_mv_1235.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1235.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1236 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1236.has_value) {
                        __auto_type first = _mv_1236.value;
                        __auto_type _mv_1237 = (*first);
                        switch (_mv_1237.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1237.data.sym;
                                return string_eq(sym.name, SLOP_STR("Fn"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1236.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
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
        __auto_type _mv_1238 = (*type_expr);
        switch (_mv_1238.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1238.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len < 2) {
                        return context_ctx_str(ctx, SLOP_STR("void* "), param_name);
                    } else {
                        {
                            __auto_type ret_type = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)(len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type ret = _mv.value; context_to_c_type_prefixed(ctx, ret); }) : (SLOP_STR("void")); });
                            if (len == 2) {
                                return context_ctx_str(ctx, context_ctx_str(ctx, ret_type, SLOP_STR("(*")), context_ctx_str(ctx, param_name, SLOP_STR(")(void)")));
                            } else {
                                __auto_type _mv_1239 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1239.has_value) {
                                    __auto_type args_expr = _mv_1239.value;
                                    {
                                        __auto_type args_str = defn_build_fn_args_str_for_param(ctx, args_expr);
                                        return context_ctx_str(ctx, context_ctx_str(ctx, ret_type, SLOP_STR("(*")), context_ctx_str(ctx, param_name, context_ctx_str(ctx, SLOP_STR(")"), args_str)));
                                    }
                                } else if (!_mv_1239.has_value) {
                                    return context_ctx_str(ctx, context_ctx_str(ctx, ret_type, SLOP_STR("(*")), context_ctx_str(ctx, param_name, SLOP_STR(")(void)")));
                                }
                                SLOP_UNREACHABLE();
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
        __auto_type _mv_1240 = (*args_expr);
        switch (_mv_1240.tag) {
            case types_SExpr_lst:
            {
                __auto_type args_list = _mv_1240.data.lst;
                {
                    __auto_type arg_items = args_list.items;
                    __auto_type arg_count = ((int64_t)((arg_items).len));
                    if (arg_count == 0) {
                        return SLOP_STR("(void)");
                    } else {
                        {
                            __auto_type result = SLOP_STR("(");
                            int64_t i = 0;
                            while (i < arg_count) {
                                __auto_type _mv_1241 = ({ __auto_type _lst = arg_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1241.has_value) {
                                    __auto_type arg_expr = _mv_1241.value;
                                    {
                                        __auto_type arg_type = context_to_c_type_prefixed(ctx, arg_expr);
                                        if (i > 0) {
                                            result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR(", "), arg_type));
                                        } else {
                                            result = context_ctx_str(ctx, result, arg_type);
                                        }
                                    }
                                } else if (!_mv_1241.has_value) {
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
        int64_t i = 3;
        __auto_type body_start = defn_find_body_start(items);
        i = body_start;
        while (i < len) {
            __auto_type _mv_1242 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1242.has_value) {
                __auto_type item = _mv_1242.value;
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
            } else if (!_mv_1242.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t defn_is_c_name_attr(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_1243 = (*expr);
    switch (_mv_1243.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1243.data.sym;
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
        int64_t i = (current_i + 1);
        uint8_t found_body = 0;
        while ((i < len) && !(found_body)) {
            __auto_type _mv_1244 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1244.has_value) {
                __auto_type item = _mv_1244.value;
                if (defn_is_annotation(item) || defn_is_c_name_attr(item)) {
                    i = (i + 1);
                } else {
                    if ((i > 0) && defn_is_c_name_attr_at(items, (i - 1))) {
                        i = (i + 1);
                    } else {
                        found_body = 1;
                    }
                }
            } else if (!_mv_1244.has_value) {
                i = (i + 1);
            }
        }
        return !(found_body);
    }
}

uint8_t defn_is_c_name_attr_at(slop_list_types_SExpr_ptr items, int64_t idx) {
    __auto_type _mv_1245 = ({ __auto_type _lst = items; size_t _idx = (size_t)idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
    if (_mv_1245.has_value) {
        __auto_type item = _mv_1245.value;
        return defn_is_c_name_attr(item);
    } else if (!_mv_1245.has_value) {
        return 0;
    }
    SLOP_UNREACHABLE();
}

int64_t defn_find_body_start(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 3;
        uint8_t found = 0;
        while ((i < len) && !(found)) {
            __auto_type _mv_1246 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1246.has_value) {
                __auto_type item = _mv_1246.value;
                if (defn_is_annotation(item)) {
                    i = (i + 1);
                } else {
                    found = 1;
                }
            } else if (!_mv_1246.has_value) {
                found = 1;
            }
        }
        return i;
    }
}

uint8_t defn_is_annotation(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_1247 = (*expr);
    switch (_mv_1247.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1247.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1248 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1248.has_value) {
                        __auto_type head = _mv_1248.value;
                        __auto_type _mv_1249 = (*head);
                        switch (_mv_1249.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1249.data.sym;
                                {
                                    __auto_type name = sym.name;
                                    return ((string_eq(name, SLOP_STR("@intent"))) || (string_eq(name, SLOP_STR("@spec"))) || (string_eq(name, SLOP_STR("@pre"))) || (string_eq(name, SLOP_STR("@post"))) || (string_eq(name, SLOP_STR("@assume"))) || (string_eq(name, SLOP_STR("@alloc"))) || (string_eq(name, SLOP_STR("@example"))) || (string_eq(name, SLOP_STR("@pure"))) || (string_eq(name, SLOP_STR("@doc"))) || (string_eq(name, SLOP_STR("@loop-invariant"))) || (string_eq(name, SLOP_STR("@property"))) || (string_eq(name, SLOP_STR("@callback-assume"))) || (string_eq(name, SLOP_STR("@generic"))));
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1248.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
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
    __auto_type _mv_1250 = (*expr);
    switch (_mv_1250.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1250.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1251 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1251.has_value) {
                        __auto_type head = _mv_1251.value;
                        __auto_type _mv_1252 = (*head);
                        switch (_mv_1252.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1252.data.sym;
                                return string_eq(sym.name, SLOP_STR("@pre"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1251.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
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
    __auto_type _mv_1253 = (*expr);
    switch (_mv_1253.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1253.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1254 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1254.has_value) {
                        __auto_type head = _mv_1254.value;
                        __auto_type _mv_1255 = (*head);
                        switch (_mv_1255.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1255.data.sym;
                                return string_eq(sym.name, SLOP_STR("@post"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1254.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
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
    __auto_type _mv_1256 = (*expr);
    switch (_mv_1256.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1256.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1257 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1257.has_value) {
                        __auto_type head = _mv_1257.value;
                        __auto_type _mv_1258 = (*head);
                        switch (_mv_1258.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1258.data.sym;
                                return string_eq(sym.name, SLOP_STR("@assume"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1257.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        default: {
            return 0;
        }
    }
}

uint8_t defn_is_verification_only_expr(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_1259 = (*expr);
    switch (_mv_1259.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1259.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if (len < 1) {
                    return 0;
                } else {
                    {
                        uint8_t found = 0;
                        int64_t i = 0;
                        __auto_type _mv_1260 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1260.has_value) {
                            __auto_type head = _mv_1260.value;
                            __auto_type _mv_1261 = (*head);
                            switch (_mv_1261.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_1261.data.sym;
                                    {
                                        __auto_type name = sym.name;
                                        if ((string_eq(name, SLOP_STR("forall"))) || (string_eq(name, SLOP_STR("exists"))) || (string_eq(name, SLOP_STR("implies")))) {
                                            found = 1;
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1260.has_value) {
                        }
                        while ((i < len) && !(found)) {
                            __auto_type _mv_1262 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1262.has_value) {
                                __auto_type item = _mv_1262.value;
                                if (defn_is_verification_only_expr(item)) {
                                    found = 1;
                                }
                            } else if (!_mv_1262.has_value) {
                            }
                            i = (i + 1);
                        }
                        return found;
                    }
                }
            }
        }
        default: {
            return 0;
        }
    }
}

uint8_t defn_is_doc_form(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_1263 = (*expr);
    switch (_mv_1263.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1263.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1264 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1264.has_value) {
                        __auto_type head = _mv_1264.value;
                        __auto_type _mv_1265 = (*head);
                        switch (_mv_1265.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1265.data.sym;
                                return string_eq(sym.name, SLOP_STR("@doc"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1264.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        default: {
            return 0;
        }
    }
}

slop_option_string defn_get_doc_string(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        slop_option_string result = (slop_option_string){.has_value = false};
        __auto_type _mv_1266 = (*expr);
        switch (_mv_1266.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1266.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) >= 2) {
                        __auto_type _mv_1267 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1267.has_value) {
                            __auto_type val = _mv_1267.value;
                            __auto_type _mv_1268 = (*val);
                            switch (_mv_1268.tag) {
                                case types_SExpr_str:
                                {
                                    __auto_type str = _mv_1268.data.str;
                                    result = (slop_option_string){.has_value = 1, .value = str.value};
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1267.has_value) {
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

slop_option_string defn_collect_doc_string(slop_arena* arena, slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 3;
        slop_option_string result = (slop_option_string){.has_value = false};
        while ((i < len) && ({ __auto_type _mv = result; _mv.has_value ? (0) : (1); })) {
            __auto_type _mv_1269 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1269.has_value) {
                __auto_type item = _mv_1269.value;
                if (defn_is_doc_form(item)) {
                    result = defn_get_doc_string(item);
                }
            } else if (!_mv_1269.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_option_types_SExpr_ptr defn_get_annotation_condition(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        slop_option_types_SExpr_ptr result = (slop_option_types_SExpr_ptr){.has_value = false};
        __auto_type _mv_1270 = (*expr);
        switch (_mv_1270.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1270.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) >= 2) {
                        __auto_type _mv_1271 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1271.has_value) {
                            __auto_type val = _mv_1271.value;
                            result = (slop_option_types_SExpr_ptr){.has_value = 1, .value = val};
                        } else if (!_mv_1271.has_value) {
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
        __auto_type result = ((slop_list_types_SExpr_ptr){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 3;
        while (i < len) {
            __auto_type _mv_1272 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1272.has_value) {
                __auto_type item = _mv_1272.value;
                if (defn_is_pre_form(item)) {
                    __auto_type _mv_1273 = defn_get_annotation_condition(item);
                    if (_mv_1273.has_value) {
                        __auto_type cond = _mv_1273.value;
                        ({ __auto_type _lst_p = &(result); __auto_type _item = (cond); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    } else if (!_mv_1273.has_value) {
                    }
                }
            } else if (!_mv_1272.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_list_types_SExpr_ptr defn_collect_postconditions(slop_arena* arena, slop_list_types_SExpr_ptr items) {
    {
        __auto_type result = ((slop_list_types_SExpr_ptr){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 3;
        while (i < len) {
            __auto_type _mv_1274 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1274.has_value) {
                __auto_type item = _mv_1274.value;
                if (defn_is_post_form(item)) {
                    __auto_type _mv_1275 = defn_get_annotation_condition(item);
                    if (_mv_1275.has_value) {
                        __auto_type cond = _mv_1275.value;
                        ({ __auto_type _lst_p = &(result); __auto_type _item = (cond); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    } else if (!_mv_1275.has_value) {
                    }
                }
            } else if (!_mv_1274.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_list_types_SExpr_ptr defn_collect_assumptions(slop_arena* arena, slop_list_types_SExpr_ptr items) {
    {
        __auto_type result = ((slop_list_types_SExpr_ptr){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 3;
        while (i < len) {
            __auto_type _mv_1276 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1276.has_value) {
                __auto_type item = _mv_1276.value;
                if (defn_is_assume_form(item)) {
                    __auto_type _mv_1277 = defn_get_annotation_condition(item);
                    if (_mv_1277.has_value) {
                        __auto_type cond = _mv_1277.value;
                        ({ __auto_type _lst_p = &(result); __auto_type _item = (cond); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    } else if (!_mv_1277.has_value) {
                    }
                }
            } else if (!_mv_1276.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

uint8_t defn_has_postconditions(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 3;
        uint8_t found = 0;
        while ((i < len) && !(found)) {
            __auto_type _mv_1278 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1278.has_value) {
                __auto_type item = _mv_1278.value;
                if (defn_is_post_form(item) || defn_is_assume_form(item)) {
                    found = 1;
                }
            } else if (!_mv_1278.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1279 = ({ __auto_type _lst = preconditions; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1279.has_value) {
                __auto_type cond_expr = _mv_1279.value;
                {
                    __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                    __auto_type expr_str = parser_pretty_print(arena, cond_expr);
                    __auto_type escaped_str = defn_escape_for_c_string(arena, expr_str);
                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("SLOP_PRE(("), cond_c, SLOP_STR("), \""), escaped_str, SLOP_STR("\");")));
                }
            } else if (!_mv_1279.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1280 = ({ __auto_type _lst = postconditions; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1280.has_value) {
                __auto_type cond_expr = _mv_1280.value;
                if (!(defn_is_verification_only_expr(cond_expr))) {
                    {
                        __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                        __auto_type expr_str = parser_pretty_print(arena, cond_expr);
                        __auto_type escaped_str = defn_escape_for_c_string(arena, expr_str);
                        context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("SLOP_POST(("), cond_c, SLOP_STR("), \""), escaped_str, SLOP_STR("\");")));
                    }
                }
            } else if (!_mv_1280.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1281 = ({ __auto_type _lst = assumptions; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1281.has_value) {
                __auto_type cond_expr = _mv_1281.value;
                if (!(defn_is_verification_only_expr(cond_expr))) {
                    {
                        __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                        __auto_type expr_str = parser_pretty_print(arena, cond_expr);
                        __auto_type escaped_str = defn_escape_for_c_string(arena, expr_str);
                        context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("SLOP_POST(("), cond_c, SLOP_STR("), \""), escaped_str, SLOP_STR("\");")));
                    }
                }
            } else if (!_mv_1281.has_value) {
            }
            i = (i + 1);
        }
    }
}

slop_string defn_escape_for_c_string(slop_arena* arena, slop_string s) {
    {
        __auto_type len = ((int64_t)(s.len));
        __auto_type buf = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, ((len * 2) + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        int64_t out_idx = 0;
        int64_t in_idx = 0;
        while (in_idx < len) {
            {
                __auto_type c = s.data[in_idx];
                if (c == 92) {
                    buf[out_idx] = 92;
                    out_idx = (out_idx + 1);
                    buf[out_idx] = 92;
                    out_idx = (out_idx + 1);
                } else if (c == 34) {
                    buf[out_idx] = 92;
                    out_idx = (out_idx + 1);
                    buf[out_idx] = 34;
                    out_idx = (out_idx + 1);
                } else if (c == 10) {
                    buf[out_idx] = 92;
                    out_idx = (out_idx + 1);
                    buf[out_idx] = 110;
                    out_idx = (out_idx + 1);
                } else if (c == 9) {
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

