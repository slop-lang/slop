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
slop_string defn_extract_spec_slop_return_type(context_TranspileContext* ctx, types_SExpr* spec_expr);
slop_string defn_get_slop_return_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
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
    __auto_type _mv_856 = (*expr);
    switch (_mv_856.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_856.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_857 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_857.has_value) {
                        __auto_type head = _mv_857.value;
                        __auto_type _mv_858 = (*head);
                        switch (_mv_858.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_858.data.sym;
                                return string_eq(sym.name, SLOP_STR("type"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_857.has_value) {
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
    __auto_type _mv_859 = (*expr);
    switch (_mv_859.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_859.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_860 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_860.has_value) {
                        __auto_type head = _mv_860.value;
                        __auto_type _mv_861 = (*head);
                        switch (_mv_861.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_861.data.sym;
                                return string_eq(sym.name, SLOP_STR("fn"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_860.has_value) {
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
    __auto_type _mv_862 = (*expr);
    switch (_mv_862.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_862.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_863 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_863.has_value) {
                        __auto_type head = _mv_863.value;
                        __auto_type _mv_864 = (*head);
                        switch (_mv_864.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_864.data.sym;
                                return string_eq(sym.name, SLOP_STR("const"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_863.has_value) {
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
    __auto_type _mv_865 = (*expr);
    switch (_mv_865.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_865.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_866 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_866.has_value) {
                        __auto_type head = _mv_866.value;
                        __auto_type _mv_867 = (*head);
                        switch (_mv_867.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_867.data.sym;
                                return string_eq(sym.name, SLOP_STR("ffi"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_866.has_value) {
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
    __auto_type _mv_868 = (*expr);
    switch (_mv_868.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_868.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_869 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_869.has_value) {
                        __auto_type head = _mv_869.value;
                        __auto_type _mv_870 = (*head);
                        switch (_mv_870.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_870.data.sym;
                                return string_eq(sym.name, SLOP_STR("ffi-struct"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_869.has_value) {
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

uint8_t defn_has_generic_annotation(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_871 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_871.has_value) {
                __auto_type item = _mv_871.value;
                __auto_type _mv_872 = (*item);
                switch (_mv_872.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type lst = _mv_872.data.lst;
                        {
                            __auto_type sub_items = lst.items;
                            if ((((int64_t)((sub_items).len)) > 0)) {
                                __auto_type _mv_873 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_873.has_value) {
                                    __auto_type head = _mv_873.value;
                                    __auto_type _mv_874 = (*head);
                                    switch (_mv_874.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_874.data.sym;
                                            if (string_eq(sym.name, SLOP_STR("@generic"))) {
                                                found = 1;
                                            } else {
                                                0;
                                            }
                                            break;
                                        }
                                        default: {
                                            0;
                                            break;
                                        }
                                    }
                                } else if (!_mv_873.has_value) {
                                    0;
                                }
                            } else {
                                0;
                            }
                        }
                        break;
                    }
                    default: {
                        0;
                        break;
                    }
                }
            } else if (!_mv_871.has_value) {
                0;
            }
            i = (i + 1);
        }
        return found;
    }
}

uint8_t defn_is_pointer_type_expr(types_SExpr* type_expr) {
    __auto_type _mv_875 = (*type_expr);
    switch (_mv_875.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_875.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_876 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_876.has_value) {
                        __auto_type head = _mv_876.value;
                        __auto_type _mv_877 = (*head);
                        switch (_mv_877.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_877.data.sym;
                                return (string_eq(sym.name, SLOP_STR("Ptr")) || string_eq(sym.name, SLOP_STR("ScopedPtr")));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_876.has_value) {
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
        __auto_type _mv_878 = (*expr);
        switch (_mv_878.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_878.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 4)) {
                        context_ctx_fail(ctx, SLOP_STR("invalid const: need name, type, value"));
                    } else {
                        __auto_type _mv_879 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_879.has_value) {
                            __auto_type name_expr = _mv_879.value;
                            __auto_type _mv_880 = (*name_expr);
                            switch (_mv_880.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_880.data.sym;
                                    {
                                        __auto_type raw_name = name_sym.name;
                                        __auto_type base_name = ctype_to_c_name(arena, raw_name);
                                        __auto_type c_name = context_ctx_prefix_type(ctx, base_name);
                                        __auto_type _mv_881 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_881.has_value) {
                                            __auto_type type_expr = _mv_881.value;
                                            {
                                                __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                                                context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, SLOP_STR("auto"), slop_type_str, 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                                __auto_type _mv_882 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_882.has_value) {
                                                    __auto_type value_expr = _mv_882.value;
                                                    defn_emit_const_def(ctx, c_name, type_expr, value_expr, is_exported);
                                                } else if (!_mv_882.has_value) {
                                                    context_ctx_fail(ctx, SLOP_STR("missing const value"));
                                                }
                                            }
                                        } else if (!_mv_881.has_value) {
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
                        } else if (!_mv_879.has_value) {
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
                if (string_eq(type_name, SLOP_STR("String"))) {
                    __auto_type _mv_883 = (*value_expr);
                    switch (_mv_883.tag) {
                        case types_SExpr_str:
                        {
                            __auto_type str = _mv_883.data.str;
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
    __auto_type _mv_884 = (*type_expr);
    switch (_mv_884.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_884.data.sym;
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
        __auto_type _mv_885 = (*expr);
        switch (_mv_885.tag) {
            case types_SExpr_num:
            {
                __auto_type num = _mv_885.data.num;
                return num.raw;
            }
            case types_SExpr_str:
            {
                __auto_type str = _mv_885.data.str;
                return context_ctx_str3(ctx, SLOP_STR("\""), str.value, SLOP_STR("\""));
            }
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_885.data.sym;
                return ctype_to_c_name(arena, sym.name);
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_885.data.lst;
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
        __auto_type _mv_886 = (*expr);
        switch (_mv_886.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_886.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    {
                        __auto_type name_idx = ((((len >= 2) && defn_is_string_expr(items, 1))) ? 2 : 1);
                        if ((len >= (name_idx + 1))) {
                            __auto_type _mv_887 = ({ __auto_type _lst = items; size_t _idx = (size_t)name_idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_887.has_value) {
                                __auto_type name_expr = _mv_887.value;
                                __auto_type _mv_888 = (*name_expr);
                                switch (_mv_888.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_888.data.sym;
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
                            } else if (!_mv_887.has_value) {
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
    __auto_type _mv_889 = ({ __auto_type _lst = items; size_t _idx = (size_t)idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
    if (_mv_889.has_value) {
        __auto_type item = _mv_889.value;
        __auto_type _mv_890 = (*item);
        switch (_mv_890.tag) {
            case types_SExpr_str:
            {
                __auto_type _ = _mv_890.data.str;
                return 1;
            }
            default: {
                return 0;
            }
        }
    } else if (!_mv_889.has_value) {
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
        __auto_type _mv_891 = (*expr);
        switch (_mv_891.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_891.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 3)) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid type: need name and definition"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    } else {
                        __auto_type _mv_892 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_892.has_value) {
                            __auto_type name_expr = _mv_892.value;
                            __auto_type _mv_893 = (*name_expr);
                            switch (_mv_893.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_893.data.sym;
                                    {
                                        __auto_type raw_name = name_sym.name;
                                        __auto_type base_name = ctype_to_c_name(arena, raw_name);
                                        __auto_type qualified_name = ((context_ctx_prefixing_enabled(ctx)) ? ({ __auto_type _mv = context_ctx_get_module(ctx); _mv.has_value ? ({ __auto_type mod_name = _mv.value; context_ctx_str(ctx, ctype_to_c_name(arena, mod_name), context_ctx_str(ctx, SLOP_STR("_"), base_name)); }) : (base_name); }) : base_name);
                                        __auto_type _mv_894 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_894.has_value) {
                                            __auto_type type_def = _mv_894.value;
                                            defn_dispatch_type_def(ctx, raw_name, qualified_name, type_def);
                                        } else if (!_mv_894.has_value) {
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
                        } else if (!_mv_892.has_value) {
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
    __auto_type _mv_895 = (*type_def);
    switch (_mv_895.tag) {
        case types_SExpr_lst:
        {
            __auto_type def_lst = _mv_895.data.lst;
            {
                __auto_type items = def_lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    context_ctx_add_error_at(ctx, SLOP_STR("empty type definition"), context_ctx_sexpr_line(type_def), context_ctx_sexpr_col(type_def));
                } else {
                    __auto_type _mv_896 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_896.has_value) {
                        __auto_type head = _mv_896.value;
                        __auto_type _mv_897 = (*head);
                        switch (_mv_897.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_897.data.sym;
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
                    } else if (!_mv_896.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("empty type definition"), context_ctx_sexpr_line(type_def), context_ctx_sexpr_col(type_def));
                    }
                }
            }
            break;
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_895.data.sym;
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
        while (((i < len) && !(found))) {
            __auto_type _mv_898 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_898.has_value) {
                __auto_type item = _mv_898.value;
                __auto_type _mv_899 = (*item);
                switch (_mv_899.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type _ = _mv_899.data.lst;
                        found = 1;
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_898.has_value) {
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
        __auto_type _mv_900 = (*expr);
        switch (_mv_900.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_900.data.lst;
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
        while ((i < len)) {
            __auto_type _mv_901 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_901.has_value) {
                __auto_type field_expr = _mv_901.value;
                defn_emit_record_field(ctx, raw_type_name, qualified_type_name, field_expr);
            } else if (!_mv_901.has_value) {
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
        __auto_type _mv_902 = (*field);
        switch (_mv_902.tag) {
            case types_SExpr_lst:
            {
                __auto_type field_lst = _mv_902.data.lst;
                {
                    __auto_type items = field_lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 2)) {
                        context_ctx_emit(ctx, SLOP_STR("    /* invalid field */"));
                    } else {
                        __auto_type _mv_903 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_903.has_value) {
                            __auto_type name_expr = _mv_903.value;
                            __auto_type _mv_904 = (*name_expr);
                            switch (_mv_904.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_904.data.sym;
                                    __auto_type _mv_905 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_905.has_value) {
                                        __auto_type type_expr = _mv_905.value;
                                        {
                                            __auto_type raw_field_name = name_sym.name;
                                            __auto_type field_name = ctype_to_c_name(arena, raw_field_name);
                                            __auto_type field_type = context_to_c_type_prefixed(ctx, type_expr);
                                            __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                                            __auto_type is_ptr = defn_is_pointer_type_expr(type_expr);
                                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("    "), field_type, SLOP_STR(" "), field_name, SLOP_STR(";")));
                                            context_ctx_register_field_type(ctx, raw_type_name, raw_field_name, field_type, slop_type_str, is_ptr);
                                            context_ctx_register_field_type(ctx, qualified_type_name, raw_field_name, field_type, slop_type_str, is_ptr);
                                        }
                                    } else if (!_mv_905.has_value) {
                                        context_ctx_emit(ctx, SLOP_STR("    /* missing field type */"));
                                    }
                                    break;
                                }
                                default: {
                                    context_ctx_emit(ctx, SLOP_STR("    /* field name must be symbol */"));
                                    break;
                                }
                            }
                        } else if (!_mv_903.has_value) {
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
        __auto_type _mv_906 = (*expr);
        switch (_mv_906.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_906.data.lst;
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
        while ((i < len)) {
            __auto_type _mv_907 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_907.has_value) {
                __auto_type val_expr = _mv_907.value;
                __auto_type _mv_908 = (*val_expr);
                switch (_mv_908.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_908.data.sym;
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
            } else if (!_mv_907.has_value) {
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
        __auto_type _mv_909 = (*expr);
        switch (_mv_909.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_909.data.lst;
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
        while ((i < len)) {
            __auto_type _mv_910 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_910.has_value) {
                __auto_type variant_expr = _mv_910.value;
                __auto_type _mv_911 = (*variant_expr);
                switch (_mv_911.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type var_lst = _mv_911.data.lst;
                        {
                            __auto_type var_items = var_lst.items;
                            __auto_type var_len = ((int64_t)((var_items).len));
                            if ((var_len >= 1)) {
                                __auto_type _mv_912 = ({ __auto_type _lst = var_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_912.has_value) {
                                    __auto_type tag_expr = _mv_912.value;
                                    __auto_type _mv_913 = (*tag_expr);
                                    switch (_mv_913.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type tag_sym = _mv_913.data.sym;
                                            {
                                                __auto_type tag_name = tag_sym.name;
                                                if ((var_len >= 2)) {
                                                    __auto_type _mv_914 = ({ __auto_type _lst = var_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_914.has_value) {
                                                        __auto_type type_expr = _mv_914.value;
                                                        {
                                                            __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                            {
                                                                __auto_type actual_type = ((string_eq(c_type, SLOP_STR("void"))) ? SLOP_STR("int") : c_type);
                                                                context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("        "), actual_type, SLOP_STR(" "), ctype_to_c_name(arena, tag_name), SLOP_STR(";")));
                                                            }
                                                        }
                                                    } else if (!_mv_914.has_value) {
                                                    }
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_912.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_910.has_value) {
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
        while ((i < len)) {
            __auto_type _mv_915 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_915.has_value) {
                __auto_type variant_expr = _mv_915.value;
                __auto_type _mv_916 = (*variant_expr);
                switch (_mv_916.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type var_lst = _mv_916.data.lst;
                        {
                            __auto_type var_items = var_lst.items;
                            if ((((int64_t)((var_items).len)) >= 1)) {
                                __auto_type _mv_917 = ({ __auto_type _lst = var_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_917.has_value) {
                                    __auto_type tag_expr = _mv_917.value;
                                    __auto_type _mv_918 = (*tag_expr);
                                    switch (_mv_918.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type tag_sym = _mv_918.data.sym;
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
                                } else if (!_mv_917.has_value) {
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
            } else if (!_mv_915.has_value) {
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
        while ((i < len)) {
            __auto_type _mv_919 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_919.has_value) {
                __auto_type variant_expr = _mv_919.value;
                __auto_type _mv_920 = (*variant_expr);
                switch (_mv_920.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type var_lst = _mv_920.data.lst;
                        {
                            __auto_type var_items = var_lst.items;
                            __auto_type var_len = ((int64_t)((var_items).len));
                            if ((var_len >= 2)) {
                                __auto_type _mv_921 = ({ __auto_type _lst = var_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_921.has_value) {
                                    __auto_type tag_expr = _mv_921.value;
                                    __auto_type _mv_922 = (*tag_expr);
                                    switch (_mv_922.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type tag_sym = _mv_922.data.sym;
                                            {
                                                __auto_type tag_name = tag_sym.name;
                                                __auto_type _mv_923 = ({ __auto_type _lst = var_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_923.has_value) {
                                                    __auto_type type_expr = _mv_923.value;
                                                    {
                                                        __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                        __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                                                        __auto_type is_ptr = defn_is_pointer_type_expr(type_expr);
                                                        context_ctx_register_field_type(ctx, raw_name, tag_name, c_type, slop_type_str, is_ptr);
                                                        context_ctx_register_field_type(ctx, qualified_name, tag_name, c_type, slop_type_str, is_ptr);
                                                    }
                                                } else if (!_mv_923.has_value) {
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_921.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_919.has_value) {
            }
            i = (i + 1);
        }
    }
    SLOP_POST((SLOP_STR("Registers field types for each union variant with payload in the context")), "\"Registers field types for each union variant with payload in the context\"");
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
    __auto_type _mv_924 = (*type_expr);
    switch (_mv_924.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_924.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_925 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_925.has_value) {
                        __auto_type head = _mv_925.value;
                        __auto_type _mv_926 = (*head);
                        switch (_mv_926.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_926.data.sym;
                                return string_eq(sym.name, SLOP_STR("Array"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_925.has_value) {
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
        __auto_type _mv_927 = (*type_expr);
        switch (_mv_927.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_927.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 3)) {
                        context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("typedef void* "), context_ctx_str(ctx, qualified_name, SLOP_STR(";"))));
                    } else {
                        __auto_type _mv_928 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_928.has_value) {
                            __auto_type elem_type_expr = _mv_928.value;
                            __auto_type _mv_929 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_929.has_value) {
                                __auto_type size_expr = _mv_929.value;
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
                            } else if (!_mv_929.has_value) {
                                context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("typedef void* "), context_ctx_str(ctx, qualified_name, SLOP_STR(";"))));
                            }
                        } else if (!_mv_928.has_value) {
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
    __auto_type _mv_930 = (*expr);
    switch (_mv_930.tag) {
        case types_SExpr_num:
        {
            __auto_type num = _mv_930.data.num;
            return num.raw;
        }
        default: {
            return SLOP_STR("0");
        }
    }
}

uint8_t defn_is_range_type(types_SExpr* type_expr) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_931 = (*type_expr);
    switch (_mv_931.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_931.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type found_dots = 0;
                __auto_type i = 0;
                while (((i < len) && !(found_dots))) {
                    __auto_type _mv_932 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_932.has_value) {
                        __auto_type item = _mv_932.value;
                        __auto_type _mv_933 = (*item);
                        switch (_mv_933.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_933.data.sym;
                                if (string_eq(sym.name, SLOP_STR(".."))) {
                                    found_dots = 1;
                                }
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_932.has_value) {
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
        __auto_type _mv_934 = (*type_expr);
        switch (_mv_934.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_934.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    __auto_type i = 1;
                    while ((i < len)) {
                        __auto_type _mv_935 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_935.has_value) {
                            __auto_type item = _mv_935.value;
                            __auto_type _mv_936 = (*item);
                            switch (_mv_936.tag) {
                                case types_SExpr_num:
                                {
                                    __auto_type num = _mv_936.data.num;
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
                                    __auto_type sym = _mv_936.data.sym;
                                    if (string_eq(sym.name, SLOP_STR(".."))) {
                                        found_dots = 1;
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_935.has_value) {
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
        context_ctx_register_type_alias(ctx, raw_name, parser_pretty_print(arena, type_expr));
    }
}

void defn_transpile_function(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_937 = (*expr);
        switch (_mv_937.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_937.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 3)) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid fn: need name and params"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    } else {
                        __auto_type _mv_938 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_938.has_value) {
                            __auto_type name_expr = _mv_938.value;
                            __auto_type _mv_939 = (*name_expr);
                            switch (_mv_939.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_939.data.sym;
                                    {
                                        __auto_type raw_name = name_sym.name;
                                        __auto_type base_name = ctype_to_c_name(arena, raw_name);
                                        __auto_type mangled_name = ((string_eq(base_name, SLOP_STR("main"))) ? base_name : context_ctx_prefix_type(ctx, base_name));
                                        __auto_type base_fn_name = context_extract_fn_c_name(arena, items, mangled_name);
                                        __auto_type fn_name = base_fn_name;
                                        __auto_type is_public_api = !(string_eq(base_fn_name, mangled_name));
                                        __auto_type _mv_940 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_940.has_value) {
                                            __auto_type params_expr = _mv_940.value;
                                            defn_emit_function_def(ctx, raw_name, fn_name, params_expr, items, is_public_api);
                                        } else if (!_mv_940.has_value) {
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
                        } else if (!_mv_938.has_value) {
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
            __auto_type param_str = defn_build_param_str(ctx, params_expr);
            __auto_type has_post = ((((int64_t)((postconditions).len)) > 0) || (((int64_t)((assumptions).len)) > 0));
            __auto_type needs_retval = (has_post && !(string_eq(actual_return, SLOP_STR("void"))));
            context_ctx_set_current_return_type(ctx, actual_return);
            __auto_type _mv_941 = result_type_opt;
            if (_mv_941.has_value) {
                __auto_type result_name = _mv_941.value;
                context_ctx_set_current_result_type(ctx, result_name);
            } else if (!_mv_941.has_value) {
                context_ctx_clear_current_result_type(ctx);
            }
            __auto_type _mv_942 = doc_string;
            if (_mv_942.has_value) {
                __auto_type doc = _mv_942.value;
                context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("/* "), doc, SLOP_STR(" */")));
            } else if (!_mv_942.has_value) {
            }
            context_ctx_emit(ctx, context_ctx_str5(ctx, actual_return, SLOP_STR(" "), fn_name, SLOP_STR("("), context_ctx_str(ctx, ((string_eq(param_str, SLOP_STR(""))) ? SLOP_STR("void") : param_str), SLOP_STR(") {"))));
            context_ctx_indent(ctx);
            context_ctx_push_scope(ctx);
            defn_bind_params_to_scope(ctx, params_expr);
            defn_emit_preconditions(ctx, preconditions);
            if (needs_retval) {
                context_ctx_emit(ctx, context_ctx_str(ctx, actual_return, SLOP_STR(" _retval;")));
                context_ctx_bind_var(ctx, (context_VarEntry){SLOP_STR("$result"), SLOP_STR("_retval"), actual_return, SLOP_STR(""), strlib_ends_with(actual_return, SLOP_STR("*")), 0, 0, SLOP_STR(""), SLOP_STR("")});
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
                __auto_type slop_ret_type = defn_get_slop_return_type(ctx, items);
                __auto_type empty_type_params = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                slop_option_types_SExpr_ptr no_source = (slop_option_types_SExpr_ptr){.has_value = false};
                context_ctx_register_func(ctx, (context_FuncEntry){raw_name, fn_name, actual_return, slop_ret_type, 0, string_eq(actual_return, SLOP_STR("slop_string")), param_types, 0, empty_type_params, no_source});
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
        __auto_type _mv_943 = (*params_expr);
        switch (_mv_943.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_943.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    __auto_type i = 0;
                    while ((i < len)) {
                        __auto_type _mv_944 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_944.has_value) {
                            __auto_type param = _mv_944.value;
                            defn_bind_single_param(ctx, param);
                        } else if (!_mv_944.has_value) {
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
        __auto_type _mv_945 = (*param);
        switch (_mv_945.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_945.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len >= 2)) {
                        {
                            __auto_type has_mode = ((len >= 3) && defn_is_param_mode(items));
                            __auto_type name_idx = ((has_mode) ? 1 : 0);
                            __auto_type type_idx = ((has_mode) ? 2 : 1);
                            __auto_type _mv_946 = ({ __auto_type _lst = items; size_t _idx = (size_t)name_idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_946.has_value) {
                                __auto_type name_expr = _mv_946.value;
                                __auto_type _mv_947 = (*name_expr);
                                switch (_mv_947.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type name_sym = _mv_947.data.sym;
                                        __auto_type _mv_948 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_948.has_value) {
                                            __auto_type type_expr = _mv_948.value;
                                            {
                                                __auto_type param_name = name_sym.name;
                                                __auto_type c_name = ctype_to_c_name(arena, param_name);
                                                __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                                                __auto_type is_ptr = defn_is_pointer_type(type_expr);
                                                __auto_type is_closure = defn_is_fn_type(type_expr);
                                                context_ctx_bind_var(ctx, (context_VarEntry){param_name, c_name, c_type, slop_type_str, is_ptr, 0, is_closure, SLOP_STR(""), SLOP_STR("")});
                                            }
                                        } else if (!_mv_948.has_value) {
                                        }
                                        break;
                                    }
                                    default: {
                                        break;
                                    }
                                }
                            } else if (!_mv_946.has_value) {
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
    __auto_type _mv_949 = (*type_expr);
    switch (_mv_949.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_949.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_950 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_950.has_value) {
                        __auto_type head = _mv_950.value;
                        __auto_type _mv_951 = (*head);
                        switch (_mv_951.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_951.data.sym;
                                return string_eq(sym.name, SLOP_STR("Ptr"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_950.has_value) {
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
        __auto_type _mv_952 = (*params_expr);
        switch (_mv_952.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_952.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    __auto_type i = 0;
                    while ((i < len)) {
                        __auto_type _mv_953 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_953.has_value) {
                            __auto_type param = _mv_953.value;
                            {
                                __auto_type c_type = defn_get_param_c_type(ctx, param);
                                __auto_type param_info = ((context_FuncParamType*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 64); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
                                (*param_info).c_type = c_type;
                                ({ __auto_type _lst_p = &(result); __auto_type _item = (param_info); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            }
                        } else if (!_mv_953.has_value) {
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
        __auto_type _mv_954 = (*param);
        switch (_mv_954.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_954.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 2)) {
                        return SLOP_STR("void*");
                    } else {
                        {
                            __auto_type has_mode = ((len >= 3) && defn_is_param_mode(items));
                            __auto_type type_idx = ((has_mode) ? 2 : 1);
                            __auto_type _mv_955 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_955.has_value) {
                                __auto_type type_expr = _mv_955.value;
                                return context_to_c_type_prefixed(ctx, type_expr);
                            } else if (!_mv_955.has_value) {
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
        __auto_type _mv_956 = (*expr);
        switch (_mv_956.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_956.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len >= 3)) {
                        __auto_type _mv_957 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_957.has_value) {
                            __auto_type name_expr = _mv_957.value;
                            __auto_type _mv_958 = (*name_expr);
                            switch (_mv_958.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_958.data.sym;
                                    {
                                        __auto_type raw_name = name_sym.name;
                                        __auto_type base_name = ctype_to_c_name(arena, raw_name);
                                        __auto_type mangled_name = context_ctx_prefix_type(ctx, base_name);
                                        __auto_type fn_name = context_extract_fn_c_name(arena, items, mangled_name);
                                        __auto_type _mv_959 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_959.has_value) {
                                            __auto_type params_expr = _mv_959.value;
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
                                        } else if (!_mv_959.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_957.has_value) {
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
        while ((i < len)) {
            __auto_type _mv_960 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_960.has_value) {
                __auto_type item = _mv_960.value;
                if (defn_is_spec_form(item)) {
                    result = defn_extract_spec_return_type(ctx, item);
                }
            } else if (!_mv_960.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

uint8_t defn_is_spec_form(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_961 = (*expr);
    switch (_mv_961.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_961.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_962 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_962.has_value) {
                        __auto_type head = _mv_962.value;
                        __auto_type _mv_963 = (*head);
                        switch (_mv_963.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_963.data.sym;
                                return string_eq(sym.name, SLOP_STR("@spec"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_962.has_value) {
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
        __auto_type _mv_964 = (*spec_expr);
        switch (_mv_964.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_964.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) < 2)) {
                        return SLOP_STR("void");
                    } else {
                        __auto_type _mv_965 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_965.has_value) {
                            __auto_type spec_body = _mv_965.value;
                            __auto_type _mv_966 = (*spec_body);
                            switch (_mv_966.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type body_lst = _mv_966.data.lst;
                                    {
                                        __auto_type body_items = body_lst.items;
                                        __auto_type body_len = ((int64_t)((body_items).len));
                                        if ((body_len < 1)) {
                                            return SLOP_STR("void");
                                        } else {
                                            __auto_type _mv_967 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_967.has_value) {
                                                __auto_type ret_type = _mv_967.value;
                                                return context_to_c_type_prefixed(ctx, ret_type);
                                            } else if (!_mv_967.has_value) {
                                                return SLOP_STR("void");
                                            }
                                        }
                                    }
                                }
                                default: {
                                    return SLOP_STR("void");
                                }
                            }
                        } else if (!_mv_965.has_value) {
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

slop_string defn_extract_spec_slop_return_type(context_TranspileContext* ctx, types_SExpr* spec_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((spec_expr != NULL)), "(!= spec-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_968 = (*spec_expr);
        switch (_mv_968.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_968.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) < 2)) {
                        return SLOP_STR("");
                    } else {
                        __auto_type _mv_969 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_969.has_value) {
                            __auto_type spec_body = _mv_969.value;
                            __auto_type _mv_970 = (*spec_body);
                            switch (_mv_970.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type body_lst = _mv_970.data.lst;
                                    {
                                        __auto_type body_items = body_lst.items;
                                        __auto_type body_len = ((int64_t)((body_items).len));
                                        if ((body_len < 1)) {
                                            return SLOP_STR("");
                                        } else {
                                            __auto_type _mv_971 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_971.has_value) {
                                                __auto_type ret_type = _mv_971.value;
                                                return parser_pretty_print(arena, ret_type);
                                            } else if (!_mv_971.has_value) {
                                                return SLOP_STR("");
                                            }
                                        }
                                    }
                                }
                                default: {
                                    return SLOP_STR("");
                                }
                            }
                        } else if (!_mv_969.has_value) {
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

slop_string defn_get_slop_return_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 3;
        __auto_type result = SLOP_STR("");
        while ((i < len)) {
            __auto_type _mv_972 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_972.has_value) {
                __auto_type item = _mv_972.value;
                if (defn_is_spec_form(item)) {
                    result = defn_extract_spec_slop_return_type(ctx, item);
                }
            } else if (!_mv_972.has_value) {
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
        while (((i < len) && ({ __auto_type _mv = result; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); }))) {
            __auto_type _mv_973 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_973.has_value) {
                __auto_type item = _mv_973.value;
                if (defn_is_spec_form(item)) {
                    result = defn_extract_result_type_name(ctx, item);
                }
            } else if (!_mv_973.has_value) {
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
        __auto_type _mv_974 = (*spec_expr);
        switch (_mv_974.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_974.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) < 2)) {
                        return (slop_option_string){.has_value = false};
                    } else {
                        __auto_type _mv_975 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_975.has_value) {
                            __auto_type spec_body = _mv_975.value;
                            __auto_type _mv_976 = (*spec_body);
                            switch (_mv_976.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type body_lst = _mv_976.data.lst;
                                    {
                                        __auto_type body_items = body_lst.items;
                                        __auto_type body_len = ((int64_t)((body_items).len));
                                        if ((body_len < 1)) {
                                            return (slop_option_string){.has_value = false};
                                        } else {
                                            __auto_type _mv_977 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_977.has_value) {
                                                __auto_type ret_type = _mv_977.value;
                                                return defn_check_result_type(ctx, ret_type);
                                            } else if (!_mv_977.has_value) {
                                                return (slop_option_string){.has_value = false};
                                            }
                                        }
                                    }
                                }
                                default: {
                                    return (slop_option_string){.has_value = false};
                                }
                            }
                        } else if (!_mv_975.has_value) {
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
        __auto_type _mv_978 = (*type_expr);
        switch (_mv_978.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_978.data.sym;
                {
                    __auto_type type_name = sym.name;
                    __auto_type _mv_979 = context_ctx_lookup_result_type_alias(ctx, type_name);
                    if (_mv_979.has_value) {
                        __auto_type alias_result = _mv_979.value;
                        return (slop_option_string){.has_value = 1, .value = alias_result};
                    } else if (!_mv_979.has_value) {
                        __auto_type _mv_980 = context_ctx_lookup_type(ctx, type_name);
                        if (_mv_980.has_value) {
                            __auto_type entry = _mv_980.value;
                            return (slop_option_string){.has_value = 1, .value = entry.c_name};
                        } else if (!_mv_980.has_value) {
                            return (slop_option_string){.has_value = false};
                        }
                    }
                }
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_978.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) < 3)) {
                        return (slop_option_string){.has_value = false};
                    } else {
                        __auto_type _mv_981 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_981.has_value) {
                            __auto_type head = _mv_981.value;
                            __auto_type _mv_982 = (*head);
                            switch (_mv_982.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_982.data.sym;
                                    if (string_eq(sym.name, SLOP_STR("Result"))) {
                                        __auto_type _mv_983 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_983.has_value) {
                                            __auto_type ok_type_expr = _mv_983.value;
                                            __auto_type _mv_984 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_984.has_value) {
                                                __auto_type err_type_expr = _mv_984.value;
                                                {
                                                    __auto_type ok_c_type = context_to_c_type_prefixed(ctx, ok_type_expr);
                                                    __auto_type err_c_type = context_to_c_type_prefixed(ctx, err_type_expr);
                                                    __auto_type result_name = defn_build_result_name(arena, ok_c_type, err_c_type);
                                                    return (slop_option_string){.has_value = 1, .value = result_name};
                                                }
                                            } else if (!_mv_984.has_value) {
                                                return (slop_option_string){.has_value = false};
                                            }
                                        } else if (!_mv_983.has_value) {
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
                        } else if (!_mv_981.has_value) {
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
        __auto_type _mv_985 = (*params_expr);
        switch (_mv_985.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_985.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    __auto_type result = SLOP_STR("");
                    __auto_type i = 0;
                    while ((i < len)) {
                        __auto_type _mv_986 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_986.has_value) {
                            __auto_type param = _mv_986.value;
                            {
                                __auto_type param_str = defn_build_single_param(ctx, param);
                                if (string_eq(result, SLOP_STR(""))) {
                                    result = param_str;
                                } else {
                                    result = context_ctx_str3(ctx, result, SLOP_STR(", "), param_str);
                                }
                            }
                        } else if (!_mv_986.has_value) {
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
        __auto_type _mv_987 = (*param);
        switch (_mv_987.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_987.data.lst;
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
                            __auto_type _mv_988 = ({ __auto_type _lst = items; size_t _idx = (size_t)name_idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_988.has_value) {
                                __auto_type name_expr = _mv_988.value;
                                __auto_type _mv_989 = (*name_expr);
                                switch (_mv_989.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type name_sym = _mv_989.data.sym;
                                        __auto_type _mv_990 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_990.has_value) {
                                            __auto_type type_expr = _mv_990.value;
                                            {
                                                __auto_type param_name = ctype_to_c_name(arena, name_sym.name);
                                                {
                                                    __auto_type param_type = context_to_c_type_prefixed(ctx, type_expr);
                                                    return context_ctx_str3(ctx, param_type, SLOP_STR(" "), param_name);
                                                }
                                            }
                                        } else if (!_mv_990.has_value) {
                                            return SLOP_STR("/* missing param type */");
                                        }
                                    }
                                    default: {
                                        return SLOP_STR("/* param name must be symbol */");
                                    }
                                }
                            } else if (!_mv_988.has_value) {
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
        __auto_type _mv_991 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_991.has_value) {
            __auto_type first = _mv_991.value;
            __auto_type _mv_992 = (*first);
            switch (_mv_992.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_992.data.sym;
                    {
                        __auto_type name = sym.name;
                        return ((string_eq(name, SLOP_STR("in"))) || (string_eq(name, SLOP_STR("out"))) || (string_eq(name, SLOP_STR("mut"))));
                    }
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_991.has_value) {
            return 0;
        }
    }
}

uint8_t defn_is_fn_type(types_SExpr* type_expr) {
    __auto_type _mv_993 = (*type_expr);
    switch (_mv_993.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_993.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_994 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_994.has_value) {
                        __auto_type first = _mv_994.value;
                        __auto_type _mv_995 = (*first);
                        switch (_mv_995.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_995.data.sym;
                                return string_eq(sym.name, SLOP_STR("Fn"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_994.has_value) {
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
        __auto_type _mv_996 = (*type_expr);
        switch (_mv_996.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_996.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 2)) {
                        return context_ctx_str(ctx, SLOP_STR("void* "), param_name);
                    } else {
                        {
                            __auto_type ret_type = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)(len - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type ret = _mv.value; context_to_c_type_prefixed(ctx, ret); }) : (SLOP_STR("void")); });
                            if ((len == 2)) {
                                return context_ctx_str(ctx, context_ctx_str(ctx, ret_type, SLOP_STR("(*")), context_ctx_str(ctx, param_name, SLOP_STR(")(void)")));
                            } else {
                                __auto_type _mv_997 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_997.has_value) {
                                    __auto_type args_expr = _mv_997.value;
                                    {
                                        __auto_type args_str = defn_build_fn_args_str_for_param(ctx, args_expr);
                                        return context_ctx_str(ctx, context_ctx_str(ctx, ret_type, SLOP_STR("(*")), context_ctx_str(ctx, param_name, context_ctx_str(ctx, SLOP_STR(")"), args_str)));
                                    }
                                } else if (!_mv_997.has_value) {
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
        __auto_type _mv_998 = (*args_expr);
        switch (_mv_998.tag) {
            case types_SExpr_lst:
            {
                __auto_type args_list = _mv_998.data.lst;
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
                                __auto_type _mv_999 = ({ __auto_type _lst = arg_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_999.has_value) {
                                    __auto_type arg_expr = _mv_999.value;
                                    {
                                        __auto_type arg_type = context_to_c_type_prefixed(ctx, arg_expr);
                                        if ((i > 0)) {
                                            result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR(", "), arg_type));
                                        } else {
                                            result = context_ctx_str(ctx, result, arg_type);
                                        }
                                    }
                                } else if (!_mv_999.has_value) {
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
        while ((i < len)) {
            __auto_type _mv_1000 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1000.has_value) {
                __auto_type item = _mv_1000.value;
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
            } else if (!_mv_1000.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t defn_is_c_name_attr(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_1001 = (*expr);
    switch (_mv_1001.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1001.data.sym;
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
        while (((i < len) && !(found_body))) {
            __auto_type _mv_1002 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1002.has_value) {
                __auto_type item = _mv_1002.value;
                if ((defn_is_annotation(item) || defn_is_c_name_attr(item))) {
                    i = (i + 1);
                } else {
                    if (((i > 0) && defn_is_c_name_attr_at(items, (i - 1)))) {
                        i = (i + 1);
                    } else {
                        found_body = 1;
                    }
                }
            } else if (!_mv_1002.has_value) {
                i = (i + 1);
            }
        }
        return !(found_body);
    }
}

uint8_t defn_is_c_name_attr_at(slop_list_types_SExpr_ptr items, int64_t idx) {
    __auto_type _mv_1003 = ({ __auto_type _lst = items; size_t _idx = (size_t)idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
    if (_mv_1003.has_value) {
        __auto_type item = _mv_1003.value;
        return defn_is_c_name_attr(item);
    } else if (!_mv_1003.has_value) {
        return 0;
    }
}

int64_t defn_find_body_start(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 3;
        uint8_t found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_1004 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1004.has_value) {
                __auto_type item = _mv_1004.value;
                if (defn_is_annotation(item)) {
                    i = (i + 1);
                } else {
                    found = 1;
                }
            } else if (!_mv_1004.has_value) {
                found = 1;
            }
        }
        return i;
    }
}

uint8_t defn_is_annotation(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_1005 = (*expr);
    switch (_mv_1005.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1005.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_1006 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1006.has_value) {
                        __auto_type head = _mv_1006.value;
                        __auto_type _mv_1007 = (*head);
                        switch (_mv_1007.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1007.data.sym;
                                {
                                    __auto_type name = sym.name;
                                    return ((string_eq(name, SLOP_STR("@intent"))) || (string_eq(name, SLOP_STR("@spec"))) || (string_eq(name, SLOP_STR("@pre"))) || (string_eq(name, SLOP_STR("@post"))) || (string_eq(name, SLOP_STR("@assume"))) || (string_eq(name, SLOP_STR("@alloc"))) || (string_eq(name, SLOP_STR("@example"))) || (string_eq(name, SLOP_STR("@pure"))) || (string_eq(name, SLOP_STR("@doc"))) || (string_eq(name, SLOP_STR("@loop-invariant"))) || (string_eq(name, SLOP_STR("@property"))));
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1006.has_value) {
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
    __auto_type _mv_1008 = (*expr);
    switch (_mv_1008.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1008.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_1009 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1009.has_value) {
                        __auto_type head = _mv_1009.value;
                        __auto_type _mv_1010 = (*head);
                        switch (_mv_1010.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1010.data.sym;
                                return string_eq(sym.name, SLOP_STR("@pre"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1009.has_value) {
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
    __auto_type _mv_1011 = (*expr);
    switch (_mv_1011.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1011.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_1012 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1012.has_value) {
                        __auto_type head = _mv_1012.value;
                        __auto_type _mv_1013 = (*head);
                        switch (_mv_1013.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1013.data.sym;
                                return string_eq(sym.name, SLOP_STR("@post"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1012.has_value) {
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
    __auto_type _mv_1014 = (*expr);
    switch (_mv_1014.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1014.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_1015 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1015.has_value) {
                        __auto_type head = _mv_1015.value;
                        __auto_type _mv_1016 = (*head);
                        switch (_mv_1016.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1016.data.sym;
                                return string_eq(sym.name, SLOP_STR("@assume"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1015.has_value) {
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

uint8_t defn_is_verification_only_expr(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_1017 = (*expr);
    switch (_mv_1017.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1017.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len < 1)) {
                    return 0;
                } else {
                    {
                        __auto_type found = 0;
                        __auto_type i = 0;
                        __auto_type _mv_1018 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1018.has_value) {
                            __auto_type head = _mv_1018.value;
                            __auto_type _mv_1019 = (*head);
                            switch (_mv_1019.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_1019.data.sym;
                                    {
                                        __auto_type name = sym.name;
                                        if (((string_eq(name, SLOP_STR("forall"))) || (string_eq(name, SLOP_STR("exists"))) || (string_eq(name, SLOP_STR("implies"))))) {
                                            found = 1;
                                        }
                                    }
                                }
                                default: {
                                }
                            }
                        } else if (!_mv_1018.has_value) {
                        }
                        while (((i < len) && !(found))) {
                            __auto_type _mv_1020 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1020.has_value) {
                                __auto_type item = _mv_1020.value;
                                if (defn_is_verification_only_expr(item)) {
                                    found = 1;
                                }
                            } else if (!_mv_1020.has_value) {
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
    __auto_type _mv_1021 = (*expr);
    switch (_mv_1021.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1021.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_1022 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1022.has_value) {
                        __auto_type head = _mv_1022.value;
                        __auto_type _mv_1023 = (*head);
                        switch (_mv_1023.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1023.data.sym;
                                return string_eq(sym.name, SLOP_STR("@doc"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1022.has_value) {
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

slop_option_string defn_get_doc_string(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        slop_option_string result = (slop_option_string){.has_value = false};
        __auto_type _mv_1024 = (*expr);
        switch (_mv_1024.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1024.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 2)) {
                        __auto_type _mv_1025 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1025.has_value) {
                            __auto_type val = _mv_1025.value;
                            __auto_type _mv_1026 = (*val);
                            switch (_mv_1026.tag) {
                                case types_SExpr_str:
                                {
                                    __auto_type str = _mv_1026.data.str;
                                    result = (slop_option_string){.has_value = 1, .value = str.value};
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1025.has_value) {
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
        while (((i < len) && ({ __auto_type _mv = result; _mv.has_value ? (0) : (1); }))) {
            __auto_type _mv_1027 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1027.has_value) {
                __auto_type item = _mv_1027.value;
                if (defn_is_doc_form(item)) {
                    result = defn_get_doc_string(item);
                }
            } else if (!_mv_1027.has_value) {
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
        __auto_type _mv_1028 = (*expr);
        switch (_mv_1028.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1028.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 2)) {
                        __auto_type _mv_1029 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1029.has_value) {
                            __auto_type val = _mv_1029.value;
                            result = (slop_option_types_SExpr_ptr){.has_value = 1, .value = val};
                        } else if (!_mv_1029.has_value) {
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
        int64_t i = 3;
        while ((i < len)) {
            __auto_type _mv_1030 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1030.has_value) {
                __auto_type item = _mv_1030.value;
                if (defn_is_pre_form(item)) {
                    __auto_type _mv_1031 = defn_get_annotation_condition(item);
                    if (_mv_1031.has_value) {
                        __auto_type cond = _mv_1031.value;
                        ({ __auto_type _lst_p = &(result); __auto_type _item = (cond); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    } else if (!_mv_1031.has_value) {
                    }
                }
            } else if (!_mv_1030.has_value) {
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
        int64_t i = 3;
        while ((i < len)) {
            __auto_type _mv_1032 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1032.has_value) {
                __auto_type item = _mv_1032.value;
                if (defn_is_post_form(item)) {
                    __auto_type _mv_1033 = defn_get_annotation_condition(item);
                    if (_mv_1033.has_value) {
                        __auto_type cond = _mv_1033.value;
                        ({ __auto_type _lst_p = &(result); __auto_type _item = (cond); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    } else if (!_mv_1033.has_value) {
                    }
                }
            } else if (!_mv_1032.has_value) {
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
        int64_t i = 3;
        while ((i < len)) {
            __auto_type _mv_1034 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1034.has_value) {
                __auto_type item = _mv_1034.value;
                if (defn_is_assume_form(item)) {
                    __auto_type _mv_1035 = defn_get_annotation_condition(item);
                    if (_mv_1035.has_value) {
                        __auto_type cond = _mv_1035.value;
                        ({ __auto_type _lst_p = &(result); __auto_type _item = (cond); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    } else if (!_mv_1035.has_value) {
                    }
                }
            } else if (!_mv_1034.has_value) {
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
        while (((i < len) && !(found))) {
            __auto_type _mv_1036 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1036.has_value) {
                __auto_type item = _mv_1036.value;
                if ((defn_is_post_form(item) || defn_is_assume_form(item))) {
                    found = 1;
                }
            } else if (!_mv_1036.has_value) {
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
        while ((i < len)) {
            __auto_type _mv_1037 = ({ __auto_type _lst = preconditions; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1037.has_value) {
                __auto_type cond_expr = _mv_1037.value;
                {
                    __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                    __auto_type expr_str = parser_pretty_print(arena, cond_expr);
                    __auto_type escaped_str = defn_escape_for_c_string(arena, expr_str);
                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("SLOP_PRE(("), cond_c, SLOP_STR("), \""), escaped_str, SLOP_STR("\");")));
                }
            } else if (!_mv_1037.has_value) {
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
        while ((i < len)) {
            __auto_type _mv_1038 = ({ __auto_type _lst = postconditions; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1038.has_value) {
                __auto_type cond_expr = _mv_1038.value;
                if (!(defn_is_verification_only_expr(cond_expr))) {
                    {
                        __auto_type cond_c_raw = expr_transpile_expr(ctx, cond_expr);
                        __auto_type cond_c = strlib_replace(arena, strlib_replace(arena, cond_c_raw, SLOP_STR("_result"), SLOP_STR("_retval")), SLOP_STR("$result"), SLOP_STR("_retval"));
                        __auto_type expr_str = parser_pretty_print(arena, cond_expr);
                        __auto_type escaped_str = defn_escape_for_c_string(arena, expr_str);
                        context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("SLOP_POST(("), cond_c, SLOP_STR("), \""), escaped_str, SLOP_STR("\");")));
                    }
                }
            } else if (!_mv_1038.has_value) {
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
        while ((i < len)) {
            __auto_type _mv_1039 = ({ __auto_type _lst = assumptions; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1039.has_value) {
                __auto_type cond_expr = _mv_1039.value;
                if (!(defn_is_verification_only_expr(cond_expr))) {
                    {
                        __auto_type cond_c_raw = expr_transpile_expr(ctx, cond_expr);
                        __auto_type cond_c = strlib_replace(arena, strlib_replace(arena, cond_c_raw, SLOP_STR("_result"), SLOP_STR("_retval")), SLOP_STR("$result"), SLOP_STR("_retval"));
                        __auto_type expr_str = parser_pretty_print(arena, cond_expr);
                        __auto_type escaped_str = defn_escape_for_c_string(arena, expr_str);
                        context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("SLOP_POST(("), cond_c, SLOP_STR("), \""), escaped_str, SLOP_STR("\");")));
                    }
                }
            } else if (!_mv_1039.has_value) {
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

