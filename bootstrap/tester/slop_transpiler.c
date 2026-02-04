#include "../runtime/slop_runtime.h"
#include "slop_transpiler.h"

transpiler_GenericInfo transpiler_extract_generic_info(slop_arena* arena, slop_list_types_SExpr_ptr items);
void transpiler_prescan_module(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void transpiler_prescan_top_level(context_TranspileContext* ctx, types_SExpr* item);
void transpiler_prescan_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void transpiler_register_enum_variants(context_TranspileContext* ctx, slop_string enum_name, slop_list_types_SExpr_ptr items);
void transpiler_register_union_variants(context_TranspileContext* ctx, slop_string union_name, slop_list_types_SExpr_ptr items);
void transpiler_prescan_fn(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
uint8_t transpiler_fn_returns_string(slop_list_types_SExpr_ptr items);
slop_string transpiler_fn_return_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void transpiler_prescan_fn_params(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_list_context_FuncParamType_ptr transpiler_prescan_collect_param_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string transpiler_prescan_get_param_c_type(context_TranspileContext* ctx, types_SExpr* param);
uint8_t transpiler_prescan_is_param_mode(slop_list_types_SExpr_ptr items);
void transpiler_prescan_fn_result_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
uint8_t transpiler_is_spec_annotation(types_SExpr* expr);
void transpiler_extract_result_type(context_TranspileContext* ctx, types_SExpr* spec_expr);
void transpiler_check_and_register_result_type(context_TranspileContext* ctx, types_SExpr* type_expr);
slop_string transpiler_build_result_type_name(context_TranspileContext* ctx, slop_string ok_type, slop_string err_type);
void transpiler_prescan_fn_for_struct_keys(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void transpiler_prescan_expr_for_struct_keys(context_TranspileContext* ctx, types_SExpr* expr);
void transpiler_prescan_register_struct_key_type(context_TranspileContext* ctx, types_SExpr* type_expr);
uint8_t transpiler_is_builtin_map_key_type(slop_string name);
void transpiler_check_and_register_result_alias(context_TranspileContext* ctx, slop_string alias_name, types_SExpr* body_expr);
void transpiler_prescan_ffi(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
uint8_t transpiler_is_type_name(slop_string name);
void transpiler_prescan_import(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void transpiler_register_types_module_variants(context_TranspileContext* ctx);
void transpiler_register_file_module_variants(context_TranspileContext* ctx);
void transpiler_prescan_const(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void transpiler_register_ffi_function(context_TranspileContext* ctx, types_SExpr* func_decl);
slop_list_context_FuncParamType_ptr transpiler_extract_ffi_param_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string transpiler_extract_ffi_c_name(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, slop_string fn_name);
void transpiler_prescan_ffi_struct(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string transpiler_get_ffi_struct_c_name(slop_arena* arena, slop_list_types_SExpr_ptr items, int64_t name_idx, slop_string default_name);
slop_string transpiler_apply_struct_prefix_heuristic(slop_arena* arena, slop_string name);
uint8_t transpiler_string_ends_with(slop_string s, slop_string suffix);
uint8_t transpiler_is_ffi_string_item(slop_list_types_SExpr_ptr items, int64_t idx);
uint8_t transpiler_is_enum_def(slop_list_types_SExpr_ptr items);
uint8_t transpiler_is_record_def(slop_list_types_SExpr_ptr items);
uint8_t transpiler_is_union_def(slop_list_types_SExpr_ptr items);
slop_string transpiler_get_array_c_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, slop_string default_c_type);
void transpiler_process_imports(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void transpiler_process_exports(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void transpiler_emit_all_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
uint8_t transpiler_is_union_type_def(types_SExpr* item);
uint8_t transpiler_is_type_def(types_SExpr* item);
void transpiler_emit_all_functions(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
uint8_t transpiler_is_fn_def(types_SExpr* item);
void transpiler_transpile_module(context_TranspileContext* ctx, types_SExpr* module_expr);
int64_t transpiler_get_body_start(slop_list_types_SExpr_ptr items);
slop_list_string transpiler_get_export_names(slop_arena* arena, slop_list_types_SExpr_ptr items);
uint8_t transpiler_list_contains_str(slop_list_string lst, slop_string needle);
void transpiler_prescan_module_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
void transpiler_scan_type_for_generics(context_TranspileContext* ctx, types_SExpr* type_expr);
void transpiler_scan_record_fields_for_generics(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void transpiler_emit_ffi_includes(context_TranspileContext* ctx);
void transpiler_emit_ffi_includes_header(context_TranspileContext* ctx);
void transpiler_emit_header_guard_open(context_TranspileContext* ctx);
void transpiler_emit_header_guard_close(context_TranspileContext* ctx);
void transpiler_emit_header_standard_includes(context_TranspileContext* ctx);
void transpiler_emit_header_dependency_includes(context_TranspileContext* ctx);
void transpiler_emit_forward_decls(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
uint8_t transpiler_is_struct_type_def(types_SExpr* item);
uint8_t transpiler_has_enum_payload_variants(slop_list_types_SExpr_ptr items);
uint8_t transpiler_is_type_alias_def(types_SExpr* item);
uint8_t transpiler_is_result_type_alias_def(types_SExpr* item);
void transpiler_emit_type_alias_to_header(context_TranspileContext* ctx, types_SExpr* type_def);
uint8_t transpiler_is_array_type_body(types_SExpr* body_expr);
void transpiler_emit_array_typedef_to_header(context_TranspileContext* ctx, slop_string c_name, types_SExpr* body_expr);
slop_string transpiler_get_array_size_string(types_SExpr* expr);
uint8_t transpiler_is_range_type_body(types_SExpr* body_expr);
transpiler_RangeBoundsHeader transpiler_parse_range_bounds_header(types_SExpr* body_expr);
int64_t transpiler_string_to_int_header(slop_string s);
slop_string transpiler_select_smallest_c_type_header(int64_t min_val, int64_t max_val, uint8_t has_min, uint8_t has_max);
void transpiler_emit_range_typedef_to_header(context_TranspileContext* ctx, slop_string raw_name, slop_string c_name, types_SExpr* body_expr);
void transpiler_emit_forward_decls_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
void transpiler_emit_fn_forward_decls(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
void transpiler_emit_fn_forward_decls_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
void transpiler_emit_c_name_aliases(context_TranspileContext* ctx);
void transpiler_emit_fn_forward_decl_header(context_TranspileContext* ctx, types_SExpr* expr);
slop_option_string transpiler_get_type_name(types_SExpr* item);
void transpiler_emit_module_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
void transpiler_emit_type_aliases(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
void transpiler_emit_enum_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
void transpiler_emit_struct_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
void transpiler_emit_result_types(context_TranspileContext* ctx);
void transpiler_emit_single_result_type(context_TranspileContext* ctx, context_ResultType rt);
void transpiler_emit_result_types_header(context_TranspileContext* ctx);
void transpiler_emit_single_result_type_header(context_TranspileContext* ctx, context_ResultType rt);
void transpiler_emit_inline_records_header(context_TranspileContext* ctx);
void transpiler_emit_option_types_header(context_TranspileContext* ctx);
void transpiler_emit_value_option_types_header(context_TranspileContext* ctx);
void transpiler_emit_complex_value_option_types_header(context_TranspileContext* ctx);
void transpiler_emit_single_option_type_header(context_TranspileContext* ctx, context_OptionType ot);
void transpiler_emit_list_types_header(context_TranspileContext* ctx);
void transpiler_emit_primitive_list_types_header(context_TranspileContext* ctx);
void transpiler_emit_primitive_option_types_header(context_TranspileContext* ctx);
uint8_t transpiler_is_primitive_or_runtime_type(slop_string type_name);
void transpiler_emit_imported_list_types_header(context_TranspileContext* ctx);
void transpiler_emit_imported_option_types_header(context_TranspileContext* ctx);
void transpiler_emit_late_registered_option_types_header(context_TranspileContext* ctx);
void transpiler_emit_value_list_types_header(context_TranspileContext* ctx);
void transpiler_emit_complex_value_list_types_header(context_TranspileContext* ctx);
void transpiler_emit_struct_hash_eq(context_TranspileContext* ctx, slop_string c_type);
void transpiler_emit_union_payload_hash_eq(context_TranspileContext* ctx, slop_list_context_UnionVariantEntry variants);
uint8_t transpiler_is_primitive_slop_type(slop_string slop_type);
uint8_t transpiler_is_range_type_alias(context_TranspileContext* ctx, slop_string slop_type);
void transpiler_emit_union_hash_fn(context_TranspileContext* ctx, slop_string c_type, slop_list_context_UnionVariantEntry variants);
void transpiler_emit_union_variant_hash(context_TranspileContext* ctx, slop_string union_name, context_UnionVariantEntry variant);
void transpiler_emit_union_eq_fn(context_TranspileContext* ctx, slop_string c_type, slop_list_context_UnionVariantEntry variants);
void transpiler_emit_union_variant_eq(context_TranspileContext* ctx, slop_string union_name, context_UnionVariantEntry variant);
void transpiler_emit_struct_hash_fn(context_TranspileContext* ctx, slop_string c_type, slop_list_context_FieldEntry fields);
void transpiler_emit_field_hash(context_TranspileContext* ctx, context_FieldEntry field);
void transpiler_emit_struct_eq_fn(context_TranspileContext* ctx, slop_string c_type, slop_list_context_FieldEntry fields);
void transpiler_emit_field_eq(context_TranspileContext* ctx, context_FieldEntry field);
void transpiler_emit_struct_key_types_header(context_TranspileContext* ctx);
uint8_t transpiler_is_pointer_elem_type(slop_string elem_type);
void transpiler_emit_single_list_type_header(context_TranspileContext* ctx, context_ListType lt);
uint8_t transpiler_is_runtime_option_type(slop_string name);
uint8_t transpiler_is_runtime_list_type(slop_string name);
void transpiler_emit_chan_types_header(context_TranspileContext* ctx);
void transpiler_emit_chan_funcs_header(context_TranspileContext* ctx);
void transpiler_emit_chan_send_recv_funcs(context_TranspileContext* ctx, slop_string c_name, slop_string elem_type);
void transpiler_emit_thread_types_header(context_TranspileContext* ctx);
uint8_t transpiler_is_runtime_chan_type(slop_string name);
uint8_t transpiler_is_default_chan_type(slop_string name);
uint8_t transpiler_is_runtime_thread_type(slop_string name);
slop_string transpiler_uppercase_name(context_TranspileContext* ctx, slop_string name);
uint8_t transpiler_is_simple_enum_def(types_SExpr* item);
void transpiler_emit_module_types_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
void transpiler_emit_simple_type_aliases_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
void transpiler_emit_type_aliases_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
void transpiler_emit_simple_enums_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
void transpiler_emit_pending_container_deps(context_TranspileContext* ctx, types_SExpr* type_def);
void transpiler_emit_option_by_c_name(context_TranspileContext* ctx, slop_string c_name);
void transpiler_emit_list_by_c_name(context_TranspileContext* ctx, slop_string c_name);
void transpiler_emit_struct_union_types_sorted(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
uint8_t transpiler_index_in_list(slop_list_int lst, int64_t idx);
uint8_t transpiler_type_deps_satisfied(context_TranspileContext* ctx, types_SExpr* type_def);
uint8_t transpiler_type_is_available(context_TranspileContext* ctx, slop_string type_name);
uint8_t transpiler_is_emittable_container_type(context_TranspileContext* ctx, slop_string type_name);
uint8_t transpiler_is_slop_runtime_type(slop_string type_name);
uint8_t transpiler_is_primitive_type(slop_string type_name);
slop_list_string transpiler_get_type_field_types(context_TranspileContext* ctx, types_SExpr* type_def);
slop_list_string transpiler_extract_record_field_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr def_items);
slop_list_string transpiler_extract_union_variant_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr def_items);
slop_string transpiler_get_field_type_string(context_TranspileContext* ctx, types_SExpr* type_expr);
void transpiler_emit_option_list_for_type(context_TranspileContext* ctx, types_SExpr* type_def);
slop_string transpiler_get_type_c_name(context_TranspileContext* ctx, types_SExpr* type_def);
void transpiler_emit_option_for_inner_type(context_TranspileContext* ctx, slop_string inner_c_name);
void transpiler_emit_list_for_elem_type(context_TranspileContext* ctx, slop_string elem_c_name);
uint8_t transpiler_struct_uses_value_list_or_option(context_TranspileContext* ctx, types_SExpr* type_def);
void transpiler_emit_struct_dependent_list_types(context_TranspileContext* ctx, types_SExpr* type_def);
void transpiler_emit_struct_dependent_option_types(context_TranspileContext* ctx, types_SExpr* type_def);
void transpiler_emit_struct_dependent_list_types_safe(context_TranspileContext* ctx, types_SExpr* type_def);
void transpiler_emit_struct_dependent_option_types_safe(context_TranspileContext* ctx, types_SExpr* type_def);
uint8_t transpiler_is_type_emitted_or_primitive(context_TranspileContext* ctx, slop_string type_name);
uint8_t transpiler_is_imported_type(context_TranspileContext* ctx, slop_string type_name);
int64_t transpiler_find_char(slop_string s, uint8_t ch);
void transpiler_emit_list_type_if_needed_safe(context_TranspileContext* ctx, slop_string inner_type);
void transpiler_emit_list_type_if_needed(context_TranspileContext* ctx, slop_string inner_type);
uint8_t transpiler_struct_uses_list_type(context_TranspileContext* ctx, types_SExpr* type_def, slop_string list_type_name);
uint8_t transpiler_struct_uses_option_type(context_TranspileContext* ctx, types_SExpr* type_def, slop_string option_type_name);
uint8_t transpiler_type_body_uses_typename(context_TranspileContext* ctx, types_SExpr* body_expr, slop_string typename);
uint8_t transpiler_field_uses_typename(context_TranspileContext* ctx, types_SExpr* field_expr, slop_string typename);
void transpiler_emit_type_to_header(context_TranspileContext* ctx, types_SExpr* type_def);
void transpiler_emit_type_body_to_header(context_TranspileContext* ctx, slop_string raw_type_name, slop_string c_name, types_SExpr* body_expr);
void transpiler_emit_enum_to_header(context_TranspileContext* ctx, slop_string c_name, slop_list_types_SExpr_ptr items);
void transpiler_emit_struct_to_header(context_TranspileContext* ctx, slop_string raw_type_name, slop_string c_name, slop_list_types_SExpr_ptr items);
void transpiler_emit_field_to_header(context_TranspileContext* ctx, slop_string raw_type_name, slop_string c_type_name, types_SExpr* field_expr);
uint8_t transpiler_is_pointer_type_expr_header(types_SExpr* type_expr);
void transpiler_emit_union_to_header(context_TranspileContext* ctx, slop_string c_name, slop_list_types_SExpr_ptr items);
slop_string transpiler_get_variant_name(types_SExpr* variant_expr);
void transpiler_emit_union_variant_to_header(context_TranspileContext* ctx, types_SExpr* variant_expr);
void transpiler_emit_module_consts(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start, slop_list_string exports);
slop_string transpiler_get_const_name(types_SExpr* item);
void transpiler_emit_module_consts_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start, slop_list_string exports);
uint8_t transpiler_emit_const_header_if_exported(context_TranspileContext* ctx, types_SExpr* item, slop_list_string exports);
void transpiler_emit_const_header_decl(context_TranspileContext* ctx, slop_string raw_name, types_SExpr* type_expr, types_SExpr* value_expr);
uint8_t transpiler_is_const_int_type(slop_string type_name);
uint8_t transpiler_is_const_def(types_SExpr* item);
void transpiler_emit_module_functions(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
void transpiler_emit_all_lambdas(context_TranspileContext* ctx);
slop_string transpiler_generate_c_output(context_TranspileContext* ctx);
void transpiler_transpile_file(context_TranspileContext* ctx, slop_list_types_SExpr_ptr exprs);
uint8_t transpiler_is_module_expr(slop_list_types_SExpr_ptr exprs);

transpiler_GenericInfo transpiler_extract_generic_info(slop_arena* arena, slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 3;
        __auto_type result_is_generic = 0;
        __auto_type result_type_params = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        while ((i < len)) {
            __auto_type _mv_995 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_995.has_value) {
                __auto_type item = _mv_995.value;
                __auto_type _mv_996 = (*item);
                switch (_mv_996.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type lst = _mv_996.data.lst;
                        {
                            __auto_type sub_items = lst.items;
                            if ((((int64_t)((sub_items).len)) >= 1)) {
                                __auto_type _mv_997 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_997.has_value) {
                                    __auto_type head = _mv_997.value;
                                    __auto_type _mv_998 = (*head);
                                    switch (_mv_998.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_998.data.sym;
                                            if (string_eq(sym.name, SLOP_STR("@generic"))) {
                                                if ((((int64_t)((sub_items).len)) >= 2)) {
                                                    __auto_type _mv_999 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_999.has_value) {
                                                        __auto_type params_expr = _mv_999.value;
                                                        __auto_type _mv_1000 = (*params_expr);
                                                        switch (_mv_1000.tag) {
                                                            case types_SExpr_lst:
                                                            {
                                                                __auto_type params_lst = _mv_1000.data.lst;
                                                                {
                                                                    __auto_type param_items = params_lst.items;
                                                                    __auto_type param_len = ((int64_t)((param_items).len));
                                                                    __auto_type j = 0;
                                                                    while ((j < param_len)) {
                                                                        __auto_type _mv_1001 = ({ __auto_type _lst = param_items; size_t _idx = (size_t)j; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                        if (_mv_1001.has_value) {
                                                                            __auto_type param = _mv_1001.value;
                                                                            __auto_type _mv_1002 = (*param);
                                                                            switch (_mv_1002.tag) {
                                                                                case types_SExpr_sym:
                                                                                {
                                                                                    __auto_type param_sym = _mv_1002.data.sym;
                                                                                    ({ __auto_type _lst_p = &(result_type_params); __auto_type _item = (param_sym.name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                                                    break;
                                                                                }
                                                                                default: {
                                                                                    break;
                                                                                }
                                                                            }
                                                                        } else if (!_mv_1001.has_value) {
                                                                        }
                                                                        j = (j + 1);
                                                                    }
                                                                }
                                                                break;
                                                            }
                                                            case types_SExpr_sym:
                                                            {
                                                                __auto_type single_sym = _mv_1000.data.sym;
                                                                ({ __auto_type _lst_p = &(result_type_params); __auto_type _item = (single_sym.name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                                break;
                                                            }
                                                            default: {
                                                                break;
                                                            }
                                                        }
                                                    } else if (!_mv_999.has_value) {
                                                    }
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_997.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_995.has_value) {
            }
            i = (i + 1);
        }
        return (transpiler_GenericInfo){(((int64_t)((result_type_params).len)) > 0), result_type_params};
    }
}

void transpiler_prescan_module(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1003 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1003.has_value) {
                __auto_type item = _mv_1003.value;
                transpiler_prescan_top_level(ctx, item);
            } else if (!_mv_1003.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_prescan_top_level(context_TranspileContext* ctx, types_SExpr* item) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1004 = (*item);
    switch (_mv_1004.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1004.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) >= 1)) {
                    __auto_type _mv_1005 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1005.has_value) {
                        __auto_type head = _mv_1005.value;
                        __auto_type _mv_1006 = (*head);
                        switch (_mv_1006.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1006.data.sym;
                                {
                                    __auto_type name = sym.name;
                                    if (string_eq(name, SLOP_STR("type"))) {
                                        transpiler_prescan_type(ctx, items);
                                    } else if (string_eq(name, SLOP_STR("fn"))) {
                                        transpiler_prescan_fn(ctx, items);
                                    } else if (string_eq(name, SLOP_STR("const"))) {
                                        transpiler_prescan_const(ctx, items);
                                    } else if (string_eq(name, SLOP_STR("ffi"))) {
                                        transpiler_prescan_ffi(ctx, items);
                                    } else if (string_eq(name, SLOP_STR("ffi-struct"))) {
                                        transpiler_prescan_ffi_struct(ctx, items);
                                    } else if (string_eq(name, SLOP_STR("import"))) {
                                        transpiler_prescan_import(ctx, items);
                                    } else {
                                    }
                                }
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_1005.has_value) {
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

void transpiler_prescan_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if ((((int64_t)((items).len)) >= 2)) {
            __auto_type _mv_1007 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1007.has_value) {
                __auto_type name_expr = _mv_1007.value;
                __auto_type _mv_1008 = (*name_expr);
                switch (_mv_1008.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_1008.data.sym;
                        {
                            __auto_type type_name = sym.name;
                            __auto_type base_c_name = ctype_to_c_name(arena, type_name);
                            __auto_type c_name = ((context_ctx_prefixing_enabled(ctx)) ? ({ __auto_type _mv = context_ctx_get_module(ctx); _mv.has_value ? ({ __auto_type mod_name = _mv.value; context_ctx_str(ctx, ctype_to_c_name(arena, mod_name), context_ctx_str(ctx, SLOP_STR("_"), base_c_name)); }) : (base_c_name); }) : base_c_name);
                            {
                                __auto_type is_enum = transpiler_is_enum_def(items);
                                __auto_type is_record = transpiler_is_record_def(items);
                                __auto_type is_union = transpiler_is_union_def(items);
                                __auto_type c_type = transpiler_get_array_c_type(ctx, items, c_name);
                                context_ctx_register_type(ctx, (context_TypeEntry){type_name, c_name, c_type, is_enum, is_record, is_union});
                                if (is_enum) {
                                    transpiler_register_enum_variants(ctx, c_name, items);
                                }
                                if (is_union) {
                                    transpiler_register_union_variants(ctx, c_name, items);
                                }
                                if ((is_record || is_union)) {
                                    if ((((int64_t)((items).len)) >= 3)) {
                                        __auto_type _mv_1009 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1009.has_value) {
                                            __auto_type def_expr = _mv_1009.value;
                                            __auto_type _mv_1010 = (*def_expr);
                                            switch (_mv_1010.tag) {
                                                case types_SExpr_lst:
                                                {
                                                    __auto_type def_lst = _mv_1010.data.lst;
                                                    transpiler_scan_record_fields_for_generics(ctx, def_lst.items);
                                                    break;
                                                }
                                                default: {
                                                    break;
                                                }
                                            }
                                        } else if (!_mv_1009.has_value) {
                                        }
                                    }
                                    {
                                        __auto_type type_id = ctype_type_to_identifier(arena, c_name);
                                        __auto_type option_c_name = context_ctx_str(ctx, SLOP_STR("slop_option_"), type_id);
                                        context_ctx_register_option_type(ctx, c_name, option_c_name);
                                    }
                                }
                                if ((((int64_t)((items).len)) >= 3)) {
                                    __auto_type _mv_1011 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_1011.has_value) {
                                        __auto_type body_expr = _mv_1011.value;
                                        transpiler_check_and_register_result_alias(ctx, type_name, body_expr);
                                        {
                                            __auto_type slop_type_str = parser_pretty_print(arena, body_expr);
                                            if (defn_is_generic_type_alias(slop_type_str)) {
                                                context_ctx_register_type_alias(ctx, type_name, slop_type_str);
                                            }
                                            if ((strlib_starts_with(slop_type_str, SLOP_STR("(Map ")) || strlib_starts_with(slop_type_str, SLOP_STR("(Set ")))) {
                                                transpiler_scan_type_for_generics(ctx, body_expr);
                                            }
                                        }
                                    } else if (!_mv_1011.has_value) {
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
            } else if (!_mv_1007.has_value) {
            }
        }
    }
}

void transpiler_register_enum_variants(context_TranspileContext* ctx, slop_string enum_name, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if ((((int64_t)((items).len)) >= 3)) {
        __auto_type _mv_1012 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1012.has_value) {
            __auto_type def_expr = _mv_1012.value;
            __auto_type _mv_1013 = (*def_expr);
            switch (_mv_1013.tag) {
                case types_SExpr_lst:
                {
                    __auto_type def_lst = _mv_1013.data.lst;
                    {
                        __auto_type def_items = def_lst.items;
                        __auto_type len = ((int64_t)((def_items).len));
                        __auto_type i = 1;
                        while ((i < len)) {
                            __auto_type _mv_1014 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1014.has_value) {
                                __auto_type variant_expr = _mv_1014.value;
                                __auto_type _mv_1015 = (*variant_expr);
                                switch (_mv_1015.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1015.data.sym;
                                        context_ctx_register_enum_variant(ctx, sym.name, enum_name);
                                        break;
                                    }
                                    case types_SExpr_lst:
                                    {
                                        __auto_type variant_lst = _mv_1015.data.lst;
                                        if ((((int64_t)((variant_lst.items).len)) > 0)) {
                                            __auto_type _mv_1016 = ({ __auto_type _lst = variant_lst.items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1016.has_value) {
                                                __auto_type name_expr = _mv_1016.value;
                                                __auto_type _mv_1017 = (*name_expr);
                                                switch (_mv_1017.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type name_sym = _mv_1017.data.sym;
                                                        context_ctx_register_enum_variant(ctx, name_sym.name, enum_name);
                                                        break;
                                                    }
                                                    default: {
                                                        break;
                                                    }
                                                }
                                            } else if (!_mv_1016.has_value) {
                                            }
                                        }
                                        break;
                                    }
                                    default: {
                                        break;
                                    }
                                }
                            } else if (!_mv_1014.has_value) {
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
        } else if (!_mv_1012.has_value) {
        }
    }
}

void transpiler_register_union_variants(context_TranspileContext* ctx, slop_string union_name, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if ((((int64_t)((items).len)) >= 3)) {
            __auto_type _mv_1018 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1018.has_value) {
                __auto_type def_expr = _mv_1018.value;
                __auto_type _mv_1019 = (*def_expr);
                switch (_mv_1019.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type def_lst = _mv_1019.data.lst;
                        {
                            __auto_type def_items = def_lst.items;
                            __auto_type len = ((int64_t)((def_items).len));
                            __auto_type i = 1;
                            while ((i < len)) {
                                __auto_type _mv_1020 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1020.has_value) {
                                    __auto_type variant_expr = _mv_1020.value;
                                    __auto_type _mv_1021 = (*variant_expr);
                                    switch (_mv_1021.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_1021.data.sym;
                                            {
                                                __auto_type variant_name = sym.name;
                                                context_ctx_register_enum_variant(ctx, variant_name, union_name);
                                                context_ctx_register_union_variant(ctx, variant_name, union_name, ctype_to_c_name(arena, variant_name), SLOP_STR(""), SLOP_STR(""));
                                            }
                                            break;
                                        }
                                        case types_SExpr_lst:
                                        {
                                            __auto_type variant_lst = _mv_1021.data.lst;
                                            {
                                                __auto_type vl_items = variant_lst.items;
                                                if ((((int64_t)((vl_items).len)) >= 2)) {
                                                    __auto_type _mv_1022 = ({ __auto_type _lst = vl_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_1022.has_value) {
                                                        __auto_type name_expr = _mv_1022.value;
                                                        __auto_type _mv_1023 = (*name_expr);
                                                        switch (_mv_1023.tag) {
                                                            case types_SExpr_sym:
                                                            {
                                                                __auto_type name_sym = _mv_1023.data.sym;
                                                                {
                                                                    __auto_type variant_name = name_sym.name;
                                                                    __auto_type c_variant_name = ctype_to_c_name(arena, variant_name);
                                                                    context_ctx_register_enum_variant(ctx, variant_name, union_name);
                                                                    __auto_type _mv_1024 = ({ __auto_type _lst = vl_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                    if (_mv_1024.has_value) {
                                                                        __auto_type type_expr = _mv_1024.value;
                                                                        {
                                                                            __auto_type slop_type = parser_pretty_print(arena, type_expr);
                                                                            __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                                            __auto_type is_ptr = transpiler_is_pointer_type_expr_header(type_expr);
                                                                            context_ctx_register_union_variant(ctx, variant_name, union_name, c_variant_name, slop_type, c_type);
                                                                            context_ctx_register_field_type(ctx, union_name, variant_name, c_type, slop_type, is_ptr);
                                                                        }
                                                                    } else if (!_mv_1024.has_value) {
                                                                        context_ctx_register_union_variant(ctx, variant_name, union_name, c_variant_name, SLOP_STR(""), SLOP_STR(""));
                                                                    }
                                                                }
                                                                break;
                                                            }
                                                            default: {
                                                                break;
                                                            }
                                                        }
                                                    } else if (!_mv_1022.has_value) {
                                                    }
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_1020.has_value) {
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
            } else if (!_mv_1018.has_value) {
            }
        }
    }
}

void transpiler_prescan_fn(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if ((((int64_t)((items).len)) >= 2)) {
            __auto_type _mv_1025 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1025.has_value) {
                __auto_type name_expr = _mv_1025.value;
                __auto_type _mv_1026 = (*name_expr);
                switch (_mv_1026.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_1026.data.sym;
                        {
                            __auto_type fn_name = sym.name;
                            __auto_type base_name = ctype_to_c_name(arena, fn_name);
                            __auto_type mangled_name = ((string_eq(base_name, SLOP_STR("main"))) ? base_name : context_ctx_prefix_type(ctx, base_name));
                            __auto_type c_name = context_extract_fn_c_name(arena, items, mangled_name);
                            __auto_type returns_str = transpiler_fn_returns_string(items);
                            __auto_type return_type = transpiler_fn_return_type(ctx, items);
                            __auto_type slop_ret_type = defn_get_slop_return_type(ctx, items);
                            __auto_type param_types = transpiler_prescan_collect_param_types(ctx, items);
                            if (!(string_eq(c_name, mangled_name))) {
                                context_ctx_add_c_name_alias(ctx, (context_FuncCNameAlias){fn_name, mangled_name, c_name});
                            }
                            {
                                __auto_type generic_info = transpiler_extract_generic_info(arena, items);
                                __auto_type is_generic = generic_info.is_generic;
                                __auto_type type_params = generic_info.type_params;
                                slop_option_types_SExpr_ptr no_source = (slop_option_types_SExpr_ptr){.has_value = false};
                                context_ctx_register_func(ctx, (context_FuncEntry){fn_name, c_name, return_type, slop_ret_type, 0, returns_str, param_types, is_generic, type_params, no_source});
                            }
                            transpiler_prescan_fn_params(ctx, items);
                            transpiler_prescan_fn_result_type(ctx, items);
                            transpiler_prescan_fn_for_struct_keys(ctx, items);
                        }
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
}

uint8_t transpiler_fn_returns_string(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 3;
        __auto_type result = 0;
        while (((i < len) && !(result))) {
            __auto_type _mv_1027 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1027.has_value) {
                __auto_type item = _mv_1027.value;
                __auto_type _mv_1028 = (*item);
                switch (_mv_1028.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type lst = _mv_1028.data.lst;
                        {
                            __auto_type sub_items = lst.items;
                            if ((((int64_t)((sub_items).len)) >= 2)) {
                                __auto_type _mv_1029 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1029.has_value) {
                                    __auto_type head = _mv_1029.value;
                                    __auto_type _mv_1030 = (*head);
                                    switch (_mv_1030.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_1030.data.sym;
                                            if (string_eq(sym.name, SLOP_STR("@spec"))) {
                                                __auto_type _mv_1031 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1031.has_value) {
                                                    __auto_type spec_body = _mv_1031.value;
                                                    __auto_type _mv_1032 = (*spec_body);
                                                    switch (_mv_1032.tag) {
                                                        case types_SExpr_lst:
                                                        {
                                                            __auto_type body_lst = _mv_1032.data.lst;
                                                            {
                                                                __auto_type body_items = body_lst.items;
                                                                __auto_type body_len = ((int64_t)((body_items).len));
                                                                if ((body_len >= 1)) {
                                                                    __auto_type _mv_1033 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                    if (_mv_1033.has_value) {
                                                                        __auto_type ret_type = _mv_1033.value;
                                                                        __auto_type _mv_1034 = (*ret_type);
                                                                        switch (_mv_1034.tag) {
                                                                            case types_SExpr_sym:
                                                                            {
                                                                                __auto_type ret_sym = _mv_1034.data.sym;
                                                                                result = string_eq(ret_sym.name, SLOP_STR("String"));
                                                                                break;
                                                                            }
                                                                            default: {
                                                                                break;
                                                                            }
                                                                        }
                                                                    } else if (!_mv_1033.has_value) {
                                                                    }
                                                                }
                                                            }
                                                            break;
                                                        }
                                                        default: {
                                                            break;
                                                        }
                                                    }
                                                } else if (!_mv_1031.has_value) {
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
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
            } else if (!_mv_1027.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_string transpiler_fn_return_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 3;
        __auto_type result = SLOP_STR("");
        while (((i < len) && string_eq(result, SLOP_STR("")))) {
            __auto_type _mv_1035 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1035.has_value) {
                __auto_type item = _mv_1035.value;
                __auto_type _mv_1036 = (*item);
                switch (_mv_1036.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type lst = _mv_1036.data.lst;
                        {
                            __auto_type sub_items = lst.items;
                            if ((((int64_t)((sub_items).len)) >= 2)) {
                                __auto_type _mv_1037 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1037.has_value) {
                                    __auto_type head = _mv_1037.value;
                                    __auto_type _mv_1038 = (*head);
                                    switch (_mv_1038.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_1038.data.sym;
                                            if (string_eq(sym.name, SLOP_STR("@spec"))) {
                                                __auto_type _mv_1039 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1039.has_value) {
                                                    __auto_type spec_body = _mv_1039.value;
                                                    __auto_type _mv_1040 = (*spec_body);
                                                    switch (_mv_1040.tag) {
                                                        case types_SExpr_lst:
                                                        {
                                                            __auto_type body_lst = _mv_1040.data.lst;
                                                            {
                                                                __auto_type body_items = body_lst.items;
                                                                __auto_type body_len = ((int64_t)((body_items).len));
                                                                if ((body_len >= 1)) {
                                                                    __auto_type _mv_1041 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                    if (_mv_1041.has_value) {
                                                                        __auto_type ret_type = _mv_1041.value;
                                                                        result = context_to_c_type_prefixed(ctx, ret_type);
                                                                    } else if (!_mv_1041.has_value) {
                                                                    }
                                                                }
                                                            }
                                                            break;
                                                        }
                                                        default: {
                                                            break;
                                                        }
                                                    }
                                                } else if (!_mv_1039.has_value) {
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_1037.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1035.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

void transpiler_prescan_fn_params(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if ((((int64_t)((items).len)) >= 3)) {
        __auto_type _mv_1042 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1042.has_value) {
            __auto_type params_expr = _mv_1042.value;
            __auto_type _mv_1043 = (*params_expr);
            switch (_mv_1043.tag) {
                case types_SExpr_lst:
                {
                    __auto_type params_lst = _mv_1043.data.lst;
                    {
                        __auto_type params = params_lst.items;
                        __auto_type param_count = ((int64_t)((params).len));
                        __auto_type i = 0;
                        while ((i < param_count)) {
                            __auto_type _mv_1044 = ({ __auto_type _lst = params; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1044.has_value) {
                                __auto_type param_expr = _mv_1044.value;
                                __auto_type _mv_1045 = (*param_expr);
                                switch (_mv_1045.tag) {
                                    case types_SExpr_lst:
                                    {
                                        __auto_type param_lst = _mv_1045.data.lst;
                                        {
                                            __auto_type param_items = param_lst.items;
                                            if ((((int64_t)((param_items).len)) >= 2)) {
                                                __auto_type _mv_1046 = ({ __auto_type _lst = param_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1046.has_value) {
                                                    __auto_type type_expr = _mv_1046.value;
                                                    transpiler_scan_type_for_generics(ctx, type_expr);
                                                } else if (!_mv_1046.has_value) {
                                                }
                                            }
                                        }
                                        break;
                                    }
                                    default: {
                                        break;
                                    }
                                }
                            } else if (!_mv_1044.has_value) {
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
        } else if (!_mv_1042.has_value) {
        }
    }
}

slop_list_context_FuncParamType_ptr transpiler_prescan_collect_param_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type result = ((slop_list_context_FuncParamType_ptr){ .data = (context_FuncParamType**)slop_arena_alloc(arena, 16 * sizeof(context_FuncParamType*)), .len = 0, .cap = 16 });
        if ((((int64_t)((items).len)) >= 3)) {
            __auto_type _mv_1047 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1047.has_value) {
                __auto_type params_expr = _mv_1047.value;
                __auto_type _mv_1048 = (*params_expr);
                switch (_mv_1048.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type params_lst = _mv_1048.data.lst;
                        {
                            __auto_type params = params_lst.items;
                            __auto_type param_count = ((int64_t)((params).len));
                            __auto_type i = 0;
                            while ((i < param_count)) {
                                __auto_type _mv_1049 = ({ __auto_type _lst = params; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1049.has_value) {
                                    __auto_type param_expr = _mv_1049.value;
                                    {
                                        __auto_type c_type = transpiler_prescan_get_param_c_type(ctx, param_expr);
                                        __auto_type param_info = ((context_FuncParamType*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 64); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
                                        (*param_info).c_type = c_type;
                                        ({ __auto_type _lst_p = &(result); __auto_type _item = (param_info); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    }
                                } else if (!_mv_1049.has_value) {
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
            } else if (!_mv_1047.has_value) {
            }
        }
        return result;
    }
}

slop_string transpiler_prescan_get_param_c_type(context_TranspileContext* ctx, types_SExpr* param) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((param != NULL)), "(!= param nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1050 = (*param);
        switch (_mv_1050.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1050.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 2)) {
                        return SLOP_STR("void*");
                    } else {
                        {
                            __auto_type has_mode = ((len >= 3) && transpiler_prescan_is_param_mode(items));
                            __auto_type type_idx = ((has_mode) ? 2 : 1);
                            __auto_type _mv_1051 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1051.has_value) {
                                __auto_type type_expr = _mv_1051.value;
                                return context_to_c_type_prefixed(ctx, type_expr);
                            } else if (!_mv_1051.has_value) {
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

uint8_t transpiler_prescan_is_param_mode(slop_list_types_SExpr_ptr items) {
    if ((((int64_t)((items).len)) < 1)) {
        return 0;
    } else {
        __auto_type _mv_1052 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1052.has_value) {
            __auto_type first = _mv_1052.value;
            __auto_type _mv_1053 = (*first);
            switch (_mv_1053.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_1053.data.sym;
                    {
                        __auto_type name = sym.name;
                        if (string_eq(name, SLOP_STR("in"))) {
                            return 1;
                        } else if (string_eq(name, SLOP_STR("mut"))) {
                            return 1;
                        } else if (string_eq(name, SLOP_STR("ref"))) {
                            return 1;
                        } else if (string_eq(name, SLOP_STR("out"))) {
                            return 1;
                        } else {
                            return 0;
                        }
                    }
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_1052.has_value) {
            return 0;
        }
    }
}

void transpiler_prescan_fn_result_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 3;
        while ((i < len)) {
            __auto_type _mv_1054 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1054.has_value) {
                __auto_type item = _mv_1054.value;
                if (transpiler_is_spec_annotation(item)) {
                    transpiler_extract_result_type(ctx, item);
                }
            } else if (!_mv_1054.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t transpiler_is_spec_annotation(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_1055 = (*expr);
    switch (_mv_1055.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1055.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_1056 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1056.has_value) {
                        __auto_type head = _mv_1056.value;
                        __auto_type _mv_1057 = (*head);
                        switch (_mv_1057.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1057.data.sym;
                                return string_eq(sym.name, SLOP_STR("@spec"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1056.has_value) {
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

void transpiler_extract_result_type(context_TranspileContext* ctx, types_SExpr* spec_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((spec_expr != NULL)), "(!= spec-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1058 = (*spec_expr);
        switch (_mv_1058.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1058.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 2)) {
                        __auto_type _mv_1059 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1059.has_value) {
                            __auto_type spec_body = _mv_1059.value;
                            __auto_type _mv_1060 = (*spec_body);
                            switch (_mv_1060.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type body_lst = _mv_1060.data.lst;
                                    {
                                        __auto_type body_items = body_lst.items;
                                        __auto_type body_len = ((int64_t)((body_items).len));
                                        if ((body_len >= 1)) {
                                            __auto_type _mv_1061 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1061.has_value) {
                                                __auto_type ret_type = _mv_1061.value;
                                                transpiler_scan_type_for_generics(ctx, ret_type);
                                                transpiler_check_and_register_result_type(ctx, ret_type);
                                            } else if (!_mv_1061.has_value) {
                                            }
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1059.has_value) {
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

void transpiler_check_and_register_result_type(context_TranspileContext* ctx, types_SExpr* type_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1062 = (*type_expr);
        switch (_mv_1062.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1062.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 3)) {
                        __auto_type _mv_1063 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1063.has_value) {
                            __auto_type head = _mv_1063.value;
                            __auto_type _mv_1064 = (*head);
                            switch (_mv_1064.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_1064.data.sym;
                                    if (string_eq(sym.name, SLOP_STR("Result"))) {
                                        __auto_type _mv_1065 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1065.has_value) {
                                            __auto_type ok_type_expr = _mv_1065.value;
                                            __auto_type _mv_1066 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1066.has_value) {
                                                __auto_type err_type_expr = _mv_1066.value;
                                                {
                                                    __auto_type ok_c_type = context_to_c_type_prefixed(ctx, ok_type_expr);
                                                    __auto_type err_c_type = context_to_c_type_prefixed(ctx, err_type_expr);
                                                    __auto_type result_name = transpiler_build_result_type_name(ctx, ok_c_type, err_c_type);
                                                    context_ctx_register_result_type(ctx, ok_c_type, err_c_type, result_name);
                                                }
                                            } else if (!_mv_1066.has_value) {
                                            }
                                        } else if (!_mv_1065.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1063.has_value) {
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

slop_string transpiler_build_result_type_name(context_TranspileContext* ctx, slop_string ok_type, slop_string err_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type ok_id = ctype_type_to_identifier(arena, ok_type);
        __auto_type err_id = ctype_type_to_identifier(arena, err_type);
        return context_ctx_str5(ctx, SLOP_STR("slop_result_"), ok_id, SLOP_STR("_"), err_id, SLOP_STR(""));
    }
}

void transpiler_prescan_fn_for_struct_keys(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 3;
        while ((i < len)) {
            __auto_type _mv_1067 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1067.has_value) {
                __auto_type item = _mv_1067.value;
                transpiler_prescan_expr_for_struct_keys(ctx, item);
            } else if (!_mv_1067.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_prescan_expr_for_struct_keys(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_1068 = (*expr);
    switch (_mv_1068.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1068.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len >= 1)) {
                    __auto_type _mv_1069 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1069.has_value) {
                        __auto_type head = _mv_1069.value;
                        __auto_type _mv_1070 = (*head);
                        switch (_mv_1070.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1070.data.sym;
                                {
                                    __auto_type name = sym.name;
                                    if (string_eq(name, SLOP_STR("map-new"))) {
                                        if ((len >= 3)) {
                                            __auto_type _mv_1071 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1071.has_value) {
                                                __auto_type key_type_expr = _mv_1071.value;
                                                transpiler_prescan_register_struct_key_type(ctx, key_type_expr);
                                            } else if (!_mv_1071.has_value) {
                                            }
                                        }
                                    } else if (string_eq(name, SLOP_STR("set-new"))) {
                                        if ((len >= 3)) {
                                            __auto_type _mv_1072 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1072.has_value) {
                                                __auto_type elem_type_expr = _mv_1072.value;
                                                transpiler_prescan_register_struct_key_type(ctx, elem_type_expr);
                                            } else if (!_mv_1072.has_value) {
                                            }
                                        }
                                    } else {
                                        {
                                            __auto_type i = 0;
                                            while ((i < len)) {
                                                __auto_type _mv_1073 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1073.has_value) {
                                                    __auto_type child = _mv_1073.value;
                                                    transpiler_prescan_expr_for_struct_keys(ctx, child);
                                                } else if (!_mv_1073.has_value) {
                                                }
                                                i = (i + 1);
                                            }
                                        }
                                    }
                                }
                                break;
                            }
                            default: {
                                {
                                    __auto_type i = 0;
                                    while ((i < len)) {
                                        __auto_type _mv_1074 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1074.has_value) {
                                            __auto_type child = _mv_1074.value;
                                            transpiler_prescan_expr_for_struct_keys(ctx, child);
                                        } else if (!_mv_1074.has_value) {
                                        }
                                        i = (i + 1);
                                    }
                                }
                                break;
                            }
                        }
                    } else if (!_mv_1069.has_value) {
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

void transpiler_prescan_register_struct_key_type(context_TranspileContext* ctx, types_SExpr* type_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1075 = (*type_expr);
        switch (_mv_1075.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_1075.data.sym;
                {
                    __auto_type name = sym.name;
                    if (!(transpiler_is_builtin_map_key_type(name))) {
                        __auto_type _mv_1076 = context_ctx_lookup_type(ctx, name);
                        if (_mv_1076.has_value) {
                            __auto_type type_entry = _mv_1076.value;
                            context_ctx_register_struct_key_type(ctx, type_entry.c_name);
                        } else if (!_mv_1076.has_value) {
                            __auto_type _mv_1077 = context_ctx_get_module(ctx);
                            if (_mv_1077.has_value) {
                                __auto_type mod = _mv_1077.value;
                                {
                                    __auto_type prefixed = context_ctx_str3(ctx, mod, SLOP_STR("_"), name);
                                    __auto_type _mv_1078 = context_ctx_lookup_type(ctx, prefixed);
                                    if (_mv_1078.has_value) {
                                        __auto_type type_entry = _mv_1078.value;
                                        context_ctx_register_struct_key_type(ctx, type_entry.c_name);
                                    } else if (!_mv_1078.has_value) {
                                        context_ctx_register_struct_key_type(ctx, ctype_to_c_name(arena, name));
                                    }
                                }
                            } else if (!_mv_1077.has_value) {
                                context_ctx_register_struct_key_type(ctx, ctype_to_c_name(arena, name));
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

uint8_t transpiler_is_builtin_map_key_type(slop_string name) {
    return (string_eq(name, SLOP_STR("String")) || (string_eq(name, SLOP_STR("Int")) || (string_eq(name, SLOP_STR("I64")) || (string_eq(name, SLOP_STR("I32")) || (string_eq(name, SLOP_STR("Uint")) || (string_eq(name, SLOP_STR("U64")) || (string_eq(name, SLOP_STR("U32")) || string_eq(name, SLOP_STR("Symbol")))))))));
}

void transpiler_check_and_register_result_alias(context_TranspileContext* ctx, slop_string alias_name, types_SExpr* body_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((body_expr != NULL)), "(!= body-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1079 = (*body_expr);
        switch (_mv_1079.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1079.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 3)) {
                        __auto_type _mv_1080 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1080.has_value) {
                            __auto_type head = _mv_1080.value;
                            __auto_type _mv_1081 = (*head);
                            switch (_mv_1081.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_1081.data.sym;
                                    if (string_eq(sym.name, SLOP_STR("Result"))) {
                                        __auto_type _mv_1082 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1082.has_value) {
                                            __auto_type ok_type_expr = _mv_1082.value;
                                            __auto_type _mv_1083 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1083.has_value) {
                                                __auto_type err_type_expr = _mv_1083.value;
                                                {
                                                    __auto_type ok_c_type = context_to_c_type_prefixed(ctx, ok_type_expr);
                                                    __auto_type err_c_type = context_to_c_type_prefixed(ctx, err_type_expr);
                                                    __auto_type result_name = transpiler_build_result_type_name(ctx, ok_c_type, err_c_type);
                                                    context_ctx_register_result_type_alias(ctx, alias_name, result_name);
                                                    context_ctx_register_result_type(ctx, ok_c_type, err_c_type, result_name);
                                                }
                                            } else if (!_mv_1083.has_value) {
                                            }
                                        } else if (!_mv_1082.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1080.has_value) {
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

void transpiler_prescan_ffi(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if ((len >= 2)) {
            __auto_type _mv_1084 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1084.has_value) {
                __auto_type header_expr = _mv_1084.value;
                __auto_type _mv_1085 = (*header_expr);
                switch (_mv_1085.tag) {
                    case types_SExpr_str:
                    {
                        __auto_type str = _mv_1085.data.str;
                        context_ctx_add_include(ctx, str.value);
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1084.has_value) {
            }
            {
                __auto_type i = 2;
                while ((i < len)) {
                    __auto_type _mv_1086 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1086.has_value) {
                        __auto_type func_decl = _mv_1086.value;
                        transpiler_register_ffi_function(ctx, func_decl);
                    } else if (!_mv_1086.has_value) {
                    }
                    i = (i + 1);
                }
            }
        }
    }
}

uint8_t transpiler_is_type_name(slop_string name) {
    if ((string_len(name) < 1)) {
        return 0;
    } else {
        {
            __auto_type first_char = strlib_char_at(name, 0);
            return ((first_char >= 65) && (first_char <= 90));
        }
    }
}

void transpiler_prescan_import(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if ((((int64_t)((items).len)) >= 3)) {
        __auto_type _mv_1087 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1087.has_value) {
            __auto_type mod_expr = _mv_1087.value;
            __auto_type _mv_1088 = (*mod_expr);
            switch (_mv_1088.tag) {
                case types_SExpr_sym:
                {
                    __auto_type mod_sym = _mv_1088.data.sym;
                    {
                        __auto_type mod_name = mod_sym.name;
                        __auto_type arena = (*ctx).arena;
                        context_ctx_add_import(ctx, mod_name);
                        if (string_eq(mod_name, SLOP_STR("types"))) {
                            transpiler_register_types_module_variants(ctx);
                        }
                        if (string_eq(mod_name, SLOP_STR("file"))) {
                            transpiler_register_file_module_variants(ctx);
                        }
                        __auto_type _mv_1089 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1089.has_value) {
                            __auto_type symbols_expr = _mv_1089.value;
                            __auto_type _mv_1090 = (*symbols_expr);
                            switch (_mv_1090.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type symbols_lst = _mv_1090.data.lst;
                                    {
                                        __auto_type syms = symbols_lst.items;
                                        __auto_type sym_len = ((int64_t)((syms).len));
                                        __auto_type j = 0;
                                        while ((j < sym_len)) {
                                            __auto_type _mv_1091 = ({ __auto_type _lst = syms; size_t _idx = (size_t)j; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1091.has_value) {
                                                __auto_type sym_item = _mv_1091.value;
                                                __auto_type _mv_1092 = (*sym_item);
                                                switch (_mv_1092.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type s = _mv_1092.data.sym;
                                                        {
                                                            __auto_type sym_name = s.name;
                                                            __auto_type c_mod_name = ctype_to_c_name(arena, mod_name);
                                                            __auto_type c_sym_name = ctype_to_c_name(arena, sym_name);
                                                            if (transpiler_is_type_name(sym_name)) {
                                                                {
                                                                    __auto_type existing = context_ctx_lookup_type(ctx, sym_name);
                                                                    __auto_type c_name = ({ __auto_type _mv = existing; _mv.has_value ? ({ __auto_type entry = _mv.value; entry.c_name; }) : (context_ctx_str3(ctx, c_mod_name, SLOP_STR("_"), c_sym_name)); });
                                                                    context_ctx_register_type(ctx, (context_TypeEntry){sym_name, c_name, c_name, ({ __auto_type _mv = existing; _mv.has_value ? ({ __auto_type e = _mv.value; e.is_enum; }) : (0); }), ({ __auto_type _mv = existing; _mv.has_value ? ({ __auto_type e = _mv.value; e.is_record; }) : (0); }), ({ __auto_type _mv = existing; _mv.has_value ? ({ __auto_type e = _mv.value; e.is_union; }) : (0); })});
                                                                    context_ctx_bind_var(ctx, (context_VarEntry){sym_name, c_name, SLOP_STR("auto"), SLOP_STR(""), 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                                                }
                                                            } else {
                                                                {
                                                                    __auto_type existing_func = context_ctx_lookup_func(ctx, sym_name);
                                                                    __auto_type c_name = ({ __auto_type _mv = existing_func; _mv.has_value ? ({ __auto_type entry = _mv.value; entry.c_name; }) : (context_ctx_str3(ctx, c_mod_name, SLOP_STR("_"), c_sym_name)); });
                                                                    __auto_type param_types = ({ __auto_type _mv = existing_func; _mv.has_value ? ({ __auto_type entry = _mv.value; entry.param_types; }) : (((slop_list_context_FuncParamType_ptr){ .data = (context_FuncParamType**)slop_arena_alloc(arena, 16 * sizeof(context_FuncParamType*)), .len = 0, .cap = 16 })); });
                                                                    __auto_type ret_type = ({ __auto_type _mv = existing_func; _mv.has_value ? ({ __auto_type entry = _mv.value; entry.return_type; }) : (SLOP_STR("")); });
                                                                    __auto_type slop_ret = ({ __auto_type _mv = existing_func; _mv.has_value ? ({ __auto_type entry = _mv.value; entry.slop_return_type; }) : (SLOP_STR("")); });
                                                                    __auto_type ret_ptr = ({ __auto_type _mv = existing_func; _mv.has_value ? ({ __auto_type entry = _mv.value; entry.returns_pointer; }) : (0); });
                                                                    __auto_type ret_str = ({ __auto_type _mv = existing_func; _mv.has_value ? ({ __auto_type entry = _mv.value; entry.returns_string; }) : (0); });
                                                                    __auto_type is_gen = ({ __auto_type _mv = existing_func; _mv.has_value ? ({ __auto_type entry = _mv.value; entry.is_generic; }) : (0); });
                                                                    __auto_type ty_params = ({ __auto_type _mv = existing_func; _mv.has_value ? ({ __auto_type entry = _mv.value; entry.type_params; }) : (((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 })); });
                                                                    slop_option_types_SExpr_ptr no_source = (slop_option_types_SExpr_ptr){.has_value = false};
                                                                    context_ctx_register_func(ctx, (context_FuncEntry){sym_name, c_name, ret_type, slop_ret, ret_ptr, ret_str, param_types, is_gen, ty_params, no_source});
                                                                }
                                                            }
                                                        }
                                                        break;
                                                    }
                                                    default: {
                                                        break;
                                                    }
                                                }
                                            } else if (!_mv_1091.has_value) {
                                            }
                                            j = (j + 1);
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1089.has_value) {
                        }
                    }
                    break;
                }
                default: {
                    break;
                }
            }
        } else if (!_mv_1087.has_value) {
        }
    }
}

void transpiler_register_types_module_variants(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("SExpr"), SLOP_STR("types_SExpr"), SLOP_STR("types_SExpr"), 0, 0, 1});
    context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("SExprSymbol"), SLOP_STR("types_SExprSymbol"), SLOP_STR("types_SExprSymbol"), 0, 1, 0});
    context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("SExprString"), SLOP_STR("types_SExprString"), SLOP_STR("types_SExprString"), 0, 1, 0});
    context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("SExprNumber"), SLOP_STR("types_SExprNumber"), SLOP_STR("types_SExprNumber"), 0, 1, 0});
    context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("SExprList"), SLOP_STR("types_SExprList"), SLOP_STR("types_SExprList"), 0, 1, 0});
    context_ctx_register_enum_variant(ctx, SLOP_STR("sym"), SLOP_STR("types_SExpr"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("str"), SLOP_STR("types_SExpr"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("num"), SLOP_STR("types_SExpr"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("lst"), SLOP_STR("types_SExpr"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("some"), SLOP_STR("Option"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("none"), SLOP_STR("Option"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("ok"), SLOP_STR("Result"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("error"), SLOP_STR("Result"));
}

void transpiler_register_file_module_variants(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_register_enum_variant(ctx, SLOP_STR("read"), SLOP_STR("file_FileMode"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("write"), SLOP_STR("file_FileMode"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("append"), SLOP_STR("file_FileMode"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("read-write"), SLOP_STR("file_FileMode"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("write-read"), SLOP_STR("file_FileMode"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("append-read"), SLOP_STR("file_FileMode"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("not-found"), SLOP_STR("file_FileError"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("permission"), SLOP_STR("file_FileError"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("io-error"), SLOP_STR("file_FileError"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("eof"), SLOP_STR("file_FileError"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("invalid-mode"), SLOP_STR("file_FileError"));
    context_ctx_register_enum_variant(ctx, SLOP_STR("closed"), SLOP_STR("file_FileError"));
    context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("FileMode"), SLOP_STR("file_FileMode"), SLOP_STR("file_FileMode"), 1, 0, 0});
    context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("FileError"), SLOP_STR("file_FileError"), SLOP_STR("file_FileError"), 1, 0, 0});
    context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("File"), SLOP_STR("file_File"), SLOP_STR("file_File"), 0, 1, 0});
}

void transpiler_prescan_const(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
}

void transpiler_register_ffi_function(context_TranspileContext* ctx, types_SExpr* func_decl) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((func_decl != NULL)), "(!= func-decl nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1093 = (*func_decl);
        switch (_mv_1093.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1093.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len >= 1)) {
                        __auto_type _mv_1094 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1094.has_value) {
                            __auto_type name_expr = _mv_1094.value;
                            __auto_type _mv_1095 = (*name_expr);
                            switch (_mv_1095.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_1095.data.sym;
                                    {
                                        __auto_type fn_name = sym.name;
                                        __auto_type c_name = transpiler_extract_ffi_c_name(ctx, items, fn_name);
                                        __auto_type param_types = transpiler_extract_ffi_param_types(ctx, items);
                                        __auto_type ret_type = (((len >= 3)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type ret_expr = _mv.value; context_to_c_type_prefixed(ctx, ret_expr); }) : (SLOP_STR("")); }) : SLOP_STR(""));
                                        __auto_type ret_is_string = string_eq(ret_type, SLOP_STR("slop_string"));
                                        __auto_type empty_type_params = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                                        slop_option_types_SExpr_ptr no_source = (slop_option_types_SExpr_ptr){.has_value = false};
                                        context_ctx_register_func(ctx, (context_FuncEntry){fn_name, c_name, ret_type, SLOP_STR(""), 1, ret_is_string, param_types, 0, empty_type_params, no_source});
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1094.has_value) {
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

slop_list_context_FuncParamType_ptr transpiler_extract_ffi_param_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type result = ((slop_list_context_FuncParamType_ptr){ .data = (context_FuncParamType**)slop_arena_alloc(arena, 16 * sizeof(context_FuncParamType*)), .len = 0, .cap = 16 });
        if ((((int64_t)((items).len)) >= 2)) {
            __auto_type _mv_1096 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1096.has_value) {
                __auto_type params_expr = _mv_1096.value;
                __auto_type _mv_1097 = (*params_expr);
                switch (_mv_1097.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type params_lst = _mv_1097.data.lst;
                        {
                            __auto_type params = params_lst.items;
                            __auto_type param_count = ((int64_t)((params).len));
                            __auto_type i = 0;
                            while ((i < param_count)) {
                                __auto_type _mv_1098 = ({ __auto_type _lst = params; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1098.has_value) {
                                    __auto_type param_expr = _mv_1098.value;
                                    {
                                        __auto_type c_type = transpiler_prescan_get_param_c_type(ctx, param_expr);
                                        __auto_type param_info = ((context_FuncParamType*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 64); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
                                        (*param_info).c_type = c_type;
                                        ({ __auto_type _lst_p = &(result); __auto_type _item = (param_info); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    }
                                } else if (!_mv_1098.has_value) {
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
            } else if (!_mv_1096.has_value) {
            }
        }
        return result;
    }
}

slop_string transpiler_extract_ffi_c_name(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, slop_string fn_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 0;
        __auto_type found_c_name = 0;
        __auto_type c_name = SLOP_STR("");
        while ((i < len)) {
            __auto_type _mv_1099 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1099.has_value) {
                __auto_type item_expr = _mv_1099.value;
                __auto_type _mv_1100 = (*item_expr);
                switch (_mv_1100.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_1100.data.sym;
                        if (string_eq(sym.name, SLOP_STR(":c-name"))) {
                            __auto_type _mv_1101 = ({ __auto_type _lst = items; size_t _idx = (size_t)(i + 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1101.has_value) {
                                __auto_type c_name_expr = _mv_1101.value;
                                __auto_type _mv_1102 = (*c_name_expr);
                                switch (_mv_1102.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type c_sym = _mv_1102.data.sym;
                                        c_name = c_sym.name;
                                        found_c_name = 1;
                                        break;
                                    }
                                    default: {
                                        break;
                                    }
                                }
                            } else if (!_mv_1101.has_value) {
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1099.has_value) {
            }
            i = (i + 1);
        }
        if (found_c_name) {
            return c_name;
        } else {
            return ctype_to_c_name(arena, fn_name);
        }
    }
}

void transpiler_prescan_ffi_struct(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if ((len >= 2)) {
            {
                __auto_type has_header = ((len >= 2) && transpiler_is_ffi_string_item(items, 1));
                __auto_type name_idx = ((((len >= 2) && transpiler_is_ffi_string_item(items, 1))) ? 2 : 1);
                if (has_header) {
                    __auto_type _mv_1103 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1103.has_value) {
                        __auto_type header_expr = _mv_1103.value;
                        __auto_type _mv_1104 = (*header_expr);
                        switch (_mv_1104.tag) {
                            case types_SExpr_str:
                            {
                                __auto_type str = _mv_1104.data.str;
                                context_ctx_add_include(ctx, str.value);
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_1103.has_value) {
                    }
                }
                if ((len >= (name_idx + 1))) {
                    __auto_type _mv_1105 = ({ __auto_type _lst = items; size_t _idx = (size_t)name_idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1105.has_value) {
                        __auto_type name_expr = _mv_1105.value;
                        __auto_type _mv_1106 = (*name_expr);
                        switch (_mv_1106.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1106.data.sym;
                                {
                                    __auto_type type_name = sym.name;
                                    __auto_type c_name = transpiler_get_ffi_struct_c_name(arena, items, name_idx, type_name);
                                    context_ctx_register_type(ctx, (context_TypeEntry){type_name, c_name, c_name, 0, 1, 0});
                                }
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_1105.has_value) {
                    }
                }
            }
        }
    }
}

slop_string transpiler_get_ffi_struct_c_name(slop_arena* arena, slop_list_types_SExpr_ptr items, int64_t name_idx, slop_string default_name) {
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type modifier_idx = (name_idx + 1);
        if ((len >= (modifier_idx + 2))) {
            __auto_type _mv_1107 = ({ __auto_type _lst = items; size_t _idx = (size_t)modifier_idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1107.has_value) {
                __auto_type mod_expr = _mv_1107.value;
                __auto_type _mv_1108 = (*mod_expr);
                switch (_mv_1108.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_1108.data.sym;
                        if (string_eq(sym.name, SLOP_STR(":c-name"))) {
                            __auto_type _mv_1109 = ({ __auto_type _lst = items; size_t _idx = (size_t)(modifier_idx + 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1109.has_value) {
                                __auto_type cname_expr = _mv_1109.value;
                                __auto_type _mv_1110 = (*cname_expr);
                                switch (_mv_1110.tag) {
                                    case types_SExpr_str:
                                    {
                                        __auto_type str = _mv_1110.data.str;
                                        return transpiler_apply_struct_prefix_heuristic(arena, str.value);
                                    }
                                    default: {
                                        return transpiler_apply_struct_prefix_heuristic(arena, default_name);
                                    }
                                }
                            } else if (!_mv_1109.has_value) {
                                return transpiler_apply_struct_prefix_heuristic(arena, default_name);
                            }
                        } else {
                            return transpiler_apply_struct_prefix_heuristic(arena, default_name);
                        }
                    }
                    default: {
                        return transpiler_apply_struct_prefix_heuristic(arena, default_name);
                    }
                }
            } else if (!_mv_1107.has_value) {
                return transpiler_apply_struct_prefix_heuristic(arena, default_name);
            }
        } else {
            return transpiler_apply_struct_prefix_heuristic(arena, default_name);
        }
    }
}

slop_string transpiler_apply_struct_prefix_heuristic(slop_arena* arena, slop_string name) {
    if (transpiler_string_ends_with(name, SLOP_STR("_t"))) {
        return name;
    } else {
        return string_concat(arena, SLOP_STR("struct "), name);
    }
}

uint8_t transpiler_string_ends_with(slop_string s, slop_string suffix) {
    {
        __auto_type s_len = string_len(s);
        __auto_type suf_len = string_len(suffix);
        if ((s_len < suf_len)) {
            return 0;
        } else {
            {
                __auto_type start = (((int64_t)(s_len)) - ((int64_t)(suf_len)));
                __auto_type i = 0;
                __auto_type matches = 1;
                while ((matches && (i < ((int64_t)(suf_len))))) {
                    {
                        __auto_type s_char = s.data[(start + i)];
                        __auto_type suf_char = suffix.data[i];
                        if ((s_char != suf_char)) {
                            matches = 0;
                        }
                    }
                    i = (i + 1);
                }
                return matches;
            }
        }
    }
}

uint8_t transpiler_is_ffi_string_item(slop_list_types_SExpr_ptr items, int64_t idx) {
    __auto_type _mv_1111 = ({ __auto_type _lst = items; size_t _idx = (size_t)idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
    if (_mv_1111.has_value) {
        __auto_type item = _mv_1111.value;
        __auto_type _mv_1112 = (*item);
        switch (_mv_1112.tag) {
            case types_SExpr_str:
            {
                __auto_type _ = _mv_1112.data.str;
                return 1;
            }
            default: {
                return 0;
            }
        }
    } else if (!_mv_1111.has_value) {
        return 0;
    }
}

uint8_t transpiler_is_enum_def(slop_list_types_SExpr_ptr items) {
    if ((((int64_t)((items).len)) < 3)) {
        return 0;
    } else {
        __auto_type _mv_1113 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1113.has_value) {
            __auto_type def_expr = _mv_1113.value;
            __auto_type _mv_1114 = (*def_expr);
            switch (_mv_1114.tag) {
                case types_SExpr_lst:
                {
                    __auto_type def_lst = _mv_1114.data.lst;
                    {
                        __auto_type def_items = def_lst.items;
                        if ((((int64_t)((def_items).len)) < 1)) {
                            return 0;
                        } else {
                            __auto_type _mv_1115 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1115.has_value) {
                                __auto_type head = _mv_1115.value;
                                __auto_type _mv_1116 = (*head);
                                switch (_mv_1116.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1116.data.sym;
                                        return string_eq(sym.name, SLOP_STR("enum"));
                                    }
                                    default: {
                                        return 0;
                                    }
                                }
                            } else if (!_mv_1115.has_value) {
                                return 0;
                            }
                        }
                    }
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_1113.has_value) {
            return 0;
        }
    }
}

uint8_t transpiler_is_record_def(slop_list_types_SExpr_ptr items) {
    if ((((int64_t)((items).len)) < 3)) {
        return 0;
    } else {
        __auto_type _mv_1117 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1117.has_value) {
            __auto_type def_expr = _mv_1117.value;
            __auto_type _mv_1118 = (*def_expr);
            switch (_mv_1118.tag) {
                case types_SExpr_lst:
                {
                    __auto_type def_lst = _mv_1118.data.lst;
                    {
                        __auto_type def_items = def_lst.items;
                        if ((((int64_t)((def_items).len)) < 1)) {
                            return 0;
                        } else {
                            __auto_type _mv_1119 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1119.has_value) {
                                __auto_type head = _mv_1119.value;
                                __auto_type _mv_1120 = (*head);
                                switch (_mv_1120.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1120.data.sym;
                                        return string_eq(sym.name, SLOP_STR("record"));
                                    }
                                    default: {
                                        return 0;
                                    }
                                }
                            } else if (!_mv_1119.has_value) {
                                return 0;
                            }
                        }
                    }
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_1117.has_value) {
            return 0;
        }
    }
}

uint8_t transpiler_is_union_def(slop_list_types_SExpr_ptr items) {
    if ((((int64_t)((items).len)) < 3)) {
        return 0;
    } else {
        __auto_type _mv_1121 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1121.has_value) {
            __auto_type def_expr = _mv_1121.value;
            __auto_type _mv_1122 = (*def_expr);
            switch (_mv_1122.tag) {
                case types_SExpr_lst:
                {
                    __auto_type def_lst = _mv_1122.data.lst;
                    {
                        __auto_type def_items = def_lst.items;
                        if ((((int64_t)((def_items).len)) < 1)) {
                            return 0;
                        } else {
                            __auto_type _mv_1123 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1123.has_value) {
                                __auto_type head = _mv_1123.value;
                                __auto_type _mv_1124 = (*head);
                                switch (_mv_1124.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1124.data.sym;
                                        return string_eq(sym.name, SLOP_STR("union"));
                                    }
                                    default: {
                                        return 0;
                                    }
                                }
                            } else if (!_mv_1123.has_value) {
                                return 0;
                            }
                        }
                    }
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_1121.has_value) {
            return 0;
        }
    }
}

slop_string transpiler_get_array_c_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, slop_string default_c_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if ((((int64_t)((items).len)) < 3)) {
        return default_c_type;
    } else {
        __auto_type _mv_1125 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1125.has_value) {
            __auto_type body_expr = _mv_1125.value;
            __auto_type _mv_1126 = (*body_expr);
            switch (_mv_1126.tag) {
                case types_SExpr_lst:
                {
                    __auto_type body_lst = _mv_1126.data.lst;
                    {
                        __auto_type body_items = body_lst.items;
                        if ((((int64_t)((body_items).len)) < 2)) {
                            return default_c_type;
                        } else {
                            __auto_type _mv_1127 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1127.has_value) {
                                __auto_type head = _mv_1127.value;
                                __auto_type _mv_1128 = (*head);
                                switch (_mv_1128.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1128.data.sym;
                                        if (string_eq(sym.name, SLOP_STR("Array"))) {
                                            __auto_type _mv_1129 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1129.has_value) {
                                                __auto_type elem_expr = _mv_1129.value;
                                                {
                                                    __auto_type elem_c = context_to_c_type_prefixed(ctx, elem_expr);
                                                    return context_ctx_str(ctx, elem_c, SLOP_STR("*"));
                                                }
                                            } else if (!_mv_1129.has_value) {
                                                return default_c_type;
                                            }
                                        } else {
                                            return default_c_type;
                                        }
                                    }
                                    default: {
                                        return default_c_type;
                                    }
                                }
                            } else if (!_mv_1127.has_value) {
                                return default_c_type;
                            }
                        }
                    }
                }
                default: {
                    return default_c_type;
                }
            }
        } else if (!_mv_1125.has_value) {
            return default_c_type;
        }
    }
}

void transpiler_process_imports(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
}

void transpiler_process_exports(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
}

void transpiler_emit_all_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1130 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1130.has_value) {
                __auto_type item = _mv_1130.value;
                if ((transpiler_is_type_def(item) && !(transpiler_is_union_type_def(item)))) {
                    defn_transpile_type(ctx, item);
                }
            } else if (!_mv_1130.has_value) {
            }
            i = (i + 1);
        }
    }
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1131 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1131.has_value) {
                __auto_type item = _mv_1131.value;
                if ((transpiler_is_type_def(item) && transpiler_is_union_type_def(item))) {
                    defn_transpile_type(ctx, item);
                }
            } else if (!_mv_1131.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t transpiler_is_union_type_def(types_SExpr* item) {
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1132 = (*item);
    switch (_mv_1132.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1132.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 3)) {
                    return 0;
                } else {
                    __auto_type _mv_1133 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1133.has_value) {
                        __auto_type def_expr = _mv_1133.value;
                        __auto_type _mv_1134 = (*def_expr);
                        switch (_mv_1134.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type def_lst = _mv_1134.data.lst;
                                {
                                    __auto_type def_items = def_lst.items;
                                    if ((((int64_t)((def_items).len)) < 1)) {
                                        return 0;
                                    } else {
                                        __auto_type _mv_1135 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1135.has_value) {
                                            __auto_type head = _mv_1135.value;
                                            __auto_type _mv_1136 = (*head);
                                            switch (_mv_1136.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type sym = _mv_1136.data.sym;
                                                    return string_eq(sym.name, SLOP_STR("union"));
                                                }
                                                default: {
                                                    return 0;
                                                }
                                            }
                                        } else if (!_mv_1135.has_value) {
                                            return 0;
                                        }
                                    }
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1133.has_value) {
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

uint8_t transpiler_is_type_def(types_SExpr* item) {
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1137 = (*item);
    switch (_mv_1137.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1137.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_1138 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1138.has_value) {
                        __auto_type head = _mv_1138.value;
                        __auto_type _mv_1139 = (*head);
                        switch (_mv_1139.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1139.data.sym;
                                return string_eq(sym.name, SLOP_STR("type"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1138.has_value) {
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

void transpiler_emit_all_functions(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1140 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1140.has_value) {
                __auto_type item = _mv_1140.value;
                if (transpiler_is_fn_def(item)) {
                    defn_transpile_function(ctx, item);
                }
            } else if (!_mv_1140.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t transpiler_is_fn_def(types_SExpr* item) {
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1141 = (*item);
    switch (_mv_1141.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1141.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_1142 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1142.has_value) {
                        __auto_type head = _mv_1142.value;
                        __auto_type _mv_1143 = (*head);
                        switch (_mv_1143.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1143.data.sym;
                                return string_eq(sym.name, SLOP_STR("fn"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1142.has_value) {
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

void transpiler_transpile_module(context_TranspileContext* ctx, types_SExpr* module_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((module_expr != NULL)), "(!= module-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1144 = (*module_expr);
        switch (_mv_1144.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1144.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len >= 2)) {
                        __auto_type _mv_1145 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1145.has_value) {
                            __auto_type name_expr = _mv_1145.value;
                            __auto_type _mv_1146 = (*name_expr);
                            switch (_mv_1146.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_1146.data.sym;
                                    context_ctx_set_module(ctx, (slop_option_string){.has_value = 1, .value = sym.name});
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1145.has_value) {
                        }
                        {
                            __auto_type body_start = transpiler_get_body_start(items);
                            __auto_type exports = transpiler_get_export_names(arena, items);
                            transpiler_prescan_module_body(ctx, items, body_start);
                            transpiler_emit_header_guard_open(ctx);
                            transpiler_emit_header_standard_includes(ctx);
                            transpiler_emit_header_dependency_includes(ctx);
                            transpiler_emit_ffi_includes_header(ctx);
                            context_ctx_emit_header(ctx, SLOP_STR(""));
                            transpiler_emit_forward_decls_header(ctx, items, body_start);
                            transpiler_emit_simple_enums_header(ctx, items, body_start);
                            transpiler_emit_inline_records_header(ctx);
                            transpiler_emit_list_types_header(ctx);
                            transpiler_emit_option_types_header(ctx);
                            transpiler_emit_chan_types_header(ctx);
                            transpiler_emit_thread_types_header(ctx);
                            transpiler_emit_simple_type_aliases_header(ctx, items, body_start);
                            transpiler_emit_primitive_list_types_header(ctx);
                            transpiler_emit_primitive_option_types_header(ctx);
                            transpiler_emit_imported_list_types_header(ctx);
                            transpiler_emit_imported_option_types_header(ctx);
                            transpiler_emit_value_list_types_header(ctx);
                            transpiler_emit_struct_union_types_sorted(ctx, items, body_start);
                            transpiler_emit_complex_value_list_types_header(ctx);
                            transpiler_emit_struct_key_types_header(ctx);
                            transpiler_emit_result_types_header(ctx);
                            transpiler_emit_type_aliases_header(ctx, items, body_start);
                            transpiler_emit_chan_funcs_header(ctx);
                            transpiler_emit_fn_forward_decls_header(ctx, items, body_start);
                            transpiler_emit_c_name_aliases(ctx);
                            transpiler_emit_module_consts_header(ctx, items, body_start, exports);
                            transpiler_emit_module_consts(ctx, items, body_start, exports);
                            transpiler_emit_fn_forward_decls(ctx, items, body_start);
                            transpiler_emit_module_functions(ctx, items, body_start);
                            transpiler_emit_late_registered_option_types_header(ctx);
                            transpiler_emit_header_guard_close(ctx);
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_emit(ctx, SLOP_STR("/* invalid module */"));
                break;
            }
        }
    }
}

int64_t transpiler_get_body_start(slop_list_types_SExpr_ptr items) {
    if ((((int64_t)((items).len)) < 3)) {
        return 2;
    } else {
        __auto_type _mv_1147 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1147.has_value) {
            __auto_type third = _mv_1147.value;
            __auto_type _mv_1148 = (*third);
            switch (_mv_1148.tag) {
                case types_SExpr_lst:
                {
                    __auto_type lst = _mv_1148.data.lst;
                    {
                        __auto_type sub_items = lst.items;
                        if ((((int64_t)((sub_items).len)) < 1)) {
                            return 2;
                        } else {
                            __auto_type _mv_1149 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1149.has_value) {
                                __auto_type head = _mv_1149.value;
                                __auto_type _mv_1150 = (*head);
                                switch (_mv_1150.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1150.data.sym;
                                        if (string_eq(sym.name, SLOP_STR("export"))) {
                                            return 3;
                                        } else {
                                            return 2;
                                        }
                                    }
                                    default: {
                                        return 2;
                                    }
                                }
                            } else if (!_mv_1149.has_value) {
                                return 2;
                            }
                        }
                    }
                }
                default: {
                    return 2;
                }
            }
        } else if (!_mv_1147.has_value) {
            return 2;
        }
    }
}

slop_list_string transpiler_get_export_names(slop_arena* arena, slop_list_types_SExpr_ptr items) {
    {
        __auto_type result = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 2;
        while ((i < len)) {
            __auto_type _mv_1151 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1151.has_value) {
                __auto_type item = _mv_1151.value;
                __auto_type _mv_1152 = (*item);
                switch (_mv_1152.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type lst = _mv_1152.data.lst;
                        {
                            __auto_type sub_items = lst.items;
                            if ((((int64_t)((sub_items).len)) >= 1)) {
                                __auto_type _mv_1153 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1153.has_value) {
                                    __auto_type head = _mv_1153.value;
                                    __auto_type _mv_1154 = (*head);
                                    switch (_mv_1154.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_1154.data.sym;
                                            if (string_eq(sym.name, SLOP_STR("export"))) {
                                                {
                                                    __auto_type export_len = ((int64_t)((sub_items).len));
                                                    __auto_type j = 1;
                                                    while ((j < export_len)) {
                                                        __auto_type _mv_1155 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)j; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                        if (_mv_1155.has_value) {
                                                            __auto_type name_expr = _mv_1155.value;
                                                            __auto_type _mv_1156 = (*name_expr);
                                                            switch (_mv_1156.tag) {
                                                                case types_SExpr_sym:
                                                                {
                                                                    __auto_type name_sym = _mv_1156.data.sym;
                                                                    ({ __auto_type _lst_p = &(result); __auto_type _item = (name_sym.name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                                    break;
                                                                }
                                                                default: {
                                                                    break;
                                                                }
                                                            }
                                                        } else if (!_mv_1155.has_value) {
                                                        }
                                                        j = (j + 1);
                                                    }
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_1153.has_value) {
                                }
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
            i = (i + 1);
        }
        return result;
    }
}

uint8_t transpiler_list_contains_str(slop_list_string lst, slop_string needle) {
    {
        __auto_type len = ((int64_t)((lst).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_1157 = ({ __auto_type _lst = lst; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1157.has_value) {
                __auto_type s = _mv_1157.value;
                if (string_eq(s, needle)) {
                    found = 1;
                }
            } else if (!_mv_1157.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

void transpiler_prescan_module_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        while ((i < len)) {
            __auto_type _mv_1158 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1158.has_value) {
                __auto_type item = _mv_1158.value;
                transpiler_prescan_top_level(ctx, item);
            } else if (!_mv_1158.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_scan_type_for_generics(context_TranspileContext* ctx, types_SExpr* type_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1159 = (*type_expr);
        switch (_mv_1159.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1159.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len >= 1)) {
                        __auto_type _mv_1160 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1160.has_value) {
                            __auto_type head = _mv_1160.value;
                            __auto_type _mv_1161 = (*head);
                            switch (_mv_1161.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_1161.data.sym;
                                    {
                                        __auto_type op = sym.name;
                                        if (string_eq(op, SLOP_STR("Option"))) {
                                            if ((len >= 2)) {
                                                __auto_type _mv_1162 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1162.has_value) {
                                                    __auto_type inner = _mv_1162.value;
                                                    {
                                                        __auto_type inner_c = context_to_c_type_prefixed(ctx, inner);
                                                        __auto_type inner_id = ctype_type_to_identifier(arena, inner_c);
                                                        __auto_type c_name = context_ctx_str(ctx, SLOP_STR("slop_option_"), inner_id);
                                                        context_ctx_register_option_type(ctx, inner_c, c_name);
                                                        transpiler_scan_type_for_generics(ctx, inner);
                                                    }
                                                } else if (!_mv_1162.has_value) {
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("List"))) {
                                            if ((len >= 2)) {
                                                __auto_type _mv_1163 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1163.has_value) {
                                                    __auto_type elem = _mv_1163.value;
                                                    {
                                                        __auto_type elem_c = context_to_c_type_prefixed(ctx, elem);
                                                        __auto_type elem_id = ctype_type_to_identifier(arena, elem_c);
                                                        __auto_type c_name = context_ctx_str(ctx, SLOP_STR("slop_list_"), elem_id);
                                                        __auto_type option_c_name = context_ctx_str(ctx, SLOP_STR("slop_option_"), elem_id);
                                                        context_ctx_register_list_type(ctx, elem_c, c_name);
                                                        context_ctx_register_option_type(ctx, elem_c, option_c_name);
                                                        transpiler_scan_type_for_generics(ctx, elem);
                                                    }
                                                } else if (!_mv_1163.has_value) {
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("Ptr"))) {
                                            if ((len >= 2)) {
                                                __auto_type _mv_1164 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1164.has_value) {
                                                    __auto_type inner = _mv_1164.value;
                                                    transpiler_scan_type_for_generics(ctx, inner);
                                                } else if (!_mv_1164.has_value) {
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("Result"))) {
                                            if ((len >= 3)) {
                                                __auto_type _mv_1165 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1165.has_value) {
                                                    __auto_type ok_type = _mv_1165.value;
                                                    __auto_type _mv_1166 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_1166.has_value) {
                                                        __auto_type err_type = _mv_1166.value;
                                                        {
                                                            __auto_type ok_c = context_to_c_type_prefixed(ctx, ok_type);
                                                            __auto_type err_c = context_to_c_type_prefixed(ctx, err_type);
                                                            __auto_type ok_id = ctype_type_to_identifier(arena, ok_c);
                                                            __auto_type err_id = ctype_type_to_identifier(arena, err_c);
                                                            __auto_type c_name = context_ctx_str5(ctx, SLOP_STR("slop_result_"), ok_id, SLOP_STR("_"), err_id, SLOP_STR(""));
                                                            context_ctx_register_result_type(ctx, ok_c, err_c, c_name);
                                                            transpiler_scan_type_for_generics(ctx, ok_type);
                                                            transpiler_scan_type_for_generics(ctx, err_type);
                                                        }
                                                    } else if (!_mv_1166.has_value) {
                                                    }
                                                } else if (!_mv_1165.has_value) {
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("Chan"))) {
                                            if ((len >= 2)) {
                                                __auto_type _mv_1167 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1167.has_value) {
                                                    __auto_type elem = _mv_1167.value;
                                                    {
                                                        __auto_type elem_c = context_to_c_type_prefixed(ctx, elem);
                                                        __auto_type elem_id = ctype_type_to_identifier(arena, elem_c);
                                                        __auto_type c_name = context_ctx_str(ctx, SLOP_STR("slop_chan_"), elem_id);
                                                        context_ctx_register_chan_type(ctx, elem_c, c_name);
                                                        transpiler_scan_type_for_generics(ctx, elem);
                                                    }
                                                } else if (!_mv_1167.has_value) {
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("Thread"))) {
                                            if ((len >= 2)) {
                                                __auto_type _mv_1168 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1168.has_value) {
                                                    __auto_type result = _mv_1168.value;
                                                    {
                                                        __auto_type result_c = context_to_c_type_prefixed(ctx, result);
                                                        {
                                                            __auto_type actual_c = ((string_eq(result_c, SLOP_STR("void"))) ? SLOP_STR("int64_t") : result_c);
                                                            __auto_type result_id = ctype_type_to_identifier(arena, actual_c);
                                                            __auto_type c_name = context_ctx_str(ctx, SLOP_STR("slop_thread_"), result_id);
                                                            context_ctx_register_thread_type(ctx, actual_c, c_name);
                                                            transpiler_scan_type_for_generics(ctx, result);
                                                        }
                                                    }
                                                } else if (!_mv_1168.has_value) {
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("Map"))) {
                                            if ((len >= 3)) {
                                                __auto_type _mv_1169 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1169.has_value) {
                                                    __auto_type key_type = _mv_1169.value;
                                                    {
                                                        __auto_type key_c = context_to_c_type_prefixed(ctx, key_type);
                                                        __auto_type key_id = ctype_type_to_identifier(arena, key_c);
                                                        __auto_type list_c_name = context_ctx_str(ctx, SLOP_STR("slop_list_"), key_id);
                                                        __auto_type option_c_name = context_ctx_str(ctx, SLOP_STR("slop_option_"), key_id);
                                                        context_ctx_register_list_type(ctx, key_c, list_c_name);
                                                        context_ctx_register_option_type(ctx, key_c, option_c_name);
                                                        transpiler_scan_type_for_generics(ctx, key_type);
                                                        __auto_type _mv_1170 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                        if (_mv_1170.has_value) {
                                                            __auto_type val_type = _mv_1170.value;
                                                            transpiler_scan_type_for_generics(ctx, val_type);
                                                        } else if (!_mv_1170.has_value) {
                                                        }
                                                    }
                                                } else if (!_mv_1169.has_value) {
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("Set"))) {
                                            if ((len >= 2)) {
                                                __auto_type _mv_1171 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1171.has_value) {
                                                    __auto_type elem_type = _mv_1171.value;
                                                    {
                                                        __auto_type elem_c = context_to_c_type_prefixed(ctx, elem_type);
                                                        __auto_type elem_id = ctype_type_to_identifier(arena, elem_c);
                                                        __auto_type list_c_name = context_ctx_str(ctx, SLOP_STR("slop_list_"), elem_id);
                                                        __auto_type option_c_name = context_ctx_str(ctx, SLOP_STR("slop_option_"), elem_id);
                                                        context_ctx_register_list_type(ctx, elem_c, list_c_name);
                                                        context_ctx_register_option_type(ctx, elem_c, option_c_name);
                                                        transpiler_scan_type_for_generics(ctx, elem_type);
                                                    }
                                                } else if (!_mv_1171.has_value) {
                                                }
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
                        } else if (!_mv_1160.has_value) {
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

void transpiler_scan_record_fields_for_generics(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 1;
        while ((i < len)) {
            __auto_type _mv_1172 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1172.has_value) {
                __auto_type field_expr = _mv_1172.value;
                __auto_type _mv_1173 = (*field_expr);
                switch (_mv_1173.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type field_lst = _mv_1173.data.lst;
                        {
                            __auto_type field_items = field_lst.items;
                            if ((((int64_t)((field_items).len)) >= 2)) {
                                __auto_type _mv_1174 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1174.has_value) {
                                    __auto_type type_expr = _mv_1174.value;
                                    transpiler_scan_type_for_generics(ctx, type_expr);
                                } else if (!_mv_1174.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1172.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_ffi_includes(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type includes = context_ctx_get_includes(ctx);
        __auto_type len = ((int64_t)((includes).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1175 = ({ __auto_type _lst = includes; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1175.has_value) {
                __auto_type header = _mv_1175.value;
                emit_emit_include(ctx, header, 1);
            } else if (!_mv_1175.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_ffi_includes_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type includes = context_ctx_get_includes(ctx);
        __auto_type len = ((int64_t)((includes).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1176 = ({ __auto_type _lst = includes; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1176.has_value) {
                __auto_type header = _mv_1176.value;
                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("#include <"), header, SLOP_STR(">")));
            } else if (!_mv_1176.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_header_guard_open(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1177 = context_ctx_get_module(ctx);
        if (_mv_1177.has_value) {
            __auto_type mod_name = _mv_1177.value;
            {
                __auto_type c_name = ctype_to_c_name(arena, mod_name);
                __auto_type guard = context_ctx_str3(ctx, SLOP_STR("SLOP_"), c_name, SLOP_STR("_H"));
                context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), guard));
                context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), guard));
                context_ctx_emit_header(ctx, SLOP_STR(""));
            }
        } else if (!_mv_1177.has_value) {
        }
    }
}

void transpiler_emit_header_guard_close(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit_header(ctx, SLOP_STR(""));
    context_ctx_emit_header(ctx, SLOP_STR("#endif"));
}

void transpiler_emit_header_standard_includes(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit_header(ctx, SLOP_STR("#include \"slop_runtime.h\""));
    context_ctx_emit_header(ctx, SLOP_STR("#include <stdint.h>"));
    context_ctx_emit_header(ctx, SLOP_STR("#include <stdbool.h>"));
}

void transpiler_emit_header_dependency_includes(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type imports = context_ctx_get_imports(ctx);
        __auto_type len = ((int64_t)((imports).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1178 = ({ __auto_type _lst = imports; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1178.has_value) {
                __auto_type mod_name = _mv_1178.value;
                {
                    __auto_type c_name = ctype_to_c_name(arena, mod_name);
                    context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("#include \"slop_"), c_name, SLOP_STR(".h\"")));
                }
            } else if (!_mv_1178.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_forward_decls(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        __auto_type emitted_any = 0;
        while ((i < len)) {
            __auto_type _mv_1179 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1179.has_value) {
                __auto_type item = _mv_1179.value;
                if ((transpiler_is_type_def(item) && transpiler_is_struct_type_def(item))) {
                    __auto_type _mv_1180 = transpiler_get_type_name(item);
                    if (_mv_1180.has_value) {
                        __auto_type type_name = _mv_1180.value;
                        {
                            __auto_type c_name = ctype_to_c_name(arena, type_name);
                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("typedef struct "), c_name, context_ctx_str(ctx, SLOP_STR(" "), context_ctx_str(ctx, c_name, SLOP_STR(";")))));
                            emitted_any = 1;
                        }
                    } else if (!_mv_1180.has_value) {
                    }
                }
            } else if (!_mv_1179.has_value) {
            }
            i = (i + 1);
        }
        if (emitted_any) {
            context_ctx_emit(ctx, SLOP_STR(""));
        }
    }
}

uint8_t transpiler_is_struct_type_def(types_SExpr* item) {
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1181 = (*item);
    switch (_mv_1181.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1181.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 3)) {
                    return 0;
                } else {
                    __auto_type _mv_1182 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1182.has_value) {
                        __auto_type def_expr = _mv_1182.value;
                        __auto_type _mv_1183 = (*def_expr);
                        switch (_mv_1183.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type def_lst = _mv_1183.data.lst;
                                {
                                    __auto_type def_items = def_lst.items;
                                    if ((((int64_t)((def_items).len)) < 1)) {
                                        return 0;
                                    } else {
                                        __auto_type _mv_1184 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1184.has_value) {
                                            __auto_type head = _mv_1184.value;
                                            __auto_type _mv_1185 = (*head);
                                            switch (_mv_1185.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type sym = _mv_1185.data.sym;
                                                    {
                                                        __auto_type kind = sym.name;
                                                        return ((string_eq(kind, SLOP_STR("record"))) || (string_eq(kind, SLOP_STR("union"))) || ((string_eq(kind, SLOP_STR("enum")) && transpiler_has_enum_payload_variants(def_items))));
                                                    }
                                                }
                                                default: {
                                                    return 0;
                                                }
                                            }
                                        } else if (!_mv_1184.has_value) {
                                            return 0;
                                        }
                                    }
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1182.has_value) {
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

uint8_t transpiler_has_enum_payload_variants(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 1;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_1186 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1186.has_value) {
                __auto_type item = _mv_1186.value;
                __auto_type _mv_1187 = (*item);
                switch (_mv_1187.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type _ = _mv_1187.data.lst;
                        found = 1;
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1186.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

uint8_t transpiler_is_type_alias_def(types_SExpr* item) {
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1188 = (*item);
    switch (_mv_1188.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1188.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 3)) {
                    return 0;
                } else {
                    __auto_type _mv_1189 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1189.has_value) {
                        __auto_type def_expr = _mv_1189.value;
                        __auto_type _mv_1190 = (*def_expr);
                        switch (_mv_1190.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type _ = _mv_1190.data.sym;
                                return 1;
                            }
                            case types_SExpr_lst:
                            {
                                __auto_type def_lst = _mv_1190.data.lst;
                                {
                                    __auto_type def_items = def_lst.items;
                                    if ((((int64_t)((def_items).len)) < 1)) {
                                        return 0;
                                    } else {
                                        __auto_type _mv_1191 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1191.has_value) {
                                            __auto_type head = _mv_1191.value;
                                            __auto_type _mv_1192 = (*head);
                                            switch (_mv_1192.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type sym = _mv_1192.data.sym;
                                                    {
                                                        __auto_type kind = sym.name;
                                                        return ((!(string_eq(kind, SLOP_STR("record")))) && (!(string_eq(kind, SLOP_STR("enum")))) && (!(string_eq(kind, SLOP_STR("union")))));
                                                    }
                                                }
                                                default: {
                                                    return 0;
                                                }
                                            }
                                        } else if (!_mv_1191.has_value) {
                                            return 0;
                                        }
                                    }
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1189.has_value) {
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

uint8_t transpiler_is_result_type_alias_def(types_SExpr* item) {
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1193 = (*item);
    switch (_mv_1193.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1193.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 3)) {
                    return 0;
                } else {
                    __auto_type _mv_1194 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1194.has_value) {
                        __auto_type def_expr = _mv_1194.value;
                        __auto_type _mv_1195 = (*def_expr);
                        switch (_mv_1195.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type def_lst = _mv_1195.data.lst;
                                {
                                    __auto_type def_items = def_lst.items;
                                    if ((((int64_t)((def_items).len)) < 1)) {
                                        return 0;
                                    } else {
                                        __auto_type _mv_1196 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1196.has_value) {
                                            __auto_type head = _mv_1196.value;
                                            __auto_type _mv_1197 = (*head);
                                            switch (_mv_1197.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type sym = _mv_1197.data.sym;
                                                    return string_eq(sym.name, SLOP_STR("Result"));
                                                }
                                                default: {
                                                    return 0;
                                                }
                                            }
                                        } else if (!_mv_1196.has_value) {
                                            return 0;
                                        }
                                    }
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1194.has_value) {
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

void transpiler_emit_type_alias_to_header(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1198 = (*type_def);
        switch (_mv_1198.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1198.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 3)) {
                        __auto_type _mv_1199 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1199.has_value) {
                            __auto_type name_expr = _mv_1199.value;
                            __auto_type _mv_1200 = (*name_expr);
                            switch (_mv_1200.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_1200.data.sym;
                                    {
                                        __auto_type type_name = name_sym.name;
                                        __auto_type base_c_name = ctype_to_c_name(arena, type_name);
                                        __auto_type c_name = context_ctx_prefix_type(ctx, base_c_name);
                                        __auto_type _mv_1201 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1201.has_value) {
                                            __auto_type body_expr = _mv_1201.value;
                                            if (transpiler_is_array_type_body(body_expr)) {
                                                transpiler_emit_array_typedef_to_header(ctx, c_name, body_expr);
                                            } else if (transpiler_is_range_type_body(body_expr)) {
                                                transpiler_emit_range_typedef_to_header(ctx, type_name, c_name, body_expr);
                                            } else {
                                                {
                                                    __auto_type c_type = context_to_c_type_prefixed(ctx, body_expr);
                                                    context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("typedef "), c_type, SLOP_STR(" "), c_name, SLOP_STR(";")));
                                                    context_ctx_emit_header(ctx, SLOP_STR(""));
                                                    context_ctx_mark_type_emitted(ctx, c_name);
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

uint8_t transpiler_is_array_type_body(types_SExpr* body_expr) {
    SLOP_PRE(((body_expr != NULL)), "(!= body-expr nil)");
    __auto_type _mv_1202 = (*body_expr);
    switch (_mv_1202.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1202.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_1203 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1203.has_value) {
                        __auto_type head = _mv_1203.value;
                        __auto_type _mv_1204 = (*head);
                        switch (_mv_1204.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1204.data.sym;
                                return string_eq(sym.name, SLOP_STR("Array"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1203.has_value) {
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

void transpiler_emit_array_typedef_to_header(context_TranspileContext* ctx, slop_string c_name, types_SExpr* body_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((body_expr != NULL)), "(!= body-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1205 = (*body_expr);
        switch (_mv_1205.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1205.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 3)) {
                        context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("typedef void* "), c_name, SLOP_STR(";")));
                    } else {
                        __auto_type _mv_1206 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1206.has_value) {
                            __auto_type elem_type_expr = _mv_1206.value;
                            __auto_type _mv_1207 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1207.has_value) {
                                __auto_type size_expr = _mv_1207.value;
                                {
                                    __auto_type elem_c_type = context_to_c_type_prefixed(ctx, elem_type_expr);
                                    __auto_type size_str = transpiler_get_array_size_string(size_expr);
                                    context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("typedef "), elem_c_type, SLOP_STR(" "), c_name, context_ctx_str3(ctx, SLOP_STR("["), size_str, SLOP_STR("];"))));
                                    context_ctx_emit_header(ctx, SLOP_STR(""));
                                }
                            } else if (!_mv_1207.has_value) {
                                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("typedef void* "), c_name, SLOP_STR(";")));
                            }
                        } else if (!_mv_1206.has_value) {
                            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("typedef void* "), c_name, SLOP_STR(";")));
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("typedef void* "), c_name, SLOP_STR(";")));
                break;
            }
        }
    }
}

slop_string transpiler_get_array_size_string(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_1208 = (*expr);
    switch (_mv_1208.tag) {
        case types_SExpr_num:
        {
            __auto_type num = _mv_1208.data.num;
            return num.raw;
        }
        default: {
            return SLOP_STR("0");
        }
    }
}

uint8_t transpiler_is_range_type_body(types_SExpr* body_expr) {
    SLOP_PRE(((body_expr != NULL)), "(!= body-expr nil)");
    __auto_type _mv_1209 = (*body_expr);
    switch (_mv_1209.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1209.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type found_dots = 0;
                __auto_type i = 0;
                while (((i < len) && !(found_dots))) {
                    __auto_type _mv_1210 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1210.has_value) {
                        __auto_type item = _mv_1210.value;
                        __auto_type _mv_1211 = (*item);
                        switch (_mv_1211.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1211.data.sym;
                                if (string_eq(sym.name, SLOP_STR(".."))) {
                                    found_dots = 1;
                                }
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_1210.has_value) {
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

transpiler_RangeBoundsHeader transpiler_parse_range_bounds_header(types_SExpr* body_expr) {
    SLOP_PRE(((body_expr != NULL)), "(!= body-expr nil)");
    {
        __auto_type min_val = 0;
        __auto_type max_val = 0;
        __auto_type has_min = 0;
        __auto_type has_max = 0;
        __auto_type found_dots = 0;
        __auto_type _mv_1212 = (*body_expr);
        switch (_mv_1212.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1212.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    __auto_type i = 1;
                    while ((i < len)) {
                        __auto_type _mv_1213 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1213.has_value) {
                            __auto_type item = _mv_1213.value;
                            __auto_type _mv_1214 = (*item);
                            switch (_mv_1214.tag) {
                                case types_SExpr_num:
                                {
                                    __auto_type num = _mv_1214.data.num;
                                    if (!(found_dots)) {
                                        min_val = transpiler_string_to_int_header(num.raw);
                                        has_min = 1;
                                    } else {
                                        max_val = transpiler_string_to_int_header(num.raw);
                                        has_max = 1;
                                    }
                                    break;
                                }
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_1214.data.sym;
                                    if (string_eq(sym.name, SLOP_STR(".."))) {
                                        found_dots = 1;
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1213.has_value) {
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
        return (transpiler_RangeBoundsHeader){min_val, max_val, has_min, has_max};
    }
}

int64_t transpiler_string_to_int_header(slop_string s) {
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

slop_string transpiler_select_smallest_c_type_header(int64_t min_val, int64_t max_val, uint8_t has_min, uint8_t has_max) {
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

void transpiler_emit_range_typedef_to_header(context_TranspileContext* ctx, slop_string raw_name, slop_string c_name, types_SExpr* body_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((body_expr != NULL)), "(!= body-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        transpiler_RangeBoundsHeader bounds = transpiler_parse_range_bounds_header(body_expr);
        int64_t min_val = bounds.min;
        int64_t max_val = bounds.max;
        uint8_t has_min = bounds.has_min;
        uint8_t has_max = bounds.has_max;
        __auto_type c_type = transpiler_select_smallest_c_type_header(min_val, max_val, has_min, has_max);
        context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("typedef "), c_type, SLOP_STR(" "), c_name, SLOP_STR(";")));
        context_ctx_emit_header(ctx, SLOP_STR(""));
        context_ctx_mark_type_emitted(ctx, c_name);
        context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("static inline "), c_name, SLOP_STR(" "), c_name, SLOP_STR("_new(int64_t v) {")));
        context_ctx_indent(ctx);
        if ((has_min && has_max)) {
            {
                __auto_type min_str = int_to_string(arena, min_val);
                __auto_type max_str = int_to_string(arena, max_val);
                context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("SLOP_PRE(v >= "), context_ctx_str(ctx, min_str, context_ctx_str(ctx, SLOP_STR(" && v <= "), context_ctx_str(ctx, max_str, context_ctx_str(ctx, SLOP_STR(", \""), context_ctx_str(ctx, c_name, context_ctx_str(ctx, SLOP_STR(" in range "), context_ctx_str(ctx, min_str, context_ctx_str(ctx, SLOP_STR(".."), context_ctx_str(ctx, max_str, SLOP_STR("\");"))))))))))));
            }
        } else if (has_min) {
            {
                __auto_type min_str = int_to_string(arena, min_val);
                context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("SLOP_PRE(v >= "), context_ctx_str(ctx, min_str, context_ctx_str(ctx, SLOP_STR(", \""), context_ctx_str(ctx, c_name, context_ctx_str(ctx, SLOP_STR(" >= "), context_ctx_str(ctx, min_str, SLOP_STR("\");"))))))));
            }
        } else if (has_max) {
            {
                __auto_type max_str = int_to_string(arena, max_val);
                context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("SLOP_PRE(v <= "), context_ctx_str(ctx, max_str, context_ctx_str(ctx, SLOP_STR(", \""), context_ctx_str(ctx, c_name, context_ctx_str(ctx, SLOP_STR(" <= "), context_ctx_str(ctx, max_str, SLOP_STR("\");"))))))));
            }
        } else {
        }
        context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("return ("), context_ctx_str(ctx, c_name, SLOP_STR(")v;"))));
        context_ctx_dedent(ctx);
        context_ctx_emit_header(ctx, SLOP_STR("}"));
        context_ctx_emit_header(ctx, SLOP_STR(""));
        context_ctx_register_type_alias(ctx, raw_name, parser_pretty_print(arena, body_expr));
    }
}

void transpiler_emit_forward_decls_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        __auto_type emitted_any = 0;
        while ((i < len)) {
            __auto_type _mv_1215 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1215.has_value) {
                __auto_type item = _mv_1215.value;
                if ((transpiler_is_type_def(item) && transpiler_is_struct_type_def(item))) {
                    __auto_type _mv_1216 = transpiler_get_type_name(item);
                    if (_mv_1216.has_value) {
                        __auto_type type_name = _mv_1216.value;
                        {
                            __auto_type base_name = ctype_to_c_name(arena, type_name);
                            __auto_type c_name = ((context_ctx_prefixing_enabled(ctx)) ? ({ __auto_type _mv = context_ctx_get_module(ctx); _mv.has_value ? ({ __auto_type mod_name = _mv.value; context_ctx_str(ctx, ctype_to_c_name(arena, mod_name), context_ctx_str(ctx, SLOP_STR("_"), base_name)); }) : (base_name); }) : base_name);
                            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("typedef struct "), c_name, context_ctx_str(ctx, SLOP_STR(" "), context_ctx_str(ctx, c_name, SLOP_STR(";")))));
                            emitted_any = 1;
                        }
                    } else if (!_mv_1216.has_value) {
                    }
                }
            } else if (!_mv_1215.has_value) {
            }
            i = (i + 1);
        }
        if (emitted_any) {
            context_ctx_emit_header(ctx, SLOP_STR(""));
        }
    }
}

void transpiler_emit_fn_forward_decls(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        __auto_type emitted_any = 0;
        while ((i < len)) {
            __auto_type _mv_1217 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1217.has_value) {
                __auto_type item = _mv_1217.value;
                if (transpiler_is_fn_def(item)) {
                    defn_emit_forward_declaration(ctx, item);
                    emitted_any = 1;
                }
            } else if (!_mv_1217.has_value) {
            }
            i = (i + 1);
        }
        if (emitted_any) {
            context_ctx_emit(ctx, SLOP_STR(""));
        }
    }
}

void transpiler_emit_fn_forward_decls_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        __auto_type emitted_any = 0;
        while ((i < len)) {
            __auto_type _mv_1218 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1218.has_value) {
                __auto_type item = _mv_1218.value;
                if (transpiler_is_fn_def(item)) {
                    transpiler_emit_fn_forward_decl_header(ctx, item);
                    emitted_any = 1;
                }
            } else if (!_mv_1218.has_value) {
            }
            i = (i + 1);
        }
        if (emitted_any) {
            context_ctx_emit_header(ctx, SLOP_STR(""));
        }
    }
}

void transpiler_emit_c_name_aliases(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type aliases = context_ctx_get_c_name_aliases(ctx);
        __auto_type len = ((int64_t)((aliases).len));
        __auto_type i = 0;
        if ((len > 0)) {
            context_ctx_emit_header(ctx, SLOP_STR("/* Function name aliases for C interop */"));
            while ((i < len)) {
                __auto_type _mv_1219 = ({ __auto_type _lst = aliases; size_t _idx = (size_t)i; slop_option_context_FuncCNameAlias _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1219.has_value) {
                    __auto_type alias = _mv_1219.value;
                    context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), context_ctx_str(ctx, alias.mangled_name, context_ctx_str(ctx, SLOP_STR(" "), alias.clean_name))));
                } else if (!_mv_1219.has_value) {
                }
                i = (i + 1);
            }
            context_ctx_emit_header(ctx, SLOP_STR(""));
        }
    }
}

void transpiler_emit_fn_forward_decl_header(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1220 = (*expr);
        switch (_mv_1220.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1220.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len >= 3)) {
                        __auto_type _mv_1221 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1221.has_value) {
                            __auto_type name_expr = _mv_1221.value;
                            __auto_type _mv_1222 = (*name_expr);
                            switch (_mv_1222.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_1222.data.sym;
                                    {
                                        __auto_type raw_name = name_sym.name;
                                        __auto_type base_name = ctype_to_c_name(arena, raw_name);
                                        __auto_type mangled_name = ((string_eq(base_name, SLOP_STR("main"))) ? base_name : context_ctx_prefix_type(ctx, base_name));
                                        __auto_type fn_name = context_extract_fn_c_name(arena, items, mangled_name);
                                        __auto_type _mv_1223 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1223.has_value) {
                                            __auto_type params_expr = _mv_1223.value;
                                            {
                                                __auto_type result_type_opt = defn_get_result_type_name(ctx, items);
                                                __auto_type raw_return = defn_get_return_type(ctx, items);
                                                {
                                                    slop_string return_type = ({ __auto_type _mv = result_type_opt; _mv.has_value ? ({ __auto_type result_name = _mv.value; result_name; }) : (raw_return); });
                                                    __auto_type actual_return = ((string_eq(base_name, SLOP_STR("main"))) ? SLOP_STR("int") : return_type);
                                                    __auto_type param_str = defn_build_param_str(ctx, params_expr);
                                                    context_ctx_emit_header(ctx, context_ctx_str5(ctx, actual_return, SLOP_STR(" "), fn_name, SLOP_STR("("), context_ctx_str(ctx, ((string_eq(param_str, SLOP_STR(""))) ? SLOP_STR("void") : param_str), SLOP_STR(");"))));
                                                }
                                            }
                                        } else if (!_mv_1223.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1221.has_value) {
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

slop_option_string transpiler_get_type_name(types_SExpr* item) {
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1224 = (*item);
    switch (_mv_1224.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1224.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 2)) {
                    return (slop_option_string){.has_value = false};
                } else {
                    __auto_type _mv_1225 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1225.has_value) {
                        __auto_type name_expr = _mv_1225.value;
                        __auto_type _mv_1226 = (*name_expr);
                        switch (_mv_1226.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1226.data.sym;
                                return (slop_option_string){.has_value = 1, .value = sym.name};
                            }
                            default: {
                                return (slop_option_string){.has_value = false};
                            }
                        }
                    } else if (!_mv_1225.has_value) {
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

void transpiler_emit_module_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        while ((i < len)) {
            __auto_type _mv_1227 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1227.has_value) {
                __auto_type item = _mv_1227.value;
                if (transpiler_is_type_def(item)) {
                    defn_transpile_type(ctx, item);
                    context_ctx_emit(ctx, SLOP_STR(""));
                }
            } else if (!_mv_1227.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_type_aliases(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        __auto_type emitted_any = 0;
        while ((i < len)) {
            __auto_type _mv_1228 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1228.has_value) {
                __auto_type item = _mv_1228.value;
                if ((transpiler_is_type_def(item) && transpiler_is_type_alias_def(item))) {
                    defn_transpile_type(ctx, item);
                    emitted_any = 1;
                }
            } else if (!_mv_1228.has_value) {
            }
            i = (i + 1);
        }
        if (emitted_any) {
            context_ctx_emit(ctx, SLOP_STR(""));
        }
    }
}

void transpiler_emit_enum_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        __auto_type emitted_any = 0;
        while ((i < len)) {
            __auto_type _mv_1229 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1229.has_value) {
                __auto_type item = _mv_1229.value;
                if ((transpiler_is_type_def(item) && transpiler_is_simple_enum_def(item))) {
                    defn_transpile_type(ctx, item);
                    emitted_any = 1;
                }
            } else if (!_mv_1229.has_value) {
            }
            i = (i + 1);
        }
        if (emitted_any) {
            context_ctx_emit(ctx, SLOP_STR(""));
        }
    }
}

void transpiler_emit_struct_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        while ((i < len)) {
            __auto_type _mv_1230 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1230.has_value) {
                __auto_type item = _mv_1230.value;
                if ((transpiler_is_type_def(item) && transpiler_is_struct_type_def(item))) {
                    defn_transpile_type(ctx, item);
                    context_ctx_emit(ctx, SLOP_STR(""));
                }
            } else if (!_mv_1230.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_result_types(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type result_types = context_ctx_get_result_types(ctx);
        __auto_type len = ((int64_t)((result_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1231 = ({ __auto_type _lst = result_types; size_t _idx = (size_t)i; slop_option_context_ResultType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1231.has_value) {
                __auto_type rt = _mv_1231.value;
                transpiler_emit_single_result_type(ctx, rt);
            } else if (!_mv_1231.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_single_result_type(context_TranspileContext* ctx, context_ResultType rt) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type ok_type = rt.ok_type;
        __auto_type err_type = rt.err_type;
        __auto_type c_name = rt.c_name;
        __auto_type guard_name = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, c_name), SLOP_STR("_DEFINED"), SLOP_STR(""));
        context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), guard_name));
        context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("#define "), guard_name));
        {
            __auto_type part1 = SLOP_STR("typedef struct { bool is_ok; union { ");
            __auto_type actual_ok_type = ((string_eq(ok_type, SLOP_STR("void"))) ? SLOP_STR("uint8_t") : ok_type);
            __auto_type part2 = context_ctx_str3(ctx, actual_ok_type, SLOP_STR(" ok; "), err_type);
            __auto_type part3 = context_ctx_str3(ctx, SLOP_STR(" err; } data; } "), c_name, SLOP_STR(";"));
            context_ctx_emit(ctx, context_ctx_str3(ctx, part1, part2, part3));
        }
        context_ctx_emit(ctx, SLOP_STR("#endif"));
        context_ctx_emit(ctx, SLOP_STR(""));
    }
}

void transpiler_emit_result_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type result_types = context_ctx_get_result_types(ctx);
        __auto_type len = ((int64_t)((result_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1232 = ({ __auto_type _lst = result_types; size_t _idx = (size_t)i; slop_option_context_ResultType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1232.has_value) {
                __auto_type rt = _mv_1232.value;
                transpiler_emit_single_result_type_header(ctx, rt);
            } else if (!_mv_1232.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_single_result_type_header(context_TranspileContext* ctx, context_ResultType rt) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type ok_type = rt.ok_type;
        __auto_type err_type = rt.err_type;
        __auto_type c_name = rt.c_name;
        __auto_type guard_name = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, c_name), SLOP_STR("_DEFINED"), SLOP_STR(""));
        context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), guard_name));
        context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), guard_name));
        {
            __auto_type part1 = SLOP_STR("typedef struct { bool is_ok; union { ");
            __auto_type actual_ok_type = ((string_eq(ok_type, SLOP_STR("void"))) ? SLOP_STR("uint8_t") : ok_type);
            __auto_type part2 = context_ctx_str3(ctx, actual_ok_type, SLOP_STR(" ok; "), err_type);
            __auto_type part3 = context_ctx_str3(ctx, SLOP_STR(" err; } data; } "), c_name, SLOP_STR(";"));
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, part1, part2, part3));
        }
        context_ctx_emit_header(ctx, SLOP_STR("#endif"));
        context_ctx_emit_header(ctx, SLOP_STR(""));
    }
}

void transpiler_emit_inline_records_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type inline_records = context_ctx_get_inline_records(ctx);
        __auto_type len = ((int64_t)((inline_records).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1233 = ({ __auto_type _lst = inline_records; size_t _idx = (size_t)i; slop_option_context_InlineRecord _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1233.has_value) {
                __auto_type ir = _mv_1233.value;
                {
                    __auto_type type_name = ir.type_name;
                    __auto_type field_body = ir.field_body;
                    __auto_type guard_name = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, type_name), SLOP_STR("_DEFINED"), SLOP_STR(""));
                    context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), guard_name));
                    context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), guard_name));
                    context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("typedef struct { "), field_body, SLOP_STR("} "), type_name, SLOP_STR(";")));
                    context_ctx_emit_header(ctx, SLOP_STR("#endif"));
                    context_ctx_emit_header(ctx, SLOP_STR(""));
                }
            } else if (!_mv_1233.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_option_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type option_types = context_ctx_get_option_types(ctx);
        __auto_type len = ((int64_t)((option_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1234 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1234.has_value) {
                __auto_type ot = _mv_1234.value;
                if (transpiler_is_pointer_elem_type(ot.inner_type)) {
                    transpiler_emit_single_option_type_header(ctx, ot);
                }
            } else if (!_mv_1234.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_value_option_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type option_types = context_ctx_get_option_types(ctx);
        __auto_type len = ((int64_t)((option_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1235 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1235.has_value) {
                __auto_type ot = _mv_1235.value;
                if ((!(transpiler_is_pointer_elem_type(ot.inner_type)) && transpiler_is_type_emitted_or_primitive(ctx, ot.inner_type))) {
                    transpiler_emit_single_option_type_header(ctx, ot);
                }
            } else if (!_mv_1235.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_complex_value_option_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type option_types = context_ctx_get_option_types(ctx);
        __auto_type len = ((int64_t)((option_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1236 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1236.has_value) {
                __auto_type ot = _mv_1236.value;
                if (!(transpiler_is_pointer_elem_type(ot.inner_type))) {
                    transpiler_emit_single_option_type_header(ctx, ot);
                }
            } else if (!_mv_1236.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_single_option_type_header(context_TranspileContext* ctx, context_OptionType ot) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type inner_type = ot.inner_type;
        __auto_type c_name = ot.c_name;
        if (!(transpiler_is_runtime_option_type(c_name))) {
            {
                __auto_type guard_name = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, c_name), SLOP_STR("_DEFINED"), SLOP_STR(""));
                context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), guard_name));
                context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), guard_name));
                if (strlib_starts_with(inner_type, SLOP_STR("set_"))) {
                    {
                        __auto_type set_guard = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, inner_type), SLOP_STR("_DEFINED"), SLOP_STR(""));
                        context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), set_guard));
                        context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), set_guard));
                        context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("typedef slop_map* "), context_ctx_str(ctx, inner_type, SLOP_STR(";"))));
                        context_ctx_emit_header(ctx, SLOP_STR("#endif"));
                    }
                }
                context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("SLOP_OPTION_DEFINE("), inner_type, SLOP_STR(", "), c_name, SLOP_STR(")")));
                context_ctx_emit_header(ctx, SLOP_STR("#endif"));
                context_ctx_emit_header(ctx, SLOP_STR(""));
                context_ctx_mark_type_emitted(ctx, c_name);
            }
        }
    }
}

void transpiler_emit_list_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type list_types = context_ctx_get_list_types(ctx);
        __auto_type len = ((int64_t)((list_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1237 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1237.has_value) {
                __auto_type lt = _mv_1237.value;
                if (transpiler_is_pointer_elem_type(lt.elem_type)) {
                    transpiler_emit_single_list_type_header(ctx, lt);
                }
            } else if (!_mv_1237.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_primitive_list_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type list_types = context_ctx_get_list_types(ctx);
        __auto_type len = ((int64_t)((list_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1238 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1238.has_value) {
                __auto_type lt = _mv_1238.value;
                if ((!(transpiler_is_pointer_elem_type(lt.elem_type)) && transpiler_is_primitive_or_runtime_type(lt.elem_type))) {
                    transpiler_emit_single_list_type_header(ctx, lt);
                    transpiler_emit_option_for_inner_type(ctx, lt.c_name);
                }
            } else if (!_mv_1238.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_primitive_option_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type option_types = context_ctx_get_option_types(ctx);
        __auto_type len = ((int64_t)((option_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1239 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1239.has_value) {
                __auto_type ot = _mv_1239.value;
                if (((!(transpiler_is_pointer_elem_type(ot.inner_type))) && (transpiler_is_primitive_or_runtime_type(ot.inner_type)) && (!(strlib_starts_with(ot.inner_type, SLOP_STR("slop_list_")))))) {
                    transpiler_emit_single_option_type_header(ctx, ot);
                }
            } else if (!_mv_1239.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t transpiler_is_primitive_or_runtime_type(slop_string type_name) {
    return (transpiler_is_primitive_type(type_name) || (strlib_starts_with(type_name, SLOP_STR("slop_")) || strlib_starts_with(type_name, SLOP_STR("set_"))));
}

void transpiler_emit_imported_list_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type list_types = context_ctx_get_list_types(ctx);
        __auto_type len = ((int64_t)((list_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1240 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1240.has_value) {
                __auto_type lt = _mv_1240.value;
                if (((!(transpiler_is_pointer_elem_type(lt.elem_type))) && (!(transpiler_is_primitive_or_runtime_type(lt.elem_type))) && (transpiler_is_imported_type(ctx, lt.elem_type)))) {
                    transpiler_emit_single_list_type_header(ctx, lt);
                    transpiler_emit_option_for_inner_type(ctx, lt.c_name);
                }
            } else if (!_mv_1240.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_imported_option_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type option_types = context_ctx_get_option_types(ctx);
        __auto_type len = ((int64_t)((option_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1241 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1241.has_value) {
                __auto_type ot = _mv_1241.value;
                if (((!(transpiler_is_pointer_elem_type(ot.inner_type))) && (!(transpiler_is_primitive_or_runtime_type(ot.inner_type))) && (!(strlib_starts_with(ot.inner_type, SLOP_STR("slop_list_")))) && (transpiler_is_imported_type(ctx, ot.inner_type)))) {
                    transpiler_emit_single_option_type_header(ctx, ot);
                }
            } else if (!_mv_1241.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_late_registered_option_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type option_types = context_ctx_get_option_types(ctx);
        __auto_type len = ((int64_t)((option_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1242 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1242.has_value) {
                __auto_type ot = _mv_1242.value;
                transpiler_emit_single_option_type_header(ctx, ot);
            } else if (!_mv_1242.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_value_list_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type list_types = context_ctx_get_list_types(ctx);
        __auto_type len = ((int64_t)((list_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1243 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1243.has_value) {
                __auto_type lt = _mv_1243.value;
                if ((!(transpiler_is_pointer_elem_type(lt.elem_type)) && transpiler_is_type_emitted_or_primitive(ctx, lt.elem_type))) {
                    transpiler_emit_single_list_type_header(ctx, lt);
                }
            } else if (!_mv_1243.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_complex_value_list_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type list_types = context_ctx_get_list_types(ctx);
        __auto_type len = ((int64_t)((list_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1244 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1244.has_value) {
                __auto_type lt = _mv_1244.value;
                if ((!(transpiler_is_pointer_elem_type(lt.elem_type)) && !(context_ctx_is_type_emitted(ctx, lt.c_name)))) {
                    transpiler_emit_single_list_type_header(ctx, lt);
                }
            } else if (!_mv_1244.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_struct_hash_eq(context_TranspileContext* ctx, slop_string c_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type union_variants = context_ctx_get_union_variants(ctx, c_type);
        if ((((int64_t)((union_variants).len)) > 0)) {
            transpiler_emit_union_payload_hash_eq(ctx, union_variants);
            transpiler_emit_union_hash_fn(ctx, c_type, union_variants);
            transpiler_emit_union_eq_fn(ctx, c_type, union_variants);
        } else {
            {
                __auto_type fields = context_ctx_get_fields_for_type(ctx, c_type);
                if ((((int64_t)((fields).len)) == 0)) {
                    context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("SLOP_STRUCT_HASH_EQ_DEFINE("), c_type, SLOP_STR(")")));
                } else {
                    transpiler_emit_struct_hash_fn(ctx, c_type, fields);
                    transpiler_emit_struct_eq_fn(ctx, c_type, fields);
                }
            }
        }
    }
}

void transpiler_emit_union_payload_hash_eq(context_TranspileContext* ctx, slop_list_context_UnionVariantEntry variants) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((variants).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1245 = ({ __auto_type _lst = variants; size_t _idx = (size_t)i; slop_option_context_UnionVariantEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1245.has_value) {
                __auto_type variant = _mv_1245.value;
                {
                    __auto_type slop_type = variant.slop_type;
                    __auto_type c_payload_type = variant.c_type;
                    if (((string_len(slop_type) > 0) && !(transpiler_is_primitive_slop_type(slop_type)))) {
                        {
                            __auto_type fields = context_ctx_get_fields_for_type(ctx, c_payload_type);
                            if ((((int64_t)((fields).len)) > 0)) {
                                {
                                    __auto_type guard_name = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, c_payload_type), SLOP_STR("_HASH_EQ_DEFINED"), SLOP_STR(""));
                                    context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), guard_name));
                                    context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), guard_name));
                                    transpiler_emit_struct_hash_fn(ctx, c_payload_type, fields);
                                    transpiler_emit_struct_eq_fn(ctx, c_payload_type, fields);
                                    context_ctx_emit_header(ctx, SLOP_STR("#endif"));
                                }
                            }
                        }
                    }
                }
            } else if (!_mv_1245.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t transpiler_is_primitive_slop_type(slop_string slop_type) {
    if (string_eq(slop_type, SLOP_STR("String"))) {
        return 1;
    } else if (string_eq(slop_type, SLOP_STR("Int"))) {
        return 1;
    } else if (string_eq(slop_type, SLOP_STR("I64"))) {
        return 1;
    } else if (string_eq(slop_type, SLOP_STR("I32"))) {
        return 1;
    } else if (string_eq(slop_type, SLOP_STR("I16"))) {
        return 1;
    } else if (string_eq(slop_type, SLOP_STR("I8"))) {
        return 1;
    } else if (string_eq(slop_type, SLOP_STR("U64"))) {
        return 1;
    } else if (string_eq(slop_type, SLOP_STR("U32"))) {
        return 1;
    } else if (string_eq(slop_type, SLOP_STR("U16"))) {
        return 1;
    } else if (string_eq(slop_type, SLOP_STR("U8"))) {
        return 1;
    } else if (string_eq(slop_type, SLOP_STR("Bool"))) {
        return 1;
    } else if (strlib_starts_with(slop_type, SLOP_STR("(Ptr"))) {
        return 1;
    } else if (strlib_starts_with(slop_type, SLOP_STR("(Int"))) {
        return 1;
    } else if (strlib_starts_with(slop_type, SLOP_STR("(I64"))) {
        return 1;
    } else if (strlib_starts_with(slop_type, SLOP_STR("(I32"))) {
        return 1;
    } else if (strlib_starts_with(slop_type, SLOP_STR("(I16"))) {
        return 1;
    } else if (strlib_starts_with(slop_type, SLOP_STR("(I8"))) {
        return 1;
    } else if (strlib_starts_with(slop_type, SLOP_STR("(U64"))) {
        return 1;
    } else if (strlib_starts_with(slop_type, SLOP_STR("(U32"))) {
        return 1;
    } else if (strlib_starts_with(slop_type, SLOP_STR("(U16"))) {
        return 1;
    } else if (strlib_starts_with(slop_type, SLOP_STR("(U8"))) {
        return 1;
    } else {
        return 0;
    }
}

uint8_t transpiler_is_range_type_alias(context_TranspileContext* ctx, slop_string slop_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    __auto_type _mv_1246 = context_ctx_lookup_type_alias(ctx, slop_type);
    if (_mv_1246.has_value) {
        __auto_type underlying = _mv_1246.value;
        if (strlib_starts_with(underlying, SLOP_STR("(Int"))) {
            return 1;
        } else if (strlib_starts_with(underlying, SLOP_STR("(I64"))) {
            return 1;
        } else if (strlib_starts_with(underlying, SLOP_STR("(I32"))) {
            return 1;
        } else if (strlib_starts_with(underlying, SLOP_STR("(I16"))) {
            return 1;
        } else if (strlib_starts_with(underlying, SLOP_STR("(I8"))) {
            return 1;
        } else if (strlib_starts_with(underlying, SLOP_STR("(U64"))) {
            return 1;
        } else if (strlib_starts_with(underlying, SLOP_STR("(U32"))) {
            return 1;
        } else if (strlib_starts_with(underlying, SLOP_STR("(U16"))) {
            return 1;
        } else if (strlib_starts_with(underlying, SLOP_STR("(U8"))) {
            return 1;
        } else {
            return 0;
        }
    } else if (!_mv_1246.has_value) {
        return 0;
    }
}

void transpiler_emit_union_hash_fn(context_TranspileContext* ctx, slop_string c_type, slop_list_context_UnionVariantEntry variants) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("static inline uint64_t slop_hash_"), c_type, SLOP_STR("(const void* key) {")));
    context_ctx_emit_header(ctx, context_ctx_str(ctx, context_ctx_str4(ctx, SLOP_STR("    const "), c_type, SLOP_STR("* _k = (const "), c_type), SLOP_STR("*)key;")));
    context_ctx_emit_header(ctx, SLOP_STR("    switch (_k->tag) {"));
    {
        __auto_type len = ((int64_t)((variants).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1247 = ({ __auto_type _lst = variants; size_t _idx = (size_t)i; slop_option_context_UnionVariantEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1247.has_value) {
                __auto_type variant = _mv_1247.value;
                transpiler_emit_union_variant_hash(ctx, c_type, variant);
            } else if (!_mv_1247.has_value) {
            }
            i = (i + 1);
        }
    }
    context_ctx_emit_header(ctx, SLOP_STR("    }"));
    context_ctx_emit_header(ctx, SLOP_STR("    return 0;"));
    context_ctx_emit_header(ctx, SLOP_STR("}"));
}

void transpiler_emit_union_variant_hash(context_TranspileContext* ctx, slop_string union_name, context_UnionVariantEntry variant) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type c_variant_name = variant.c_variant_name;
        __auto_type slop_type = variant.slop_type;
        __auto_type c_payload_type = variant.c_type;
        __auto_type tag_const = context_ctx_str3(ctx, union_name, SLOP_STR("_"), c_variant_name);
        context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("        case "), context_ctx_str(ctx, tag_const, SLOP_STR(":"))));
        if (string_eq(slop_type, SLOP_STR(""))) {
            context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("            return (uint64_t)"), context_ctx_str(ctx, tag_const, SLOP_STR(";"))));
        } else {
            if (string_eq(slop_type, SLOP_STR("String"))) {
                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("            return slop_hash_string(&_k->data."), c_variant_name, SLOP_STR(");")));
            } else if ((string_eq(slop_type, SLOP_STR("Int")) || string_eq(slop_type, SLOP_STR("I64")))) {
                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("            return slop_hash_int(&_k->data."), c_variant_name, SLOP_STR(");")));
            } else if ((string_eq(slop_type, SLOP_STR("U64")) || (string_eq(slop_type, SLOP_STR("U32")) || (string_eq(slop_type, SLOP_STR("U16")) || string_eq(slop_type, SLOP_STR("U8")))))) {
                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("            { uint64_t _tmp = (uint64_t)_k->data."), c_variant_name, SLOP_STR("; return slop_hash_uint(&_tmp); }")));
            } else if ((string_eq(slop_type, SLOP_STR("I32")) || (string_eq(slop_type, SLOP_STR("I16")) || string_eq(slop_type, SLOP_STR("I8"))))) {
                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("            { int64_t _tmp = (int64_t)_k->data."), c_variant_name, SLOP_STR("; return slop_hash_int(&_tmp); }")));
            } else if (string_eq(slop_type, SLOP_STR("Bool"))) {
                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("            return (uint64_t)_k->data."), c_variant_name, SLOP_STR(";")));
            } else if (strlib_starts_with(slop_type, SLOP_STR("(Ptr"))) {
                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("            return slop_hash_ptr(&_k->data."), c_variant_name, SLOP_STR(");")));
            } else if ((strlib_starts_with(slop_type, SLOP_STR("(Int")) || (strlib_starts_with(slop_type, SLOP_STR("(I64")) || strlib_starts_with(slop_type, SLOP_STR("(I32"))))) {
                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("            { int64_t _tmp = (int64_t)_k->data."), c_variant_name, SLOP_STR("; return slop_hash_int(&_tmp); }")));
            } else if ((strlib_starts_with(slop_type, SLOP_STR("(I16")) || strlib_starts_with(slop_type, SLOP_STR("(I8")))) {
                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("            { int64_t _tmp = (int64_t)_k->data."), c_variant_name, SLOP_STR("; return slop_hash_int(&_tmp); }")));
            } else if ((strlib_starts_with(slop_type, SLOP_STR("(U64")) || (strlib_starts_with(slop_type, SLOP_STR("(U32")) || (strlib_starts_with(slop_type, SLOP_STR("(U16")) || strlib_starts_with(slop_type, SLOP_STR("(U8")))))) {
                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("            { uint64_t _tmp = (uint64_t)_k->data."), c_variant_name, SLOP_STR("; return slop_hash_uint(&_tmp); }")));
            } else {
                context_ctx_emit_header(ctx, context_ctx_str(ctx, context_ctx_str3(ctx, SLOP_STR("            return slop_hash_"), c_payload_type, SLOP_STR("(&_k->data.")), context_ctx_str(ctx, c_variant_name, SLOP_STR(");"))));
            }
        }
    }
}

void transpiler_emit_union_eq_fn(context_TranspileContext* ctx, slop_string c_type, slop_list_context_UnionVariantEntry variants) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("static inline bool slop_eq_"), c_type, SLOP_STR("(const void* a, const void* b) {")));
    context_ctx_emit_header(ctx, context_ctx_str(ctx, context_ctx_str4(ctx, SLOP_STR("    const "), c_type, SLOP_STR("* _a = (const "), c_type), SLOP_STR("*)a;")));
    context_ctx_emit_header(ctx, context_ctx_str(ctx, context_ctx_str4(ctx, SLOP_STR("    const "), c_type, SLOP_STR("* _b = (const "), c_type), SLOP_STR("*)b;")));
    context_ctx_emit_header(ctx, SLOP_STR("    if (_a->tag != _b->tag) return false;"));
    context_ctx_emit_header(ctx, SLOP_STR("    switch (_a->tag) {"));
    {
        __auto_type len = ((int64_t)((variants).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1248 = ({ __auto_type _lst = variants; size_t _idx = (size_t)i; slop_option_context_UnionVariantEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1248.has_value) {
                __auto_type variant = _mv_1248.value;
                transpiler_emit_union_variant_eq(ctx, c_type, variant);
            } else if (!_mv_1248.has_value) {
            }
            i = (i + 1);
        }
    }
    context_ctx_emit_header(ctx, SLOP_STR("    }"));
    context_ctx_emit_header(ctx, SLOP_STR("    return false;"));
    context_ctx_emit_header(ctx, SLOP_STR("}"));
}

void transpiler_emit_union_variant_eq(context_TranspileContext* ctx, slop_string union_name, context_UnionVariantEntry variant) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type c_variant_name = variant.c_variant_name;
        __auto_type slop_type = variant.slop_type;
        __auto_type c_payload_type = variant.c_type;
        __auto_type tag_const = context_ctx_str3(ctx, union_name, SLOP_STR("_"), c_variant_name);
        context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("        case "), context_ctx_str(ctx, tag_const, SLOP_STR(":"))));
        if (string_eq(slop_type, SLOP_STR(""))) {
            context_ctx_emit_header(ctx, SLOP_STR("            return true;"));
        } else {
            if (string_eq(slop_type, SLOP_STR("String"))) {
                context_ctx_emit_header(ctx, context_ctx_str(ctx, context_ctx_str3(ctx, SLOP_STR("            return slop_eq_string(&_a->data."), c_variant_name, SLOP_STR(", &_b->data.")), context_ctx_str(ctx, c_variant_name, SLOP_STR(");"))));
            } else if ((string_eq(slop_type, SLOP_STR("Int")) || (string_eq(slop_type, SLOP_STR("I64")) || (string_eq(slop_type, SLOP_STR("I32")) || (string_eq(slop_type, SLOP_STR("I16")) || (string_eq(slop_type, SLOP_STR("I8")) || (string_eq(slop_type, SLOP_STR("U64")) || (string_eq(slop_type, SLOP_STR("U32")) || (string_eq(slop_type, SLOP_STR("U16")) || string_eq(slop_type, SLOP_STR("U8"))))))))))) {
                context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("            return _a->data."), c_variant_name, SLOP_STR(" == _b->data."), c_variant_name, SLOP_STR(";")));
            } else if (string_eq(slop_type, SLOP_STR("Bool"))) {
                context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("            return _a->data."), c_variant_name, SLOP_STR(" == _b->data."), c_variant_name, SLOP_STR(";")));
            } else if (strlib_starts_with(slop_type, SLOP_STR("(Ptr"))) {
                context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("            return _a->data."), c_variant_name, SLOP_STR(" == _b->data."), c_variant_name, SLOP_STR(";")));
            } else if ((strlib_starts_with(slop_type, SLOP_STR("(Int")) || (strlib_starts_with(slop_type, SLOP_STR("(I64")) || (strlib_starts_with(slop_type, SLOP_STR("(I32")) || (strlib_starts_with(slop_type, SLOP_STR("(I16")) || (strlib_starts_with(slop_type, SLOP_STR("(I8")) || (strlib_starts_with(slop_type, SLOP_STR("(U64")) || (strlib_starts_with(slop_type, SLOP_STR("(U32")) || (strlib_starts_with(slop_type, SLOP_STR("(U16")) || strlib_starts_with(slop_type, SLOP_STR("(U8"))))))))))) {
                context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("            return _a->data."), c_variant_name, SLOP_STR(" == _b->data."), c_variant_name, SLOP_STR(";")));
            } else {
                context_ctx_emit_header(ctx, context_ctx_str(ctx, context_ctx_str5(ctx, SLOP_STR("            return slop_eq_"), c_payload_type, SLOP_STR("(&_a->data."), c_variant_name, SLOP_STR(", &_b->data.")), context_ctx_str(ctx, c_variant_name, SLOP_STR(");"))));
            }
        }
    }
}

void transpiler_emit_struct_hash_fn(context_TranspileContext* ctx, slop_string c_type, slop_list_context_FieldEntry fields) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("static inline uint64_t slop_hash_"), c_type, SLOP_STR("(const void* key) {")));
    context_ctx_emit_header(ctx, context_ctx_str(ctx, context_ctx_str4(ctx, SLOP_STR("    const "), c_type, SLOP_STR("* _k = (const "), c_type), SLOP_STR("*)key;")));
    context_ctx_emit_header(ctx, SLOP_STR("    uint64_t hash = 14695981039346656037ULL;"));
    {
        __auto_type len = ((int64_t)((fields).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1249 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_context_FieldEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1249.has_value) {
                __auto_type field = _mv_1249.value;
                transpiler_emit_field_hash(ctx, field);
            } else if (!_mv_1249.has_value) {
            }
            i = (i + 1);
        }
    }
    context_ctx_emit_header(ctx, SLOP_STR("    return hash;"));
    context_ctx_emit_header(ctx, SLOP_STR("}"));
}

void transpiler_emit_field_hash(context_TranspileContext* ctx, context_FieldEntry field) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type field_name = field.field_name;
        __auto_type slop_type = field.slop_type;
        __auto_type c_field_name = ctype_to_c_name((*ctx).arena, field_name);
        if (string_eq(slop_type, SLOP_STR("String"))) {
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    hash ^= slop_hash_string(&_k->"), c_field_name, SLOP_STR("); hash *= 1099511628211ULL;")));
        } else if ((string_eq(slop_type, SLOP_STR("Int")) || string_eq(slop_type, SLOP_STR("I64")))) {
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    hash ^= slop_hash_int(&_k->"), c_field_name, SLOP_STR("); hash *= 1099511628211ULL;")));
        } else if ((string_eq(slop_type, SLOP_STR("I32")) || (string_eq(slop_type, SLOP_STR("I16")) || string_eq(slop_type, SLOP_STR("I8"))))) {
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    { int64_t _tmp = (int64_t)_k->"), c_field_name, SLOP_STR("; hash ^= slop_hash_int(&_tmp); hash *= 1099511628211ULL; }")));
        } else if ((string_eq(slop_type, SLOP_STR("U64")) || (string_eq(slop_type, SLOP_STR("U32")) || (string_eq(slop_type, SLOP_STR("U16")) || string_eq(slop_type, SLOP_STR("U8")))))) {
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    { uint64_t _tmp = (uint64_t)_k->"), c_field_name, SLOP_STR("; hash ^= slop_hash_uint(&_tmp); hash *= 1099511628211ULL; }")));
        } else if (string_eq(slop_type, SLOP_STR("Bool"))) {
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    hash ^= (uint64_t)_k->"), c_field_name, SLOP_STR("; hash *= 1099511628211ULL;")));
        } else if (strlib_starts_with(slop_type, SLOP_STR("(Ptr"))) {
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    hash ^= slop_hash_ptr(&_k->"), c_field_name, SLOP_STR("); hash *= 1099511628211ULL;")));
        } else if ((strlib_starts_with(slop_type, SLOP_STR("(List")) || (strlib_starts_with(slop_type, SLOP_STR("(Map")) || (strlib_starts_with(slop_type, SLOP_STR("(Set")) || (strlib_starts_with(slop_type, SLOP_STR("(Option")) || strlib_starts_with(slop_type, SLOP_STR("(Result"))))))) {
            {
                __auto_type c_type = field.c_type;
                context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("    { const uint8_t* _b = (const uint8_t*)&_k->"), c_field_name, SLOP_STR("; for(size_t _i=0; _i<sizeof(_k->"), c_field_name, SLOP_STR("); _i++) { hash ^= _b[_i]; hash *= 1099511628211ULL; } }")));
            }
        } else if (transpiler_is_range_type_alias(ctx, slop_type)) {
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    { int64_t _tmp = (int64_t)_k->"), c_field_name, SLOP_STR("; hash ^= slop_hash_int(&_tmp); hash *= 1099511628211ULL; }")));
        } else {
            {
                __auto_type nested_c_type = field.c_type;
                if (transpiler_is_pointer_elem_type(nested_c_type)) {
                    context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    hash ^= slop_hash_ptr(&_k->"), c_field_name, SLOP_STR("); hash *= 1099511628211ULL;")));
                } else {
                    context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("    hash ^= slop_hash_"), nested_c_type, SLOP_STR("(&_k->"), c_field_name, SLOP_STR("); hash *= 1099511628211ULL;")));
                }
            }
        }
    }
}

void transpiler_emit_struct_eq_fn(context_TranspileContext* ctx, slop_string c_type, slop_list_context_FieldEntry fields) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("static inline bool slop_eq_"), c_type, SLOP_STR("(const void* a, const void* b) {")));
    context_ctx_emit_header(ctx, context_ctx_str(ctx, context_ctx_str4(ctx, SLOP_STR("    const "), c_type, SLOP_STR("* _a = (const "), c_type), SLOP_STR("*)a;")));
    context_ctx_emit_header(ctx, context_ctx_str(ctx, context_ctx_str4(ctx, SLOP_STR("    const "), c_type, SLOP_STR("* _b = (const "), c_type), SLOP_STR("*)b;")));
    {
        __auto_type len = ((int64_t)((fields).len));
        if ((len == 0)) {
            context_ctx_emit_header(ctx, SLOP_STR("    return true;"));
        } else {
            context_ctx_emit_header(ctx, SLOP_STR("    return true"));
            {
                __auto_type i = 0;
                while ((i < len)) {
                    __auto_type _mv_1250 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_context_FieldEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1250.has_value) {
                        __auto_type field = _mv_1250.value;
                        transpiler_emit_field_eq(ctx, field);
                    } else if (!_mv_1250.has_value) {
                    }
                    i = (i + 1);
                }
            }
            context_ctx_emit_header(ctx, SLOP_STR("    ;"));
        }
    }
    context_ctx_emit_header(ctx, SLOP_STR("}"));
}

void transpiler_emit_field_eq(context_TranspileContext* ctx, context_FieldEntry field) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type field_name = field.field_name;
        __auto_type slop_type = field.slop_type;
        __auto_type c_field_name = ctype_to_c_name((*ctx).arena, field_name);
        if (string_eq(slop_type, SLOP_STR("String"))) {
            context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("        && slop_eq_string(&_a->"), c_field_name, SLOP_STR(", &_b->"), c_field_name, SLOP_STR(")")));
        } else if ((string_eq(slop_type, SLOP_STR("Int")) || (string_eq(slop_type, SLOP_STR("I64")) || (string_eq(slop_type, SLOP_STR("I32")) || (string_eq(slop_type, SLOP_STR("I16")) || (string_eq(slop_type, SLOP_STR("I8")) || (string_eq(slop_type, SLOP_STR("U64")) || (string_eq(slop_type, SLOP_STR("U32")) || (string_eq(slop_type, SLOP_STR("U16")) || string_eq(slop_type, SLOP_STR("U8"))))))))))) {
            context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("        && _a->"), c_field_name, SLOP_STR(" == _b->"), c_field_name));
        } else if (string_eq(slop_type, SLOP_STR("Bool"))) {
            context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("        && _a->"), c_field_name, SLOP_STR(" == _b->"), c_field_name));
        } else if (strlib_starts_with(slop_type, SLOP_STR("(Ptr"))) {
            context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("        && _a->"), c_field_name, SLOP_STR(" == _b->"), c_field_name));
        } else if ((strlib_starts_with(slop_type, SLOP_STR("(List")) || (strlib_starts_with(slop_type, SLOP_STR("(Map")) || (strlib_starts_with(slop_type, SLOP_STR("(Set")) || (strlib_starts_with(slop_type, SLOP_STR("(Option")) || strlib_starts_with(slop_type, SLOP_STR("(Result"))))))) {
            {
                __auto_type c_type = field.c_type;
                context_ctx_emit_header(ctx, context_ctx_str(ctx, context_ctx_str(ctx, context_ctx_str5(ctx, SLOP_STR("        && memcmp(&_a->"), c_field_name, SLOP_STR(", &_b->"), c_field_name, SLOP_STR(", sizeof(_a->")), c_field_name), SLOP_STR(")) == 0")));
            }
        } else if (transpiler_is_range_type_alias(ctx, slop_type)) {
            context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("        && _a->"), c_field_name, SLOP_STR(" == _b->"), c_field_name));
        } else {
            {
                __auto_type nested_c_type = field.c_type;
                if (transpiler_is_pointer_elem_type(nested_c_type)) {
                    context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("        && _a->"), c_field_name, SLOP_STR(" == _b->"), c_field_name));
                } else {
                    context_ctx_emit_header(ctx, context_ctx_str(ctx, context_ctx_str5(ctx, SLOP_STR("        && slop_eq_"), nested_c_type, SLOP_STR("(&_a->"), c_field_name, SLOP_STR(", &_b->")), context_ctx_str(ctx, c_field_name, SLOP_STR(")"))));
                }
            }
        }
    }
}

void transpiler_emit_struct_key_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type struct_key_types = context_ctx_get_struct_key_types(ctx);
        __auto_type len = ((int64_t)((struct_key_types).len));
        __auto_type i = 0;
        if ((len > 0)) {
            context_ctx_emit_header(ctx, SLOP_STR(""));
            context_ctx_emit_header(ctx, SLOP_STR("/* Hash/eq functions and list types for struct map/set keys */"));
        }
        while ((i < len)) {
            __auto_type _mv_1251 = ({ __auto_type _lst = struct_key_types; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1251.has_value) {
                __auto_type c_type = _mv_1251.value;
                {
                    __auto_type guard_name = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, c_type), SLOP_STR("_HASH_EQ_DEFINED"), SLOP_STR(""));
                    __auto_type list_c_name = context_ctx_str(ctx, SLOP_STR("slop_list_"), c_type);
                    context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), guard_name));
                    context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), guard_name));
                    transpiler_emit_struct_hash_eq(ctx, c_type);
                    if (!(context_ctx_is_type_emitted(ctx, list_c_name))) {
                        context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("SLOP_LIST_DEFINE("), c_type, SLOP_STR(", "), list_c_name, SLOP_STR(")")));
                        context_ctx_mark_type_emitted(ctx, list_c_name);
                    }
                    context_ctx_emit_header(ctx, SLOP_STR("#endif"));
                    context_ctx_emit_header(ctx, SLOP_STR(""));
                }
            } else if (!_mv_1251.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t transpiler_is_pointer_elem_type(slop_string elem_type) {
    {
        __auto_type len = ((int64_t)(elem_type.len));
        if ((len <= 0)) {
            return 0;
        } else {
            {
                __auto_type data = elem_type.data;
                __auto_type last_char = data[(len - 1)];
                return (last_char == ((uint8_t)(42)));
            }
        }
    }
}

void transpiler_emit_single_list_type_header(context_TranspileContext* ctx, context_ListType lt) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type elem_type = lt.elem_type;
        __auto_type c_name = lt.c_name;
        if (!(transpiler_is_runtime_list_type(c_name))) {
            {
                __auto_type guard_name = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, c_name), SLOP_STR("_DEFINED"), SLOP_STR(""));
                context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), guard_name));
                context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), guard_name));
                context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("SLOP_LIST_DEFINE("), elem_type, SLOP_STR(", "), c_name, SLOP_STR(")")));
                context_ctx_emit_header(ctx, SLOP_STR("#endif"));
                context_ctx_emit_header(ctx, SLOP_STR(""));
                context_ctx_mark_type_emitted(ctx, c_name);
            }
        }
    }
}

uint8_t transpiler_is_runtime_option_type(slop_string name) {
    return (string_eq(name, SLOP_STR("slop_option_int")) || (string_eq(name, SLOP_STR("slop_option_float")) || (string_eq(name, SLOP_STR("slop_option_string")) || (string_eq(name, SLOP_STR("slop_option_ptr")) || string_eq(name, SLOP_STR("slop_option_bool"))))));
}

uint8_t transpiler_is_runtime_list_type(slop_string name) {
    return (string_eq(name, SLOP_STR("slop_list_int")) || (string_eq(name, SLOP_STR("slop_list_float")) || (string_eq(name, SLOP_STR("slop_list_string")) || string_eq(name, SLOP_STR("slop_list_ptr")))));
}

void transpiler_emit_chan_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type chan_types = context_ctx_get_chan_types(ctx);
        __auto_type len = ((int64_t)((chan_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1252 = ({ __auto_type _lst = chan_types; size_t _idx = (size_t)i; slop_option_context_ChanType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1252.has_value) {
                __auto_type ct = _mv_1252.value;
                {
                    __auto_type elem_type = ct.elem_type;
                    __auto_type c_name = ct.c_name;
                    if (!(transpiler_is_runtime_chan_type(c_name))) {
                        {
                            __auto_type guard_name = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, c_name), SLOP_STR("_DEFINED"), SLOP_STR(""));
                            context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), guard_name));
                            context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), guard_name));
                            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("typedef struct "), c_name, SLOP_STR(" {")));
                            context_ctx_emit_header(ctx, SLOP_STR("    uint8_t mutex[64];       /* pthread_mutex_t storage */"));
                            context_ctx_emit_header(ctx, SLOP_STR("    uint8_t not_empty[64];   /* pthread_cond_t storage */"));
                            context_ctx_emit_header(ctx, SLOP_STR("    uint8_t not_full[64];    /* pthread_cond_t storage */"));
                            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    "), elem_type, SLOP_STR("* buffer;         /* Ring buffer */")));
                            context_ctx_emit_header(ctx, SLOP_STR("    size_t capacity;         /* Buffer capacity (0 = unbuffered) */"));
                            context_ctx_emit_header(ctx, SLOP_STR("    size_t count;            /* Current item count */"));
                            context_ctx_emit_header(ctx, SLOP_STR("    size_t head;             /* Read index */"));
                            context_ctx_emit_header(ctx, SLOP_STR("    size_t tail;             /* Write index */"));
                            context_ctx_emit_header(ctx, SLOP_STR("    bool closed;             /* Channel closed flag */"));
                            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("} "), c_name, SLOP_STR(";")));
                            context_ctx_emit_header(ctx, SLOP_STR("#endif"));
                            context_ctx_emit_header(ctx, SLOP_STR(""));
                        }
                    }
                }
            } else if (!_mv_1252.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_chan_funcs_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type chan_types = context_ctx_get_chan_types(ctx);
        __auto_type len = ((int64_t)((chan_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1253 = ({ __auto_type _lst = chan_types; size_t _idx = (size_t)i; slop_option_context_ChanType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1253.has_value) {
                __auto_type ct = _mv_1253.value;
                {
                    __auto_type elem_type = ct.elem_type;
                    __auto_type c_name = ct.c_name;
                    if ((!(transpiler_is_runtime_chan_type(c_name)) && !(transpiler_is_default_chan_type(c_name)))) {
                        transpiler_emit_chan_send_recv_funcs(ctx, c_name, elem_type);
                    }
                }
            } else if (!_mv_1253.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_chan_send_recv_funcs(context_TranspileContext* ctx, slop_string c_name, slop_string elem_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = ctx->arena;
        __auto_type elem_id = ctype_type_to_identifier(arena, elem_type);
        context_ctx_emit_header(ctx, SLOP_STR("#ifndef SLOP_RESULT_VOID_THREAD_CHANERROR_DEFINED"));
        context_ctx_emit_header(ctx, SLOP_STR("#define SLOP_RESULT_VOID_THREAD_CHANERROR_DEFINED"));
        context_ctx_emit_header(ctx, SLOP_STR("typedef struct slop_result_void_thread_ChanError {"));
        context_ctx_emit_header(ctx, SLOP_STR("    bool is_ok;"));
        context_ctx_emit_header(ctx, SLOP_STR("    union { uint8_t ok; thread_ChanError err; } data;"));
        context_ctx_emit_header(ctx, SLOP_STR("} slop_result_void_thread_ChanError;"));
        context_ctx_emit_header(ctx, SLOP_STR("#endif"));
        context_ctx_emit_header(ctx, SLOP_STR(""));
        {
            __auto_type recv_result_type = context_ctx_str3(ctx, SLOP_STR("slop_result_"), elem_id, SLOP_STR("_thread_ChanError"));
            __auto_type recv_guard = context_ctx_str3(ctx, SLOP_STR("SLOP_RESULT_"), transpiler_uppercase_name(ctx, elem_id), SLOP_STR("_THREAD_CHANERROR_DEFINED"));
            context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), recv_guard));
            context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), recv_guard));
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("typedef struct "), recv_result_type, SLOP_STR(" {")));
            context_ctx_emit_header(ctx, SLOP_STR("    bool is_ok;"));
            {
                __auto_type union_line = context_ctx_str(ctx, SLOP_STR("    union { "), context_ctx_str(ctx, elem_type, SLOP_STR(" ok; thread_ChanError err; } data;")));
                context_ctx_emit_header(ctx, union_line);
            }
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("} "), recv_result_type, SLOP_STR(";")));
            context_ctx_emit_header(ctx, SLOP_STR("#endif"));
            context_ctx_emit_header(ctx, SLOP_STR(""));
            {
                __auto_type send_name = context_ctx_str(ctx, SLOP_STR("thread_send_"), c_name);
                __auto_type recv_name = context_ctx_str(ctx, SLOP_STR("thread_recv_"), c_name);
                __auto_type send_result_type = SLOP_STR("slop_result_void_thread_ChanError");
                __auto_type ret_ok = context_ctx_str3(ctx, SLOP_STR("        return ("), send_result_type, SLOP_STR("){.is_ok = 1};"));
                __auto_type ret_closed = context_ctx_str3(ctx, SLOP_STR("        return ("), send_result_type, SLOP_STR("){.is_ok = 0, .data.err = thread_ChanError_send_on_closed};"));
                __auto_type ret_closed12 = context_ctx_str3(ctx, SLOP_STR("            return ("), send_result_type, SLOP_STR("){.is_ok = 0, .data.err = thread_ChanError_send_on_closed};"));
                __auto_type ret_err_closed = context_ctx_str3(ctx, SLOP_STR("        return ("), recv_result_type, SLOP_STR("){.is_ok = 0, .data.err = thread_ChanError_closed};"));
                {
                    __auto_type send_sig_1 = context_ctx_str3(ctx, SLOP_STR("static "), send_result_type, SLOP_STR(" "));
                    __auto_type send_sig_2 = context_ctx_str(ctx, send_sig_1, send_name);
                    __auto_type send_sig_3 = context_ctx_str(ctx, send_sig_2, SLOP_STR("("));
                    __auto_type send_sig_4 = context_ctx_str(ctx, send_sig_3, c_name);
                    __auto_type send_sig_5 = context_ctx_str(ctx, send_sig_4, SLOP_STR("* ch, "));
                    __auto_type send_sig_6 = context_ctx_str(ctx, send_sig_5, elem_type);
                    __auto_type send_sig = context_ctx_str(ctx, send_sig_6, SLOP_STR(" value) {"));
                    context_ctx_emit_header(ctx, send_sig);
                }
                context_ctx_emit_header(ctx, SLOP_STR("    pthread_mutex_lock((pthread_mutex_t*)ch->mutex);"));
                context_ctx_emit_header(ctx, SLOP_STR("    if (ch->closed) {"));
                context_ctx_emit_header(ctx, SLOP_STR("        pthread_mutex_unlock((pthread_mutex_t*)ch->mutex);"));
                context_ctx_emit_header(ctx, ret_closed);
                context_ctx_emit_header(ctx, SLOP_STR("    }"));
                context_ctx_emit_header(ctx, SLOP_STR("    if (ch->capacity == 0) {"));
                context_ctx_emit_header(ctx, SLOP_STR("        /* Unbuffered: synchronous handoff */"));
                context_ctx_emit_header(ctx, SLOP_STR("        while (ch->count > 0 && !ch->closed)"));
                context_ctx_emit_header(ctx, SLOP_STR("            pthread_cond_wait((pthread_cond_t*)ch->not_full, (pthread_mutex_t*)ch->mutex);"));
                context_ctx_emit_header(ctx, SLOP_STR("        if (ch->closed) {"));
                context_ctx_emit_header(ctx, SLOP_STR("            pthread_mutex_unlock((pthread_mutex_t*)ch->mutex);"));
                context_ctx_emit_header(ctx, ret_closed12);
                context_ctx_emit_header(ctx, SLOP_STR("        }"));
                context_ctx_emit_header(ctx, SLOP_STR("        /* Store value in single-element inline storage */"));
                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("        if (!ch->buffer) ch->buffer = malloc(sizeof("), elem_type, SLOP_STR("));")));
                context_ctx_emit_header(ctx, SLOP_STR("        ch->buffer[0] = value;"));
                context_ctx_emit_header(ctx, SLOP_STR("        ch->count = 1;"));
                context_ctx_emit_header(ctx, SLOP_STR("        pthread_cond_signal((pthread_cond_t*)ch->not_empty);"));
                context_ctx_emit_header(ctx, SLOP_STR("        /* Wait for receiver to take it */"));
                context_ctx_emit_header(ctx, SLOP_STR("        while (ch->count > 0 && !ch->closed)"));
                context_ctx_emit_header(ctx, SLOP_STR("            pthread_cond_wait((pthread_cond_t*)ch->not_full, (pthread_mutex_t*)ch->mutex);"));
                context_ctx_emit_header(ctx, SLOP_STR("        pthread_mutex_unlock((pthread_mutex_t*)ch->mutex);"));
                context_ctx_emit_header(ctx, ret_ok);
                context_ctx_emit_header(ctx, SLOP_STR("    } else {"));
                context_ctx_emit_header(ctx, SLOP_STR("        /* Buffered: enqueue to ring buffer */"));
                context_ctx_emit_header(ctx, SLOP_STR("        while (ch->count >= ch->capacity && !ch->closed)"));
                context_ctx_emit_header(ctx, SLOP_STR("            pthread_cond_wait((pthread_cond_t*)ch->not_full, (pthread_mutex_t*)ch->mutex);"));
                context_ctx_emit_header(ctx, SLOP_STR("        if (ch->closed) {"));
                context_ctx_emit_header(ctx, SLOP_STR("            pthread_mutex_unlock((pthread_mutex_t*)ch->mutex);"));
                context_ctx_emit_header(ctx, ret_closed12);
                context_ctx_emit_header(ctx, SLOP_STR("        }"));
                context_ctx_emit_header(ctx, SLOP_STR("        ch->buffer[ch->tail] = value;"));
                context_ctx_emit_header(ctx, SLOP_STR("        ch->tail = (ch->tail + 1) % ch->capacity;"));
                context_ctx_emit_header(ctx, SLOP_STR("        ch->count++;"));
                context_ctx_emit_header(ctx, SLOP_STR("        pthread_cond_signal((pthread_cond_t*)ch->not_empty);"));
                context_ctx_emit_header(ctx, SLOP_STR("        pthread_mutex_unlock((pthread_mutex_t*)ch->mutex);"));
                context_ctx_emit_header(ctx, ret_ok);
                context_ctx_emit_header(ctx, SLOP_STR("    }"));
                context_ctx_emit_header(ctx, SLOP_STR("}"));
                context_ctx_emit_header(ctx, SLOP_STR(""));
                {
                    __auto_type recv_sig_1 = context_ctx_str3(ctx, SLOP_STR("static "), recv_result_type, SLOP_STR(" "));
                    __auto_type recv_sig_2 = context_ctx_str(ctx, recv_sig_1, recv_name);
                    __auto_type recv_sig_3 = context_ctx_str(ctx, recv_sig_2, SLOP_STR("("));
                    __auto_type recv_sig_4 = context_ctx_str(ctx, recv_sig_3, c_name);
                    __auto_type recv_sig = context_ctx_str(ctx, recv_sig_4, SLOP_STR("* ch) {"));
                    context_ctx_emit_header(ctx, recv_sig);
                }
                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    "), elem_type, SLOP_STR(" _value;")));
                context_ctx_emit_header(ctx, SLOP_STR("    pthread_mutex_lock((pthread_mutex_t*)ch->mutex);"));
                context_ctx_emit_header(ctx, SLOP_STR("    while (ch->count == 0 && !ch->closed)"));
                context_ctx_emit_header(ctx, SLOP_STR("        pthread_cond_wait((pthread_cond_t*)ch->not_empty, (pthread_mutex_t*)ch->mutex);"));
                context_ctx_emit_header(ctx, SLOP_STR("    if (ch->count == 0 && ch->closed) {"));
                context_ctx_emit_header(ctx, SLOP_STR("        pthread_mutex_unlock((pthread_mutex_t*)ch->mutex);"));
                context_ctx_emit_header(ctx, ret_err_closed);
                context_ctx_emit_header(ctx, SLOP_STR("    }"));
                context_ctx_emit_header(ctx, SLOP_STR("    if (ch->capacity == 0) {"));
                context_ctx_emit_header(ctx, SLOP_STR("        /* Unbuffered */"));
                context_ctx_emit_header(ctx, SLOP_STR("        _value = ch->buffer[0];"));
                context_ctx_emit_header(ctx, SLOP_STR("        ch->count = 0;"));
                context_ctx_emit_header(ctx, SLOP_STR("        pthread_cond_signal((pthread_cond_t*)ch->not_full);"));
                context_ctx_emit_header(ctx, SLOP_STR("    } else {"));
                context_ctx_emit_header(ctx, SLOP_STR("        /* Buffered */"));
                context_ctx_emit_header(ctx, SLOP_STR("        _value = ch->buffer[ch->head];"));
                context_ctx_emit_header(ctx, SLOP_STR("        ch->head = (ch->head + 1) % ch->capacity;"));
                context_ctx_emit_header(ctx, SLOP_STR("        ch->count--;"));
                context_ctx_emit_header(ctx, SLOP_STR("        pthread_cond_signal((pthread_cond_t*)ch->not_full);"));
                context_ctx_emit_header(ctx, SLOP_STR("    }"));
                context_ctx_emit_header(ctx, SLOP_STR("    pthread_mutex_unlock((pthread_mutex_t*)ch->mutex);"));
                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    return ("), recv_result_type, SLOP_STR("){.is_ok = 1, .data.ok = _value};")));
                context_ctx_emit_header(ctx, SLOP_STR("}"));
                context_ctx_emit_header(ctx, SLOP_STR(""));
            }
        }
    }
}

void transpiler_emit_thread_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type thread_types = context_ctx_get_thread_types(ctx);
        __auto_type len = ((int64_t)((thread_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1254 = ({ __auto_type _lst = thread_types; size_t _idx = (size_t)i; slop_option_context_ThreadType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1254.has_value) {
                __auto_type tt = _mv_1254.value;
                {
                    __auto_type result_type = tt.result_type;
                    __auto_type c_name = tt.c_name;
                    if (!(transpiler_is_runtime_thread_type(c_name))) {
                        {
                            __auto_type guard_name = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, c_name), SLOP_STR("_DEFINED"), SLOP_STR(""));
                            __auto_type entry_name = context_ctx_str(ctx, c_name, SLOP_STR("_entry"));
                            context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), guard_name));
                            context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), guard_name));
                            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("typedef struct "), c_name, SLOP_STR(" {")));
                            context_ctx_emit_header(ctx, SLOP_STR("    pthread_t id;            /* pthread handle */"));
                            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    "), result_type, SLOP_STR(" result;          /* Thread return value */")));
                            context_ctx_emit_header(ctx, SLOP_STR("    void* func;              /* Function pointer */"));
                            context_ctx_emit_header(ctx, SLOP_STR("    void* env;               /* Closure environment */"));
                            context_ctx_emit_header(ctx, SLOP_STR("    bool done;               /* Completion flag */"));
                            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("} "), c_name, SLOP_STR(";")));
                            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("static void* "), entry_name, SLOP_STR("(void* arg) {")));
                            context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("    "), c_name, SLOP_STR("* s = ("), c_name, SLOP_STR("*)arg;")));
                            context_ctx_emit_header(ctx, SLOP_STR("    if (s->env) {"));
                            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("        s->result = (("), result_type, SLOP_STR("(*)(void*))(s->func))(s->env);")));
                            context_ctx_emit_header(ctx, SLOP_STR("    } else {"));
                            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("        s->result = (("), result_type, SLOP_STR("(*)(void))(s->func))();")));
                            context_ctx_emit_header(ctx, SLOP_STR("    }"));
                            context_ctx_emit_header(ctx, SLOP_STR("    s->done = true;"));
                            context_ctx_emit_header(ctx, SLOP_STR("    return NULL;"));
                            context_ctx_emit_header(ctx, SLOP_STR("}"));
                            context_ctx_emit_header(ctx, SLOP_STR("#endif"));
                            context_ctx_emit_header(ctx, SLOP_STR(""));
                        }
                    }
                }
            } else if (!_mv_1254.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t transpiler_is_runtime_chan_type(slop_string name) {
    return (string_eq(name, SLOP_STR("slop_chan_int64_t")) || (string_eq(name, SLOP_STR("slop_chan_double")) || string_eq(name, SLOP_STR("slop_chan_ptr"))));
}

uint8_t transpiler_is_default_chan_type(slop_string name) {
    return string_eq(name, SLOP_STR("slop_chan_int"));
}

uint8_t transpiler_is_runtime_thread_type(slop_string name) {
    return (string_eq(name, SLOP_STR("slop_thread_int64_t")) || (string_eq(name, SLOP_STR("slop_thread_double")) || string_eq(name, SLOP_STR("slop_thread_ptr"))));
}

slop_string transpiler_uppercase_name(context_TranspileContext* ctx, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)(name.len));
        __auto_type data = name.data;
        __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (len + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
        __auto_type i = 0;
        while ((i < len)) {
            {
                __auto_type c = ((int64_t)(data[i]));
                if (((c >= 97) && (c <= 122))) {
                    buf[i] = ((uint8_t)((c - 32)));
                } else {
                    buf[i] = ((uint8_t)(c));
                }
            }
            i = (i + 1);
        }
        buf[len] = 0;
        return (slop_string){.len = ((uint64_t)(len)), .data = buf};
    }
}

uint8_t transpiler_is_simple_enum_def(types_SExpr* item) {
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1255 = (*item);
    switch (_mv_1255.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1255.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 3)) {
                    return 0;
                } else {
                    __auto_type _mv_1256 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1256.has_value) {
                        __auto_type def_expr = _mv_1256.value;
                        __auto_type _mv_1257 = (*def_expr);
                        switch (_mv_1257.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type def_lst = _mv_1257.data.lst;
                                {
                                    __auto_type def_items = def_lst.items;
                                    if ((((int64_t)((def_items).len)) < 1)) {
                                        return 0;
                                    } else {
                                        __auto_type _mv_1258 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1258.has_value) {
                                            __auto_type head = _mv_1258.value;
                                            __auto_type _mv_1259 = (*head);
                                            switch (_mv_1259.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type sym = _mv_1259.data.sym;
                                                    return (string_eq(sym.name, SLOP_STR("enum")) && !(transpiler_has_enum_payload_variants(def_items)));
                                                }
                                                default: {
                                                    return 0;
                                                }
                                            }
                                        } else if (!_mv_1258.has_value) {
                                            return 0;
                                        }
                                    }
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1256.has_value) {
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

void transpiler_emit_module_types_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        while ((i < len)) {
            __auto_type _mv_1260 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1260.has_value) {
                __auto_type item = _mv_1260.value;
                if ((transpiler_is_type_def(item) && transpiler_is_type_alias_def(item))) {
                    transpiler_emit_type_alias_to_header(ctx, item);
                }
            } else if (!_mv_1260.has_value) {
            }
            i = (i + 1);
        }
        i = start;
        while ((i < len)) {
            __auto_type _mv_1261 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1261.has_value) {
                __auto_type item = _mv_1261.value;
                if ((transpiler_is_type_def(item) && transpiler_is_simple_enum_def(item))) {
                    transpiler_emit_type_to_header(ctx, item);
                }
            } else if (!_mv_1261.has_value) {
            }
            i = (i + 1);
        }
        i = start;
        while ((i < len)) {
            __auto_type _mv_1262 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1262.has_value) {
                __auto_type item = _mv_1262.value;
                if ((transpiler_is_type_def(item) && transpiler_is_struct_type_def(item))) {
                    transpiler_emit_type_to_header(ctx, item);
                }
            } else if (!_mv_1262.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_simple_type_aliases_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        while ((i < len)) {
            __auto_type _mv_1263 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1263.has_value) {
                __auto_type item = _mv_1263.value;
                if (((transpiler_is_type_def(item)) && (transpiler_is_type_alias_def(item)) && (!(transpiler_is_result_type_alias_def(item))))) {
                    transpiler_emit_type_alias_to_header(ctx, item);
                }
            } else if (!_mv_1263.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_type_aliases_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        __auto_type emitted_any = 0;
        while ((i < len)) {
            __auto_type _mv_1264 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1264.has_value) {
                __auto_type item = _mv_1264.value;
                if (((transpiler_is_type_def(item)) && (transpiler_is_type_alias_def(item)) && (transpiler_is_result_type_alias_def(item)))) {
                    transpiler_emit_type_alias_to_header(ctx, item);
                    emitted_any = 1;
                }
            } else if (!_mv_1264.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_simple_enums_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        while ((i < len)) {
            __auto_type _mv_1265 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1265.has_value) {
                __auto_type item = _mv_1265.value;
                if ((transpiler_is_type_def(item) && transpiler_is_simple_enum_def(item))) {
                    transpiler_emit_type_to_header(ctx, item);
                }
            } else if (!_mv_1265.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_pending_container_deps(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type field_types = transpiler_get_type_field_types(ctx, type_def);
        __auto_type len = ((int64_t)((field_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1266 = ({ __auto_type _lst = field_types; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1266.has_value) {
                __auto_type field_type = _mv_1266.value;
                if ((!(context_ctx_is_type_emitted(ctx, field_type)) && transpiler_is_emittable_container_type(ctx, field_type))) {
                    if (strlib_starts_with(field_type, SLOP_STR("slop_option_"))) {
                        transpiler_emit_option_by_c_name(ctx, field_type);
                    }
                    if (strlib_starts_with(field_type, SLOP_STR("slop_list_"))) {
                        transpiler_emit_list_by_c_name(ctx, field_type);
                    }
                }
            } else if (!_mv_1266.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_option_by_c_name(context_TranspileContext* ctx, slop_string c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type option_types = context_ctx_get_option_types(ctx);
        __auto_type len = ((int64_t)((option_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1267 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1267.has_value) {
                __auto_type ot = _mv_1267.value;
                if (string_eq(ot.c_name, c_name)) {
                    transpiler_emit_single_option_type_header(ctx, ot);
                }
            } else if (!_mv_1267.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_list_by_c_name(context_TranspileContext* ctx, slop_string c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type list_types = context_ctx_get_list_types(ctx);
        __auto_type len = ((int64_t)((list_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1268 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1268.has_value) {
                __auto_type lt = _mv_1268.value;
                if (string_eq(lt.c_name, c_name)) {
                    transpiler_emit_single_list_type_header(ctx, lt);
                }
            } else if (!_mv_1268.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_struct_union_types_sorted(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type arena = (*ctx).arena;
        slop_list_int emitted = ((slop_list_int){ .data = (int64_t*)slop_arena_alloc(arena, 16 * sizeof(int64_t)), .len = 0, .cap = 16 });
        __auto_type prev_count = -1;
        __auto_type current_count = 0;
        while ((prev_count != current_count)) {
            prev_count = current_count;
            {
                __auto_type i = start;
                while ((i < len)) {
                    if (!(transpiler_index_in_list(emitted, i))) {
                        __auto_type _mv_1269 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1269.has_value) {
                            __auto_type item = _mv_1269.value;
                            if ((transpiler_is_type_def(item) && transpiler_is_struct_type_def(item))) {
                                if (transpiler_type_deps_satisfied(ctx, item)) {
                                    transpiler_emit_pending_container_deps(ctx, item);
                                    transpiler_emit_type_to_header(ctx, item);
                                    ({ __auto_type _lst_p = &(emitted); __auto_type _item = (i); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    current_count = (current_count + 1);
                                    transpiler_emit_option_list_for_type(ctx, item);
                                }
                            }
                        } else if (!_mv_1269.has_value) {
                        }
                    }
                    i = (i + 1);
                }
            }
        }
    }
}

uint8_t transpiler_index_in_list(slop_list_int lst, int64_t idx) {
    {
        __auto_type len = ((int64_t)((lst).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_1270 = ({ __auto_type _lst = lst; size_t _idx = (size_t)i; slop_option_int _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1270.has_value) {
                __auto_type v = _mv_1270.value;
                if ((v == idx)) {
                    found = 1;
                }
            } else if (!_mv_1270.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

uint8_t transpiler_type_deps_satisfied(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type field_types = transpiler_get_type_field_types(ctx, type_def);
        __auto_type len = ((int64_t)((field_types).len));
        __auto_type i = 0;
        __auto_type all_satisfied = 1;
        while (((i < len) && all_satisfied)) {
            __auto_type _mv_1271 = ({ __auto_type _lst = field_types; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1271.has_value) {
                __auto_type field_type = _mv_1271.value;
                if (!(transpiler_type_is_available(ctx, field_type))) {
                    all_satisfied = 0;
                }
            } else if (!_mv_1271.has_value) {
            }
            i = (i + 1);
        }
        return all_satisfied;
    }
}

uint8_t transpiler_type_is_available(context_TranspileContext* ctx, slop_string type_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return ((transpiler_is_primitive_type(type_name)) || (strlib_starts_with(type_name, SLOP_STR("Ptr "))) || (strlib_starts_with(type_name, SLOP_STR("(Ptr"))) || (transpiler_is_slop_runtime_type(type_name)) || (transpiler_is_runtime_option_type(type_name)) || (transpiler_is_runtime_list_type(type_name)) || (transpiler_is_type_emitted_or_primitive(ctx, type_name)) || (transpiler_is_imported_type(ctx, type_name)) || (transpiler_is_emittable_container_type(ctx, type_name)));
}

uint8_t transpiler_is_emittable_container_type(context_TranspileContext* ctx, slop_string type_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (strlib_starts_with(type_name, SLOP_STR("slop_option_"))) {
            {
                __auto_type inner = strlib_substring(arena, type_name, 12, (((int64_t)(type_name.len)) - 12));
                return ((transpiler_is_primitive_type(inner)) || (transpiler_is_type_emitted_or_primitive(ctx, inner)) || (transpiler_is_imported_type(ctx, inner)));
            }
        } else if (strlib_starts_with(type_name, SLOP_STR("slop_list_"))) {
            {
                __auto_type inner = strlib_substring(arena, type_name, 10, (((int64_t)(type_name.len)) - 10));
                return ((transpiler_is_primitive_type(inner)) || (transpiler_is_type_emitted_or_primitive(ctx, inner)) || (transpiler_is_imported_type(ctx, inner)));
            }
        } else {
            return 0;
        }
    }
}

uint8_t transpiler_is_slop_runtime_type(slop_string type_name) {
    return ((strlib_starts_with(type_name, SLOP_STR("slop_"))) && (!(strlib_starts_with(type_name, SLOP_STR("slop_list_")))) && (!(strlib_starts_with(type_name, SLOP_STR("slop_option_")))));
}

uint8_t transpiler_is_primitive_type(slop_string type_name) {
    return ((string_eq(type_name, SLOP_STR("Int"))) || (string_eq(type_name, SLOP_STR("Bool"))) || (string_eq(type_name, SLOP_STR("String"))) || (string_eq(type_name, SLOP_STR("Unit"))) || (string_eq(type_name, SLOP_STR("U8"))) || (string_eq(type_name, SLOP_STR("U16"))) || (string_eq(type_name, SLOP_STR("U32"))) || (string_eq(type_name, SLOP_STR("U64"))) || (string_eq(type_name, SLOP_STR("I8"))) || (string_eq(type_name, SLOP_STR("I16"))) || (string_eq(type_name, SLOP_STR("I32"))) || (string_eq(type_name, SLOP_STR("I64"))) || (string_eq(type_name, SLOP_STR("Float"))) || (string_eq(type_name, SLOP_STR("Double"))) || (string_eq(type_name, SLOP_STR("Char"))) || (string_eq(type_name, SLOP_STR("Arena"))) || (string_eq(type_name, SLOP_STR("int64_t"))) || (string_eq(type_name, SLOP_STR("uint8_t"))) || (string_eq(type_name, SLOP_STR("uint16_t"))) || (string_eq(type_name, SLOP_STR("uint32_t"))) || (string_eq(type_name, SLOP_STR("uint64_t"))) || (string_eq(type_name, SLOP_STR("int8_t"))) || (string_eq(type_name, SLOP_STR("int16_t"))) || (string_eq(type_name, SLOP_STR("int32_t"))) || (string_eq(type_name, SLOP_STR("bool"))) || (string_eq(type_name, SLOP_STR("void"))));
}

slop_list_string transpiler_get_type_field_types(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type result = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        __auto_type _mv_1272 = (*type_def);
        switch (_mv_1272.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1272.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 3)) {
                        __auto_type _mv_1273 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1273.has_value) {
                            __auto_type def_expr = _mv_1273.value;
                            __auto_type _mv_1274 = (*def_expr);
                            switch (_mv_1274.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type def_lst = _mv_1274.data.lst;
                                    {
                                        __auto_type def_items = def_lst.items;
                                        __auto_type def_len = ((int64_t)((def_items).len));
                                        if ((def_len > 0)) {
                                            __auto_type _mv_1275 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1275.has_value) {
                                                __auto_type head = _mv_1275.value;
                                                __auto_type _mv_1276 = (*head);
                                                switch (_mv_1276.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type sym = _mv_1276.data.sym;
                                                        {
                                                            __auto_type kind = sym.name;
                                                            if (string_eq(kind, SLOP_STR("record"))) {
                                                                result = transpiler_extract_record_field_types(ctx, def_items);
                                                            } else if (string_eq(kind, SLOP_STR("union"))) {
                                                                result = transpiler_extract_union_variant_types(ctx, def_items);
                                                            } else {
                                                            }
                                                        }
                                                        break;
                                                    }
                                                    default: {
                                                        break;
                                                    }
                                                }
                                            } else if (!_mv_1275.has_value) {
                                            }
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1273.has_value) {
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

slop_list_string transpiler_extract_record_field_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr def_items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type result = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        __auto_type len = ((int64_t)((def_items).len));
        __auto_type i = 1;
        while ((i < len)) {
            __auto_type _mv_1277 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1277.has_value) {
                __auto_type field_expr = _mv_1277.value;
                __auto_type _mv_1278 = (*field_expr);
                switch (_mv_1278.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type field_lst = _mv_1278.data.lst;
                        if ((((int64_t)((field_lst.items).len)) >= 2)) {
                            __auto_type _mv_1279 = ({ __auto_type _lst = field_lst.items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1279.has_value) {
                                __auto_type type_expr = _mv_1279.value;
                                {
                                    __auto_type type_str = transpiler_get_field_type_string(ctx, type_expr);
                                    if (!(string_eq(type_str, SLOP_STR("")))) {
                                        ({ __auto_type _lst_p = &(result); __auto_type _item = (type_str); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    }
                                }
                            } else if (!_mv_1279.has_value) {
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1277.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_list_string transpiler_extract_union_variant_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr def_items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type result = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        __auto_type len = ((int64_t)((def_items).len));
        __auto_type i = 1;
        while ((i < len)) {
            __auto_type _mv_1280 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1280.has_value) {
                __auto_type variant_expr = _mv_1280.value;
                __auto_type _mv_1281 = (*variant_expr);
                switch (_mv_1281.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type variant_lst = _mv_1281.data.lst;
                        if ((((int64_t)((variant_lst.items).len)) >= 2)) {
                            __auto_type _mv_1282 = ({ __auto_type _lst = variant_lst.items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1282.has_value) {
                                __auto_type type_expr = _mv_1282.value;
                                {
                                    __auto_type type_str = transpiler_get_field_type_string(ctx, type_expr);
                                    if (!(string_eq(type_str, SLOP_STR("")))) {
                                        ({ __auto_type _lst_p = &(result); __auto_type _item = (type_str); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    }
                                }
                            } else if (!_mv_1282.has_value) {
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1280.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_string transpiler_get_field_type_string(context_TranspileContext* ctx, types_SExpr* type_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1283 = (*type_expr);
        switch (_mv_1283.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_1283.data.sym;
                {
                    __auto_type name = sym.name;
                    __auto_type _mv_1284 = context_ctx_lookup_type(ctx, name);
                    if (_mv_1284.has_value) {
                        __auto_type entry = _mv_1284.value;
                        return entry.c_name;
                    } else if (!_mv_1284.has_value) {
                        return ctype_to_c_type(arena, type_expr);
                    }
                }
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1283.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) < 1)) {
                        return SLOP_STR("");
                    } else {
                        __auto_type _mv_1285 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1285.has_value) {
                            __auto_type head = _mv_1285.value;
                            __auto_type _mv_1286 = (*head);
                            switch (_mv_1286.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_1286.data.sym;
                                    {
                                        __auto_type kind = sym.name;
                                        if (string_eq(kind, SLOP_STR("Ptr"))) {
                                            return SLOP_STR("");
                                        } else if (string_eq(kind, SLOP_STR("Option"))) {
                                            if ((((int64_t)((items).len)) >= 2)) {
                                                __auto_type _mv_1287 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1287.has_value) {
                                                    __auto_type inner = _mv_1287.value;
                                                    {
                                                        __auto_type inner_str = transpiler_get_field_type_string(ctx, inner);
                                                        if (string_eq(inner_str, SLOP_STR(""))) {
                                                            return SLOP_STR("");
                                                        } else {
                                                            return context_ctx_str(ctx, SLOP_STR("slop_option_"), ctype_type_to_identifier(arena, inner_str));
                                                        }
                                                    }
                                                } else if (!_mv_1287.has_value) {
                                                    return SLOP_STR("");
                                                }
                                            } else {
                                                return SLOP_STR("");
                                            }
                                        } else if (string_eq(kind, SLOP_STR("List"))) {
                                            if ((((int64_t)((items).len)) >= 2)) {
                                                __auto_type _mv_1288 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1288.has_value) {
                                                    __auto_type inner = _mv_1288.value;
                                                    {
                                                        __auto_type inner_str = transpiler_get_field_type_string(ctx, inner);
                                                        if (string_eq(inner_str, SLOP_STR(""))) {
                                                            return SLOP_STR("");
                                                        } else {
                                                            return context_ctx_str(ctx, SLOP_STR("slop_list_"), ctype_type_to_identifier(arena, inner_str));
                                                        }
                                                    }
                                                } else if (!_mv_1288.has_value) {
                                                    return SLOP_STR("");
                                                }
                                            } else {
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
                        } else if (!_mv_1285.has_value) {
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

void transpiler_emit_option_list_for_type(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type c_name = transpiler_get_type_c_name(ctx, type_def);
        if (!(string_eq(c_name, SLOP_STR("")))) {
            transpiler_emit_option_for_inner_type(ctx, c_name);
            transpiler_emit_list_for_elem_type(ctx, c_name);
        }
    }
}

slop_string transpiler_get_type_c_name(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    __auto_type _mv_1289 = (*type_def);
    switch (_mv_1289.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1289.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 2)) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_1290 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1290.has_value) {
                        __auto_type name_expr = _mv_1290.value;
                        __auto_type _mv_1291 = (*name_expr);
                        switch (_mv_1291.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1291.data.sym;
                                {
                                    __auto_type name = sym.name;
                                    __auto_type _mv_1292 = context_ctx_lookup_type(ctx, name);
                                    if (_mv_1292.has_value) {
                                        __auto_type entry = _mv_1292.value;
                                        return entry.c_name;
                                    } else if (!_mv_1292.has_value) {
                                        return SLOP_STR("");
                                    }
                                }
                            }
                            default: {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_1290.has_value) {
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

void transpiler_emit_option_for_inner_type(context_TranspileContext* ctx, slop_string inner_c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type option_types = context_ctx_get_option_types(ctx);
        __auto_type len = ((int64_t)((option_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1293 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1293.has_value) {
                __auto_type ot = _mv_1293.value;
                if ((string_eq(ot.inner_type, inner_c_name) && !(transpiler_is_pointer_elem_type(ot.inner_type)))) {
                    transpiler_emit_single_option_type_header(ctx, ot);
                }
            } else if (!_mv_1293.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_list_for_elem_type(context_TranspileContext* ctx, slop_string elem_c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type list_types = context_ctx_get_list_types(ctx);
        __auto_type len = ((int64_t)((list_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1294 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1294.has_value) {
                __auto_type lt = _mv_1294.value;
                if ((string_eq(lt.elem_type, elem_c_name) && !(transpiler_is_pointer_elem_type(lt.elem_type)))) {
                    transpiler_emit_single_list_type_header(ctx, lt);
                    transpiler_emit_option_for_inner_type(ctx, lt.c_name);
                }
            } else if (!_mv_1294.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t transpiler_struct_uses_value_list_or_option(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type list_types = context_ctx_get_list_types(ctx);
        __auto_type option_types = context_ctx_get_option_types(ctx);
        __auto_type found = 0;
        {
            __auto_type len = ((int64_t)((list_types).len));
            __auto_type i = 0;
            while (((i < len) && !(found))) {
                __auto_type _mv_1295 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1295.has_value) {
                    __auto_type lt = _mv_1295.value;
                    if ((!(transpiler_is_pointer_elem_type(lt.elem_type)) && transpiler_struct_uses_list_type(ctx, type_def, lt.c_name))) {
                        found = 1;
                    }
                } else if (!_mv_1295.has_value) {
                }
                i = (i + 1);
            }
        }
        if (!(found)) {
            {
                __auto_type len2 = ((int64_t)((option_types).len));
                __auto_type j = 0;
                while (((j < len2) && !(found))) {
                    __auto_type _mv_1296 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)j; slop_option_context_OptionType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1296.has_value) {
                        __auto_type ot = _mv_1296.value;
                        if ((!(transpiler_is_pointer_elem_type(ot.inner_type)) && transpiler_struct_uses_option_type(ctx, type_def, ot.c_name))) {
                            found = 1;
                        }
                    } else if (!_mv_1296.has_value) {
                    }
                    j = (j + 1);
                }
            }
        }
        return found;
    }
}

void transpiler_emit_struct_dependent_list_types(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type list_types = context_ctx_get_list_types(ctx);
        __auto_type len = ((int64_t)((list_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1297 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1297.has_value) {
                __auto_type lt = _mv_1297.value;
                if ((!(transpiler_is_pointer_elem_type(lt.elem_type)) && transpiler_struct_uses_list_type(ctx, type_def, lt.c_name))) {
                    transpiler_emit_single_list_type_header(ctx, lt);
                }
            } else if (!_mv_1297.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_struct_dependent_option_types(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type option_types = context_ctx_get_option_types(ctx);
        __auto_type len = ((int64_t)((option_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1298 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1298.has_value) {
                __auto_type ot = _mv_1298.value;
                if ((!(transpiler_is_pointer_elem_type(ot.inner_type)) && transpiler_struct_uses_option_type(ctx, type_def, ot.c_name))) {
                    transpiler_emit_list_type_if_needed(ctx, ot.inner_type);
                    transpiler_emit_single_option_type_header(ctx, ot);
                }
            } else if (!_mv_1298.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_struct_dependent_list_types_safe(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type list_types = context_ctx_get_list_types(ctx);
        __auto_type len = ((int64_t)((list_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1299 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1299.has_value) {
                __auto_type lt = _mv_1299.value;
                if ((!(transpiler_is_pointer_elem_type(lt.elem_type)) && transpiler_struct_uses_list_type(ctx, type_def, lt.c_name))) {
                    if (transpiler_is_type_emitted_or_primitive(ctx, lt.elem_type)) {
                        transpiler_emit_single_list_type_header(ctx, lt);
                    }
                }
            } else if (!_mv_1299.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_struct_dependent_option_types_safe(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type option_types = context_ctx_get_option_types(ctx);
        __auto_type len = ((int64_t)((option_types).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1300 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1300.has_value) {
                __auto_type ot = _mv_1300.value;
                if ((!(transpiler_is_pointer_elem_type(ot.inner_type)) && transpiler_struct_uses_option_type(ctx, type_def, ot.c_name))) {
                    if (transpiler_is_type_emitted_or_primitive(ctx, ot.inner_type)) {
                        transpiler_emit_list_type_if_needed_safe(ctx, ot.inner_type);
                        transpiler_emit_single_option_type_header(ctx, ot);
                    }
                }
            } else if (!_mv_1300.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t transpiler_is_type_emitted_or_primitive(context_TranspileContext* ctx, slop_string type_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if ((string_eq(type_name, SLOP_STR("int64_t")) || (string_eq(type_name, SLOP_STR("uint8_t")) || (string_eq(type_name, SLOP_STR("int8_t")) || (string_eq(type_name, SLOP_STR("int16_t")) || (string_eq(type_name, SLOP_STR("int32_t")) || (string_eq(type_name, SLOP_STR("uint16_t")) || (string_eq(type_name, SLOP_STR("uint32_t")) || (string_eq(type_name, SLOP_STR("uint64_t")) || (string_eq(type_name, SLOP_STR("double")) || (string_eq(type_name, SLOP_STR("float")) || string_eq(type_name, SLOP_STR("slop_string"))))))))))))) {
        return 1;
    } else {
        if (transpiler_is_imported_type(ctx, type_name)) {
            return 1;
        } else {
            return context_ctx_is_type_emitted(ctx, type_name);
        }
    }
}

uint8_t transpiler_is_imported_type(context_TranspileContext* ctx, slop_string type_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if ((strlib_starts_with(type_name, SLOP_STR("slop_list_")) || strlib_starts_with(type_name, SLOP_STR("slop_option_")))) {
        return 0;
    } else {
        __auto_type _mv_1301 = context_ctx_get_module(ctx);
        if (_mv_1301.has_value) {
            __auto_type current_mod = _mv_1301.value;
            {
                __auto_type arena = (*ctx).arena;
                __auto_type c_mod = ctype_to_c_name(arena, current_mod);
                __auto_type current_prefix = context_ctx_str(ctx, c_mod, SLOP_STR("_"));
                {
                    __auto_type underscore_pos = transpiler_find_char(type_name, ((uint8_t)(95)));
                    if ((underscore_pos > 0)) {
                        return !(strlib_starts_with(type_name, current_prefix));
                    } else {
                        return 0;
                    }
                }
            }
        } else if (!_mv_1301.has_value) {
            return 0;
        }
    }
}

int64_t transpiler_find_char(slop_string s, uint8_t ch) {
    {
        __auto_type data = s.data;
        __auto_type len = ((int64_t)(s.len));
        __auto_type i = 0;
        __auto_type result = -1;
        while (((i < len) && (result < 0))) {
            if ((data[i] == ch)) {
                result = i;
            } else {
                i = (i + 1);
            }
        }
        return result;
    }
}

void transpiler_emit_list_type_if_needed_safe(context_TranspileContext* ctx, slop_string inner_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (strlib_starts_with(inner_type, SLOP_STR("slop_list_"))) {
        {
            __auto_type list_types = context_ctx_get_list_types(ctx);
            __auto_type len = ((int64_t)((list_types).len));
            __auto_type i = 0;
            while ((i < len)) {
                __auto_type _mv_1302 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1302.has_value) {
                    __auto_type lt = _mv_1302.value;
                    if ((string_eq(lt.c_name, inner_type) && transpiler_is_type_emitted_or_primitive(ctx, lt.elem_type))) {
                        transpiler_emit_single_list_type_header(ctx, lt);
                    }
                } else if (!_mv_1302.has_value) {
                }
                i = (i + 1);
            }
        }
    }
}

void transpiler_emit_list_type_if_needed(context_TranspileContext* ctx, slop_string inner_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (strlib_starts_with(inner_type, SLOP_STR("slop_list_"))) {
        {
            __auto_type list_types = context_ctx_get_list_types(ctx);
            __auto_type len = ((int64_t)((list_types).len));
            __auto_type i = 0;
            while ((i < len)) {
                __auto_type _mv_1303 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1303.has_value) {
                    __auto_type lt = _mv_1303.value;
                    if (string_eq(lt.c_name, inner_type)) {
                        transpiler_emit_single_list_type_header(ctx, lt);
                    }
                } else if (!_mv_1303.has_value) {
                }
                i = (i + 1);
            }
        }
    }
}

uint8_t transpiler_struct_uses_list_type(context_TranspileContext* ctx, types_SExpr* type_def, slop_string list_type_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1304 = (*type_def);
        switch (_mv_1304.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1304.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) < 3)) {
                        return 0;
                    } else {
                        __auto_type _mv_1305 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1305.has_value) {
                            __auto_type body_expr = _mv_1305.value;
                            return transpiler_type_body_uses_typename(ctx, body_expr, list_type_name);
                        } else if (!_mv_1305.has_value) {
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
}

uint8_t transpiler_struct_uses_option_type(context_TranspileContext* ctx, types_SExpr* type_def, slop_string option_type_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    return transpiler_struct_uses_list_type(ctx, type_def, option_type_name);
}

uint8_t transpiler_type_body_uses_typename(context_TranspileContext* ctx, types_SExpr* body_expr, slop_string typename) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((body_expr != NULL)), "(!= body-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1306 = (*body_expr);
        switch (_mv_1306.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1306.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    __auto_type found = 0;
                    __auto_type i = 1;
                    while (((i < len) && !(found))) {
                        __auto_type _mv_1307 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1307.has_value) {
                            __auto_type field_expr = _mv_1307.value;
                            if (transpiler_field_uses_typename(ctx, field_expr, typename)) {
                                found = 1;
                            }
                        } else if (!_mv_1307.has_value) {
                        }
                        i = (i + 1);
                    }
                    return found;
                }
            }
            default: {
                return 0;
            }
        }
    }
}

uint8_t transpiler_field_uses_typename(context_TranspileContext* ctx, types_SExpr* field_expr, slop_string typename) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((field_expr != NULL)), "(!= field-expr nil)");
    __auto_type _mv_1308 = (*field_expr);
    switch (_mv_1308.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1308.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 2)) {
                    return 0;
                } else {
                    __auto_type _mv_1309 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1309.has_value) {
                        __auto_type type_expr = _mv_1309.value;
                        {
                            __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                            return string_eq(c_type, typename);
                        }
                    } else if (!_mv_1309.has_value) {
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

void transpiler_emit_type_to_header(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1310 = (*type_def);
        switch (_mv_1310.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1310.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len >= 3)) {
                        __auto_type _mv_1311 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1311.has_value) {
                            __auto_type name_expr = _mv_1311.value;
                            __auto_type _mv_1312 = (*name_expr);
                            switch (_mv_1312.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_1312.data.sym;
                                    {
                                        __auto_type type_name = name_sym.name;
                                        __auto_type base_name = ctype_to_c_name(arena, type_name);
                                        __auto_type c_name = ((context_ctx_prefixing_enabled(ctx)) ? ({ __auto_type _mv = context_ctx_get_module(ctx); _mv.has_value ? ({ __auto_type mod_name = _mv.value; context_ctx_str(ctx, ctype_to_c_name(arena, mod_name), context_ctx_str(ctx, SLOP_STR("_"), base_name)); }) : (base_name); }) : base_name);
                                        __auto_type _mv_1313 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1313.has_value) {
                                            __auto_type body_expr = _mv_1313.value;
                                            transpiler_emit_type_body_to_header(ctx, type_name, c_name, body_expr);
                                            context_ctx_mark_type_emitted(ctx, c_name);
                                        } else if (!_mv_1313.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1311.has_value) {
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

void transpiler_emit_type_body_to_header(context_TranspileContext* ctx, slop_string raw_type_name, slop_string c_name, types_SExpr* body_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((body_expr != NULL)), "(!= body-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1314 = (*body_expr);
        switch (_mv_1314.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1314.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) < 1)) {
                    } else {
                        __auto_type _mv_1315 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1315.has_value) {
                            __auto_type kind_expr = _mv_1315.value;
                            __auto_type _mv_1316 = (*kind_expr);
                            switch (_mv_1316.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type kind_sym = _mv_1316.data.sym;
                                    {
                                        __auto_type kind = kind_sym.name;
                                        if (string_eq(kind, SLOP_STR("enum"))) {
                                            transpiler_emit_enum_to_header(ctx, c_name, items);
                                        } else if (string_eq(kind, SLOP_STR("record"))) {
                                            transpiler_emit_struct_to_header(ctx, raw_type_name, c_name, items);
                                        } else if (string_eq(kind, SLOP_STR("union"))) {
                                            transpiler_emit_union_to_header(ctx, c_name, items);
                                        } else {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1315.has_value) {
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

void transpiler_emit_enum_to_header(context_TranspileContext* ctx, slop_string c_name, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 1;
        context_ctx_emit_header(ctx, SLOP_STR("typedef enum {"));
        while ((i < len)) {
            __auto_type _mv_1317 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1317.has_value) {
                __auto_type variant_expr = _mv_1317.value;
                __auto_type _mv_1318 = (*variant_expr);
                switch (_mv_1318.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type variant_sym = _mv_1318.data.sym;
                        {
                            __auto_type variant_name = variant_sym.name;
                            __auto_type c_variant = context_ctx_str3(ctx, c_name, SLOP_STR("_"), ctype_to_c_name(arena, variant_name));
                            __auto_type is_last = (i == (len - 1));
                            if (is_last) {
                                context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("    "), c_variant));
                            } else {
                                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    "), c_variant, SLOP_STR(",")));
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1317.has_value) {
            }
            i = (i + 1);
        }
        context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("} "), c_name, SLOP_STR(";")));
        context_ctx_emit_header(ctx, SLOP_STR(""));
        context_ctx_mark_type_emitted(ctx, c_name);
    }
}

void transpiler_emit_struct_to_header(context_TranspileContext* ctx, slop_string raw_type_name, slop_string c_name, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 1;
        context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("struct "), c_name, SLOP_STR(" {")));
        while ((i < len)) {
            __auto_type _mv_1319 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1319.has_value) {
                __auto_type field_expr = _mv_1319.value;
                transpiler_emit_field_to_header(ctx, raw_type_name, c_name, field_expr);
            } else if (!_mv_1319.has_value) {
            }
            i = (i + 1);
        }
        context_ctx_emit_header(ctx, SLOP_STR("};"));
        context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("typedef struct "), c_name, SLOP_STR(" "), context_ctx_str(ctx, c_name, SLOP_STR(";"))));
        context_ctx_emit_header(ctx, SLOP_STR(""));
    }
}

void transpiler_emit_field_to_header(context_TranspileContext* ctx, slop_string raw_type_name, slop_string c_type_name, types_SExpr* field_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((field_expr != NULL)), "(!= field-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1320 = (*field_expr);
        switch (_mv_1320.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1320.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 2)) {
                        __auto_type _mv_1321 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1321.has_value) {
                            __auto_type name_expr = _mv_1321.value;
                            __auto_type _mv_1322 = (*name_expr);
                            switch (_mv_1322.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_1322.data.sym;
                                    {
                                        __auto_type field_name = name_sym.name;
                                        __auto_type c_field_name = ctype_to_c_name(arena, field_name);
                                        __auto_type _mv_1323 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1323.has_value) {
                                            __auto_type type_expr = _mv_1323.value;
                                            {
                                                __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                                                __auto_type is_ptr = transpiler_is_pointer_type_expr_header(type_expr);
                                                context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("    "), c_type, SLOP_STR(" "), context_ctx_str(ctx, c_field_name, SLOP_STR(";"))));
                                                context_ctx_register_field_type(ctx, raw_type_name, field_name, c_type, slop_type_str, is_ptr);
                                                context_ctx_register_field_type(ctx, c_type_name, field_name, c_type, slop_type_str, is_ptr);
                                            }
                                        } else if (!_mv_1323.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1321.has_value) {
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

uint8_t transpiler_is_pointer_type_expr_header(types_SExpr* type_expr) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_1324 = (*type_expr);
    switch (_mv_1324.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1324.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_1325 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1325.has_value) {
                        __auto_type head = _mv_1325.value;
                        __auto_type _mv_1326 = (*head);
                        switch (_mv_1326.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1326.data.sym;
                                return string_eq(sym.name, SLOP_STR("Ptr"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1325.has_value) {
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

void transpiler_emit_union_to_header(context_TranspileContext* ctx, slop_string c_name, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type tag_name = context_ctx_str(ctx, c_name, SLOP_STR("_tag"));
        context_ctx_emit_header(ctx, SLOP_STR("typedef enum {"));
        {
            __auto_type i = 1;
            while ((i < len)) {
                __auto_type _mv_1327 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1327.has_value) {
                    __auto_type variant_expr = _mv_1327.value;
                    {
                        __auto_type variant_name = transpiler_get_variant_name(variant_expr);
                        __auto_type c_variant = context_ctx_str3(ctx, c_name, SLOP_STR("_"), ctype_to_c_name(arena, variant_name));
                        __auto_type is_last = (i == (len - 1));
                        if (is_last) {
                            context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("    "), c_variant));
                        } else {
                            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    "), c_variant, SLOP_STR(",")));
                        }
                    }
                } else if (!_mv_1327.has_value) {
                }
                i = (i + 1);
            }
        }
        context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("} "), tag_name, SLOP_STR(";")));
        context_ctx_emit_header(ctx, SLOP_STR(""));
        context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("struct "), c_name, SLOP_STR(" {")));
        context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("    "), context_ctx_str(ctx, tag_name, SLOP_STR(" tag;"))));
        context_ctx_emit_header(ctx, SLOP_STR("    union {"));
        {
            __auto_type i = 1;
            while ((i < len)) {
                __auto_type _mv_1328 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1328.has_value) {
                    __auto_type variant_expr = _mv_1328.value;
                    transpiler_emit_union_variant_to_header(ctx, variant_expr);
                } else if (!_mv_1328.has_value) {
                }
                i = (i + 1);
            }
        }
        context_ctx_emit_header(ctx, SLOP_STR("    } data;"));
        context_ctx_emit_header(ctx, SLOP_STR("};"));
        context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("typedef struct "), c_name, SLOP_STR(" "), context_ctx_str(ctx, c_name, SLOP_STR(";"))));
        context_ctx_emit_header(ctx, SLOP_STR(""));
    }
}

slop_string transpiler_get_variant_name(types_SExpr* variant_expr) {
    SLOP_PRE(((variant_expr != NULL)), "(!= variant-expr nil)");
    __auto_type _mv_1329 = (*variant_expr);
    switch (_mv_1329.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1329.data.sym;
            return sym.name;
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1329.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return SLOP_STR("unknown");
                } else {
                    __auto_type _mv_1330 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1330.has_value) {
                        __auto_type name_expr = _mv_1330.value;
                        __auto_type _mv_1331 = (*name_expr);
                        switch (_mv_1331.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type name_sym = _mv_1331.data.sym;
                                return name_sym.name;
                            }
                            default: {
                                return SLOP_STR("unknown");
                            }
                        }
                    } else if (!_mv_1330.has_value) {
                        return SLOP_STR("unknown");
                    }
                }
            }
        }
        default: {
            return SLOP_STR("unknown");
        }
    }
}

void transpiler_emit_union_variant_to_header(context_TranspileContext* ctx, types_SExpr* variant_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((variant_expr != NULL)), "(!= variant-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1332 = (*variant_expr);
        switch (_mv_1332.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_1332.data.sym;
                break;
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1332.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 2)) {
                        __auto_type _mv_1333 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1333.has_value) {
                            __auto_type name_expr = _mv_1333.value;
                            __auto_type _mv_1334 = (*name_expr);
                            switch (_mv_1334.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_1334.data.sym;
                                    {
                                        __auto_type variant_name = name_sym.name;
                                        __auto_type c_field = ctype_to_c_name(arena, variant_name);
                                        __auto_type _mv_1335 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1335.has_value) {
                                            __auto_type type_expr = _mv_1335.value;
                                            {
                                                __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                {
                                                    __auto_type actual_type = ((string_eq(c_type, SLOP_STR("void"))) ? SLOP_STR("int") : c_type);
                                                    context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("        "), actual_type, SLOP_STR(" "), context_ctx_str(ctx, c_field, SLOP_STR(";"))));
                                                }
                                            }
                                        } else if (!_mv_1335.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1333.has_value) {
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

void transpiler_emit_module_consts(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start, slop_list_string exports) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        __auto_type emitted_any = 0;
        while ((i < len)) {
            __auto_type _mv_1336 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1336.has_value) {
                __auto_type item = _mv_1336.value;
                if (transpiler_is_const_def(item)) {
                    {
                        __auto_type const_name = transpiler_get_const_name(item);
                        __auto_type is_exported = transpiler_list_contains_str(exports, const_name);
                        defn_transpile_const(ctx, item, is_exported);
                    }
                    emitted_any = 1;
                }
            } else if (!_mv_1336.has_value) {
            }
            i = (i + 1);
        }
        if (emitted_any) {
            context_ctx_emit(ctx, SLOP_STR(""));
        }
    }
}

slop_string transpiler_get_const_name(types_SExpr* item) {
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1337 = (*item);
    switch (_mv_1337.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1337.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 2)) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_1338 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1338.has_value) {
                        __auto_type name_expr = _mv_1338.value;
                        __auto_type _mv_1339 = (*name_expr);
                        switch (_mv_1339.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1339.data.sym;
                                return sym.name;
                            }
                            default: {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_1338.has_value) {
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

void transpiler_emit_module_consts_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start, slop_list_string exports) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        __auto_type emitted_any = 0;
        while ((i < len)) {
            __auto_type _mv_1340 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1340.has_value) {
                __auto_type item = _mv_1340.value;
                if (transpiler_is_const_def(item)) {
                    if (transpiler_emit_const_header_if_exported(ctx, item, exports)) {
                        emitted_any = 1;
                    }
                }
            } else if (!_mv_1340.has_value) {
            }
            i = (i + 1);
        }
        if (emitted_any) {
            context_ctx_emit_header(ctx, SLOP_STR(""));
        }
    }
}

uint8_t transpiler_emit_const_header_if_exported(context_TranspileContext* ctx, types_SExpr* item, slop_list_string exports) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1341 = (*item);
    switch (_mv_1341.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1341.data.lst;
            {
                __auto_type const_items = lst.items;
                if ((((int64_t)((const_items).len)) < 4)) {
                    return 0;
                } else {
                    __auto_type _mv_1342 = ({ __auto_type _lst = const_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1342.has_value) {
                        __auto_type name_expr = _mv_1342.value;
                        __auto_type _mv_1343 = (*name_expr);
                        switch (_mv_1343.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type name_sym = _mv_1343.data.sym;
                                {
                                    __auto_type raw_name = name_sym.name;
                                    if (!(transpiler_list_contains_str(exports, raw_name))) {
                                        return 0;
                                    } else {
                                        __auto_type _mv_1344 = ({ __auto_type _lst = const_items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1344.has_value) {
                                            __auto_type type_expr = _mv_1344.value;
                                            transpiler_emit_const_header_decl(ctx, raw_name, type_expr, ({ __auto_type _mv = ({ __auto_type _lst = const_items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type v = _mv.value; v; }) : (NULL); }));
                                            return 1;
                                        } else if (!_mv_1344.has_value) {
                                            return 0;
                                        }
                                    }
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1342.has_value) {
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

void transpiler_emit_const_header_decl(context_TranspileContext* ctx, slop_string raw_name, types_SExpr* type_expr, types_SExpr* value_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
        __auto_type base_name = ctype_to_c_name(arena, raw_name);
        __auto_type c_name = context_ctx_prefix_type(ctx, base_name);
        __auto_type type_name = defn_get_type_name_str(type_expr);
        if (transpiler_is_const_int_type(type_name)) {
            if ((value_expr != NULL)) {
                {
                    __auto_type value_c = defn_eval_const_value(ctx, value_expr);
                    context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("#define "), c_name, SLOP_STR(" ("), context_ctx_str(ctx, value_c, SLOP_STR(")"))));
                }
            }
        } else {
            context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("extern const "), c_type, SLOP_STR(" "), context_ctx_str(ctx, c_name, SLOP_STR(";"))));
        }
    }
}

uint8_t transpiler_is_const_int_type(slop_string type_name) {
    return ((string_eq(type_name, SLOP_STR("Int"))) || (string_eq(type_name, SLOP_STR("I8"))) || (string_eq(type_name, SLOP_STR("I16"))) || (string_eq(type_name, SLOP_STR("I32"))) || (string_eq(type_name, SLOP_STR("I64"))) || (string_eq(type_name, SLOP_STR("U8"))) || (string_eq(type_name, SLOP_STR("U16"))) || (string_eq(type_name, SLOP_STR("U32"))) || (string_eq(type_name, SLOP_STR("U64"))));
}

uint8_t transpiler_is_const_def(types_SExpr* item) {
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    return defn_is_const_form(item);
}

void transpiler_emit_module_functions(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        context_ctx_start_function_buffer(ctx);
        while ((i < len)) {
            __auto_type _mv_1345 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1345.has_value) {
                __auto_type item = _mv_1345.value;
                if (transpiler_is_fn_def(item)) {
                    defn_transpile_function(ctx, item);
                }
            } else if (!_mv_1345.has_value) {
            }
            i = (i + 1);
        }
        context_ctx_stop_function_buffer(ctx);
        transpiler_emit_all_lambdas(ctx);
        context_ctx_flush_function_buffer(ctx);
    }
}

void transpiler_emit_all_lambdas(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type lambdas = context_ctx_get_deferred_lambdas(ctx);
        __auto_type count = ((int64_t)((lambdas).len));
        __auto_type i = 0;
        if ((count > 0)) {
            while ((i < count)) {
                __auto_type _mv_1346 = ({ __auto_type _lst = lambdas; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1346.has_value) {
                    __auto_type lambda_code = _mv_1346.value;
                    context_ctx_emit(ctx, lambda_code);
                    context_ctx_emit(ctx, SLOP_STR(""));
                } else if (!_mv_1346.has_value) {
                }
                i = (i + 1);
            }
            context_ctx_clear_deferred_lambdas(ctx);
        }
    }
}

slop_string transpiler_generate_c_output(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type output_lines = context_ctx_get_output(ctx);
        __auto_type len = ((int64_t)((output_lines).len));
        __auto_type result = SLOP_STR("");
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_1347 = ({ __auto_type _lst = output_lines; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1347.has_value) {
                __auto_type line = _mv_1347.value;
                result = context_ctx_str3(ctx, result, line, SLOP_STR("\n"));
            } else if (!_mv_1347.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

void transpiler_transpile_file(context_TranspileContext* ctx, slop_list_types_SExpr_ptr exprs) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((exprs).len));
        __auto_type i = 0;
        if (((len > 0) && transpiler_is_module_expr(exprs))) {
            __auto_type _mv_1348 = ({ __auto_type _lst = exprs; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1348.has_value) {
                __auto_type module_expr = _mv_1348.value;
                transpiler_transpile_module(ctx, module_expr);
            } else if (!_mv_1348.has_value) {
            }
        } else {
            emit_emit_standard_includes(ctx);
            context_ctx_emit(ctx, SLOP_STR(""));
            transpiler_prescan_module(ctx, exprs);
            transpiler_emit_all_types(ctx, exprs);
            transpiler_emit_all_functions(ctx, exprs);
        }
    }
}

uint8_t transpiler_is_module_expr(slop_list_types_SExpr_ptr exprs) {
    if ((((int64_t)((exprs).len)) < 1)) {
        return 0;
    } else {
        __auto_type _mv_1349 = ({ __auto_type _lst = exprs; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1349.has_value) {
            __auto_type first = _mv_1349.value;
            __auto_type _mv_1350 = (*first);
            switch (_mv_1350.tag) {
                case types_SExpr_lst:
                {
                    __auto_type lst = _mv_1350.data.lst;
                    {
                        __auto_type items = lst.items;
                        if ((((int64_t)((items).len)) < 1)) {
                            return 0;
                        } else {
                            __auto_type _mv_1351 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1351.has_value) {
                                __auto_type head = _mv_1351.value;
                                __auto_type _mv_1352 = (*head);
                                switch (_mv_1352.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1352.data.sym;
                                        return string_eq(sym.name, SLOP_STR("module"));
                                    }
                                    default: {
                                        return 0;
                                    }
                                }
                            } else if (!_mv_1351.has_value) {
                                return 0;
                            }
                        }
                    }
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_1349.has_value) {
            return 0;
        }
    }
}

