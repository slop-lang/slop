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
slop_string transpiler_alias_target_c_type(context_TranspileContext* ctx, types_SExpr* type_def);
slop_string transpiler_alias_own_c_name(context_TranspileContext* ctx, types_SExpr* type_def);
uint8_t transpiler_container_alias_ready(context_TranspileContext* ctx, types_SExpr* type_def);
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
void transpiler_emit_late_registered_list_types_header(context_TranspileContext* ctx);
void transpiler_emit_late_registered_option_types_header(context_TranspileContext* ctx);
void transpiler_emit_value_list_types_header(context_TranspileContext* ctx);
void transpiler_emit_complex_value_list_types_header(context_TranspileContext* ctx);
void transpiler_emit_struct_hash_eq(context_TranspileContext* ctx, slop_string c_type);
void transpiler_emit_union_payload_hash_eq(context_TranspileContext* ctx, slop_list_context_UnionVariantEntry variants);
void transpiler_emit_record_field_dependencies(context_TranspileContext* ctx, slop_list_context_FieldEntry fields);
uint8_t transpiler_is_primitive_slop_type(slop_string slop_type);
uint8_t transpiler_is_range_type_alias(context_TranspileContext* ctx, slop_string slop_type);
uint8_t transpiler_is_unsigned_payload_type(slop_string slop_type);
uint8_t transpiler_is_narrow_signed_payload_type(slop_string slop_type);
slop_string transpiler_resolve_payload_slop_type(context_TranspileContext* ctx, slop_string slop_type);
void transpiler_container_payload_error(context_TranspileContext* ctx, slop_string slop_type, slop_string c_payload_type);
slop_string transpiler_payload_hash_expr(context_TranspileContext* ctx, slop_string raw_slop_type, slop_string c_payload_type, slop_string access);
slop_string transpiler_payload_eq_expr(context_TranspileContext* ctx, slop_string raw_slop_type, slop_string c_payload_type, slop_string a_access, slop_string b_access);
slop_list_transpiler_PayloadSlot transpiler_union_variant_payloads(context_TranspileContext* ctx, slop_string union_name, slop_string variant_name);
void transpiler_emit_union_hash_fn(context_TranspileContext* ctx, slop_string c_type, slop_list_context_UnionVariantEntry variants);
void transpiler_emit_union_variant_hash(context_TranspileContext* ctx, slop_string union_name, context_UnionVariantEntry variant);
void transpiler_emit_multi_payload_hash(context_TranspileContext* ctx, slop_string c_variant_name, slop_list_transpiler_PayloadSlot payloads);
void transpiler_emit_union_eq_fn(context_TranspileContext* ctx, slop_string c_type, slop_list_context_UnionVariantEntry variants);
void transpiler_emit_union_variant_eq(context_TranspileContext* ctx, slop_string union_name, context_UnionVariantEntry variant);
void transpiler_emit_multi_payload_eq(context_TranspileContext* ctx, slop_string c_variant_name, slop_list_transpiler_PayloadSlot payloads);
void transpiler_emit_struct_hash_fn(context_TranspileContext* ctx, slop_string c_type, slop_list_context_FieldEntry fields);
void transpiler_emit_field_hash(context_TranspileContext* ctx, context_FieldEntry field);
void transpiler_emit_struct_eq_fn(context_TranspileContext* ctx, slop_string c_type, slop_list_context_FieldEntry fields);
void transpiler_emit_field_eq(context_TranspileContext* ctx, context_FieldEntry field);
void transpiler_emit_struct_key_types_header(context_TranspileContext* ctx);
void transpiler_emit_late_registered_struct_key_types_header(context_TranspileContext* ctx);
uint8_t transpiler_is_pointer_elem_type(slop_string elem_type);
void transpiler_emit_single_list_type_header(context_TranspileContext* ctx, context_ListType lt);
void transpiler_emit_list_type_declare_only(context_TranspileContext* ctx, context_ListType lt);
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
uint8_t transpiler_has_unemitted_struct_types(slop_list_types_SExpr_ptr items, int64_t start, int64_t len, slop_list_int emitted);
void transpiler_break_list_cycles(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start, int64_t len, slop_list_int emitted);
slop_list_string transpiler_find_blocking_list_deps(context_TranspileContext* ctx, types_SExpr* type_def);
void transpiler_emit_list_declare_by_c_name(context_TranspileContext* ctx, slop_string c_name);
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
        int64_t i = 3;
        __auto_type result_is_generic = 0;
        __auto_type result_type_params = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        while (i < len) {
            __auto_type _mv_1264 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1264.has_value) {
                __auto_type item = _mv_1264.value;
                __auto_type _mv_1265 = (*item);
                switch (_mv_1265.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type lst = _mv_1265.data.lst;
                        {
                            __auto_type sub_items = lst.items;
                            if (((int64_t)((sub_items).len)) >= 1) {
                                __auto_type _mv_1266 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1266.has_value) {
                                    __auto_type head = _mv_1266.value;
                                    __auto_type _mv_1267 = (*head);
                                    switch (_mv_1267.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_1267.data.sym;
                                            if (string_eq(sym.name, SLOP_STR("@generic"))) {
                                                if (((int64_t)((sub_items).len)) >= 2) {
                                                    __auto_type _mv_1268 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_1268.has_value) {
                                                        __auto_type params_expr = _mv_1268.value;
                                                        __auto_type _mv_1269 = (*params_expr);
                                                        switch (_mv_1269.tag) {
                                                            case types_SExpr_lst:
                                                            {
                                                                __auto_type params_lst = _mv_1269.data.lst;
                                                                {
                                                                    __auto_type param_items = params_lst.items;
                                                                    __auto_type param_len = ((int64_t)((param_items).len));
                                                                    __auto_type j = 0;
                                                                    while (j < param_len) {
                                                                        __auto_type _mv_1270 = ({ __auto_type _lst = param_items; size_t _idx = (size_t)j; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                        if (_mv_1270.has_value) {
                                                                            __auto_type param = _mv_1270.value;
                                                                            __auto_type _mv_1271 = (*param);
                                                                            switch (_mv_1271.tag) {
                                                                                case types_SExpr_sym:
                                                                                {
                                                                                    __auto_type param_sym = _mv_1271.data.sym;
                                                                                    ({ __auto_type _lst_p = &(result_type_params); __auto_type _item = (param_sym.name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                                                    break;
                                                                                }
                                                                                default: {
                                                                                    break;
                                                                                }
                                                                            }
                                                                        } else if (!_mv_1270.has_value) {
                                                                        }
                                                                        j = (j + 1);
                                                                    }
                                                                }
                                                                break;
                                                            }
                                                            case types_SExpr_sym:
                                                            {
                                                                __auto_type single_sym = _mv_1269.data.sym;
                                                                ({ __auto_type _lst_p = &(result_type_params); __auto_type _item = (single_sym.name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                                break;
                                                            }
                                                            default: {
                                                                break;
                                                            }
                                                        }
                                                    } else if (!_mv_1268.has_value) {
                                                    }
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_1266.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1264.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1272 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1272.has_value) {
                __auto_type item = _mv_1272.value;
                transpiler_prescan_top_level(ctx, item);
            } else if (!_mv_1272.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_prescan_top_level(context_TranspileContext* ctx, types_SExpr* item) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1273 = (*item);
    switch (_mv_1273.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1273.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) >= 1) {
                    __auto_type _mv_1274 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1274.has_value) {
                        __auto_type head = _mv_1274.value;
                        __auto_type _mv_1275 = (*head);
                        switch (_mv_1275.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1275.data.sym;
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
                    } else if (!_mv_1274.has_value) {
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
        if (((int64_t)((items).len)) >= 2) {
            __auto_type _mv_1276 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1276.has_value) {
                __auto_type name_expr = _mv_1276.value;
                __auto_type _mv_1277 = (*name_expr);
                switch (_mv_1277.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_1277.data.sym;
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
                                if (is_record || is_union) {
                                    if (((int64_t)((items).len)) >= 3) {
                                        __auto_type _mv_1278 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1278.has_value) {
                                            __auto_type def_expr = _mv_1278.value;
                                            __auto_type _mv_1279 = (*def_expr);
                                            switch (_mv_1279.tag) {
                                                case types_SExpr_lst:
                                                {
                                                    __auto_type def_lst = _mv_1279.data.lst;
                                                    transpiler_scan_record_fields_for_generics(ctx, def_lst.items);
                                                    break;
                                                }
                                                default: {
                                                    break;
                                                }
                                            }
                                        } else if (!_mv_1278.has_value) {
                                        }
                                    }
                                    {
                                        __auto_type type_id = ctype_type_to_identifier(arena, c_name);
                                        __auto_type option_c_name = context_ctx_str(ctx, SLOP_STR("slop_option_"), type_id);
                                        context_ctx_register_option_type(ctx, c_name, option_c_name);
                                    }
                                }
                                if (((int64_t)((items).len)) >= 3) {
                                    __auto_type _mv_1280 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_1280.has_value) {
                                        __auto_type body_expr = _mv_1280.value;
                                        transpiler_check_and_register_result_alias(ctx, type_name, body_expr);
                                        {
                                            __auto_type slop_type_str = parser_pretty_print(arena, body_expr);
                                            if (defn_is_generic_type_alias(slop_type_str)) {
                                                context_ctx_register_type_alias(ctx, type_name, slop_type_str);
                                                if (!(string_eq(c_name, type_name))) {
                                                    context_ctx_register_type_alias(ctx, c_name, slop_type_str);
                                                }
                                            }
                                            transpiler_scan_type_for_generics(ctx, body_expr);
                                        }
                                    } else if (!_mv_1280.has_value) {
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
            } else if (!_mv_1276.has_value) {
            }
        }
    }
}

void transpiler_register_enum_variants(context_TranspileContext* ctx, slop_string enum_name, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (((int64_t)((items).len)) >= 3) {
        __auto_type _mv_1281 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1281.has_value) {
            __auto_type def_expr = _mv_1281.value;
            __auto_type _mv_1282 = (*def_expr);
            switch (_mv_1282.tag) {
                case types_SExpr_lst:
                {
                    __auto_type def_lst = _mv_1282.data.lst;
                    {
                        __auto_type def_items = def_lst.items;
                        __auto_type len = ((int64_t)((def_items).len));
                        __auto_type i = 1;
                        while (i < len) {
                            __auto_type _mv_1283 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1283.has_value) {
                                __auto_type variant_expr = _mv_1283.value;
                                __auto_type _mv_1284 = (*variant_expr);
                                switch (_mv_1284.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1284.data.sym;
                                        context_ctx_register_enum_variant(ctx, sym.name, enum_name);
                                        break;
                                    }
                                    case types_SExpr_lst:
                                    {
                                        __auto_type variant_lst = _mv_1284.data.lst;
                                        if (((int64_t)((variant_lst.items).len)) > 0) {
                                            __auto_type _mv_1285 = ({ __auto_type _lst = variant_lst.items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1285.has_value) {
                                                __auto_type name_expr = _mv_1285.value;
                                                __auto_type _mv_1286 = (*name_expr);
                                                switch (_mv_1286.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type name_sym = _mv_1286.data.sym;
                                                        context_ctx_register_enum_variant(ctx, name_sym.name, enum_name);
                                                        break;
                                                    }
                                                    default: {
                                                        break;
                                                    }
                                                }
                                            } else if (!_mv_1285.has_value) {
                                            }
                                        }
                                        break;
                                    }
                                    default: {
                                        break;
                                    }
                                }
                            } else if (!_mv_1283.has_value) {
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
        } else if (!_mv_1281.has_value) {
        }
    }
}

void transpiler_register_union_variants(context_TranspileContext* ctx, slop_string union_name, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (((int64_t)((items).len)) >= 3) {
            __auto_type _mv_1287 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1287.has_value) {
                __auto_type def_expr = _mv_1287.value;
                __auto_type _mv_1288 = (*def_expr);
                switch (_mv_1288.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type def_lst = _mv_1288.data.lst;
                        {
                            __auto_type def_items = def_lst.items;
                            __auto_type len = ((int64_t)((def_items).len));
                            __auto_type i = 1;
                            while (i < len) {
                                __auto_type _mv_1289 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1289.has_value) {
                                    __auto_type variant_expr = _mv_1289.value;
                                    __auto_type _mv_1290 = (*variant_expr);
                                    switch (_mv_1290.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_1290.data.sym;
                                            {
                                                __auto_type variant_name = sym.name;
                                                context_ctx_register_enum_variant(ctx, variant_name, union_name);
                                                context_ctx_register_union_variant(ctx, variant_name, union_name, ctype_to_c_name(arena, variant_name), SLOP_STR(""), SLOP_STR(""));
                                            }
                                            break;
                                        }
                                        case types_SExpr_lst:
                                        {
                                            __auto_type variant_lst = _mv_1290.data.lst;
                                            {
                                                __auto_type vl_items = variant_lst.items;
                                                __auto_type vl_len = ((int64_t)((vl_items).len));
                                                if (vl_len >= 2) {
                                                    __auto_type _mv_1291 = ({ __auto_type _lst = vl_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_1291.has_value) {
                                                        __auto_type name_expr = _mv_1291.value;
                                                        __auto_type _mv_1292 = (*name_expr);
                                                        switch (_mv_1292.tag) {
                                                            case types_SExpr_sym:
                                                            {
                                                                __auto_type name_sym = _mv_1292.data.sym;
                                                                {
                                                                    __auto_type variant_name = name_sym.name;
                                                                    __auto_type c_variant_name = ctype_to_c_name(arena, variant_name);
                                                                    context_ctx_register_enum_variant(ctx, variant_name, union_name);
                                                                    __auto_type _mv_1293 = ({ __auto_type _lst = vl_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                    if (_mv_1293.has_value) {
                                                                        __auto_type type_expr = _mv_1293.value;
                                                                        {
                                                                            __auto_type slop_type = parser_pretty_print(arena, type_expr);
                                                                            __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                                            __auto_type is_ptr = transpiler_is_pointer_type_expr_header(type_expr);
                                                                            context_ctx_register_union_variant(ctx, variant_name, union_name, c_variant_name, slop_type, c_type);
                                                                            context_ctx_register_field_type(ctx, union_name, variant_name, c_type, slop_type, is_ptr);
                                                                        }
                                                                    } else if (!_mv_1293.has_value) {
                                                                        context_ctx_register_union_variant(ctx, variant_name, union_name, c_variant_name, SLOP_STR(""), SLOP_STR(""));
                                                                    }
                                                                    if (vl_len >= 3) {
                                                                        {
                                                                            __auto_type count_key = context_ctx_str3(ctx, variant_name, SLOP_STR("__count"), SLOP_STR(""));
                                                                            __auto_type count_str = int_to_string(arena, (vl_len - 1));
                                                                            context_ctx_register_field_type(ctx, union_name, count_key, count_str, SLOP_STR(""), 0);
                                                                        }
                                                                        for (int64_t fi = 1; fi < vl_len; fi++) {
                                                                            __auto_type _mv_1294 = ({ __auto_type _lst = vl_items; size_t _idx = (size_t)fi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                            if (_mv_1294.has_value) {
                                                                                __auto_type type_expr = _mv_1294.value;
                                                                                {
                                                                                    __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                                                    __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                                                                                    __auto_type is_ptr = transpiler_is_pointer_type_expr_header(type_expr);
                                                                                    __auto_type field_key = context_ctx_str3(ctx, variant_name, SLOP_STR("__"), int_to_string(arena, (fi - 1)));
                                                                                    context_ctx_register_field_type(ctx, union_name, field_key, c_type, slop_type_str, is_ptr);
                                                                                }
                                                                            } else if (!_mv_1294.has_value) {
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
                                                    } else if (!_mv_1291.has_value) {
                                                    }
                                                } else {
                                                    if (((int64_t)((vl_items).len)) == 1) {
                                                        __auto_type _mv_1295 = ({ __auto_type _lst = vl_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                        if (_mv_1295.has_value) {
                                                            __auto_type name_expr = _mv_1295.value;
                                                            __auto_type _mv_1296 = (*name_expr);
                                                            switch (_mv_1296.tag) {
                                                                case types_SExpr_sym:
                                                                {
                                                                    __auto_type name_sym = _mv_1296.data.sym;
                                                                    {
                                                                        __auto_type variant_name = name_sym.name;
                                                                        context_ctx_register_enum_variant(ctx, variant_name, union_name);
                                                                        context_ctx_register_union_variant(ctx, variant_name, union_name, ctype_to_c_name(arena, variant_name), SLOP_STR(""), SLOP_STR(""));
                                                                    }
                                                                    break;
                                                                }
                                                                default: {
                                                                    break;
                                                                }
                                                            }
                                                        } else if (!_mv_1295.has_value) {
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
                                } else if (!_mv_1289.has_value) {
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
            } else if (!_mv_1287.has_value) {
            }
        }
    }
}

void transpiler_prescan_fn(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (((int64_t)((items).len)) >= 2) {
            __auto_type _mv_1297 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1297.has_value) {
                __auto_type name_expr = _mv_1297.value;
                __auto_type _mv_1298 = (*name_expr);
                switch (_mv_1298.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_1298.data.sym;
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
            } else if (!_mv_1297.has_value) {
            }
        }
    }
}

uint8_t transpiler_fn_returns_string(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 3;
        uint8_t result = 0;
        while ((i < len) && !(result)) {
            __auto_type _mv_1299 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1299.has_value) {
                __auto_type item = _mv_1299.value;
                __auto_type _mv_1300 = (*item);
                switch (_mv_1300.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type lst = _mv_1300.data.lst;
                        {
                            __auto_type sub_items = lst.items;
                            if (((int64_t)((sub_items).len)) >= 2) {
                                __auto_type _mv_1301 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1301.has_value) {
                                    __auto_type head = _mv_1301.value;
                                    __auto_type _mv_1302 = (*head);
                                    switch (_mv_1302.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_1302.data.sym;
                                            if (string_eq(sym.name, SLOP_STR("@spec"))) {
                                                __auto_type _mv_1303 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1303.has_value) {
                                                    __auto_type spec_body = _mv_1303.value;
                                                    __auto_type _mv_1304 = (*spec_body);
                                                    switch (_mv_1304.tag) {
                                                        case types_SExpr_lst:
                                                        {
                                                            __auto_type body_lst = _mv_1304.data.lst;
                                                            {
                                                                __auto_type body_items = body_lst.items;
                                                                __auto_type body_len = ((int64_t)((body_items).len));
                                                                if (body_len >= 1) {
                                                                    __auto_type _mv_1305 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                    if (_mv_1305.has_value) {
                                                                        __auto_type ret_type = _mv_1305.value;
                                                                        __auto_type _mv_1306 = (*ret_type);
                                                                        switch (_mv_1306.tag) {
                                                                            case types_SExpr_sym:
                                                                            {
                                                                                __auto_type ret_sym = _mv_1306.data.sym;
                                                                                result = string_eq(ret_sym.name, SLOP_STR("String"));
                                                                                break;
                                                                            }
                                                                            default: {
                                                                                break;
                                                                            }
                                                                        }
                                                                    } else if (!_mv_1305.has_value) {
                                                                    }
                                                                }
                                                            }
                                                            break;
                                                        }
                                                        default: {
                                                            break;
                                                        }
                                                    }
                                                } else if (!_mv_1303.has_value) {
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_1301.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1299.has_value) {
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
        int64_t i = 3;
        __auto_type result = SLOP_STR("");
        while ((i < len) && string_eq(result, SLOP_STR(""))) {
            __auto_type _mv_1307 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1307.has_value) {
                __auto_type item = _mv_1307.value;
                __auto_type _mv_1308 = (*item);
                switch (_mv_1308.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type lst = _mv_1308.data.lst;
                        {
                            __auto_type sub_items = lst.items;
                            if (((int64_t)((sub_items).len)) >= 2) {
                                __auto_type _mv_1309 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1309.has_value) {
                                    __auto_type head = _mv_1309.value;
                                    __auto_type _mv_1310 = (*head);
                                    switch (_mv_1310.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_1310.data.sym;
                                            if (string_eq(sym.name, SLOP_STR("@spec"))) {
                                                __auto_type _mv_1311 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1311.has_value) {
                                                    __auto_type spec_body = _mv_1311.value;
                                                    __auto_type _mv_1312 = (*spec_body);
                                                    switch (_mv_1312.tag) {
                                                        case types_SExpr_lst:
                                                        {
                                                            __auto_type body_lst = _mv_1312.data.lst;
                                                            {
                                                                __auto_type body_items = body_lst.items;
                                                                __auto_type body_len = ((int64_t)((body_items).len));
                                                                if (body_len >= 1) {
                                                                    __auto_type _mv_1313 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                    if (_mv_1313.has_value) {
                                                                        __auto_type ret_type = _mv_1313.value;
                                                                        result = context_to_c_type_prefixed(ctx, ret_type);
                                                                    } else if (!_mv_1313.has_value) {
                                                                    }
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
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_1309.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1307.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

void transpiler_prescan_fn_params(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (((int64_t)((items).len)) >= 3) {
        __auto_type _mv_1314 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1314.has_value) {
            __auto_type params_expr = _mv_1314.value;
            __auto_type _mv_1315 = (*params_expr);
            switch (_mv_1315.tag) {
                case types_SExpr_lst:
                {
                    __auto_type params_lst = _mv_1315.data.lst;
                    {
                        __auto_type params = params_lst.items;
                        __auto_type param_count = ((int64_t)((params).len));
                        __auto_type i = 0;
                        while (i < param_count) {
                            __auto_type _mv_1316 = ({ __auto_type _lst = params; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1316.has_value) {
                                __auto_type param_expr = _mv_1316.value;
                                __auto_type _mv_1317 = (*param_expr);
                                switch (_mv_1317.tag) {
                                    case types_SExpr_lst:
                                    {
                                        __auto_type param_lst = _mv_1317.data.lst;
                                        {
                                            __auto_type param_items = param_lst.items;
                                            if (((int64_t)((param_items).len)) >= 2) {
                                                __auto_type _mv_1318 = ({ __auto_type _lst = param_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1318.has_value) {
                                                    __auto_type type_expr = _mv_1318.value;
                                                    transpiler_scan_type_for_generics(ctx, type_expr);
                                                } else if (!_mv_1318.has_value) {
                                                }
                                            }
                                        }
                                        break;
                                    }
                                    default: {
                                        break;
                                    }
                                }
                            } else if (!_mv_1316.has_value) {
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
        } else if (!_mv_1314.has_value) {
        }
    }
}

slop_list_context_FuncParamType_ptr transpiler_prescan_collect_param_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type result = ((slop_list_context_FuncParamType_ptr){ .data = (context_FuncParamType**)slop_arena_alloc(arena, 16 * sizeof(context_FuncParamType*)), .len = 0, .cap = 16 });
        if (((int64_t)((items).len)) >= 3) {
            __auto_type _mv_1319 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1319.has_value) {
                __auto_type params_expr = _mv_1319.value;
                __auto_type _mv_1320 = (*params_expr);
                switch (_mv_1320.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type params_lst = _mv_1320.data.lst;
                        {
                            __auto_type params = params_lst.items;
                            __auto_type param_count = ((int64_t)((params).len));
                            __auto_type i = 0;
                            while (i < param_count) {
                                __auto_type _mv_1321 = ({ __auto_type _lst = params; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1321.has_value) {
                                    __auto_type param_expr = _mv_1321.value;
                                    {
                                        __auto_type c_type = transpiler_prescan_get_param_c_type(ctx, param_expr);
                                        __auto_type param_info = ((context_FuncParamType*)(({ __auto_type _alloc = (context_FuncParamType*)slop_arena_alloc(arena, sizeof(context_FuncParamType)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
                                        (*param_info).c_type = c_type;
                                        ({ __auto_type _lst_p = &(result); __auto_type _item = (param_info); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    }
                                } else if (!_mv_1321.has_value) {
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
            } else if (!_mv_1319.has_value) {
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
        __auto_type _mv_1322 = (*param);
        switch (_mv_1322.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1322.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len < 2) {
                        return SLOP_STR("void*");
                    } else {
                        {
                            __auto_type has_mode = ((len >= 3) && transpiler_prescan_is_param_mode(items));
                            __auto_type type_idx = ((has_mode) ? 2 : 1);
                            __auto_type _mv_1323 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1323.has_value) {
                                __auto_type type_expr = _mv_1323.value;
                                return context_to_c_type_prefixed(ctx, type_expr);
                            } else if (!_mv_1323.has_value) {
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

uint8_t transpiler_prescan_is_param_mode(slop_list_types_SExpr_ptr items) {
    if (((int64_t)((items).len)) < 1) {
        return 0;
    } else {
        __auto_type _mv_1324 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1324.has_value) {
            __auto_type first = _mv_1324.value;
            __auto_type _mv_1325 = (*first);
            switch (_mv_1325.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_1325.data.sym;
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
        } else if (!_mv_1324.has_value) {
            return 0;
        }
        SLOP_UNREACHABLE();
    }
}

void transpiler_prescan_fn_result_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 3;
        while (i < len) {
            __auto_type _mv_1326 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1326.has_value) {
                __auto_type item = _mv_1326.value;
                if (transpiler_is_spec_annotation(item)) {
                    transpiler_extract_result_type(ctx, item);
                }
            } else if (!_mv_1326.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t transpiler_is_spec_annotation(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_1327 = (*expr);
    switch (_mv_1327.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1327.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1328 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1328.has_value) {
                        __auto_type head = _mv_1328.value;
                        __auto_type _mv_1329 = (*head);
                        switch (_mv_1329.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1329.data.sym;
                                return string_eq(sym.name, SLOP_STR("@spec"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1328.has_value) {
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

void transpiler_extract_result_type(context_TranspileContext* ctx, types_SExpr* spec_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((spec_expr != NULL)), "(!= spec-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1330 = (*spec_expr);
        switch (_mv_1330.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1330.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) >= 2) {
                        __auto_type _mv_1331 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1331.has_value) {
                            __auto_type spec_body = _mv_1331.value;
                            __auto_type _mv_1332 = (*spec_body);
                            switch (_mv_1332.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type body_lst = _mv_1332.data.lst;
                                    {
                                        __auto_type body_items = body_lst.items;
                                        __auto_type body_len = ((int64_t)((body_items).len));
                                        if (body_len >= 1) {
                                            __auto_type _mv_1333 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1333.has_value) {
                                                __auto_type ret_type = _mv_1333.value;
                                                transpiler_scan_type_for_generics(ctx, ret_type);
                                                transpiler_check_and_register_result_type(ctx, ret_type);
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
                        } else if (!_mv_1331.has_value) {
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
        __auto_type _mv_1334 = (*type_expr);
        switch (_mv_1334.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1334.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) >= 3) {
                        __auto_type _mv_1335 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1335.has_value) {
                            __auto_type head = _mv_1335.value;
                            __auto_type _mv_1336 = (*head);
                            switch (_mv_1336.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_1336.data.sym;
                                    if (string_eq(sym.name, SLOP_STR("Result"))) {
                                        __auto_type _mv_1337 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1337.has_value) {
                                            __auto_type ok_type_expr = _mv_1337.value;
                                            __auto_type _mv_1338 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1338.has_value) {
                                                __auto_type err_type_expr = _mv_1338.value;
                                                {
                                                    __auto_type ok_c_type = context_to_c_type_prefixed(ctx, ok_type_expr);
                                                    __auto_type err_c_type = context_to_c_type_prefixed(ctx, err_type_expr);
                                                    __auto_type result_name = transpiler_build_result_type_name(ctx, ok_c_type, err_c_type);
                                                    context_ctx_register_result_type(ctx, ok_c_type, err_c_type, result_name);
                                                }
                                            } else if (!_mv_1338.has_value) {
                                            }
                                        } else if (!_mv_1337.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1335.has_value) {
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
        int64_t i = 3;
        while (i < len) {
            __auto_type _mv_1339 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1339.has_value) {
                __auto_type item = _mv_1339.value;
                transpiler_prescan_expr_for_struct_keys(ctx, item);
            } else if (!_mv_1339.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_prescan_expr_for_struct_keys(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_1340 = (*expr);
    switch (_mv_1340.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1340.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if (len >= 1) {
                    __auto_type _mv_1341 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1341.has_value) {
                        __auto_type head = _mv_1341.value;
                        __auto_type _mv_1342 = (*head);
                        switch (_mv_1342.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1342.data.sym;
                                {
                                    __auto_type name = sym.name;
                                    if (string_eq(name, SLOP_STR("map-new"))) {
                                        if (len >= 3) {
                                            __auto_type _mv_1343 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1343.has_value) {
                                                __auto_type key_type_expr = _mv_1343.value;
                                                transpiler_prescan_register_struct_key_type(ctx, key_type_expr);
                                            } else if (!_mv_1343.has_value) {
                                            }
                                        }
                                    } else if (string_eq(name, SLOP_STR("set-new"))) {
                                        if (len >= 3) {
                                            __auto_type _mv_1344 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1344.has_value) {
                                                __auto_type elem_type_expr = _mv_1344.value;
                                                transpiler_prescan_register_struct_key_type(ctx, elem_type_expr);
                                            } else if (!_mv_1344.has_value) {
                                            }
                                        }
                                    } else if (string_eq(name, SLOP_STR("chan-buffered"))) {
                                        if (len >= 4) {
                                            __auto_type _mv_1345 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1345.has_value) {
                                                __auto_type type_expr = _mv_1345.value;
                                                {
                                                    __auto_type elem_c = context_to_c_type_prefixed(ctx, type_expr);
                                                    __auto_type elem_id = ctype_type_to_identifier((*ctx).arena, elem_c);
                                                    __auto_type c_name = context_ctx_str(ctx, SLOP_STR("slop_chan_"), elem_id);
                                                    context_ctx_register_chan_type(ctx, elem_c, c_name);
                                                }
                                            } else if (!_mv_1345.has_value) {
                                            }
                                        }
                                    } else if (string_eq(name, SLOP_STR("chan"))) {
                                        if (len >= 3) {
                                            __auto_type _mv_1346 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1346.has_value) {
                                                __auto_type type_expr = _mv_1346.value;
                                                {
                                                    __auto_type elem_c = context_to_c_type_prefixed(ctx, type_expr);
                                                    __auto_type elem_id = ctype_type_to_identifier((*ctx).arena, elem_c);
                                                    __auto_type c_name = context_ctx_str(ctx, SLOP_STR("slop_chan_"), elem_id);
                                                    context_ctx_register_chan_type(ctx, elem_c, c_name);
                                                }
                                            } else if (!_mv_1346.has_value) {
                                            }
                                        }
                                    } else {
                                        {
                                            __auto_type i = 0;
                                            while (i < len) {
                                                __auto_type _mv_1347 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1347.has_value) {
                                                    __auto_type child = _mv_1347.value;
                                                    transpiler_prescan_expr_for_struct_keys(ctx, child);
                                                } else if (!_mv_1347.has_value) {
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
                                    while (i < len) {
                                        __auto_type _mv_1348 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1348.has_value) {
                                            __auto_type child = _mv_1348.value;
                                            transpiler_prescan_expr_for_struct_keys(ctx, child);
                                        } else if (!_mv_1348.has_value) {
                                        }
                                        i = (i + 1);
                                    }
                                }
                                break;
                            }
                        }
                    } else if (!_mv_1341.has_value) {
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
        __auto_type _mv_1349 = (*type_expr);
        switch (_mv_1349.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_1349.data.sym;
                {
                    __auto_type name = sym.name;
                    if (!(transpiler_is_builtin_map_key_type(name))) {
                        __auto_type _mv_1350 = context_ctx_lookup_type(ctx, name);
                        if (_mv_1350.has_value) {
                            __auto_type type_entry = _mv_1350.value;
                            context_ctx_register_struct_key_type(ctx, type_entry.c_name);
                        } else if (!_mv_1350.has_value) {
                            __auto_type _mv_1351 = context_ctx_get_module(ctx);
                            if (_mv_1351.has_value) {
                                __auto_type mod = _mv_1351.value;
                                {
                                    __auto_type prefixed = context_ctx_str3(ctx, mod, SLOP_STR("_"), name);
                                    __auto_type _mv_1352 = context_ctx_lookup_type(ctx, prefixed);
                                    if (_mv_1352.has_value) {
                                        __auto_type type_entry = _mv_1352.value;
                                        context_ctx_register_struct_key_type(ctx, type_entry.c_name);
                                    } else if (!_mv_1352.has_value) {
                                        context_ctx_register_struct_key_type(ctx, ctype_to_c_name(arena, name));
                                    }
                                }
                            } else if (!_mv_1351.has_value) {
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
        __auto_type _mv_1353 = (*body_expr);
        switch (_mv_1353.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1353.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) >= 3) {
                        __auto_type _mv_1354 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1354.has_value) {
                            __auto_type head = _mv_1354.value;
                            __auto_type _mv_1355 = (*head);
                            switch (_mv_1355.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_1355.data.sym;
                                    if (string_eq(sym.name, SLOP_STR("Result"))) {
                                        __auto_type _mv_1356 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1356.has_value) {
                                            __auto_type ok_type_expr = _mv_1356.value;
                                            __auto_type _mv_1357 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1357.has_value) {
                                                __auto_type err_type_expr = _mv_1357.value;
                                                {
                                                    __auto_type ok_c_type = context_to_c_type_prefixed(ctx, ok_type_expr);
                                                    __auto_type err_c_type = context_to_c_type_prefixed(ctx, err_type_expr);
                                                    __auto_type result_name = transpiler_build_result_type_name(ctx, ok_c_type, err_c_type);
                                                    context_ctx_register_result_type_alias(ctx, alias_name, result_name);
                                                    context_ctx_register_result_type(ctx, ok_c_type, err_c_type, result_name);
                                                }
                                            } else if (!_mv_1357.has_value) {
                                            }
                                        } else if (!_mv_1356.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1354.has_value) {
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
        if (len >= 2) {
            __auto_type _mv_1358 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1358.has_value) {
                __auto_type header_expr = _mv_1358.value;
                __auto_type _mv_1359 = (*header_expr);
                switch (_mv_1359.tag) {
                    case types_SExpr_str:
                    {
                        __auto_type str = _mv_1359.data.str;
                        context_ctx_add_include(ctx, str.value);
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1358.has_value) {
            }
            {
                int64_t i = 2;
                while (i < len) {
                    __auto_type _mv_1360 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1360.has_value) {
                        __auto_type func_decl = _mv_1360.value;
                        transpiler_register_ffi_function(ctx, func_decl);
                    } else if (!_mv_1360.has_value) {
                    }
                    i = (i + 1);
                }
            }
        }
    }
}

uint8_t transpiler_is_type_name(slop_string name) {
    if (string_len(name) < 1) {
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
    if (((int64_t)((items).len)) >= 3) {
        __auto_type _mv_1361 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1361.has_value) {
            __auto_type mod_expr = _mv_1361.value;
            __auto_type _mv_1362 = (*mod_expr);
            switch (_mv_1362.tag) {
                case types_SExpr_sym:
                {
                    __auto_type mod_sym = _mv_1362.data.sym;
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
                        __auto_type _mv_1363 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1363.has_value) {
                            __auto_type symbols_expr = _mv_1363.value;
                            __auto_type _mv_1364 = (*symbols_expr);
                            switch (_mv_1364.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type symbols_lst = _mv_1364.data.lst;
                                    {
                                        __auto_type syms = symbols_lst.items;
                                        __auto_type sym_len = ((int64_t)((syms).len));
                                        __auto_type j = 0;
                                        while (j < sym_len) {
                                            __auto_type _mv_1365 = ({ __auto_type _lst = syms; size_t _idx = (size_t)j; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1365.has_value) {
                                                __auto_type sym_item = _mv_1365.value;
                                                __auto_type _mv_1366 = (*sym_item);
                                                switch (_mv_1366.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type s = _mv_1366.data.sym;
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
                                            } else if (!_mv_1365.has_value) {
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
                        } else if (!_mv_1363.has_value) {
                        }
                    }
                    break;
                }
                default: {
                    break;
                }
            }
        } else if (!_mv_1361.has_value) {
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
    {
        __auto_type arena = (*ctx).arena;
        if (((int64_t)((items).len)) >= 3) {
            __auto_type _mv_1367 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1367.has_value) {
                __auto_type name_expr = _mv_1367.value;
                __auto_type _mv_1368 = (*name_expr);
                switch (_mv_1368.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_1368.data.sym;
                        {
                            __auto_type const_name = sym.name;
                            __auto_type base_name = ctype_to_c_name(arena, const_name);
                            __auto_type c_name = context_ctx_prefix_type(ctx, base_name);
                            context_ctx_bind_var(ctx, (context_VarEntry){const_name, c_name, SLOP_STR("auto"), SLOP_STR(""), 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1367.has_value) {
            }
        }
    }
}

void transpiler_register_ffi_function(context_TranspileContext* ctx, types_SExpr* func_decl) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((func_decl != NULL)), "(!= func-decl nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1369 = (*func_decl);
        switch (_mv_1369.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1369.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len >= 1) {
                        __auto_type _mv_1370 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1370.has_value) {
                            __auto_type name_expr = _mv_1370.value;
                            __auto_type _mv_1371 = (*name_expr);
                            switch (_mv_1371.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_1371.data.sym;
                                    {
                                        __auto_type fn_name = sym.name;
                                        __auto_type c_name = transpiler_extract_ffi_c_name(ctx, items, fn_name);
                                        __auto_type param_types = transpiler_extract_ffi_param_types(ctx, items);
                                        __auto_type ret_type = (((len >= 3)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type ret_expr = _mv.value; context_to_c_type_prefixed(ctx, ret_expr); }) : (SLOP_STR("")); }) : SLOP_STR(""));
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
                        } else if (!_mv_1370.has_value) {
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
        if (((int64_t)((items).len)) >= 2) {
            __auto_type _mv_1372 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1372.has_value) {
                __auto_type params_expr = _mv_1372.value;
                __auto_type _mv_1373 = (*params_expr);
                switch (_mv_1373.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type params_lst = _mv_1373.data.lst;
                        {
                            __auto_type params = params_lst.items;
                            __auto_type param_count = ((int64_t)((params).len));
                            __auto_type i = 0;
                            while (i < param_count) {
                                __auto_type _mv_1374 = ({ __auto_type _lst = params; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1374.has_value) {
                                    __auto_type param_expr = _mv_1374.value;
                                    {
                                        __auto_type c_type = transpiler_prescan_get_param_c_type(ctx, param_expr);
                                        __auto_type param_info = ((context_FuncParamType*)(({ __auto_type _alloc = (context_FuncParamType*)slop_arena_alloc(arena, sizeof(context_FuncParamType)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
                                        (*param_info).c_type = c_type;
                                        ({ __auto_type _lst_p = &(result); __auto_type _item = (param_info); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    }
                                } else if (!_mv_1374.has_value) {
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
            } else if (!_mv_1372.has_value) {
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
        int64_t i = 0;
        uint8_t found_c_name = 0;
        __auto_type c_name = SLOP_STR("");
        while (i < len) {
            __auto_type _mv_1375 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1375.has_value) {
                __auto_type item_expr = _mv_1375.value;
                __auto_type _mv_1376 = (*item_expr);
                switch (_mv_1376.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_1376.data.sym;
                        if (string_eq(sym.name, SLOP_STR(":c-name"))) {
                            __auto_type _mv_1377 = ({ __auto_type _lst = items; size_t _idx = (size_t)(i + 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1377.has_value) {
                                __auto_type c_name_expr = _mv_1377.value;
                                __auto_type _mv_1378 = (*c_name_expr);
                                switch (_mv_1378.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type c_sym = _mv_1378.data.sym;
                                        c_name = c_sym.name;
                                        found_c_name = 1;
                                        break;
                                    }
                                    default: {
                                        break;
                                    }
                                }
                            } else if (!_mv_1377.has_value) {
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1375.has_value) {
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
        if (len >= 2) {
            {
                __auto_type has_header = ((len >= 2) && transpiler_is_ffi_string_item(items, 1));
                __auto_type name_idx = ((((len >= 2) && transpiler_is_ffi_string_item(items, 1))) ? 2 : 1);
                if (has_header) {
                    __auto_type _mv_1379 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1379.has_value) {
                        __auto_type header_expr = _mv_1379.value;
                        __auto_type _mv_1380 = (*header_expr);
                        switch (_mv_1380.tag) {
                            case types_SExpr_str:
                            {
                                __auto_type str = _mv_1380.data.str;
                                context_ctx_add_include(ctx, str.value);
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_1379.has_value) {
                    }
                }
                if (len >= (name_idx + 1)) {
                    __auto_type _mv_1381 = ({ __auto_type _lst = items; size_t _idx = (size_t)name_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1381.has_value) {
                        __auto_type name_expr = _mv_1381.value;
                        __auto_type _mv_1382 = (*name_expr);
                        switch (_mv_1382.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1382.data.sym;
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
                    } else if (!_mv_1381.has_value) {
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
        if (len >= (modifier_idx + 2)) {
            __auto_type _mv_1383 = ({ __auto_type _lst = items; size_t _idx = (size_t)modifier_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1383.has_value) {
                __auto_type mod_expr = _mv_1383.value;
                __auto_type _mv_1384 = (*mod_expr);
                switch (_mv_1384.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_1384.data.sym;
                        if (string_eq(sym.name, SLOP_STR(":c-name"))) {
                            __auto_type _mv_1385 = ({ __auto_type _lst = items; size_t _idx = (size_t)(modifier_idx + 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1385.has_value) {
                                __auto_type cname_expr = _mv_1385.value;
                                __auto_type _mv_1386 = (*cname_expr);
                                switch (_mv_1386.tag) {
                                    case types_SExpr_str:
                                    {
                                        __auto_type str = _mv_1386.data.str;
                                        return transpiler_apply_struct_prefix_heuristic(arena, str.value);
                                    }
                                    default: {
                                        return transpiler_apply_struct_prefix_heuristic(arena, default_name);
                                    }
                                }
                            } else if (!_mv_1385.has_value) {
                                return transpiler_apply_struct_prefix_heuristic(arena, default_name);
                            }
                            SLOP_UNREACHABLE();
                        } else {
                            return transpiler_apply_struct_prefix_heuristic(arena, default_name);
                        }
                    }
                    default: {
                        return transpiler_apply_struct_prefix_heuristic(arena, default_name);
                    }
                }
            } else if (!_mv_1383.has_value) {
                return transpiler_apply_struct_prefix_heuristic(arena, default_name);
            }
            SLOP_UNREACHABLE();
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
        if (s_len < suf_len) {
            return 0;
        } else {
            {
                __auto_type start = (((int64_t)(s_len)) - ((int64_t)(suf_len)));
                int64_t i = 0;
                uint8_t matches = 1;
                while (matches && (i < ((int64_t)(suf_len)))) {
                    {
                        __auto_type s_char = s.data[(start + i)];
                        __auto_type suf_char = suffix.data[i];
                        if (s_char != suf_char) {
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
    __auto_type _mv_1387 = ({ __auto_type _lst = items; size_t _idx = (size_t)idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
    if (_mv_1387.has_value) {
        __auto_type item = _mv_1387.value;
        __auto_type _mv_1388 = (*item);
        switch (_mv_1388.tag) {
            case types_SExpr_str:
            {
                __auto_type _ = _mv_1388.data.str;
                return 1;
            }
            default: {
                return 0;
            }
        }
    } else if (!_mv_1387.has_value) {
        return 0;
    }
    SLOP_UNREACHABLE();
}

uint8_t transpiler_is_enum_def(slop_list_types_SExpr_ptr items) {
    if (((int64_t)((items).len)) < 3) {
        return 0;
    } else {
        __auto_type _mv_1389 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1389.has_value) {
            __auto_type def_expr = _mv_1389.value;
            __auto_type _mv_1390 = (*def_expr);
            switch (_mv_1390.tag) {
                case types_SExpr_lst:
                {
                    __auto_type def_lst = _mv_1390.data.lst;
                    {
                        __auto_type def_items = def_lst.items;
                        if (((int64_t)((def_items).len)) < 1) {
                            return 0;
                        } else {
                            __auto_type _mv_1391 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1391.has_value) {
                                __auto_type head = _mv_1391.value;
                                __auto_type _mv_1392 = (*head);
                                switch (_mv_1392.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1392.data.sym;
                                        return string_eq(sym.name, SLOP_STR("enum"));
                                    }
                                    default: {
                                        return 0;
                                    }
                                }
                            } else if (!_mv_1391.has_value) {
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
        } else if (!_mv_1389.has_value) {
            return 0;
        }
        SLOP_UNREACHABLE();
    }
}

uint8_t transpiler_is_record_def(slop_list_types_SExpr_ptr items) {
    if (((int64_t)((items).len)) < 3) {
        return 0;
    } else {
        __auto_type _mv_1393 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1393.has_value) {
            __auto_type def_expr = _mv_1393.value;
            __auto_type _mv_1394 = (*def_expr);
            switch (_mv_1394.tag) {
                case types_SExpr_lst:
                {
                    __auto_type def_lst = _mv_1394.data.lst;
                    {
                        __auto_type def_items = def_lst.items;
                        if (((int64_t)((def_items).len)) < 1) {
                            return 0;
                        } else {
                            __auto_type _mv_1395 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1395.has_value) {
                                __auto_type head = _mv_1395.value;
                                __auto_type _mv_1396 = (*head);
                                switch (_mv_1396.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1396.data.sym;
                                        return string_eq(sym.name, SLOP_STR("record"));
                                    }
                                    default: {
                                        return 0;
                                    }
                                }
                            } else if (!_mv_1395.has_value) {
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
        } else if (!_mv_1393.has_value) {
            return 0;
        }
        SLOP_UNREACHABLE();
    }
}

uint8_t transpiler_is_union_def(slop_list_types_SExpr_ptr items) {
    if (((int64_t)((items).len)) < 3) {
        return 0;
    } else {
        __auto_type _mv_1397 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1397.has_value) {
            __auto_type def_expr = _mv_1397.value;
            __auto_type _mv_1398 = (*def_expr);
            switch (_mv_1398.tag) {
                case types_SExpr_lst:
                {
                    __auto_type def_lst = _mv_1398.data.lst;
                    {
                        __auto_type def_items = def_lst.items;
                        if (((int64_t)((def_items).len)) < 1) {
                            return 0;
                        } else {
                            __auto_type _mv_1399 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1399.has_value) {
                                __auto_type head = _mv_1399.value;
                                __auto_type _mv_1400 = (*head);
                                switch (_mv_1400.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1400.data.sym;
                                        return string_eq(sym.name, SLOP_STR("union"));
                                    }
                                    default: {
                                        return 0;
                                    }
                                }
                            } else if (!_mv_1399.has_value) {
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
        } else if (!_mv_1397.has_value) {
            return 0;
        }
        SLOP_UNREACHABLE();
    }
}

slop_string transpiler_get_array_c_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, slop_string default_c_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (((int64_t)((items).len)) < 3) {
        return default_c_type;
    } else {
        __auto_type _mv_1401 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1401.has_value) {
            __auto_type body_expr = _mv_1401.value;
            __auto_type _mv_1402 = (*body_expr);
            switch (_mv_1402.tag) {
                case types_SExpr_lst:
                {
                    __auto_type body_lst = _mv_1402.data.lst;
                    {
                        __auto_type body_items = body_lst.items;
                        if (((int64_t)((body_items).len)) < 2) {
                            return default_c_type;
                        } else {
                            __auto_type _mv_1403 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1403.has_value) {
                                __auto_type head = _mv_1403.value;
                                __auto_type _mv_1404 = (*head);
                                switch (_mv_1404.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1404.data.sym;
                                        if (string_eq(sym.name, SLOP_STR("Array"))) {
                                            __auto_type _mv_1405 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1405.has_value) {
                                                __auto_type elem_expr = _mv_1405.value;
                                                {
                                                    __auto_type elem_c = context_to_c_type_prefixed(ctx, elem_expr);
                                                    return context_ctx_str(ctx, elem_c, SLOP_STR("*"));
                                                }
                                            } else if (!_mv_1405.has_value) {
                                                return default_c_type;
                                            }
                                            SLOP_UNREACHABLE();
                                        } else {
                                            return default_c_type;
                                        }
                                    }
                                    default: {
                                        return default_c_type;
                                    }
                                }
                            } else if (!_mv_1403.has_value) {
                                return default_c_type;
                            }
                            SLOP_UNREACHABLE();
                        }
                    }
                }
                default: {
                    return default_c_type;
                }
            }
        } else if (!_mv_1401.has_value) {
            return default_c_type;
        }
        SLOP_UNREACHABLE();
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1406 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1406.has_value) {
                __auto_type item = _mv_1406.value;
                if (transpiler_is_type_def(item) && !(transpiler_is_union_type_def(item))) {
                    defn_transpile_type(ctx, item);
                }
            } else if (!_mv_1406.has_value) {
            }
            i = (i + 1);
        }
    }
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1407 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1407.has_value) {
                __auto_type item = _mv_1407.value;
                if (transpiler_is_type_def(item) && transpiler_is_union_type_def(item)) {
                    defn_transpile_type(ctx, item);
                }
            } else if (!_mv_1407.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t transpiler_is_union_type_def(types_SExpr* item) {
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1408 = (*item);
    switch (_mv_1408.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1408.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 3) {
                    return 0;
                } else {
                    __auto_type _mv_1409 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1409.has_value) {
                        __auto_type def_expr = _mv_1409.value;
                        __auto_type _mv_1410 = (*def_expr);
                        switch (_mv_1410.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type def_lst = _mv_1410.data.lst;
                                {
                                    __auto_type def_items = def_lst.items;
                                    if (((int64_t)((def_items).len)) < 1) {
                                        return 0;
                                    } else {
                                        __auto_type _mv_1411 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1411.has_value) {
                                            __auto_type head = _mv_1411.value;
                                            __auto_type _mv_1412 = (*head);
                                            switch (_mv_1412.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type sym = _mv_1412.data.sym;
                                                    return string_eq(sym.name, SLOP_STR("union"));
                                                }
                                                default: {
                                                    return 0;
                                                }
                                            }
                                        } else if (!_mv_1411.has_value) {
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
                    } else if (!_mv_1409.has_value) {
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

uint8_t transpiler_is_type_def(types_SExpr* item) {
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1413 = (*item);
    switch (_mv_1413.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1413.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1414 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1414.has_value) {
                        __auto_type head = _mv_1414.value;
                        __auto_type _mv_1415 = (*head);
                        switch (_mv_1415.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1415.data.sym;
                                return string_eq(sym.name, SLOP_STR("type"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1414.has_value) {
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

void transpiler_emit_all_functions(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1416 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1416.has_value) {
                __auto_type item = _mv_1416.value;
                if (transpiler_is_fn_def(item)) {
                    defn_transpile_function(ctx, item);
                }
            } else if (!_mv_1416.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t transpiler_is_fn_def(types_SExpr* item) {
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1417 = (*item);
    switch (_mv_1417.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1417.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1418 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1418.has_value) {
                        __auto_type head = _mv_1418.value;
                        __auto_type _mv_1419 = (*head);
                        switch (_mv_1419.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1419.data.sym;
                                return string_eq(sym.name, SLOP_STR("fn"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1418.has_value) {
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

void transpiler_transpile_module(context_TranspileContext* ctx, types_SExpr* module_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((module_expr != NULL)), "(!= module-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1420 = (*module_expr);
        switch (_mv_1420.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1420.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len >= 2) {
                        __auto_type _mv_1421 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1421.has_value) {
                            __auto_type name_expr = _mv_1421.value;
                            __auto_type _mv_1422 = (*name_expr);
                            switch (_mv_1422.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_1422.data.sym;
                                    context_ctx_set_module(ctx, (slop_option_string){.has_value = 1, .value = sym.name});
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1421.has_value) {
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
                            transpiler_emit_late_registered_list_types_header(ctx);
                            transpiler_emit_late_registered_struct_key_types_header(ctx);
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
    if (((int64_t)((items).len)) < 3) {
        return 2;
    } else {
        __auto_type _mv_1423 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1423.has_value) {
            __auto_type third = _mv_1423.value;
            __auto_type _mv_1424 = (*third);
            switch (_mv_1424.tag) {
                case types_SExpr_lst:
                {
                    __auto_type lst = _mv_1424.data.lst;
                    {
                        __auto_type sub_items = lst.items;
                        if (((int64_t)((sub_items).len)) < 1) {
                            return 2;
                        } else {
                            __auto_type _mv_1425 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1425.has_value) {
                                __auto_type head = _mv_1425.value;
                                __auto_type _mv_1426 = (*head);
                                switch (_mv_1426.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1426.data.sym;
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
                            } else if (!_mv_1425.has_value) {
                                return 2;
                            }
                            SLOP_UNREACHABLE();
                        }
                    }
                }
                default: {
                    return 2;
                }
            }
        } else if (!_mv_1423.has_value) {
            return 2;
        }
        SLOP_UNREACHABLE();
    }
}

slop_list_string transpiler_get_export_names(slop_arena* arena, slop_list_types_SExpr_ptr items) {
    {
        __auto_type result = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 2;
        while (i < len) {
            __auto_type _mv_1427 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1427.has_value) {
                __auto_type item = _mv_1427.value;
                __auto_type _mv_1428 = (*item);
                switch (_mv_1428.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type lst = _mv_1428.data.lst;
                        {
                            __auto_type sub_items = lst.items;
                            if (((int64_t)((sub_items).len)) >= 1) {
                                __auto_type _mv_1429 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1429.has_value) {
                                    __auto_type head = _mv_1429.value;
                                    __auto_type _mv_1430 = (*head);
                                    switch (_mv_1430.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_1430.data.sym;
                                            if (string_eq(sym.name, SLOP_STR("export"))) {
                                                {
                                                    __auto_type export_len = ((int64_t)((sub_items).len));
                                                    __auto_type j = 1;
                                                    while (j < export_len) {
                                                        __auto_type _mv_1431 = ({ __auto_type _lst = sub_items; size_t _idx = (size_t)j; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                        if (_mv_1431.has_value) {
                                                            __auto_type name_expr = _mv_1431.value;
                                                            __auto_type _mv_1432 = (*name_expr);
                                                            switch (_mv_1432.tag) {
                                                                case types_SExpr_sym:
                                                                {
                                                                    __auto_type name_sym = _mv_1432.data.sym;
                                                                    ({ __auto_type _lst_p = &(result); __auto_type _item = (name_sym.name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                                    break;
                                                                }
                                                                default: {
                                                                    break;
                                                                }
                                                            }
                                                        } else if (!_mv_1431.has_value) {
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
                                } else if (!_mv_1429.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1427.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

uint8_t transpiler_list_contains_str(slop_list_string lst, slop_string needle) {
    {
        __auto_type len = ((int64_t)((lst).len));
        int64_t i = 0;
        uint8_t found = 0;
        while ((i < len) && !(found)) {
            __auto_type _mv_1433 = ({ __auto_type _lst = lst; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1433.has_value) {
                __auto_type s = _mv_1433.value;
                if (string_eq(s, needle)) {
                    found = 1;
                }
            } else if (!_mv_1433.has_value) {
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
        int64_t i = start;
        while (i < len) {
            __auto_type _mv_1434 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1434.has_value) {
                __auto_type item = _mv_1434.value;
                transpiler_prescan_top_level(ctx, item);
            } else if (!_mv_1434.has_value) {
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
        __auto_type _mv_1435 = (*type_expr);
        switch (_mv_1435.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1435.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len >= 1) {
                        __auto_type _mv_1436 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1436.has_value) {
                            __auto_type head = _mv_1436.value;
                            __auto_type _mv_1437 = (*head);
                            switch (_mv_1437.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_1437.data.sym;
                                    {
                                        __auto_type op = sym.name;
                                        if (string_eq(op, SLOP_STR("Option"))) {
                                            if (len >= 2) {
                                                __auto_type _mv_1438 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1438.has_value) {
                                                    __auto_type inner = _mv_1438.value;
                                                    {
                                                        __auto_type inner_c = context_to_c_type_prefixed(ctx, inner);
                                                        __auto_type inner_id = ctype_type_to_identifier(arena, inner_c);
                                                        __auto_type c_name = context_ctx_str(ctx, SLOP_STR("slop_option_"), inner_id);
                                                        context_ctx_register_option_type(ctx, inner_c, c_name);
                                                        transpiler_scan_type_for_generics(ctx, inner);
                                                    }
                                                } else if (!_mv_1438.has_value) {
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("List"))) {
                                            if (len >= 2) {
                                                __auto_type _mv_1439 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1439.has_value) {
                                                    __auto_type elem = _mv_1439.value;
                                                    {
                                                        __auto_type elem_c = context_to_c_type_prefixed(ctx, elem);
                                                        __auto_type elem_id = ctype_type_to_identifier(arena, elem_c);
                                                        __auto_type c_name = context_ctx_str(ctx, SLOP_STR("slop_list_"), elem_id);
                                                        __auto_type option_c_name = context_ctx_str(ctx, SLOP_STR("slop_option_"), elem_id);
                                                        context_ctx_register_list_type(ctx, elem_c, c_name);
                                                        context_ctx_register_option_type(ctx, elem_c, option_c_name);
                                                        transpiler_scan_type_for_generics(ctx, elem);
                                                    }
                                                } else if (!_mv_1439.has_value) {
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("Ptr"))) {
                                            if (len >= 2) {
                                                __auto_type _mv_1440 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1440.has_value) {
                                                    __auto_type inner = _mv_1440.value;
                                                    transpiler_scan_type_for_generics(ctx, inner);
                                                } else if (!_mv_1440.has_value) {
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("Result"))) {
                                            if (len >= 3) {
                                                __auto_type _mv_1441 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1441.has_value) {
                                                    __auto_type ok_type = _mv_1441.value;
                                                    __auto_type _mv_1442 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_1442.has_value) {
                                                        __auto_type err_type = _mv_1442.value;
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
                                                    } else if (!_mv_1442.has_value) {
                                                    }
                                                } else if (!_mv_1441.has_value) {
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("Chan"))) {
                                            if (len >= 2) {
                                                __auto_type _mv_1443 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1443.has_value) {
                                                    __auto_type elem = _mv_1443.value;
                                                    {
                                                        __auto_type elem_c = context_to_c_type_prefixed(ctx, elem);
                                                        __auto_type elem_id = ctype_type_to_identifier(arena, elem_c);
                                                        __auto_type c_name = context_ctx_str(ctx, SLOP_STR("slop_chan_"), elem_id);
                                                        context_ctx_register_chan_type(ctx, elem_c, c_name);
                                                        transpiler_scan_type_for_generics(ctx, elem);
                                                    }
                                                } else if (!_mv_1443.has_value) {
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("Thread"))) {
                                            if (len >= 2) {
                                                __auto_type _mv_1444 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1444.has_value) {
                                                    __auto_type result = _mv_1444.value;
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
                                                } else if (!_mv_1444.has_value) {
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("Map"))) {
                                            if (len >= 3) {
                                                __auto_type _mv_1445 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1445.has_value) {
                                                    __auto_type key_type = _mv_1445.value;
                                                    {
                                                        __auto_type key_c = context_to_c_type_prefixed(ctx, key_type);
                                                        __auto_type key_id = ctype_type_to_identifier(arena, key_c);
                                                        __auto_type list_c_name = context_ctx_str(ctx, SLOP_STR("slop_list_"), key_id);
                                                        __auto_type option_c_name = context_ctx_str(ctx, SLOP_STR("slop_option_"), key_id);
                                                        context_ctx_register_list_type(ctx, key_c, list_c_name);
                                                        context_ctx_register_option_type(ctx, key_c, option_c_name);
                                                        transpiler_scan_type_for_generics(ctx, key_type);
                                                        __auto_type _mv_1446 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                        if (_mv_1446.has_value) {
                                                            __auto_type val_type = _mv_1446.value;
                                                            {
                                                                __auto_type val_c = context_to_c_type_prefixed(ctx, val_type);
                                                                __auto_type val_id = ctype_type_to_identifier(arena, val_c);
                                                                __auto_type val_option_c_name = context_ctx_str(ctx, SLOP_STR("slop_option_"), val_id);
                                                                context_ctx_register_option_type(ctx, val_c, val_option_c_name);
                                                                transpiler_scan_type_for_generics(ctx, val_type);
                                                            }
                                                        } else if (!_mv_1446.has_value) {
                                                        }
                                                    }
                                                } else if (!_mv_1445.has_value) {
                                                }
                                            }
                                        } else if (string_eq(op, SLOP_STR("Set"))) {
                                            if (len >= 2) {
                                                __auto_type _mv_1447 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1447.has_value) {
                                                    __auto_type elem_type = _mv_1447.value;
                                                    {
                                                        __auto_type elem_c = context_to_c_type_prefixed(ctx, elem_type);
                                                        __auto_type elem_id = ctype_type_to_identifier(arena, elem_c);
                                                        __auto_type list_c_name = context_ctx_str(ctx, SLOP_STR("slop_list_"), elem_id);
                                                        __auto_type option_c_name = context_ctx_str(ctx, SLOP_STR("slop_option_"), elem_id);
                                                        context_ctx_register_list_type(ctx, elem_c, list_c_name);
                                                        context_ctx_register_option_type(ctx, elem_c, option_c_name);
                                                        transpiler_scan_type_for_generics(ctx, elem_type);
                                                    }
                                                } else if (!_mv_1447.has_value) {
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
                        } else if (!_mv_1436.has_value) {
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
        int64_t i = 1;
        while (i < len) {
            __auto_type _mv_1448 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1448.has_value) {
                __auto_type field_expr = _mv_1448.value;
                __auto_type _mv_1449 = (*field_expr);
                switch (_mv_1449.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type field_lst = _mv_1449.data.lst;
                        {
                            __auto_type field_items = field_lst.items;
                            if (((int64_t)((field_items).len)) >= 2) {
                                __auto_type _mv_1450 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1450.has_value) {
                                    __auto_type type_expr = _mv_1450.value;
                                    transpiler_scan_type_for_generics(ctx, type_expr);
                                } else if (!_mv_1450.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1448.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1451 = ({ __auto_type _lst = includes; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1451.has_value) {
                __auto_type header = _mv_1451.value;
                emit_emit_include(ctx, header, 1);
            } else if (!_mv_1451.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1452 = ({ __auto_type _lst = includes; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1452.has_value) {
                __auto_type header = _mv_1452.value;
                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("#include <"), header, SLOP_STR(">")));
            } else if (!_mv_1452.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_header_guard_open(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1453 = context_ctx_get_module(ctx);
        if (_mv_1453.has_value) {
            __auto_type mod_name = _mv_1453.value;
            {
                __auto_type c_name = ctype_to_c_name(arena, mod_name);
                __auto_type guard = context_ctx_str3(ctx, SLOP_STR("SLOP_"), c_name, SLOP_STR("_H"));
                context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), guard));
                context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), guard));
                context_ctx_emit_header(ctx, SLOP_STR(""));
            }
        } else if (!_mv_1453.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1454 = ({ __auto_type _lst = imports; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1454.has_value) {
                __auto_type mod_name = _mv_1454.value;
                {
                    __auto_type c_name = ctype_to_c_name(arena, mod_name);
                    context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("#include \"slop_"), c_name, SLOP_STR(".h\"")));
                }
            } else if (!_mv_1454.has_value) {
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
        int64_t i = start;
        uint8_t emitted_any = 0;
        while (i < len) {
            __auto_type _mv_1455 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1455.has_value) {
                __auto_type item = _mv_1455.value;
                if (transpiler_is_type_def(item) && transpiler_is_struct_type_def(item)) {
                    __auto_type _mv_1456 = transpiler_get_type_name(item);
                    if (_mv_1456.has_value) {
                        __auto_type type_name = _mv_1456.value;
                        {
                            __auto_type c_name = ctype_to_c_name(arena, type_name);
                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("typedef struct "), c_name, context_ctx_str(ctx, SLOP_STR(" "), context_ctx_str(ctx, c_name, SLOP_STR(";")))));
                            emitted_any = 1;
                        }
                    } else if (!_mv_1456.has_value) {
                    }
                }
            } else if (!_mv_1455.has_value) {
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
    __auto_type _mv_1457 = (*item);
    switch (_mv_1457.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1457.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 3) {
                    return 0;
                } else {
                    __auto_type _mv_1458 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1458.has_value) {
                        __auto_type def_expr = _mv_1458.value;
                        __auto_type _mv_1459 = (*def_expr);
                        switch (_mv_1459.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type def_lst = _mv_1459.data.lst;
                                {
                                    __auto_type def_items = def_lst.items;
                                    if (((int64_t)((def_items).len)) < 1) {
                                        return 0;
                                    } else {
                                        __auto_type _mv_1460 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1460.has_value) {
                                            __auto_type head = _mv_1460.value;
                                            __auto_type _mv_1461 = (*head);
                                            switch (_mv_1461.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type sym = _mv_1461.data.sym;
                                                    {
                                                        __auto_type kind = sym.name;
                                                        return ((string_eq(kind, SLOP_STR("record"))) || (string_eq(kind, SLOP_STR("union"))) || ((string_eq(kind, SLOP_STR("enum")) && transpiler_has_enum_payload_variants(def_items))));
                                                    }
                                                }
                                                default: {
                                                    return 0;
                                                }
                                            }
                                        } else if (!_mv_1460.has_value) {
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
                    } else if (!_mv_1458.has_value) {
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

uint8_t transpiler_has_enum_payload_variants(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 1;
        uint8_t found = 0;
        while ((i < len) && !(found)) {
            __auto_type _mv_1462 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1462.has_value) {
                __auto_type item = _mv_1462.value;
                __auto_type _mv_1463 = (*item);
                switch (_mv_1463.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type _ = _mv_1463.data.lst;
                        found = 1;
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1462.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

uint8_t transpiler_is_type_alias_def(types_SExpr* item) {
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1464 = (*item);
    switch (_mv_1464.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1464.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 3) {
                    return 0;
                } else {
                    __auto_type _mv_1465 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1465.has_value) {
                        __auto_type def_expr = _mv_1465.value;
                        __auto_type _mv_1466 = (*def_expr);
                        switch (_mv_1466.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type _ = _mv_1466.data.sym;
                                return 1;
                            }
                            case types_SExpr_lst:
                            {
                                __auto_type def_lst = _mv_1466.data.lst;
                                {
                                    __auto_type def_items = def_lst.items;
                                    if (((int64_t)((def_items).len)) < 1) {
                                        return 0;
                                    } else {
                                        __auto_type _mv_1467 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1467.has_value) {
                                            __auto_type head = _mv_1467.value;
                                            __auto_type _mv_1468 = (*head);
                                            switch (_mv_1468.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type sym = _mv_1468.data.sym;
                                                    {
                                                        __auto_type kind = sym.name;
                                                        return ((!(string_eq(kind, SLOP_STR("record")))) && (!(string_eq(kind, SLOP_STR("enum")))) && (!(string_eq(kind, SLOP_STR("union")))));
                                                    }
                                                }
                                                default: {
                                                    return 0;
                                                }
                                            }
                                        } else if (!_mv_1467.has_value) {
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
                    } else if (!_mv_1465.has_value) {
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

uint8_t transpiler_is_result_type_alias_def(types_SExpr* item) {
    SLOP_PRE(((item != NULL)), "(!= item nil)");
    __auto_type _mv_1469 = (*item);
    switch (_mv_1469.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1469.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 3) {
                    return 0;
                } else {
                    __auto_type _mv_1470 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1470.has_value) {
                        __auto_type def_expr = _mv_1470.value;
                        __auto_type _mv_1471 = (*def_expr);
                        switch (_mv_1471.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type def_lst = _mv_1471.data.lst;
                                {
                                    __auto_type def_items = def_lst.items;
                                    if (((int64_t)((def_items).len)) < 1) {
                                        return 0;
                                    } else {
                                        __auto_type _mv_1472 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1472.has_value) {
                                            __auto_type head = _mv_1472.value;
                                            __auto_type _mv_1473 = (*head);
                                            switch (_mv_1473.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type sym = _mv_1473.data.sym;
                                                    {
                                                        __auto_type head_name = sym.name;
                                                        return ((string_eq(head_name, SLOP_STR("Result"))) || (string_eq(head_name, SLOP_STR("List"))) || (string_eq(head_name, SLOP_STR("Option"))));
                                                    }
                                                }
                                                default: {
                                                    return 0;
                                                }
                                            }
                                        } else if (!_mv_1472.has_value) {
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
                    } else if (!_mv_1470.has_value) {
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

slop_string transpiler_alias_target_c_type(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    __auto_type _mv_1474 = (*type_def);
    switch (_mv_1474.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1474.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 3) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_1475 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1475.has_value) {
                        __auto_type body_expr = _mv_1475.value;
                        return context_to_c_type_prefixed(ctx, body_expr);
                    } else if (!_mv_1475.has_value) {
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

slop_string transpiler_alias_own_c_name(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1476 = (*type_def);
        switch (_mv_1476.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1476.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) < 2) {
                        return SLOP_STR("");
                    } else {
                        __auto_type _mv_1477 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1477.has_value) {
                            __auto_type name_expr = _mv_1477.value;
                            __auto_type _mv_1478 = (*name_expr);
                            switch (_mv_1478.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_1478.data.sym;
                                    return context_ctx_prefix_type(ctx, ctype_to_c_name(arena, name_sym.name));
                                }
                                default: {
                                    return SLOP_STR("");
                                }
                            }
                        } else if (!_mv_1477.has_value) {
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

uint8_t transpiler_container_alias_ready(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type c_type = transpiler_alias_target_c_type(ctx, type_def);
        return ((transpiler_is_runtime_option_type(c_type)) || (transpiler_is_runtime_list_type(c_type)) || (context_ctx_is_type_emitted(ctx, c_type)));
    }
}

void transpiler_emit_type_alias_to_header(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1479 = (*type_def);
        switch (_mv_1479.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1479.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) >= 3) {
                        __auto_type _mv_1480 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1480.has_value) {
                            __auto_type name_expr = _mv_1480.value;
                            __auto_type _mv_1481 = (*name_expr);
                            switch (_mv_1481.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_1481.data.sym;
                                    {
                                        __auto_type type_name = name_sym.name;
                                        __auto_type base_c_name = ctype_to_c_name(arena, type_name);
                                        __auto_type c_name = context_ctx_prefix_type(ctx, base_c_name);
                                        __auto_type _mv_1482 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1482.has_value) {
                                            __auto_type body_expr = _mv_1482.value;
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
                                        } else if (!_mv_1482.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1480.has_value) {
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
    __auto_type _mv_1483 = (*body_expr);
    switch (_mv_1483.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1483.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1484 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1484.has_value) {
                        __auto_type head = _mv_1484.value;
                        __auto_type _mv_1485 = (*head);
                        switch (_mv_1485.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1485.data.sym;
                                return string_eq(sym.name, SLOP_STR("Array"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1484.has_value) {
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

void transpiler_emit_array_typedef_to_header(context_TranspileContext* ctx, slop_string c_name, types_SExpr* body_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((body_expr != NULL)), "(!= body-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1486 = (*body_expr);
        switch (_mv_1486.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1486.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len < 3) {
                        context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("typedef void* "), c_name, SLOP_STR(";")));
                    } else {
                        __auto_type _mv_1487 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1487.has_value) {
                            __auto_type elem_type_expr = _mv_1487.value;
                            __auto_type _mv_1488 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1488.has_value) {
                                __auto_type size_expr = _mv_1488.value;
                                {
                                    __auto_type elem_c_type = context_to_c_type_prefixed(ctx, elem_type_expr);
                                    __auto_type size_str = transpiler_get_array_size_string(size_expr);
                                    context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("typedef "), elem_c_type, SLOP_STR(" "), c_name, context_ctx_str3(ctx, SLOP_STR("["), size_str, SLOP_STR("];"))));
                                    context_ctx_emit_header(ctx, SLOP_STR(""));
                                }
                            } else if (!_mv_1488.has_value) {
                                context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("typedef void* "), c_name, SLOP_STR(";")));
                            }
                        } else if (!_mv_1487.has_value) {
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
    __auto_type _mv_1489 = (*expr);
    switch (_mv_1489.tag) {
        case types_SExpr_num:
        {
            __auto_type num = _mv_1489.data.num;
            return num.raw;
        }
        default: {
            return SLOP_STR("0");
        }
    }
}

uint8_t transpiler_is_range_type_body(types_SExpr* body_expr) {
    SLOP_PRE(((body_expr != NULL)), "(!= body-expr nil)");
    __auto_type _mv_1490 = (*body_expr);
    switch (_mv_1490.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1490.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type found_dots = 0;
                __auto_type i = 0;
                while ((i < len) && !(found_dots)) {
                    __auto_type _mv_1491 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1491.has_value) {
                        __auto_type item = _mv_1491.value;
                        __auto_type _mv_1492 = (*item);
                        switch (_mv_1492.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1492.data.sym;
                                if (string_eq(sym.name, SLOP_STR(".."))) {
                                    found_dots = 1;
                                }
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_1491.has_value) {
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
        int64_t min_val = 0;
        int64_t max_val = 0;
        uint8_t has_min = 0;
        uint8_t has_max = 0;
        uint8_t found_dots = 0;
        __auto_type _mv_1493 = (*body_expr);
        switch (_mv_1493.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1493.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    __auto_type i = 1;
                    while (i < len) {
                        __auto_type _mv_1494 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1494.has_value) {
                            __auto_type item = _mv_1494.value;
                            __auto_type _mv_1495 = (*item);
                            switch (_mv_1495.tag) {
                                case types_SExpr_num:
                                {
                                    __auto_type num = _mv_1495.data.num;
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
                                    __auto_type sym = _mv_1495.data.sym;
                                    if (string_eq(sym.name, SLOP_STR(".."))) {
                                        found_dots = 1;
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1494.has_value) {
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

slop_string transpiler_select_smallest_c_type_header(int64_t min_val, int64_t max_val, uint8_t has_min, uint8_t has_max) {
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
        if (has_min && has_max) {
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
        int64_t i = start;
        uint8_t emitted_any = 0;
        while (i < len) {
            __auto_type _mv_1496 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1496.has_value) {
                __auto_type item = _mv_1496.value;
                if (transpiler_is_type_def(item) && transpiler_is_struct_type_def(item)) {
                    __auto_type _mv_1497 = transpiler_get_type_name(item);
                    if (_mv_1497.has_value) {
                        __auto_type type_name = _mv_1497.value;
                        {
                            __auto_type base_name = ctype_to_c_name(arena, type_name);
                            __auto_type c_name = ((context_ctx_prefixing_enabled(ctx)) ? ({ __auto_type _mv = context_ctx_get_module(ctx); _mv.has_value ? ({ __auto_type mod_name = _mv.value; context_ctx_str(ctx, ctype_to_c_name(arena, mod_name), context_ctx_str(ctx, SLOP_STR("_"), base_name)); }) : (base_name); }) : base_name);
                            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("typedef struct "), c_name, context_ctx_str(ctx, SLOP_STR(" "), context_ctx_str(ctx, c_name, SLOP_STR(";")))));
                            emitted_any = 1;
                        }
                    } else if (!_mv_1497.has_value) {
                    }
                }
            } else if (!_mv_1496.has_value) {
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
        int64_t i = start;
        uint8_t emitted_any = 0;
        while (i < len) {
            __auto_type _mv_1498 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1498.has_value) {
                __auto_type item = _mv_1498.value;
                if (transpiler_is_fn_def(item)) {
                    defn_emit_forward_declaration(ctx, item);
                    emitted_any = 1;
                }
            } else if (!_mv_1498.has_value) {
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
        int64_t i = start;
        uint8_t emitted_any = 0;
        while (i < len) {
            __auto_type _mv_1499 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1499.has_value) {
                __auto_type item = _mv_1499.value;
                if (transpiler_is_fn_def(item)) {
                    transpiler_emit_fn_forward_decl_header(ctx, item);
                    emitted_any = 1;
                }
            } else if (!_mv_1499.has_value) {
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
        int64_t i = 0;
        if (len > 0) {
            context_ctx_emit_header(ctx, SLOP_STR("/* Function name aliases for C interop */"));
            while (i < len) {
                __auto_type _mv_1500 = ({ __auto_type _lst = aliases; size_t _idx = (size_t)i; slop_option_context_FuncCNameAlias _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1500.has_value) {
                    __auto_type alias = _mv_1500.value;
                    context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), context_ctx_str(ctx, alias.mangled_name, context_ctx_str(ctx, SLOP_STR(" "), alias.clean_name))));
                } else if (!_mv_1500.has_value) {
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
        __auto_type _mv_1501 = (*expr);
        switch (_mv_1501.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1501.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len >= 3) {
                        __auto_type _mv_1502 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1502.has_value) {
                            __auto_type name_expr = _mv_1502.value;
                            __auto_type _mv_1503 = (*name_expr);
                            switch (_mv_1503.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_1503.data.sym;
                                    {
                                        __auto_type raw_name = name_sym.name;
                                        __auto_type base_name = ctype_to_c_name(arena, raw_name);
                                        __auto_type mangled_name = ((string_eq(base_name, SLOP_STR("main"))) ? base_name : context_ctx_prefix_type(ctx, base_name));
                                        __auto_type fn_name = context_extract_fn_c_name(arena, items, mangled_name);
                                        __auto_type _mv_1504 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1504.has_value) {
                                            __auto_type params_expr = _mv_1504.value;
                                            {
                                                __auto_type result_type_opt = defn_get_result_type_name(ctx, items);
                                                __auto_type raw_return = defn_get_return_type(ctx, items);
                                                {
                                                    slop_string return_type = ({ __auto_type _mv = result_type_opt; _mv.has_value ? ({ __auto_type result_name = _mv.value; result_name; }) : (raw_return); });
                                                    __auto_type actual_return = ((string_eq(base_name, SLOP_STR("main"))) ? SLOP_STR("int") : return_type);
                                                    __auto_type param_str = ((string_eq(base_name, SLOP_STR("main"))) ? SLOP_STR("int argc, char** _c_argv") : defn_build_param_str(ctx, params_expr));
                                                    context_ctx_emit_header(ctx, context_ctx_str5(ctx, actual_return, SLOP_STR(" "), fn_name, SLOP_STR("("), context_ctx_str(ctx, ((string_eq(param_str, SLOP_STR(""))) ? SLOP_STR("void") : param_str), SLOP_STR(");"))));
                                                }
                                            }
                                        } else if (!_mv_1504.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1502.has_value) {
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
    __auto_type _mv_1505 = (*item);
    switch (_mv_1505.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1505.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 2) {
                    return (slop_option_string){.has_value = false};
                } else {
                    __auto_type _mv_1506 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1506.has_value) {
                        __auto_type name_expr = _mv_1506.value;
                        __auto_type _mv_1507 = (*name_expr);
                        switch (_mv_1507.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1507.data.sym;
                                return (slop_option_string){.has_value = 1, .value = sym.name};
                            }
                            default: {
                                return (slop_option_string){.has_value = false};
                            }
                        }
                    } else if (!_mv_1506.has_value) {
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

void transpiler_emit_module_types(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = start;
        while (i < len) {
            __auto_type _mv_1508 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1508.has_value) {
                __auto_type item = _mv_1508.value;
                if (transpiler_is_type_def(item)) {
                    defn_transpile_type(ctx, item);
                    context_ctx_emit(ctx, SLOP_STR(""));
                }
            } else if (!_mv_1508.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_type_aliases(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = start;
        uint8_t emitted_any = 0;
        while (i < len) {
            __auto_type _mv_1509 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1509.has_value) {
                __auto_type item = _mv_1509.value;
                if (transpiler_is_type_def(item) && transpiler_is_type_alias_def(item)) {
                    defn_transpile_type(ctx, item);
                    emitted_any = 1;
                }
            } else if (!_mv_1509.has_value) {
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
        int64_t i = start;
        uint8_t emitted_any = 0;
        while (i < len) {
            __auto_type _mv_1510 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1510.has_value) {
                __auto_type item = _mv_1510.value;
                if (transpiler_is_type_def(item) && transpiler_is_simple_enum_def(item)) {
                    defn_transpile_type(ctx, item);
                    emitted_any = 1;
                }
            } else if (!_mv_1510.has_value) {
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
        int64_t i = start;
        while (i < len) {
            __auto_type _mv_1511 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1511.has_value) {
                __auto_type item = _mv_1511.value;
                if (transpiler_is_type_def(item) && transpiler_is_struct_type_def(item)) {
                    defn_transpile_type(ctx, item);
                    context_ctx_emit(ctx, SLOP_STR(""));
                }
            } else if (!_mv_1511.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1512 = ({ __auto_type _lst = result_types; size_t _idx = (size_t)i; slop_option_context_ResultType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1512.has_value) {
                __auto_type rt = _mv_1512.value;
                transpiler_emit_single_result_type(ctx, rt);
            } else if (!_mv_1512.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1513 = ({ __auto_type _lst = result_types; size_t _idx = (size_t)i; slop_option_context_ResultType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1513.has_value) {
                __auto_type rt = _mv_1513.value;
                transpiler_emit_single_result_type_header(ctx, rt);
            } else if (!_mv_1513.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1514 = ({ __auto_type _lst = inline_records; size_t _idx = (size_t)i; slop_option_context_InlineRecord _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1514.has_value) {
                __auto_type ir = _mv_1514.value;
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
            } else if (!_mv_1514.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1515 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1515.has_value) {
                __auto_type ot = _mv_1515.value;
                if (transpiler_is_pointer_elem_type(ot.inner_type)) {
                    transpiler_emit_single_option_type_header(ctx, ot);
                }
            } else if (!_mv_1515.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1516 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1516.has_value) {
                __auto_type ot = _mv_1516.value;
                if (!(transpiler_is_pointer_elem_type(ot.inner_type)) && transpiler_is_type_emitted_or_primitive(ctx, ot.inner_type)) {
                    transpiler_emit_single_option_type_header(ctx, ot);
                }
            } else if (!_mv_1516.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1517 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1517.has_value) {
                __auto_type ot = _mv_1517.value;
                if (!(transpiler_is_pointer_elem_type(ot.inner_type))) {
                    transpiler_emit_single_option_type_header(ctx, ot);
                }
            } else if (!_mv_1517.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1518 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1518.has_value) {
                __auto_type lt = _mv_1518.value;
                if (transpiler_is_pointer_elem_type(lt.elem_type)) {
                    transpiler_emit_single_list_type_header(ctx, lt);
                    transpiler_emit_option_for_inner_type(ctx, lt.c_name);
                }
            } else if (!_mv_1518.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1519 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1519.has_value) {
                __auto_type lt = _mv_1519.value;
                if (!(transpiler_is_pointer_elem_type(lt.elem_type)) && transpiler_is_primitive_or_runtime_type(lt.elem_type)) {
                    transpiler_emit_single_list_type_header(ctx, lt);
                    transpiler_emit_option_for_inner_type(ctx, lt.c_name);
                }
            } else if (!_mv_1519.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1520 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1520.has_value) {
                __auto_type ot = _mv_1520.value;
                if ((!(transpiler_is_pointer_elem_type(ot.inner_type))) && (transpiler_is_primitive_or_runtime_type(ot.inner_type)) && (!(strlib_starts_with(ot.inner_type, SLOP_STR("slop_list_"))))) {
                    transpiler_emit_single_option_type_header(ctx, ot);
                }
            } else if (!_mv_1520.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1521 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1521.has_value) {
                __auto_type lt = _mv_1521.value;
                if ((!(transpiler_is_pointer_elem_type(lt.elem_type))) && (!(transpiler_is_primitive_or_runtime_type(lt.elem_type))) && (transpiler_is_imported_type(ctx, lt.elem_type))) {
                    transpiler_emit_single_list_type_header(ctx, lt);
                    transpiler_emit_option_for_inner_type(ctx, lt.c_name);
                }
            } else if (!_mv_1521.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1522 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1522.has_value) {
                __auto_type ot = _mv_1522.value;
                if ((!(transpiler_is_pointer_elem_type(ot.inner_type))) && (!(transpiler_is_primitive_or_runtime_type(ot.inner_type))) && (!(strlib_starts_with(ot.inner_type, SLOP_STR("slop_list_")))) && (transpiler_is_imported_type(ctx, ot.inner_type))) {
                    transpiler_emit_single_option_type_header(ctx, ot);
                }
            } else if (!_mv_1522.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_late_registered_list_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type list_types = context_ctx_get_list_types(ctx);
        __auto_type len = ((int64_t)((list_types).len));
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1523 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1523.has_value) {
                __auto_type lt = _mv_1523.value;
                transpiler_emit_single_list_type_header(ctx, lt);
            } else if (!_mv_1523.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1524 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1524.has_value) {
                __auto_type ot = _mv_1524.value;
                transpiler_emit_single_option_type_header(ctx, ot);
            } else if (!_mv_1524.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1525 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1525.has_value) {
                __auto_type lt = _mv_1525.value;
                if (!(transpiler_is_pointer_elem_type(lt.elem_type)) && transpiler_is_type_emitted_or_primitive(ctx, lt.elem_type)) {
                    transpiler_emit_single_list_type_header(ctx, lt);
                }
            } else if (!_mv_1525.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1526 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1526.has_value) {
                __auto_type lt = _mv_1526.value;
                if (!(transpiler_is_pointer_elem_type(lt.elem_type)) && !(context_ctx_is_type_emitted(ctx, lt.c_name))) {
                    transpiler_emit_single_list_type_header(ctx, lt);
                }
            } else if (!_mv_1526.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_struct_hash_eq(context_TranspileContext* ctx, slop_string c_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type union_variants = context_ctx_get_union_variants(ctx, c_type);
        if (((int64_t)((union_variants).len)) > 0) {
            transpiler_emit_union_payload_hash_eq(ctx, union_variants);
            transpiler_emit_union_hash_fn(ctx, c_type, union_variants);
            transpiler_emit_union_eq_fn(ctx, c_type, union_variants);
        } else {
            {
                __auto_type fields = context_ctx_get_fields_for_type(ctx, c_type);
                if (((int64_t)((fields).len)) == 0) {
                    context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("SLOP_STRUCT_HASH_EQ_DEFINE("), c_type, SLOP_STR(")")));
                } else {
                    transpiler_emit_record_field_dependencies(ctx, fields);
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1527 = ({ __auto_type _lst = variants; size_t _idx = (size_t)i; slop_option_context_UnionVariantEntry _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1527.has_value) {
                __auto_type variant = _mv_1527.value;
                {
                    __auto_type slop_type = variant.slop_type;
                    __auto_type c_payload_type = variant.c_type;
                    if ((string_len(slop_type) > 0) && !(transpiler_is_primitive_slop_type(slop_type))) {
                        {
                            __auto_type fields = context_ctx_get_fields_for_type(ctx, c_payload_type);
                            if (((int64_t)((fields).len)) > 0) {
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
            } else if (!_mv_1527.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_record_field_dependencies(context_TranspileContext* ctx, slop_list_context_FieldEntry fields) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((fields).len));
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1528 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_context_FieldEntry _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1528.has_value) {
                __auto_type field = _mv_1528.value;
                {
                    __auto_type slop_type = field.slop_type;
                    __auto_type c_type = field.c_type;
                    if (!(transpiler_is_primitive_slop_type(slop_type))) {
                        {
                            __auto_type union_variants = context_ctx_get_union_variants(ctx, c_type);
                            if (((int64_t)((union_variants).len)) > 0) {
                                {
                                    __auto_type guard_name = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, c_type), SLOP_STR("_HASH_EQ_DEFINED"), SLOP_STR(""));
                                    context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), guard_name));
                                    context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), guard_name));
                                    transpiler_emit_union_payload_hash_eq(ctx, union_variants);
                                    transpiler_emit_union_hash_fn(ctx, c_type, union_variants);
                                    transpiler_emit_union_eq_fn(ctx, c_type, union_variants);
                                    context_ctx_emit_header(ctx, SLOP_STR("#endif"));
                                }
                            } else {
                                {
                                    __auto_type nested_fields = context_ctx_get_fields_for_type(ctx, c_type);
                                    if (((int64_t)((nested_fields).len)) > 0) {
                                        {
                                            __auto_type guard_name = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, c_type), SLOP_STR("_HASH_EQ_DEFINED"), SLOP_STR(""));
                                            context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), guard_name));
                                            context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), guard_name));
                                            transpiler_emit_record_field_dependencies(ctx, nested_fields);
                                            transpiler_emit_struct_hash_fn(ctx, c_type, nested_fields);
                                            transpiler_emit_struct_eq_fn(ctx, c_type, nested_fields);
                                            context_ctx_emit_header(ctx, SLOP_STR("#endif"));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            } else if (!_mv_1528.has_value) {
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
    __auto_type _mv_1529 = context_ctx_lookup_type_alias(ctx, slop_type);
    if (_mv_1529.has_value) {
        __auto_type underlying = _mv_1529.value;
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
    } else if (!_mv_1529.has_value) {
        return 0;
    }
    SLOP_UNREACHABLE();
}

uint8_t transpiler_is_unsigned_payload_type(slop_string slop_type) {
    return ((string_eq(slop_type, SLOP_STR("U64"))) || (string_eq(slop_type, SLOP_STR("U32"))) || (string_eq(slop_type, SLOP_STR("U16"))) || (string_eq(slop_type, SLOP_STR("U8"))) || (strlib_starts_with(slop_type, SLOP_STR("(U64"))) || (strlib_starts_with(slop_type, SLOP_STR("(U32"))) || (strlib_starts_with(slop_type, SLOP_STR("(U16"))) || (strlib_starts_with(slop_type, SLOP_STR("(U8"))));
}

uint8_t transpiler_is_narrow_signed_payload_type(slop_string slop_type) {
    return ((string_eq(slop_type, SLOP_STR("I32"))) || (string_eq(slop_type, SLOP_STR("I16"))) || (string_eq(slop_type, SLOP_STR("I8"))) || (strlib_starts_with(slop_type, SLOP_STR("(Int"))) || (strlib_starts_with(slop_type, SLOP_STR("(I64"))) || (strlib_starts_with(slop_type, SLOP_STR("(I32"))) || (strlib_starts_with(slop_type, SLOP_STR("(I16"))) || (strlib_starts_with(slop_type, SLOP_STR("(I8"))));
}

slop_string transpiler_resolve_payload_slop_type(context_TranspileContext* ctx, slop_string slop_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (transpiler_is_range_type_alias(ctx, slop_type)) {
        __auto_type _mv_1530 = context_ctx_lookup_type_alias(ctx, slop_type);
        if (_mv_1530.has_value) {
            __auto_type underlying = _mv_1530.value;
            return underlying;
        } else if (!_mv_1530.has_value) {
            return slop_type;
        }
        SLOP_UNREACHABLE();
    } else {
        return slop_type;
    }
}

void transpiler_container_payload_error(context_TranspileContext* ctx, slop_string slop_type, slop_string c_payload_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type marker = context_ctx_str(ctx, SLOP_STR("containerpayload:"), c_payload_type);
        if (!(context_ctx_is_type_emitted(ctx, marker))) {
            context_ctx_mark_type_emitted(ctx, marker);
            context_ctx_add_error(ctx, context_ctx_str3(ctx, SLOP_STR("union payload of type '"), slop_type, SLOP_STR("' has no structural equality - a container payload cannot be compared with == or keyed in a Map/Set")));
        }
    }
}

slop_string transpiler_payload_hash_expr(context_TranspileContext* ctx, slop_string raw_slop_type, slop_string c_payload_type, slop_string access) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type slop_type = transpiler_resolve_payload_slop_type(ctx, raw_slop_type);
        if (string_eq(slop_type, SLOP_STR("String"))) {
            return context_ctx_str3(ctx, SLOP_STR("slop_hash_string(&"), access, SLOP_STR(")"));
        } else if (string_eq(slop_type, SLOP_STR("Int")) || string_eq(slop_type, SLOP_STR("I64"))) {
            return context_ctx_str3(ctx, SLOP_STR("slop_hash_int(&"), access, SLOP_STR(")"));
        } else if (string_eq(slop_type, SLOP_STR("Bool"))) {
            return context_ctx_str3(ctx, SLOP_STR("((uint64_t)"), access, SLOP_STR(")"));
        } else if (strlib_starts_with(slop_type, SLOP_STR("(Ptr"))) {
            return context_ctx_str3(ctx, SLOP_STR("slop_hash_ptr(&"), access, SLOP_STR(")"));
        } else if (transpiler_is_unsigned_payload_type(slop_type)) {
            return context_ctx_str3(ctx, SLOP_STR("slop_hash_uint(&(uint64_t){ (uint64_t)"), access, SLOP_STR(" })"));
        } else if (transpiler_is_narrow_signed_payload_type(slop_type)) {
            return context_ctx_str3(ctx, SLOP_STR("slop_hash_int(&(int64_t){ (int64_t)"), access, SLOP_STR(" })"));
        } else if (ctype_is_container_c_type(c_payload_type)) {
            transpiler_container_payload_error(ctx, raw_slop_type, c_payload_type);
            return SLOP_STR("0");
        } else {
            return context_ctx_str5(ctx, SLOP_STR("slop_hash_"), c_payload_type, SLOP_STR("(&"), access, SLOP_STR(")"));
        }
    }
}

slop_string transpiler_payload_eq_expr(context_TranspileContext* ctx, slop_string raw_slop_type, slop_string c_payload_type, slop_string a_access, slop_string b_access) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type slop_type = transpiler_resolve_payload_slop_type(ctx, raw_slop_type);
        if (string_eq(slop_type, SLOP_STR("String"))) {
            return context_ctx_str5(ctx, SLOP_STR("slop_eq_string(&"), a_access, SLOP_STR(", &"), b_access, SLOP_STR(")"));
        } else if ((string_eq(slop_type, SLOP_STR("Int"))) || (string_eq(slop_type, SLOP_STR("I64"))) || (string_eq(slop_type, SLOP_STR("Bool"))) || (strlib_starts_with(slop_type, SLOP_STR("(Ptr"))) || (transpiler_is_unsigned_payload_type(slop_type)) || (transpiler_is_narrow_signed_payload_type(slop_type))) {
            return context_ctx_str3(ctx, a_access, SLOP_STR(" == "), b_access);
        } else if (ctype_is_container_c_type(c_payload_type)) {
            transpiler_container_payload_error(ctx, raw_slop_type, c_payload_type);
            return SLOP_STR("false");
        } else {
            return context_ctx_str5(ctx, SLOP_STR("slop_eq_"), c_payload_type, SLOP_STR("(&"), a_access, context_ctx_str3(ctx, SLOP_STR(", &"), b_access, SLOP_STR(")")));
        }
    }
}

slop_list_transpiler_PayloadSlot transpiler_union_variant_payloads(context_TranspileContext* ctx, slop_string union_name, slop_string variant_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type slots = ((slop_list_transpiler_PayloadSlot){ .data = (transpiler_PayloadSlot*)slop_arena_alloc(arena, 16 * sizeof(transpiler_PayloadSlot)), .len = 0, .cap = 16 });
        __auto_type count_key = context_ctx_str(ctx, variant_name, SLOP_STR("__count"));
        __auto_type _mv_1531 = context_ctx_lookup_field_type(ctx, union_name, count_key);
        if (_mv_1531.has_value) {
            __auto_type _ = _mv_1531.value;
            {
                __auto_type i = 0;
                __auto_type more = 1;
                while (more) {
                    {
                        __auto_type key = context_ctx_str3(ctx, variant_name, SLOP_STR("__"), int_to_string(arena, i));
                        __auto_type _mv_1532 = context_ctx_lookup_field_type(ctx, union_name, key);
                        if (_mv_1532.has_value) {
                            __auto_type slot_c_type = _mv_1532.value;
                            {
                                __auto_type slot_slop_type = ({ __auto_type _mv = context_ctx_lookup_field_slop_type(ctx, union_name, key); _mv.has_value ? ({ __auto_type st = _mv.value; st; }) : (SLOP_STR("")); });
                                ({ __auto_type _lst_p = &(slots); __auto_type _item = ((transpiler_PayloadSlot){slot_slop_type, slot_c_type}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                i = (i + 1);
                            }
                        } else if (!_mv_1532.has_value) {
                            more = 0;
                        }
                    }
                }
            }
        } else if (!_mv_1531.has_value) {
        }
        return slots;
    }
}

void transpiler_emit_union_hash_fn(context_TranspileContext* ctx, slop_string c_type, slop_list_context_UnionVariantEntry variants) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("static inline uint64_t slop_hash_"), c_type, SLOP_STR("(const void* key) {")));
    context_ctx_emit_header(ctx, context_ctx_str(ctx, context_ctx_str4(ctx, SLOP_STR("    const "), c_type, SLOP_STR("* _k = (const "), c_type), SLOP_STR("*)key;")));
    context_ctx_emit_header(ctx, SLOP_STR("    switch (_k->tag) {"));
    {
        __auto_type len = ((int64_t)((variants).len));
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1533 = ({ __auto_type _lst = variants; size_t _idx = (size_t)i; slop_option_context_UnionVariantEntry _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1533.has_value) {
                __auto_type variant = _mv_1533.value;
                transpiler_emit_union_variant_hash(ctx, c_type, variant);
            } else if (!_mv_1533.has_value) {
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
        __auto_type payloads = transpiler_union_variant_payloads(ctx, union_name, variant.variant_name);
        context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("        case "), context_ctx_str(ctx, tag_const, SLOP_STR(":"))));
        if (string_eq(slop_type, SLOP_STR(""))) {
            context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("            return (uint64_t)"), context_ctx_str(ctx, tag_const, SLOP_STR(";"))));
        } else if (((int64_t)((payloads).len)) > 0) {
            transpiler_emit_multi_payload_hash(ctx, c_variant_name, payloads);
        } else {
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("            return "), transpiler_payload_hash_expr(ctx, slop_type, c_payload_type, context_ctx_str(ctx, SLOP_STR("_k->data."), c_variant_name)), SLOP_STR(";")));
        }
    }
}

void transpiler_emit_multi_payload_hash(context_TranspileContext* ctx, slop_string c_variant_name, slop_list_transpiler_PayloadSlot payloads) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((payloads).len));
        int64_t i = 0;
        context_ctx_emit_header(ctx, SLOP_STR("            {"));
        context_ctx_emit_header(ctx, SLOP_STR("                uint64_t hash = 14695981039346656037ULL;"));
        while (i < len) {
            __auto_type _mv_1534 = ({ __auto_type _lst = payloads; size_t _idx = (size_t)i; slop_option_transpiler_PayloadSlot _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1534.has_value) {
                __auto_type slot = _mv_1534.value;
                {
                    __auto_type access = context_ctx_str4(ctx, SLOP_STR("_k->data."), c_variant_name, SLOP_STR(".f"), int_to_string(arena, i));
                    context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("                hash ^= "), transpiler_payload_hash_expr(ctx, slot.slop_type, slot.c_type, access), SLOP_STR("; hash *= 1099511628211ULL;")));
                }
            } else if (!_mv_1534.has_value) {
            }
            i = (i + 1);
        }
        context_ctx_emit_header(ctx, SLOP_STR("                return hash;"));
        context_ctx_emit_header(ctx, SLOP_STR("            }"));
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1535 = ({ __auto_type _lst = variants; size_t _idx = (size_t)i; slop_option_context_UnionVariantEntry _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1535.has_value) {
                __auto_type variant = _mv_1535.value;
                transpiler_emit_union_variant_eq(ctx, c_type, variant);
            } else if (!_mv_1535.has_value) {
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
        __auto_type payloads = transpiler_union_variant_payloads(ctx, union_name, variant.variant_name);
        context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("        case "), context_ctx_str(ctx, tag_const, SLOP_STR(":"))));
        if (string_eq(slop_type, SLOP_STR(""))) {
            context_ctx_emit_header(ctx, SLOP_STR("            return true;"));
        } else if (((int64_t)((payloads).len)) > 0) {
            transpiler_emit_multi_payload_eq(ctx, c_variant_name, payloads);
        } else {
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("            return "), transpiler_payload_eq_expr(ctx, slop_type, c_payload_type, context_ctx_str(ctx, SLOP_STR("_a->data."), c_variant_name), context_ctx_str(ctx, SLOP_STR("_b->data."), c_variant_name)), SLOP_STR(";")));
        }
    }
}

void transpiler_emit_multi_payload_eq(context_TranspileContext* ctx, slop_string c_variant_name, slop_list_transpiler_PayloadSlot payloads) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((payloads).len));
        int64_t i = 0;
        context_ctx_emit_header(ctx, SLOP_STR("            return true"));
        while (i < len) {
            __auto_type _mv_1536 = ({ __auto_type _lst = payloads; size_t _idx = (size_t)i; slop_option_transpiler_PayloadSlot _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1536.has_value) {
                __auto_type slot = _mv_1536.value;
                {
                    __auto_type a_access = context_ctx_str4(ctx, SLOP_STR("_a->data."), c_variant_name, SLOP_STR(".f"), int_to_string(arena, i));
                    __auto_type b_access = context_ctx_str4(ctx, SLOP_STR("_b->data."), c_variant_name, SLOP_STR(".f"), int_to_string(arena, i));
                    context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("                && "), transpiler_payload_eq_expr(ctx, slot.slop_type, slot.c_type, a_access, b_access)));
                }
            } else if (!_mv_1536.has_value) {
            }
            i = (i + 1);
        }
        context_ctx_emit_header(ctx, SLOP_STR("            ;"));
    }
}

void transpiler_emit_struct_hash_fn(context_TranspileContext* ctx, slop_string c_type, slop_list_context_FieldEntry fields) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("static inline uint64_t slop_hash_"), c_type, SLOP_STR("(const void* key) {")));
    context_ctx_emit_header(ctx, context_ctx_str(ctx, context_ctx_str4(ctx, SLOP_STR("    const "), c_type, SLOP_STR("* _k = (const "), c_type), SLOP_STR("*)key;")));
    context_ctx_emit_header(ctx, SLOP_STR("    uint64_t hash = 14695981039346656037ULL;"));
    {
        __auto_type len = ((int64_t)((fields).len));
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1537 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_context_FieldEntry _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1537.has_value) {
                __auto_type field = _mv_1537.value;
                transpiler_emit_field_hash(ctx, field);
            } else if (!_mv_1537.has_value) {
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
        } else if (string_eq(slop_type, SLOP_STR("Int")) || string_eq(slop_type, SLOP_STR("I64"))) {
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    hash ^= slop_hash_int(&_k->"), c_field_name, SLOP_STR("); hash *= 1099511628211ULL;")));
        } else if (string_eq(slop_type, SLOP_STR("I32")) || (string_eq(slop_type, SLOP_STR("I16")) || string_eq(slop_type, SLOP_STR("I8")))) {
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    { int64_t _tmp = (int64_t)_k->"), c_field_name, SLOP_STR("; hash ^= slop_hash_int(&_tmp); hash *= 1099511628211ULL; }")));
        } else if (string_eq(slop_type, SLOP_STR("U64")) || (string_eq(slop_type, SLOP_STR("U32")) || (string_eq(slop_type, SLOP_STR("U16")) || string_eq(slop_type, SLOP_STR("U8"))))) {
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    { uint64_t _tmp = (uint64_t)_k->"), c_field_name, SLOP_STR("; hash ^= slop_hash_uint(&_tmp); hash *= 1099511628211ULL; }")));
        } else if (string_eq(slop_type, SLOP_STR("Bool"))) {
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    hash ^= (uint64_t)_k->"), c_field_name, SLOP_STR("; hash *= 1099511628211ULL;")));
        } else if (strlib_starts_with(slop_type, SLOP_STR("(Ptr"))) {
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    hash ^= slop_hash_ptr(&_k->"), c_field_name, SLOP_STR("); hash *= 1099511628211ULL;")));
        } else if (strlib_starts_with(slop_type, SLOP_STR("(List")) || (strlib_starts_with(slop_type, SLOP_STR("(Map")) || (strlib_starts_with(slop_type, SLOP_STR("(Set")) || (strlib_starts_with(slop_type, SLOP_STR("(Option")) || strlib_starts_with(slop_type, SLOP_STR("(Result")))))) {
            {
                __auto_type c_type = field.c_type;
                context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("    { const uint8_t* _b = (const uint8_t*)&_k->"), c_field_name, SLOP_STR("; for(size_t _i=0; _i<sizeof(_k->"), c_field_name, SLOP_STR("); _i++) { hash ^= _b[_i]; hash *= 1099511628211ULL; } }")));
            }
        } else if (transpiler_is_range_type_alias(ctx, slop_type)) {
            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("    { int64_t _tmp = (int64_t)_k->"), c_field_name, SLOP_STR("; hash ^= slop_hash_int(&_tmp); hash *= 1099511628211ULL; }")));
        } else if (((int64_t)((context_ctx_get_union_variants(ctx, field.c_type)).len)) > 0) {
            {
                __auto_type nested_c_type = field.c_type;
                context_ctx_register_struct_key_type(ctx, nested_c_type);
                context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("    hash ^= slop_hash_"), nested_c_type, SLOP_STR("(&_k->"), c_field_name, SLOP_STR("); hash *= 1099511628211ULL;")));
            }
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
        if (len == 0) {
            context_ctx_emit_header(ctx, SLOP_STR("    return true;"));
        } else {
            context_ctx_emit_header(ctx, SLOP_STR("    return true"));
            {
                int64_t i = 0;
                while (i < len) {
                    __auto_type _mv_1538 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_context_FieldEntry _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1538.has_value) {
                        __auto_type field = _mv_1538.value;
                        transpiler_emit_field_eq(ctx, field);
                    } else if (!_mv_1538.has_value) {
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
        } else if (string_eq(slop_type, SLOP_STR("Int")) || (string_eq(slop_type, SLOP_STR("I64")) || (string_eq(slop_type, SLOP_STR("I32")) || (string_eq(slop_type, SLOP_STR("I16")) || (string_eq(slop_type, SLOP_STR("I8")) || (string_eq(slop_type, SLOP_STR("U64")) || (string_eq(slop_type, SLOP_STR("U32")) || (string_eq(slop_type, SLOP_STR("U16")) || string_eq(slop_type, SLOP_STR("U8")))))))))) {
            context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("        && _a->"), c_field_name, SLOP_STR(" == _b->"), c_field_name));
        } else if (string_eq(slop_type, SLOP_STR("Bool"))) {
            context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("        && _a->"), c_field_name, SLOP_STR(" == _b->"), c_field_name));
        } else if (strlib_starts_with(slop_type, SLOP_STR("(Ptr"))) {
            context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("        && _a->"), c_field_name, SLOP_STR(" == _b->"), c_field_name));
        } else if (strlib_starts_with(slop_type, SLOP_STR("(List")) || (strlib_starts_with(slop_type, SLOP_STR("(Map")) || (strlib_starts_with(slop_type, SLOP_STR("(Set")) || (strlib_starts_with(slop_type, SLOP_STR("(Option")) || strlib_starts_with(slop_type, SLOP_STR("(Result")))))) {
            {
                __auto_type c_type = field.c_type;
                context_ctx_emit_header(ctx, context_ctx_str(ctx, context_ctx_str(ctx, context_ctx_str5(ctx, SLOP_STR("        && memcmp(&_a->"), c_field_name, SLOP_STR(", &_b->"), c_field_name, SLOP_STR(", sizeof(_a->")), c_field_name), SLOP_STR(")) == 0")));
            }
        } else if (transpiler_is_range_type_alias(ctx, slop_type)) {
            context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("        && _a->"), c_field_name, SLOP_STR(" == _b->"), c_field_name));
        } else if (((int64_t)((context_ctx_get_union_variants(ctx, field.c_type)).len)) > 0) {
            {
                __auto_type nested_c_type = field.c_type;
                context_ctx_register_struct_key_type(ctx, nested_c_type);
                context_ctx_emit_header(ctx, context_ctx_str(ctx, context_ctx_str5(ctx, SLOP_STR("        && slop_eq_"), nested_c_type, SLOP_STR("(&_a->"), c_field_name, SLOP_STR(", &_b->")), context_ctx_str(ctx, c_field_name, SLOP_STR(")"))));
            }
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
        uint8_t banner = 0;
        int64_t i = 0;
        while (i < ((int64_t)((struct_key_types).len))) {
            __auto_type _mv_1539 = ({ __auto_type _lst = struct_key_types; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1539.has_value) {
                __auto_type c_type = _mv_1539.value;
                {
                    __auto_type emitted_marker = context_ctx_str(ctx, SLOP_STR("hasheq:"), c_type);
                    if (!(context_ctx_is_type_emitted(ctx, emitted_marker))) {
                        {
                            __auto_type guard_name = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, c_type), SLOP_STR("_HASH_EQ_DEFINED"), SLOP_STR(""));
                            __auto_type list_c_name = context_ctx_str(ctx, SLOP_STR("slop_list_"), ctype_type_to_identifier((*ctx).arena, c_type));
                            context_ctx_mark_type_emitted(ctx, emitted_marker);
                            if (!(banner)) {
                                banner = 1;
                                context_ctx_emit_header(ctx, SLOP_STR(""));
                                context_ctx_emit_header(ctx, SLOP_STR("/* Hash/eq functions and list types for struct map/set keys */"));
                            }
                            context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), guard_name));
                            context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), guard_name));
                            transpiler_emit_struct_hash_eq(ctx, c_type);
                            if (!(context_ctx_is_type_emitted(ctx, list_c_name))) {
                                {
                                    __auto_type list_guard = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, list_c_name), SLOP_STR("_DEFINED"), SLOP_STR(""));
                                    __auto_type impl_guard = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, list_c_name), SLOP_STR("_IMPL_DEFINED"), SLOP_STR(""));
                                    context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), list_guard));
                                    context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), list_guard));
                                    context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), impl_guard));
                                    context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("SLOP_LIST_DEFINE("), c_type, SLOP_STR(", "), list_c_name, SLOP_STR(")")));
                                    context_ctx_emit_header(ctx, SLOP_STR("#endif"));
                                }
                                context_ctx_mark_type_emitted(ctx, list_c_name);
                            }
                            context_ctx_emit_header(ctx, SLOP_STR("#endif"));
                            context_ctx_emit_header(ctx, SLOP_STR(""));
                        }
                    }
                }
            } else if (!_mv_1539.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_late_registered_struct_key_types_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    transpiler_emit_struct_key_types_header(ctx);
}

uint8_t transpiler_is_pointer_elem_type(slop_string elem_type) {
    {
        __auto_type len = ((int64_t)(elem_type.len));
        if (len <= 0) {
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
        __auto_type arena = (*ctx).arena;
        if (!(transpiler_is_runtime_list_type(c_name))) {
            {
                __auto_type decl_marker = string_concat(arena, SLOP_STR("decl:"), c_name);
                if (context_ctx_is_type_emitted(ctx, decl_marker)) {
                    {
                        __auto_type impl_guard = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, c_name), SLOP_STR("_IMPL_DEFINED"), SLOP_STR(""));
                        context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), impl_guard));
                        context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), impl_guard));
                        context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("SLOP_LIST_IMPL("), elem_type, SLOP_STR(", "), c_name, SLOP_STR(")")));
                        context_ctx_emit_header(ctx, SLOP_STR("#endif"));
                        context_ctx_emit_header(ctx, SLOP_STR(""));
                    }
                } else if (context_ctx_is_type_emitted(ctx, c_name)) {
                } else {
                    {
                        __auto_type guard_name = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, c_name), SLOP_STR("_DEFINED"), SLOP_STR(""));
                        __auto_type impl_guard = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, c_name), SLOP_STR("_IMPL_DEFINED"), SLOP_STR(""));
                        context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), guard_name));
                        context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), guard_name));
                        context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), impl_guard));
                        context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("SLOP_LIST_DEFINE("), elem_type, SLOP_STR(", "), c_name, SLOP_STR(")")));
                        context_ctx_emit_header(ctx, SLOP_STR("#endif"));
                        context_ctx_emit_header(ctx, SLOP_STR(""));
                        context_ctx_mark_type_emitted(ctx, c_name);
                    }
                }
            }
        }
    }
}

void transpiler_emit_list_type_declare_only(context_TranspileContext* ctx, context_ListType lt) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type elem_type = lt.elem_type;
        __auto_type c_name = lt.c_name;
        __auto_type arena = (*ctx).arena;
        if (!(transpiler_is_runtime_list_type(c_name))) {
            if (!(context_ctx_is_type_emitted(ctx, c_name))) {
                {
                    __auto_type guard_name = context_ctx_str3(ctx, transpiler_uppercase_name(ctx, c_name), SLOP_STR("_DEFINED"), SLOP_STR(""));
                    __auto_type decl_marker = string_concat(arena, SLOP_STR("decl:"), c_name);
                    context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#ifndef "), guard_name));
                    context_ctx_emit_header(ctx, context_ctx_str(ctx, SLOP_STR("#define "), guard_name));
                    context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("SLOP_LIST_DECLARE("), elem_type, SLOP_STR(", "), c_name, SLOP_STR(")")));
                    context_ctx_emit_header(ctx, SLOP_STR("#endif"));
                    context_ctx_emit_header(ctx, SLOP_STR(""));
                    context_ctx_mark_type_emitted(ctx, c_name);
                    context_ctx_mark_type_emitted(ctx, decl_marker);
                }
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1540 = ({ __auto_type _lst = chan_types; size_t _idx = (size_t)i; slop_option_context_ChanType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1540.has_value) {
                __auto_type ct = _mv_1540.value;
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
            } else if (!_mv_1540.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1541 = ({ __auto_type _lst = chan_types; size_t _idx = (size_t)i; slop_option_context_ChanType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1541.has_value) {
                __auto_type ct = _mv_1541.value;
                {
                    __auto_type elem_type = ct.elem_type;
                    __auto_type c_name = ct.c_name;
                    if (!(transpiler_is_runtime_chan_type(c_name)) && !(transpiler_is_default_chan_type(c_name))) {
                        transpiler_emit_chan_send_recv_funcs(ctx, c_name, elem_type);
                    }
                }
            } else if (!_mv_1541.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1542 = ({ __auto_type _lst = thread_types; size_t _idx = (size_t)i; slop_option_context_ThreadType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1542.has_value) {
                __auto_type tt = _mv_1542.value;
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
            } else if (!_mv_1542.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            {
                __auto_type c = ((int64_t)(data[i]));
                if ((c >= 97) && (c <= 122)) {
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
    __auto_type _mv_1543 = (*item);
    switch (_mv_1543.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1543.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 3) {
                    return 0;
                } else {
                    __auto_type _mv_1544 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1544.has_value) {
                        __auto_type def_expr = _mv_1544.value;
                        __auto_type _mv_1545 = (*def_expr);
                        switch (_mv_1545.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type def_lst = _mv_1545.data.lst;
                                {
                                    __auto_type def_items = def_lst.items;
                                    if (((int64_t)((def_items).len)) < 1) {
                                        return 0;
                                    } else {
                                        __auto_type _mv_1546 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1546.has_value) {
                                            __auto_type head = _mv_1546.value;
                                            __auto_type _mv_1547 = (*head);
                                            switch (_mv_1547.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type sym = _mv_1547.data.sym;
                                                    return (string_eq(sym.name, SLOP_STR("enum")) && !(transpiler_has_enum_payload_variants(def_items)));
                                                }
                                                default: {
                                                    return 0;
                                                }
                                            }
                                        } else if (!_mv_1546.has_value) {
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
                    } else if (!_mv_1544.has_value) {
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

void transpiler_emit_module_types_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        int64_t i = start;
        while (i < len) {
            __auto_type _mv_1548 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1548.has_value) {
                __auto_type item = _mv_1548.value;
                if (transpiler_is_type_def(item) && transpiler_is_type_alias_def(item)) {
                    transpiler_emit_type_alias_to_header(ctx, item);
                }
            } else if (!_mv_1548.has_value) {
            }
            i = (i + 1);
        }
        i = start;
        while (i < len) {
            __auto_type _mv_1549 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1549.has_value) {
                __auto_type item = _mv_1549.value;
                if (transpiler_is_type_def(item) && transpiler_is_simple_enum_def(item)) {
                    transpiler_emit_type_to_header(ctx, item);
                }
            } else if (!_mv_1549.has_value) {
            }
            i = (i + 1);
        }
        i = start;
        while (i < len) {
            __auto_type _mv_1550 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1550.has_value) {
                __auto_type item = _mv_1550.value;
                if (transpiler_is_type_def(item) && transpiler_is_struct_type_def(item)) {
                    transpiler_emit_type_to_header(ctx, item);
                }
            } else if (!_mv_1550.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_simple_type_aliases_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = start;
        while (i < len) {
            __auto_type _mv_1551 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1551.has_value) {
                __auto_type item = _mv_1551.value;
                if ((transpiler_is_type_def(item)) && (transpiler_is_type_alias_def(item)) && ((!(transpiler_is_result_type_alias_def(item)) || transpiler_container_alias_ready(ctx, item)))) {
                    transpiler_emit_type_alias_to_header(ctx, item);
                }
            } else if (!_mv_1551.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_type_aliases_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = start;
        while (i < len) {
            __auto_type _mv_1552 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1552.has_value) {
                __auto_type item = _mv_1552.value;
                if ((transpiler_is_type_def(item)) && (transpiler_is_type_alias_def(item)) && (transpiler_is_result_type_alias_def(item)) && (!(context_ctx_is_type_emitted(ctx, transpiler_alias_own_c_name(ctx, item))))) {
                    transpiler_emit_type_alias_to_header(ctx, item);
                }
            } else if (!_mv_1552.has_value) {
            }
            i = (i + 1);
        }
    }
}

void transpiler_emit_simple_enums_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = start;
        while (i < len) {
            __auto_type _mv_1553 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1553.has_value) {
                __auto_type item = _mv_1553.value;
                if (transpiler_is_type_def(item) && transpiler_is_simple_enum_def(item)) {
                    transpiler_emit_type_to_header(ctx, item);
                }
            } else if (!_mv_1553.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1554 = ({ __auto_type _lst = field_types; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1554.has_value) {
                __auto_type field_type = _mv_1554.value;
                if (!(context_ctx_is_type_emitted(ctx, field_type)) && transpiler_is_emittable_container_type(ctx, field_type)) {
                    if (strlib_starts_with(field_type, SLOP_STR("slop_option_"))) {
                        transpiler_emit_option_by_c_name(ctx, field_type);
                    }
                    if (strlib_starts_with(field_type, SLOP_STR("slop_list_"))) {
                        transpiler_emit_list_by_c_name(ctx, field_type);
                    }
                }
            } else if (!_mv_1554.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1555 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1555.has_value) {
                __auto_type ot = _mv_1555.value;
                if (string_eq(ot.c_name, c_name)) {
                    transpiler_emit_single_option_type_header(ctx, ot);
                }
            } else if (!_mv_1555.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1556 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1556.has_value) {
                __auto_type lt = _mv_1556.value;
                if (string_eq(lt.c_name, c_name)) {
                    transpiler_emit_single_list_type_header(ctx, lt);
                }
            } else if (!_mv_1556.has_value) {
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
        int64_t prev_count = -1;
        int64_t current_count = 0;
        while (prev_count != current_count) {
            prev_count = current_count;
            {
                int64_t i = start;
                while (i < len) {
                    if (!(transpiler_index_in_list(emitted, i))) {
                        __auto_type _mv_1557 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1557.has_value) {
                            __auto_type item = _mv_1557.value;
                            if (transpiler_is_type_def(item) && transpiler_is_struct_type_def(item)) {
                                if (transpiler_type_deps_satisfied(ctx, item)) {
                                    transpiler_emit_pending_container_deps(ctx, item);
                                    transpiler_emit_type_to_header(ctx, item);
                                    ({ __auto_type _lst_p = &(emitted); __auto_type _item = (i); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    current_count = (current_count + 1);
                                    transpiler_emit_option_list_for_type(ctx, item);
                                }
                            }
                        } else if (!_mv_1557.has_value) {
                        }
                    }
                    i = (i + 1);
                }
            }
        }
        if (transpiler_has_unemitted_struct_types(items, start, len, emitted)) {
            transpiler_break_list_cycles(ctx, items, start, len, emitted);
            prev_count = -1;
            current_count = ((int64_t)((emitted).len));
            while (prev_count != current_count) {
                prev_count = current_count;
                {
                    int64_t i = start;
                    while (i < len) {
                        if (!(transpiler_index_in_list(emitted, i))) {
                            __auto_type _mv_1558 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1558.has_value) {
                                __auto_type item = _mv_1558.value;
                                if (transpiler_is_type_def(item) && transpiler_is_struct_type_def(item)) {
                                    if (transpiler_type_deps_satisfied(ctx, item)) {
                                        transpiler_emit_pending_container_deps(ctx, item);
                                        transpiler_emit_type_to_header(ctx, item);
                                        ({ __auto_type _lst_p = &(emitted); __auto_type _item = (i); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                        current_count = (current_count + 1);
                                        transpiler_emit_option_list_for_type(ctx, item);
                                    }
                                }
                            } else if (!_mv_1558.has_value) {
                            }
                        }
                        i = (i + 1);
                    }
                }
            }
        }
    }
}

uint8_t transpiler_has_unemitted_struct_types(slop_list_types_SExpr_ptr items, int64_t start, int64_t len, slop_list_int emitted) {
    {
        int64_t i = start;
        uint8_t found = 0;
        while ((i < len) && !(found)) {
            if (!(transpiler_index_in_list(emitted, i))) {
                __auto_type _mv_1559 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1559.has_value) {
                    __auto_type item = _mv_1559.value;
                    if (transpiler_is_type_def(item) && transpiler_is_struct_type_def(item)) {
                        found = 1;
                    }
                } else if (!_mv_1559.has_value) {
                }
            }
            i = (i + 1);
        }
        return found;
    }
}

void transpiler_break_list_cycles(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start, int64_t len, slop_list_int emitted) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        int64_t i = start;
        while (i < len) {
            if (!(transpiler_index_in_list(emitted, i))) {
                __auto_type _mv_1560 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1560.has_value) {
                    __auto_type item = _mv_1560.value;
                    if (transpiler_is_type_def(item) && transpiler_is_struct_type_def(item)) {
                        {
                            __auto_type blocking_deps = transpiler_find_blocking_list_deps(ctx, item);
                            __auto_type dep_len = ((int64_t)((blocking_deps).len));
                            __auto_type j = 0;
                            while (j < dep_len) {
                                __auto_type _mv_1561 = ({ __auto_type _lst = blocking_deps; size_t _idx = (size_t)j; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1561.has_value) {
                                    __auto_type dep_name = _mv_1561.value;
                                    transpiler_emit_list_declare_by_c_name(ctx, dep_name);
                                } else if (!_mv_1561.has_value) {
                                }
                                j = (j + 1);
                            }
                        }
                    }
                } else if (!_mv_1560.has_value) {
                }
            }
            i = (i + 1);
        }
    }
}

slop_list_string transpiler_find_blocking_list_deps(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type field_types = transpiler_get_type_field_types(ctx, type_def);
        __auto_type len = ((int64_t)((field_types).len));
        __auto_type result = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1562 = ({ __auto_type _lst = field_types; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1562.has_value) {
                __auto_type field_type = _mv_1562.value;
                if ((strlib_starts_with(field_type, SLOP_STR("slop_list_"))) && (!(context_ctx_is_type_emitted(ctx, field_type))) && (!(transpiler_is_runtime_list_type(field_type)))) {
                    ({ __auto_type _lst_p = &(result); __auto_type _item = (field_type); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                }
            } else if (!_mv_1562.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

void transpiler_emit_list_declare_by_c_name(context_TranspileContext* ctx, slop_string c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type list_types = context_ctx_get_list_types(ctx);
        __auto_type len = ((int64_t)((list_types).len));
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1563 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1563.has_value) {
                __auto_type lt = _mv_1563.value;
                if (string_eq(lt.c_name, c_name)) {
                    transpiler_emit_list_type_declare_only(ctx, lt);
                }
            } else if (!_mv_1563.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t transpiler_index_in_list(slop_list_int lst, int64_t idx) {
    {
        __auto_type len = ((int64_t)((lst).len));
        int64_t i = 0;
        uint8_t found = 0;
        while ((i < len) && !(found)) {
            __auto_type _mv_1564 = ({ __auto_type _lst = lst; size_t _idx = (size_t)i; slop_option_int _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1564.has_value) {
                __auto_type v = _mv_1564.value;
                if (v == idx) {
                    found = 1;
                }
            } else if (!_mv_1564.has_value) {
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
        int64_t i = 0;
        uint8_t all_satisfied = 1;
        while ((i < len) && all_satisfied) {
            __auto_type _mv_1565 = ({ __auto_type _lst = field_types; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1565.has_value) {
                __auto_type field_type = _mv_1565.value;
                if (!(transpiler_type_is_available(ctx, field_type))) {
                    all_satisfied = 0;
                }
            } else if (!_mv_1565.has_value) {
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
    return ((string_eq(type_name, SLOP_STR("Int"))) || (string_eq(type_name, SLOP_STR("Bool"))) || (string_eq(type_name, SLOP_STR("String"))) || (string_eq(type_name, SLOP_STR("Unit"))) || (string_eq(type_name, SLOP_STR("U8"))) || (string_eq(type_name, SLOP_STR("U16"))) || (string_eq(type_name, SLOP_STR("U32"))) || (string_eq(type_name, SLOP_STR("U64"))) || (string_eq(type_name, SLOP_STR("I8"))) || (string_eq(type_name, SLOP_STR("I16"))) || (string_eq(type_name, SLOP_STR("I32"))) || (string_eq(type_name, SLOP_STR("I64"))) || (string_eq(type_name, SLOP_STR("Float"))) || (string_eq(type_name, SLOP_STR("F32"))) || (string_eq(type_name, SLOP_STR("F64"))) || (string_eq(type_name, SLOP_STR("Double"))) || (string_eq(type_name, SLOP_STR("Char"))) || (string_eq(type_name, SLOP_STR("Arena"))) || (string_eq(type_name, SLOP_STR("int64_t"))) || (string_eq(type_name, SLOP_STR("uint8_t"))) || (string_eq(type_name, SLOP_STR("uint16_t"))) || (string_eq(type_name, SLOP_STR("uint32_t"))) || (string_eq(type_name, SLOP_STR("uint64_t"))) || (string_eq(type_name, SLOP_STR("int8_t"))) || (string_eq(type_name, SLOP_STR("int16_t"))) || (string_eq(type_name, SLOP_STR("int32_t"))) || (string_eq(type_name, SLOP_STR("bool"))) || (string_eq(type_name, SLOP_STR("float"))) || (string_eq(type_name, SLOP_STR("double"))) || (string_eq(type_name, SLOP_STR("void"))));
}

slop_list_string transpiler_get_type_field_types(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type result = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        __auto_type _mv_1566 = (*type_def);
        switch (_mv_1566.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1566.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) >= 3) {
                        __auto_type _mv_1567 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1567.has_value) {
                            __auto_type def_expr = _mv_1567.value;
                            __auto_type _mv_1568 = (*def_expr);
                            switch (_mv_1568.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type def_lst = _mv_1568.data.lst;
                                    {
                                        __auto_type def_items = def_lst.items;
                                        __auto_type def_len = ((int64_t)((def_items).len));
                                        if (def_len > 0) {
                                            __auto_type _mv_1569 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1569.has_value) {
                                                __auto_type head = _mv_1569.value;
                                                __auto_type _mv_1570 = (*head);
                                                switch (_mv_1570.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type sym = _mv_1570.data.sym;
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
                                            } else if (!_mv_1569.has_value) {
                                            }
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1567.has_value) {
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
        int64_t i = 1;
        while (i < len) {
            __auto_type _mv_1571 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1571.has_value) {
                __auto_type field_expr = _mv_1571.value;
                __auto_type _mv_1572 = (*field_expr);
                switch (_mv_1572.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type field_lst = _mv_1572.data.lst;
                        if (((int64_t)((field_lst.items).len)) >= 2) {
                            __auto_type _mv_1573 = ({ __auto_type _lst = field_lst.items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1573.has_value) {
                                __auto_type type_expr = _mv_1573.value;
                                {
                                    __auto_type type_str = transpiler_get_field_type_string(ctx, type_expr);
                                    if (!(string_eq(type_str, SLOP_STR("")))) {
                                        ({ __auto_type _lst_p = &(result); __auto_type _item = (type_str); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    }
                                }
                            } else if (!_mv_1573.has_value) {
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1571.has_value) {
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
        int64_t i = 1;
        while (i < len) {
            __auto_type _mv_1574 = ({ __auto_type _lst = def_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1574.has_value) {
                __auto_type variant_expr = _mv_1574.value;
                __auto_type _mv_1575 = (*variant_expr);
                switch (_mv_1575.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type variant_lst = _mv_1575.data.lst;
                        if (((int64_t)((variant_lst.items).len)) >= 2) {
                            __auto_type _mv_1576 = ({ __auto_type _lst = variant_lst.items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1576.has_value) {
                                __auto_type type_expr = _mv_1576.value;
                                {
                                    __auto_type type_str = transpiler_get_field_type_string(ctx, type_expr);
                                    if (!(string_eq(type_str, SLOP_STR("")))) {
                                        ({ __auto_type _lst_p = &(result); __auto_type _item = (type_str); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    }
                                }
                            } else if (!_mv_1576.has_value) {
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1574.has_value) {
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
        __auto_type _mv_1577 = (*type_expr);
        switch (_mv_1577.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_1577.data.sym;
                {
                    __auto_type name = sym.name;
                    __auto_type _mv_1578 = context_ctx_lookup_type(ctx, name);
                    if (_mv_1578.has_value) {
                        __auto_type entry = _mv_1578.value;
                        return entry.c_name;
                    } else if (!_mv_1578.has_value) {
                        return ctype_to_c_type(arena, type_expr);
                    }
                    SLOP_UNREACHABLE();
                }
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1577.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) < 1) {
                        return SLOP_STR("");
                    } else {
                        __auto_type _mv_1579 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1579.has_value) {
                            __auto_type head = _mv_1579.value;
                            __auto_type _mv_1580 = (*head);
                            switch (_mv_1580.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_1580.data.sym;
                                    {
                                        __auto_type kind = sym.name;
                                        if (string_eq(kind, SLOP_STR("Ptr"))) {
                                            return SLOP_STR("");
                                        } else if (string_eq(kind, SLOP_STR("Option"))) {
                                            if (((int64_t)((items).len)) >= 2) {
                                                __auto_type _mv_1581 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1581.has_value) {
                                                    __auto_type inner = _mv_1581.value;
                                                    {
                                                        __auto_type inner_str = transpiler_get_field_type_string(ctx, inner);
                                                        if (string_eq(inner_str, SLOP_STR(""))) {
                                                            return SLOP_STR("");
                                                        } else {
                                                            return context_ctx_str(ctx, SLOP_STR("slop_option_"), ctype_type_to_identifier(arena, inner_str));
                                                        }
                                                    }
                                                } else if (!_mv_1581.has_value) {
                                                    return SLOP_STR("");
                                                }
                                                SLOP_UNREACHABLE();
                                            } else {
                                                return SLOP_STR("");
                                            }
                                        } else if (string_eq(kind, SLOP_STR("List"))) {
                                            if (((int64_t)((items).len)) >= 2) {
                                                __auto_type _mv_1582 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1582.has_value) {
                                                    __auto_type inner = _mv_1582.value;
                                                    {
                                                        __auto_type inner_str = transpiler_get_field_type_string(ctx, inner);
                                                        if (string_eq(inner_str, SLOP_STR(""))) {
                                                            return SLOP_STR("");
                                                        } else {
                                                            return context_ctx_str(ctx, SLOP_STR("slop_list_"), ctype_type_to_identifier(arena, inner_str));
                                                        }
                                                    }
                                                } else if (!_mv_1582.has_value) {
                                                    return SLOP_STR("");
                                                }
                                                SLOP_UNREACHABLE();
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
                        } else if (!_mv_1579.has_value) {
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
    __auto_type _mv_1583 = (*type_def);
    switch (_mv_1583.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1583.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 2) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_1584 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1584.has_value) {
                        __auto_type name_expr = _mv_1584.value;
                        __auto_type _mv_1585 = (*name_expr);
                        switch (_mv_1585.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1585.data.sym;
                                {
                                    __auto_type name = sym.name;
                                    __auto_type _mv_1586 = context_ctx_lookup_type(ctx, name);
                                    if (_mv_1586.has_value) {
                                        __auto_type entry = _mv_1586.value;
                                        return entry.c_name;
                                    } else if (!_mv_1586.has_value) {
                                        return SLOP_STR("");
                                    }
                                    SLOP_UNREACHABLE();
                                }
                            }
                            default: {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_1584.has_value) {
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

void transpiler_emit_option_for_inner_type(context_TranspileContext* ctx, slop_string inner_c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type option_types = context_ctx_get_option_types(ctx);
        __auto_type len = ((int64_t)((option_types).len));
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1587 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1587.has_value) {
                __auto_type ot = _mv_1587.value;
                if (string_eq(ot.inner_type, inner_c_name) && !(transpiler_is_pointer_elem_type(ot.inner_type))) {
                    transpiler_emit_single_option_type_header(ctx, ot);
                }
            } else if (!_mv_1587.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1588 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1588.has_value) {
                __auto_type lt = _mv_1588.value;
                if (string_eq(lt.elem_type, elem_c_name) && !(transpiler_is_pointer_elem_type(lt.elem_type))) {
                    transpiler_emit_single_list_type_header(ctx, lt);
                    transpiler_emit_option_for_inner_type(ctx, lt.c_name);
                }
            } else if (!_mv_1588.has_value) {
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
        uint8_t found = 0;
        {
            __auto_type len = ((int64_t)((list_types).len));
            int64_t i = 0;
            while ((i < len) && !(found)) {
                __auto_type _mv_1589 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1589.has_value) {
                    __auto_type lt = _mv_1589.value;
                    if (!(transpiler_is_pointer_elem_type(lt.elem_type)) && transpiler_struct_uses_list_type(ctx, type_def, lt.c_name)) {
                        found = 1;
                    }
                } else if (!_mv_1589.has_value) {
                }
                i = (i + 1);
            }
        }
        if (!(found)) {
            {
                __auto_type len2 = ((int64_t)((option_types).len));
                int64_t j = 0;
                while ((j < len2) && !(found)) {
                    __auto_type _mv_1590 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)j; slop_option_context_OptionType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1590.has_value) {
                        __auto_type ot = _mv_1590.value;
                        if (!(transpiler_is_pointer_elem_type(ot.inner_type)) && transpiler_struct_uses_option_type(ctx, type_def, ot.c_name)) {
                            found = 1;
                        }
                    } else if (!_mv_1590.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1591 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1591.has_value) {
                __auto_type lt = _mv_1591.value;
                if (!(transpiler_is_pointer_elem_type(lt.elem_type)) && transpiler_struct_uses_list_type(ctx, type_def, lt.c_name)) {
                    transpiler_emit_single_list_type_header(ctx, lt);
                }
            } else if (!_mv_1591.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1592 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1592.has_value) {
                __auto_type ot = _mv_1592.value;
                if (!(transpiler_is_pointer_elem_type(ot.inner_type)) && transpiler_struct_uses_option_type(ctx, type_def, ot.c_name)) {
                    transpiler_emit_list_type_if_needed(ctx, ot.inner_type);
                    transpiler_emit_single_option_type_header(ctx, ot);
                }
            } else if (!_mv_1592.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1593 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1593.has_value) {
                __auto_type lt = _mv_1593.value;
                if (!(transpiler_is_pointer_elem_type(lt.elem_type)) && transpiler_struct_uses_list_type(ctx, type_def, lt.c_name)) {
                    if (transpiler_is_type_emitted_or_primitive(ctx, lt.elem_type)) {
                        transpiler_emit_single_list_type_header(ctx, lt);
                    }
                }
            } else if (!_mv_1593.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1594 = ({ __auto_type _lst = option_types; size_t _idx = (size_t)i; slop_option_context_OptionType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1594.has_value) {
                __auto_type ot = _mv_1594.value;
                if (!(transpiler_is_pointer_elem_type(ot.inner_type)) && transpiler_struct_uses_option_type(ctx, type_def, ot.c_name)) {
                    if (transpiler_is_type_emitted_or_primitive(ctx, ot.inner_type)) {
                        transpiler_emit_list_type_if_needed_safe(ctx, ot.inner_type);
                        transpiler_emit_single_option_type_header(ctx, ot);
                    }
                }
            } else if (!_mv_1594.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t transpiler_is_type_emitted_or_primitive(context_TranspileContext* ctx, slop_string type_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (string_eq(type_name, SLOP_STR("int64_t")) || (string_eq(type_name, SLOP_STR("uint8_t")) || (string_eq(type_name, SLOP_STR("int8_t")) || (string_eq(type_name, SLOP_STR("int16_t")) || (string_eq(type_name, SLOP_STR("int32_t")) || (string_eq(type_name, SLOP_STR("uint16_t")) || (string_eq(type_name, SLOP_STR("uint32_t")) || (string_eq(type_name, SLOP_STR("uint64_t")) || (string_eq(type_name, SLOP_STR("double")) || (string_eq(type_name, SLOP_STR("float")) || string_eq(type_name, SLOP_STR("slop_string")))))))))))) {
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
    if (strlib_starts_with(type_name, SLOP_STR("slop_list_")) || strlib_starts_with(type_name, SLOP_STR("slop_option_"))) {
        return 0;
    } else {
        __auto_type _mv_1595 = context_ctx_get_module(ctx);
        if (_mv_1595.has_value) {
            __auto_type current_mod = _mv_1595.value;
            {
                __auto_type arena = (*ctx).arena;
                __auto_type c_mod = ctype_to_c_name(arena, current_mod);
                __auto_type current_prefix = context_ctx_str(ctx, c_mod, SLOP_STR("_"));
                {
                    __auto_type underscore_pos = transpiler_find_char(type_name, ((uint8_t)(95)));
                    if (underscore_pos > 0) {
                        return !(strlib_starts_with(type_name, current_prefix));
                    } else {
                        return 0;
                    }
                }
            }
        } else if (!_mv_1595.has_value) {
            return 0;
        }
        SLOP_UNREACHABLE();
    }
}

int64_t transpiler_find_char(slop_string s, uint8_t ch) {
    {
        __auto_type data = s.data;
        __auto_type len = ((int64_t)(s.len));
        int64_t i = 0;
        int64_t result = -1;
        while ((i < len) && (result < 0)) {
            if (data[i] == ch) {
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
            int64_t i = 0;
            while (i < len) {
                __auto_type _mv_1596 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1596.has_value) {
                    __auto_type lt = _mv_1596.value;
                    if (string_eq(lt.c_name, inner_type) && transpiler_is_type_emitted_or_primitive(ctx, lt.elem_type)) {
                        transpiler_emit_single_list_type_header(ctx, lt);
                    }
                } else if (!_mv_1596.has_value) {
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
            int64_t i = 0;
            while (i < len) {
                __auto_type _mv_1597 = ({ __auto_type _lst = list_types; size_t _idx = (size_t)i; slop_option_context_ListType _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1597.has_value) {
                    __auto_type lt = _mv_1597.value;
                    if (string_eq(lt.c_name, inner_type)) {
                        transpiler_emit_single_list_type_header(ctx, lt);
                    }
                } else if (!_mv_1597.has_value) {
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
        __auto_type _mv_1598 = (*type_def);
        switch (_mv_1598.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1598.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) < 3) {
                        return 0;
                    } else {
                        __auto_type _mv_1599 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1599.has_value) {
                            __auto_type body_expr = _mv_1599.value;
                            return transpiler_type_body_uses_typename(ctx, body_expr, list_type_name);
                        } else if (!_mv_1599.has_value) {
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
        __auto_type _mv_1600 = (*body_expr);
        switch (_mv_1600.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1600.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    __auto_type found = 0;
                    __auto_type i = 1;
                    while ((i < len) && !(found)) {
                        __auto_type _mv_1601 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1601.has_value) {
                            __auto_type field_expr = _mv_1601.value;
                            if (transpiler_field_uses_typename(ctx, field_expr, typename)) {
                                found = 1;
                            }
                        } else if (!_mv_1601.has_value) {
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
    __auto_type _mv_1602 = (*field_expr);
    switch (_mv_1602.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1602.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 2) {
                    return 0;
                } else {
                    __auto_type _mv_1603 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1603.has_value) {
                        __auto_type type_expr = _mv_1603.value;
                        {
                            __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                            return string_eq(c_type, typename);
                        }
                    } else if (!_mv_1603.has_value) {
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

void transpiler_emit_type_to_header(context_TranspileContext* ctx, types_SExpr* type_def) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_def != NULL)), "(!= type-def nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_1604 = (*type_def);
        switch (_mv_1604.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1604.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len >= 3) {
                        __auto_type _mv_1605 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1605.has_value) {
                            __auto_type name_expr = _mv_1605.value;
                            __auto_type _mv_1606 = (*name_expr);
                            switch (_mv_1606.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_1606.data.sym;
                                    {
                                        __auto_type type_name = name_sym.name;
                                        __auto_type base_name = ctype_to_c_name(arena, type_name);
                                        __auto_type c_name = ((context_ctx_prefixing_enabled(ctx)) ? ({ __auto_type _mv = context_ctx_get_module(ctx); _mv.has_value ? ({ __auto_type mod_name = _mv.value; context_ctx_str(ctx, ctype_to_c_name(arena, mod_name), context_ctx_str(ctx, SLOP_STR("_"), base_name)); }) : (base_name); }) : base_name);
                                        __auto_type _mv_1607 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1607.has_value) {
                                            __auto_type body_expr = _mv_1607.value;
                                            transpiler_emit_type_body_to_header(ctx, type_name, c_name, body_expr);
                                            context_ctx_mark_type_emitted(ctx, c_name);
                                        } else if (!_mv_1607.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1605.has_value) {
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
        __auto_type _mv_1608 = (*body_expr);
        switch (_mv_1608.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1608.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) < 1) {
                    } else {
                        __auto_type _mv_1609 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1609.has_value) {
                            __auto_type kind_expr = _mv_1609.value;
                            __auto_type _mv_1610 = (*kind_expr);
                            switch (_mv_1610.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type kind_sym = _mv_1610.data.sym;
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
                        } else if (!_mv_1609.has_value) {
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
        int64_t i = 1;
        context_ctx_emit_header(ctx, SLOP_STR("typedef enum {"));
        while (i < len) {
            __auto_type _mv_1611 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1611.has_value) {
                __auto_type variant_expr = _mv_1611.value;
                __auto_type _mv_1612 = (*variant_expr);
                switch (_mv_1612.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type variant_sym = _mv_1612.data.sym;
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
            } else if (!_mv_1611.has_value) {
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
        int64_t i = 1;
        context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("struct "), c_name, SLOP_STR(" {")));
        while (i < len) {
            __auto_type _mv_1613 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1613.has_value) {
                __auto_type field_expr = _mv_1613.value;
                transpiler_emit_field_to_header(ctx, raw_type_name, c_name, field_expr);
            } else if (!_mv_1613.has_value) {
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
        __auto_type _mv_1614 = (*field_expr);
        switch (_mv_1614.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1614.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) >= 2) {
                        __auto_type _mv_1615 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1615.has_value) {
                            __auto_type name_expr = _mv_1615.value;
                            __auto_type _mv_1616 = (*name_expr);
                            switch (_mv_1616.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_1616.data.sym;
                                    {
                                        __auto_type field_name = name_sym.name;
                                        __auto_type c_field_name = ctype_to_c_name(arena, field_name);
                                        __auto_type _mv_1617 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1617.has_value) {
                                            __auto_type type_expr = _mv_1617.value;
                                            {
                                                __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                __auto_type slop_type_str = parser_pretty_print(arena, type_expr);
                                                __auto_type is_ptr = transpiler_is_pointer_type_expr_header(type_expr);
                                                context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("    "), c_type, SLOP_STR(" "), context_ctx_str(ctx, c_field_name, SLOP_STR(";"))));
                                                context_ctx_register_field_type(ctx, raw_type_name, field_name, c_type, slop_type_str, is_ptr);
                                                context_ctx_register_field_type(ctx, c_type_name, field_name, c_type, slop_type_str, is_ptr);
                                            }
                                        } else if (!_mv_1617.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1615.has_value) {
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
    __auto_type _mv_1618 = (*type_expr);
    switch (_mv_1618.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1618.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_1619 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1619.has_value) {
                        __auto_type head = _mv_1619.value;
                        __auto_type _mv_1620 = (*head);
                        switch (_mv_1620.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1620.data.sym;
                                return string_eq(sym.name, SLOP_STR("Ptr"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1619.has_value) {
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

void transpiler_emit_union_to_header(context_TranspileContext* ctx, slop_string c_name, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type tag_name = context_ctx_str(ctx, c_name, SLOP_STR("_tag"));
        context_ctx_emit_header(ctx, SLOP_STR("typedef enum {"));
        {
            int64_t i = 1;
            while (i < len) {
                __auto_type _mv_1621 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1621.has_value) {
                    __auto_type variant_expr = _mv_1621.value;
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
                } else if (!_mv_1621.has_value) {
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
            int64_t i = 1;
            while (i < len) {
                __auto_type _mv_1622 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1622.has_value) {
                    __auto_type variant_expr = _mv_1622.value;
                    transpiler_emit_union_variant_to_header(ctx, variant_expr);
                } else if (!_mv_1622.has_value) {
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
    __auto_type _mv_1623 = (*variant_expr);
    switch (_mv_1623.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1623.data.sym;
            return sym.name;
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1623.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return SLOP_STR("unknown");
                } else {
                    __auto_type _mv_1624 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1624.has_value) {
                        __auto_type name_expr = _mv_1624.value;
                        __auto_type _mv_1625 = (*name_expr);
                        switch (_mv_1625.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type name_sym = _mv_1625.data.sym;
                                return name_sym.name;
                            }
                            default: {
                                return SLOP_STR("unknown");
                            }
                        }
                    } else if (!_mv_1624.has_value) {
                        return SLOP_STR("unknown");
                    }
                    SLOP_UNREACHABLE();
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
        __auto_type _mv_1626 = (*variant_expr);
        switch (_mv_1626.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_1626.data.sym;
                break;
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1626.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type num_items = ((int64_t)((items).len));
                    if (num_items >= 2) {
                        __auto_type _mv_1627 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1627.has_value) {
                            __auto_type name_expr = _mv_1627.value;
                            __auto_type _mv_1628 = (*name_expr);
                            switch (_mv_1628.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type name_sym = _mv_1628.data.sym;
                                    {
                                        __auto_type variant_name = name_sym.name;
                                        __auto_type c_field = ctype_to_c_name(arena, variant_name);
                                        if (num_items == 2) {
                                            __auto_type _mv_1629 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_1629.has_value) {
                                                __auto_type type_expr = _mv_1629.value;
                                                {
                                                    __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                    {
                                                        __auto_type actual_type = ((string_eq(c_type, SLOP_STR("void"))) ? SLOP_STR("int") : c_type);
                                                        context_ctx_emit_header(ctx, context_ctx_str4(ctx, SLOP_STR("        "), actual_type, SLOP_STR(" "), context_ctx_str(ctx, c_field, SLOP_STR(";"))));
                                                    }
                                                }
                                            } else if (!_mv_1629.has_value) {
                                            }
                                        } else if (num_items >= 3) {
                                            context_ctx_emit_header(ctx, SLOP_STR("        struct {"));
                                            for (int64_t fi = 1; fi < num_items; fi++) {
                                                __auto_type _mv_1630 = ({ __auto_type _lst = items; size_t _idx = (size_t)fi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1630.has_value) {
                                                    __auto_type type_expr = _mv_1630.value;
                                                    {
                                                        __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                        {
                                                            __auto_type actual_type = ((string_eq(c_type, SLOP_STR("void"))) ? SLOP_STR("int") : c_type);
                                                            __auto_type field_name = context_ctx_str(ctx, SLOP_STR("f"), int_to_string(arena, (fi - 1)));
                                                            context_ctx_emit_header(ctx, context_ctx_str5(ctx, SLOP_STR("            "), actual_type, SLOP_STR(" "), field_name, SLOP_STR(";")));
                                                        }
                                                    }
                                                } else if (!_mv_1630.has_value) {
                                                }
                                            }
                                            context_ctx_emit_header(ctx, context_ctx_str3(ctx, SLOP_STR("        } "), c_field, SLOP_STR(";")));
                                        } else {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_1627.has_value) {
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
        int64_t i = start;
        uint8_t emitted_any = 0;
        while (i < len) {
            __auto_type _mv_1631 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1631.has_value) {
                __auto_type item = _mv_1631.value;
                if (transpiler_is_const_def(item)) {
                    {
                        __auto_type const_name = transpiler_get_const_name(item);
                        __auto_type is_exported = transpiler_list_contains_str(exports, const_name);
                        defn_transpile_const(ctx, item, is_exported);
                    }
                    emitted_any = 1;
                }
            } else if (!_mv_1631.has_value) {
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
    __auto_type _mv_1632 = (*item);
    switch (_mv_1632.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1632.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 2) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_1633 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1633.has_value) {
                        __auto_type name_expr = _mv_1633.value;
                        __auto_type _mv_1634 = (*name_expr);
                        switch (_mv_1634.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1634.data.sym;
                                return sym.name;
                            }
                            default: {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_1633.has_value) {
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

void transpiler_emit_module_consts_header(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start, slop_list_string exports) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = start;
        uint8_t emitted_any = 0;
        while (i < len) {
            __auto_type _mv_1635 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1635.has_value) {
                __auto_type item = _mv_1635.value;
                if (transpiler_is_const_def(item)) {
                    if (transpiler_emit_const_header_if_exported(ctx, item, exports)) {
                        emitted_any = 1;
                    }
                }
            } else if (!_mv_1635.has_value) {
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
    __auto_type _mv_1636 = (*item);
    switch (_mv_1636.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1636.data.lst;
            {
                __auto_type const_items = lst.items;
                if (((int64_t)((const_items).len)) < 4) {
                    return 0;
                } else {
                    __auto_type _mv_1637 = ({ __auto_type _lst = const_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1637.has_value) {
                        __auto_type name_expr = _mv_1637.value;
                        __auto_type _mv_1638 = (*name_expr);
                        switch (_mv_1638.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type name_sym = _mv_1638.data.sym;
                                {
                                    __auto_type raw_name = name_sym.name;
                                    if (!(transpiler_list_contains_str(exports, raw_name))) {
                                        return 0;
                                    } else {
                                        __auto_type _mv_1639 = ({ __auto_type _lst = const_items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1639.has_value) {
                                            __auto_type type_expr = _mv_1639.value;
                                            transpiler_emit_const_header_decl(ctx, raw_name, type_expr, ({ __auto_type _mv = ({ __auto_type _lst = const_items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type v = _mv.value; v; }) : (NULL); }));
                                            return 1;
                                        } else if (!_mv_1639.has_value) {
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
                    } else if (!_mv_1637.has_value) {
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
            if (value_expr != NULL) {
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
        int64_t i = start;
        context_ctx_start_function_buffer(ctx);
        while (i < len) {
            __auto_type _mv_1640 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1640.has_value) {
                __auto_type item = _mv_1640.value;
                if (transpiler_is_fn_def(item)) {
                    defn_transpile_function(ctx, item);
                }
            } else if (!_mv_1640.has_value) {
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
        int64_t i = 0;
        if (count > 0) {
            while (i < count) {
                __auto_type _mv_1641 = ({ __auto_type _lst = lambdas; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1641.has_value) {
                    __auto_type lambda_code = _mv_1641.value;
                    context_ctx_emit(ctx, lambda_code);
                    context_ctx_emit(ctx, SLOP_STR(""));
                } else if (!_mv_1641.has_value) {
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
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1642 = ({ __auto_type _lst = output_lines; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1642.has_value) {
                __auto_type line = _mv_1642.value;
                result = context_ctx_str3(ctx, result, line, SLOP_STR("\n"));
            } else if (!_mv_1642.has_value) {
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
        int64_t i = 0;
        if ((len > 0) && transpiler_is_module_expr(exprs)) {
            __auto_type _mv_1643 = ({ __auto_type _lst = exprs; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1643.has_value) {
                __auto_type module_expr = _mv_1643.value;
                transpiler_transpile_module(ctx, module_expr);
            } else if (!_mv_1643.has_value) {
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
    if (((int64_t)((exprs).len)) < 1) {
        return 0;
    } else {
        __auto_type _mv_1644 = ({ __auto_type _lst = exprs; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1644.has_value) {
            __auto_type first = _mv_1644.value;
            __auto_type _mv_1645 = (*first);
            switch (_mv_1645.tag) {
                case types_SExpr_lst:
                {
                    __auto_type lst = _mv_1645.data.lst;
                    {
                        __auto_type items = lst.items;
                        if (((int64_t)((items).len)) < 1) {
                            return 0;
                        } else {
                            __auto_type _mv_1646 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1646.has_value) {
                                __auto_type head = _mv_1646.value;
                                __auto_type _mv_1647 = (*head);
                                switch (_mv_1647.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_1647.data.sym;
                                        return string_eq(sym.name, SLOP_STR("module"));
                                    }
                                    default: {
                                        return 0;
                                    }
                                }
                            } else if (!_mv_1646.has_value) {
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
        } else if (!_mv_1644.has_value) {
            return 0;
        }
        SLOP_UNREACHABLE();
    }
}

