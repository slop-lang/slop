#ifndef SLOP_transpiler_H
#define SLOP_transpiler_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_types.h"
#include "slop_context.h"
#include "slop_ctype.h"
#include "slop_emit.h"
#include "slop_defn.h"
#include "slop_stmt.h"
#include "slop_expr.h"
#include "slop_match.h"
#include "slop_strlib.h"
#include "slop_parser.h"

typedef struct transpiler_GenericInfo transpiler_GenericInfo;
typedef struct transpiler_RangeBoundsHeader transpiler_RangeBoundsHeader;

#ifndef SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
SLOP_LIST_DEFINE(types_SExpr*, slop_list_types_SExpr_ptr)
#endif

#ifndef SLOP_LIST_CONTEXT_FUNCPARAMTYPE_PTR_DEFINED
#define SLOP_LIST_CONTEXT_FUNCPARAMTYPE_PTR_DEFINED
SLOP_LIST_DEFINE(context_FuncParamType*, slop_list_context_FuncParamType_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_CONTEXT_FUNCPARAMTYPE_PTR_DEFINED
#define SLOP_OPTION_CONTEXT_FUNCPARAMTYPE_PTR_DEFINED
SLOP_OPTION_DEFINE(context_FuncParamType*, slop_option_context_FuncParamType_ptr)
#endif

#ifndef SLOP_LIST_CONTEXT_UNIONVARIANTENTRY_DEFINED
#define SLOP_LIST_CONTEXT_UNIONVARIANTENTRY_DEFINED
SLOP_LIST_DEFINE(context_UnionVariantEntry, slop_list_context_UnionVariantEntry)
#endif

#ifndef SLOP_LIST_CONTEXT_FIELDENTRY_DEFINED
#define SLOP_LIST_CONTEXT_FIELDENTRY_DEFINED
SLOP_LIST_DEFINE(context_FieldEntry, slop_list_context_FieldEntry)
#endif

#ifndef SLOP_OPTION_CONTEXT_UNIONVARIANTENTRY_DEFINED
#define SLOP_OPTION_CONTEXT_UNIONVARIANTENTRY_DEFINED
SLOP_OPTION_DEFINE(context_UnionVariantEntry, slop_option_context_UnionVariantEntry)
#endif

#ifndef SLOP_OPTION_CONTEXT_FIELDENTRY_DEFINED
#define SLOP_OPTION_CONTEXT_FIELDENTRY_DEFINED
SLOP_OPTION_DEFINE(context_FieldEntry, slop_option_context_FieldEntry)
#endif

#ifndef SLOP_LIST_CONTEXT_UNIONVARIANTENTRY_DEFINED
#define SLOP_LIST_CONTEXT_UNIONVARIANTENTRY_DEFINED
SLOP_LIST_DEFINE(context_UnionVariantEntry, slop_list_context_UnionVariantEntry)
#endif

#ifndef SLOP_LIST_CONTEXT_FIELDENTRY_DEFINED
#define SLOP_LIST_CONTEXT_FIELDENTRY_DEFINED
SLOP_LIST_DEFINE(context_FieldEntry, slop_list_context_FieldEntry)
#endif

struct transpiler_GenericInfo {
    uint8_t is_generic;
    slop_list_string type_params;
};
typedef struct transpiler_GenericInfo transpiler_GenericInfo;

#ifndef SLOP_OPTION_TRANSPILER_GENERICINFO_DEFINED
#define SLOP_OPTION_TRANSPILER_GENERICINFO_DEFINED
SLOP_OPTION_DEFINE(transpiler_GenericInfo, slop_option_transpiler_GenericInfo)
#endif

struct transpiler_RangeBoundsHeader {
    int64_t min;
    int64_t max;
    uint8_t has_min;
    uint8_t has_max;
};
typedef struct transpiler_RangeBoundsHeader transpiler_RangeBoundsHeader;

#ifndef SLOP_OPTION_TRANSPILER_RANGEBOUNDSHEADER_DEFINED
#define SLOP_OPTION_TRANSPILER_RANGEBOUNDSHEADER_DEFINED
SLOP_OPTION_DEFINE(transpiler_RangeBoundsHeader, slop_option_transpiler_RangeBoundsHeader)
#endif

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
void transpiler_emit_record_field_dependencies(context_TranspileContext* ctx, slop_list_context_FieldEntry fields);
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

#ifndef SLOP_OPTION_TRANSPILER_GENERICINFO_DEFINED
#define SLOP_OPTION_TRANSPILER_GENERICINFO_DEFINED
SLOP_OPTION_DEFINE(transpiler_GenericInfo, slop_option_transpiler_GenericInfo)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_CONTEXT_FUNCPARAMTYPE_PTR_DEFINED
#define SLOP_OPTION_CONTEXT_FUNCPARAMTYPE_PTR_DEFINED
SLOP_OPTION_DEFINE(context_FuncParamType*, slop_option_context_FuncParamType_ptr)
#endif

#ifndef SLOP_OPTION_TRANSPILER_RANGEBOUNDSHEADER_DEFINED
#define SLOP_OPTION_TRANSPILER_RANGEBOUNDSHEADER_DEFINED
SLOP_OPTION_DEFINE(transpiler_RangeBoundsHeader, slop_option_transpiler_RangeBoundsHeader)
#endif

#ifndef SLOP_OPTION_CONTEXT_UNIONVARIANTENTRY_DEFINED
#define SLOP_OPTION_CONTEXT_UNIONVARIANTENTRY_DEFINED
SLOP_OPTION_DEFINE(context_UnionVariantEntry, slop_option_context_UnionVariantEntry)
#endif

#ifndef SLOP_OPTION_CONTEXT_FIELDENTRY_DEFINED
#define SLOP_OPTION_CONTEXT_FIELDENTRY_DEFINED
SLOP_OPTION_DEFINE(context_FieldEntry, slop_option_context_FieldEntry)
#endif


#endif
