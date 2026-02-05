#ifndef SLOP_defn_H
#define SLOP_defn_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_types.h"
#include "slop_context.h"
#include "slop_ctype.h"
#include "slop_stmt.h"
#include "slop_expr.h"
#include "slop_strlib.h"
#include "slop_parser.h"

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

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_CONTEXT_FUNCPARAMTYPE_PTR_DEFINED
#define SLOP_OPTION_CONTEXT_FUNCPARAMTYPE_PTR_DEFINED
SLOP_OPTION_DEFINE(context_FuncParamType*, slop_option_context_FuncParamType_ptr)
#endif


#endif
