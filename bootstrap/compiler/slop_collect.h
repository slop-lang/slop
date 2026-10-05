#ifndef SLOP_collect_H
#define SLOP_collect_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_parser.h"
#include "slop_types.h"
#include "slop_type_env.h"
#include "slop_strlib.h"
#include "slop_resolve.h"

#ifndef SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_IMPL_DEFINED
SLOP_LIST_DEFINE(types_SExpr*, slop_list_types_SExpr_ptr)
#endif

#ifndef SLOP_LIST_TYPES_RESOLVEDTYPE_PTR_DEFINED
#define SLOP_LIST_TYPES_RESOLVEDTYPE_PTR_DEFINED
#define SLOP_LIST_TYPES_RESOLVEDTYPE_PTR_IMPL_DEFINED
SLOP_LIST_DEFINE(types_ResolvedType*, slop_list_types_ResolvedType_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
#define SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
SLOP_OPTION_DEFINE(types_ResolvedType*, slop_option_types_ResolvedType_ptr)
#endif

#ifndef SLOP_LIST_TYPES_PARAMINFO_DEFINED
#define SLOP_LIST_TYPES_PARAMINFO_DEFINED
#define SLOP_LIST_TYPES_PARAMINFO_IMPL_DEFINED
SLOP_LIST_DEFINE(types_ParamInfo, slop_list_types_ParamInfo)
#endif

#ifndef SLOP_OPTION_TYPES_PARAMINFO_DEFINED
#define SLOP_OPTION_TYPES_PARAMINFO_DEFINED
SLOP_OPTION_DEFINE(types_ParamInfo, slop_option_types_ParamInfo)
#endif

void collect_collect_module(type_env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
slop_option_string collect_ast_module_name(slop_list_types_SExpr_ptr ast);
void collect_collect_type_names(type_env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void collect_collect_type_bodies(type_env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void collect_register_type_name(type_env_TypeEnv* env, slop_arena* arena, types_SExpr* expr);
void collect_resolve_type_body(type_env_TypeEnv* env, slop_arena* arena, types_SExpr* expr);
void collect_collect_record_fields(type_env_TypeEnv* env, slop_arena* arena, types_ResolvedType* resolved, types_SExpr* record_expr);
types_SExpr* collect_get_type_arg(types_SExpr* type_expr, int64_t idx);
types_ResolvedType* collect_get_field_type(type_env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr);
uint8_t collect_is_type_param(slop_string name, slop_list_string type_params);
types_ResolvedType* collect_get_field_type_generic(type_env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr, slop_list_string type_params);
slop_list_string collect_find_fn_type_params(slop_arena* arena, types_SExpr* fn_form);
types_ResolvedType* collect_find_fn_return_type_generic(type_env_TypeEnv* env, types_SExpr* fn_form, slop_list_string type_params);
types_ResolvedType* collect_extract_spec_return_type_generic(type_env_TypeEnv* env, types_SExpr* spec_form, slop_list_string type_params);
slop_list_types_ResolvedType_ptr collect_collect_fn_spec_params(type_env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form, slop_list_string type_params);
void collect_set_module_name_from_form(type_env_TypeEnv* env, types_SExpr* module_form);
void collect_register_module_type_names(type_env_TypeEnv* env, types_SExpr* module_form);
void collect_resolve_module_type_bodies(type_env_TypeEnv* env, types_SExpr* module_form);
void collect_check_range_forms(type_env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void collect_check_range_forms_in(type_env_TypeEnv* env, types_SExpr* expr);
uint8_t collect_is_unchecked_range_base(slop_string name);
uint8_t collect_is_range_type_expr(types_SExpr* type_expr);
types_ResolvedType* collect_get_range_base_type(type_env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr);
slop_string collect_get_type_name_from_expr(types_SExpr* expr);
uint8_t collect_is_reserved_variant_name(slop_string name);
void collect_collect_union_variants(type_env_TypeEnv* env, slop_arena* arena, types_ResolvedType* resolved, types_SExpr* union_expr);
slop_list_types_ResolvedType_ptr collect_get_variant_payload_types(type_env_TypeEnv* env, types_SExpr* variant_form);
slop_option_types_ResolvedType_ptr collect_get_variant_payload_type(type_env_TypeEnv* env, types_SExpr* variant_form);
slop_string collect_checker_get_variant_name(types_SExpr* variant_form);
uint8_t collect_check_type_expr_recursive(types_SExpr* type_expr, slop_string union_name);
uint8_t collect_has_recursive_value_payload(types_SExpr* variant_form, slop_string union_name);
void collect_collect_single_union_variant(type_env_TypeEnv* env, slop_arena* arena, types_ResolvedType* resolved, types_SExpr* variant_form, int64_t variant_idx);
void collect_collect_enum_variants(type_env_TypeEnv* env, types_ResolvedType* enum_type, types_SExpr* enum_expr);
void collect_collect_constants(type_env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void collect_collect_module_constants(type_env_TypeEnv* env, types_SExpr* module_form);
void collect_collect_single_constant(type_env_TypeEnv* env, slop_arena* arena, types_SExpr* const_form);
types_ResolvedType* collect_constant_value_type(type_env_TypeEnv* env, slop_arena* arena, slop_string const_name, types_ResolvedType* declared, types_SExpr* const_form);
types_ResolvedType* collect_get_const_type(type_env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr);
void collect_collect_functions(type_env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void collect_collect_module_functions(type_env_TypeEnv* env, types_SExpr* module_form);
void collect_collect_ffi_functions(type_env_TypeEnv* env, slop_arena* arena, types_SExpr* ffi_form);
void collect_collect_ffi_function(type_env_TypeEnv* env, slop_arena* arena, types_SExpr* func_decl);
uint8_t collect_ffi_has_variadic(types_SExpr* func_decl);
slop_list_types_ParamInfo collect_collect_ffi_params(type_env_TypeEnv* env, slop_arena* arena, types_SExpr* func_decl);
types_ResolvedType* collect_get_ffi_return_type(type_env_TypeEnv* env, slop_arena* arena, types_SExpr* func_decl);
void collect_collect_single_function(type_env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form);
uint8_t collect_is_reserved_builtin_name(slop_string name);
uint8_t collect_is_reserved_special_form(slop_string name);
uint8_t collect_is_reserved_special_form_rest(slop_string name);
uint8_t collect_is_reserved_collection_name(slop_string name);
uint8_t collect_is_reserved_collection_name_rest(slop_string name);
uint8_t collect_is_reserved_constructor_name(slop_string name);
uint8_t collect_is_reserved_memory_name(slop_string name);
void collect_report_reserved_name(type_env_TypeEnv* env, slop_string name, slop_string what, int64_t line, int64_t col);
uint8_t collect_is_integer_type_name(slop_string name);
void collect_validate_main_params(type_env_TypeEnv* env, types_SExpr* fn_form, slop_list_types_ParamInfo params);
slop_list_types_ParamInfo collect_collect_fn_params(type_env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form);
slop_list_types_ParamInfo collect_collect_fn_params_generic(type_env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form, slop_list_string type_params);
types_ResolvedType* collect_find_fn_return_type(type_env_TypeEnv* env, types_SExpr* fn_form);
types_ResolvedType* collect_checker_extract_spec_return_type(type_env_TypeEnv* env, types_SExpr* spec_form);

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
#define SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
SLOP_OPTION_DEFINE(types_ResolvedType*, slop_option_types_ResolvedType_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_PARAMINFO_DEFINED
#define SLOP_OPTION_TYPES_PARAMINFO_DEFINED
SLOP_OPTION_DEFINE(types_ParamInfo, slop_option_types_ParamInfo)
#endif

#ifndef SLOP_OPTION_TYPES_RANGEBOUNDS_DEFINED
#define SLOP_OPTION_TYPES_RANGEBOUNDS_DEFINED
SLOP_OPTION_DEFINE(types_RangeBounds, slop_option_types_RangeBounds)
#endif


#endif
