#ifndef SLOP_infer_H
#define SLOP_infer_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_parser.h"
#include "slop_types.h"
#include "slop_env.h"
#include "slop_strlib.h"

#ifndef SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
SLOP_LIST_DEFINE(types_SExpr*, slop_list_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

uint8_t infer_types_equal(types_ResolvedType* a, types_ResolvedType* b);
uint8_t infer_types_compatible_with_range(types_ResolvedType* a, types_ResolvedType* b);
types_ResolvedType* infer_unify_branch_types(env_TypeEnv* env, types_ResolvedType* a, types_ResolvedType* b, int64_t line, int64_t col);
types_ResolvedType* infer_infer_expr(env_TypeEnv* env, types_SExpr* expr);
types_ResolvedType* infer_infer_list_expr(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst);
types_ResolvedType* infer_infer_special_form(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst, slop_string op);
void infer_check_fn_call_args(env_TypeEnv* env, types_FnSignature* sig, types_SExpr* expr, int64_t line, int64_t col);
void infer_check_single_arg(env_TypeEnv* env, types_FnSignature* sig, types_SExpr* expr, int64_t arg_idx, int64_t line, int64_t col);
void infer_check_builtin_args(env_TypeEnv* env, slop_string op, int64_t expected, int64_t actual, int64_t line, int64_t col);
void infer_infer_builtin_args(env_TypeEnv* env, types_SExpr* expr);
void infer_infer_body_exprs(env_TypeEnv* env, types_SExpr* expr, int64_t start_idx);
types_ResolvedType* infer_infer_field_access(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst, int64_t line, int64_t col);
types_ResolvedType* infer_check_field_exists(env_TypeEnv* env, types_ResolvedType* obj_type, slop_string field_name, int64_t line, int64_t col);
types_ResolvedType* infer_infer_cond_expr(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst);
void infer_bind_match_pattern(env_TypeEnv* env, types_ResolvedType* scrutinee_type, types_SExpr* pattern);
types_ResolvedType* infer_infer_match_expr(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst);
void infer_check_return_type(env_TypeEnv* env, types_SExpr* fn_form, slop_string fn_name, types_ResolvedType* inferred_type, int64_t fn_line, int64_t fn_col);
void infer_check_spec_return_type(env_TypeEnv* env, types_SExpr* spec_form, slop_string fn_name, types_ResolvedType* inferred_type, int64_t fn_line, int64_t fn_col);
void infer_check_spec_body_return(env_TypeEnv* env, types_SExpr* spec_body, slop_string fn_name, types_ResolvedType* inferred_type, int64_t fn_line, int64_t fn_col);
uint8_t infer_is_primitive_type(slop_string name);
void infer_check_return_expr(env_TypeEnv* env, types_SExpr* ret_expr, slop_string fn_name, types_ResolvedType* inferred_type, int64_t fn_line, int64_t fn_col);
void infer_bind_param_from_form(env_TypeEnv* env, types_SExpr* param_form);
types_ResolvedType* infer_get_param_type_from_form(env_TypeEnv* env, types_SExpr* param_form);
types_ResolvedType* infer_resolve_complex_type_expr(env_TypeEnv* env, types_SExpr* type_expr);
types_ResolvedType* infer_resolve_option_inner_type(env_TypeEnv* env, types_SExpr* type_expr);
types_ResolvedType* infer_resolve_ptr_inner_type(env_TypeEnv* env, types_SExpr* type_expr);
types_ResolvedType* infer_resolve_simple_type(env_TypeEnv* env, slop_string type_name);
void infer_bind_let_binding(env_TypeEnv* env, types_SExpr* binding_form);
types_ResolvedType* infer_infer_let_expr(env_TypeEnv* env, types_SExpr* expr);
types_ResolvedType* infer_infer_with_arena_expr(env_TypeEnv* env, types_SExpr* expr);
slop_string infer_get_fn_name(types_SExpr* fn_form);
types_ResolvedType* infer_resolve_hole_type(env_TypeEnv* env, slop_list_types_SExpr_ptr items, int64_t len);
slop_string infer_get_hole_prompt(slop_list_types_SExpr_ptr items, int64_t len);
int64_t infer_find_last_body_idx(slop_list_types_SExpr_ptr items);
uint8_t infer_is_c_name_related(slop_list_types_SExpr_ptr items, int64_t idx);
types_ResolvedType* infer_infer_fn_body(env_TypeEnv* env, types_SExpr* fn_form);
void infer_check_match_patterns(env_TypeEnv* env, types_ResolvedType* scrutinee_type, slop_list_types_SExpr_ptr patterns);

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif


#endif
