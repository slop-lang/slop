#ifndef SLOP_checker_H
#define SLOP_checker_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_parser.h"
#include "slop_types.h"
#include "slop_env.h"
#include "slop_collect.h"
#include "slop_resolve.h"
#include "slop_infer.h"
#include "slop_file.h"
#include "slop_strlib.h"
#include <stdio.h>
#include <string.h>

typedef enum {
    checker_OutputFormat_fmt_text,
    checker_OutputFormat_fmt_json
} checker_OutputFormat;

#ifndef SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
SLOP_LIST_DEFINE(types_SExpr*, slop_list_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_LIST_TYPES_DIAGNOSTIC_DEFINED
#define SLOP_LIST_TYPES_DIAGNOSTIC_DEFINED
SLOP_LIST_DEFINE(types_Diagnostic, slop_list_types_Diagnostic)
#endif

#ifndef SLOP_OPTION_TYPES_DIAGNOSTIC_DEFINED
#define SLOP_OPTION_TYPES_DIAGNOSTIC_DEFINED
SLOP_OPTION_DEFINE(types_Diagnostic, slop_option_types_Diagnostic)
#endif

#ifndef SLOP_LIST_TYPES_DIAGNOSTIC_DEFINED
#define SLOP_LIST_TYPES_DIAGNOSTIC_DEFINED
SLOP_LIST_DEFINE(types_Diagnostic, slop_list_types_Diagnostic)
#endif

#ifndef SLOP_RESULT_ENV_TYPEENV_PTR_TYPES_TYPEERROR_DEFINED
#define SLOP_RESULT_ENV_TYPEENV_PTR_TYPES_TYPEERROR_DEFINED
typedef struct { bool is_ok; union { env_TypeEnv* ok; types_TypeError err; } data; } slop_result_env_TypeEnv_ptr_types_TypeError;
#endif

typedef slop_result_env_TypeEnv_ptr_types_TypeError checker_TypeCheckResult;

slop_result_env_TypeEnv_ptr_types_TypeError checker_type_check(slop_arena* arena, slop_list_types_SExpr_ptr ast);
void checker_type_check_with_env(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void checker_check_all_functions(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
uint8_t checker_is_annotation_form(types_SExpr* item);
uint8_t checker_is_valid_toplevel_form(types_SExpr* item);
slop_string checker_get_form_name(types_SExpr* item);
void checker_check_module_functions(env_TypeEnv* env, types_SExpr* module_form);
void checker_print_str(uint8_t* s);
void checker_print_string(slop_string s);
void checker_print_json_string(slop_arena* arena, slop_string s);
slop_string checker_extract_module_name(slop_list_types_SExpr_ptr exprs);
void checker_print_diagnostic(slop_arena* arena, slop_string filename, types_Diagnostic diag);
void checker_output_diagnostics_text(slop_arena* arena, slop_string filename, slop_list_types_Diagnostic diagnostics);
void checker_output_diagnostics_json(slop_arena* arena, slop_list_types_Diagnostic diagnostics);
void checker_output_single_diagnostic_json(slop_arena* arena, types_Diagnostic diag);
void checker_output_module_json(slop_arena* arena, slop_string mod_name, slop_list_types_Diagnostic diagnostics, uint8_t first);
int64_t checker_check_single_file(env_TypeEnv* env, slop_arena* arena, uint8_t* filename, checker_OutputFormat format, uint8_t first);
int64_t checker_count_errors(slop_list_types_Diagnostic diagnostics);
slop_string checker_argv_to_string(uint8_t** argv, int64_t index);
types_ResolvedType* checker_resolve_type_name(env_TypeEnv* env, slop_string type_name);
void checker_parse_and_bind_params(env_TypeEnv* env, slop_arena* arena, slop_string params_str);
uint8_t checker_types_names_equal(types_ResolvedType* a, types_ResolvedType* b);
int64_t checker_check_expr_mode(slop_arena* arena, env_TypeEnv* env, slop_string expr_str, slop_string type_str, slop_string context_file, slop_string params_str);
void checker_output_expr_result(slop_arena* arena, uint8_t valid, slop_string inferred_type, slop_string expected_type, slop_list_types_Diagnostic diagnostics);
int main(int64_t argc, uint8_t** argv);

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_DIAGNOSTIC_DEFINED
#define SLOP_OPTION_TYPES_DIAGNOSTIC_DEFINED
SLOP_OPTION_DEFINE(types_Diagnostic, slop_option_types_Diagnostic)
#endif


#endif
