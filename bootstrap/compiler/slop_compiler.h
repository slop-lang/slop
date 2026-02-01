#ifndef SLOP_compiler_H
#define SLOP_compiler_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_parser.h"
#include "slop_types.h"
#include "slop_env.h"
#include "slop_collect.h"
#include "slop_resolve.h"
#include "slop_infer.h"
#include "slop_ctype.h"
#include "slop_context.h"
#include "slop_transpiler.h"
#include "slop_file.h"
#include "slop_strlib.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef enum {
    compiler_Subcommand_cmd_check,
    compiler_Subcommand_cmd_transpile,
    compiler_Subcommand_cmd_typed_ast,
    compiler_Subcommand_cmd_help
} compiler_Subcommand;

typedef enum {
    compiler_OutputFormat_fmt_text,
    compiler_OutputFormat_fmt_json
} compiler_OutputFormat;

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

void compiler_print_str(uint8_t* s);
void compiler_print_string(slop_string s);
void compiler_print_json_string(slop_arena* arena, slop_string s);
slop_string compiler_lines_to_string(slop_arena* arena, slop_list_string lines);
slop_string compiler_extract_module_name(slop_list_types_SExpr_ptr exprs);
slop_string compiler_argv_to_string(uint8_t** argv, int64_t index);
void compiler_type_check_with_env(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void compiler_check_all_functions(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
uint8_t compiler_is_annotation_form(types_SExpr* item);
uint8_t compiler_is_valid_toplevel_form(types_SExpr* item);
slop_string compiler_get_form_name(types_SExpr* item);
void compiler_check_module_functions(env_TypeEnv* env, types_SExpr* module_form);
int64_t compiler_count_errors(slop_list_types_Diagnostic diagnostics);
void compiler_print_diagnostic(slop_arena* arena, slop_string filename, types_Diagnostic diag);
void compiler_output_diagnostics_text(slop_arena* arena, slop_string filename, slop_list_types_Diagnostic diagnostics);
void compiler_output_diagnostics_json(slop_arena* arena, slop_list_types_Diagnostic diagnostics);
void compiler_output_single_diagnostic_json(slop_arena* arena, types_Diagnostic diag);
void compiler_output_check_module_json(slop_arena* arena, slop_string mod_name, slop_list_types_Diagnostic diagnostics, uint8_t first);
int64_t compiler_check_single_file(env_TypeEnv* env, slop_arena* arena, uint8_t* filename, compiler_OutputFormat format, uint8_t first);
types_ResolvedType* compiler_resolve_type_string(env_TypeEnv* env, slop_arena* arena, slop_string type_str);
void compiler_parse_and_bind_params(env_TypeEnv* env, slop_arena* arena, slop_string params_str);
uint8_t compiler_types_names_equal(types_ResolvedType* a, types_ResolvedType* b);
int64_t compiler_check_expr_mode(slop_arena* arena, env_TypeEnv* env, slop_string expr_str, slop_string type_str, slop_string context_file, slop_string params_str);
void compiler_output_expr_result(slop_arena* arena, uint8_t valid, slop_string inferred_type, slop_string expected_type, slop_list_types_Diagnostic diagnostics);
int64_t compiler_transpile_single_file(env_TypeEnv* env, context_TranspileContext* ctx, slop_arena* arena, uint8_t* filename, uint8_t first);
void compiler_output_transpile_module_json(slop_arena* arena, context_TranspileContext* ctx, slop_string mod_name, uint8_t first);
slop_string compiler_emit_sexpr_inner(slop_arena* arena, types_SExpr* expr);
slop_string compiler_emit_typed_sexpr(slop_arena* arena, types_SExpr* expr);
slop_string compiler_emit_typed_list(slop_arena* arena, slop_list_types_SExpr_ptr items);
slop_string compiler_emit_typed_toplevel(slop_arena* arena, types_SExpr* expr);
slop_string compiler_emit_typed_module(slop_arena* arena, types_SExpr* module_form);
slop_string compiler_emit_typed_ast(slop_arena* arena, slop_list_types_SExpr_ptr ast);
int64_t compiler_typed_ast_single_file(env_TypeEnv* env, slop_arena* arena, uint8_t* filename, compiler_OutputFormat format, uint8_t first);
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
