#ifndef SLOP_test_emit_H
#define SLOP_test_emit_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_types.h"
#include "slop_parser.h"
#include "slop_extract.h"
#include "slop_strlib.h"
#include "slop_type_extract.h"
#include "slop_ctype.h"
#include "slop_context.h"
#include "slop_expr.h"
#include "slop_transpiler.h"
#include <string.h>

typedef struct test_emit_EmitContext test_emit_EmitContext;
typedef struct test_emit_CompareInfo test_emit_CompareInfo;

#ifndef SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
SLOP_LIST_DEFINE(types_SExpr*, slop_list_types_SExpr_ptr)
#endif

#ifndef SLOP_LIST_EXTRACT_TESTCASE_PTR_DEFINED
#define SLOP_LIST_EXTRACT_TESTCASE_PTR_DEFINED
SLOP_LIST_DEFINE(extract_TestCase*, slop_list_extract_TestCase_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_EXTRACT_TESTCASE_PTR_DEFINED
#define SLOP_OPTION_EXTRACT_TESTCASE_PTR_DEFINED
SLOP_OPTION_DEFINE(extract_TestCase*, slop_option_extract_TestCase_ptr)
#endif

#ifndef SLOP_LIST_TYPE_EXTRACT_IMPORTENTRY_DEFINED
#define SLOP_LIST_TYPE_EXTRACT_IMPORTENTRY_DEFINED
SLOP_LIST_DEFINE(type_extract_ImportEntry, slop_list_type_extract_ImportEntry)
#endif

#ifndef SLOP_LIST_TYPE_EXTRACT_TSTFIELDENTRY_DEFINED
#define SLOP_LIST_TYPE_EXTRACT_TSTFIELDENTRY_DEFINED
SLOP_LIST_DEFINE(type_extract_TstFieldEntry, slop_list_type_extract_TstFieldEntry)
#endif

#ifndef SLOP_OPTION_TYPE_EXTRACT_IMPORTENTRY_DEFINED
#define SLOP_OPTION_TYPE_EXTRACT_IMPORTENTRY_DEFINED
SLOP_OPTION_DEFINE(type_extract_ImportEntry, slop_option_type_extract_ImportEntry)
#endif

#ifndef SLOP_OPTION_TYPE_EXTRACT_TSTFIELDENTRY_DEFINED
#define SLOP_OPTION_TYPE_EXTRACT_TSTFIELDENTRY_DEFINED
SLOP_OPTION_DEFINE(type_extract_TstFieldEntry, slop_option_type_extract_TstFieldEntry)
#endif

#ifndef SLOP_LIST_TYPE_EXTRACT_IMPORTENTRY_DEFINED
#define SLOP_LIST_TYPE_EXTRACT_IMPORTENTRY_DEFINED
SLOP_LIST_DEFINE(type_extract_ImportEntry, slop_list_type_extract_ImportEntry)
#endif

#ifndef SLOP_LIST_TYPE_EXTRACT_TSTFIELDENTRY_DEFINED
#define SLOP_LIST_TYPE_EXTRACT_TSTFIELDENTRY_DEFINED
SLOP_LIST_DEFINE(type_extract_TstFieldEntry, slop_list_type_extract_TstFieldEntry)
#endif

struct test_emit_EmitContext {
    slop_list_string lines;
    slop_arena* arena;
    type_extract_TypeRegistry* types;
    context_TranspileContext* tctx;
    uint8_t has_types;
};
typedef struct test_emit_EmitContext test_emit_EmitContext;

#ifndef SLOP_OPTION_TEST_EMIT_EMITCONTEXT_DEFINED
#define SLOP_OPTION_TEST_EMIT_EMITCONTEXT_DEFINED
SLOP_OPTION_DEFINE(test_emit_EmitContext, slop_option_test_emit_EmitContext)
#endif

struct test_emit_CompareInfo {
    slop_string compare_expr;
    slop_string result_fmt;
    slop_string result_args;
    slop_string expected_fmt;
    slop_string expected_args;
};
typedef struct test_emit_CompareInfo test_emit_CompareInfo;

#ifndef SLOP_OPTION_TEST_EMIT_COMPAREINFO_DEFINED
#define SLOP_OPTION_TEST_EMIT_COMPAREINFO_DEFINED
SLOP_OPTION_DEFINE(test_emit_CompareInfo, slop_option_test_emit_CompareInfo)
#endif

types_SExpr* test_emit_make_sexpr_sym(slop_arena* arena, slop_string name);
types_SExpr* test_emit_make_sexpr_num(slop_arena* arena, slop_string raw);
types_SExpr* test_emit_make_sexpr_list(slop_arena* arena, slop_list_types_SExpr_ptr items);
uint8_t test_emit_is_wildcard_like_symbol(slop_string name);
uint8_t test_emit_has_ellipsis(types_SExpr* expr);
uint8_t test_emit_args_have_ellipsis(slop_list_types_SExpr_ptr args);
uint8_t test_emit_is_type_constructor_name(slop_string name);
uint8_t test_emit_contains_wildcard(types_SExpr* expr);
types_SExpr* test_emit_replace_wildcards(slop_arena* arena, types_SExpr* expr);
slop_string test_emit_replace_wildcard_tokens(slop_arena* arena, slop_string s);
slop_string test_emit_transpile_expr_safe(slop_arena* arena, context_TranspileContext* tctx, types_SExpr* expr);
slop_string test_emit_prefix_symbol(slop_arena* arena, slop_string name, slop_string prefix, type_extract_TypeRegistry types);
test_emit_EmitContext* test_emit_emit_ctx_new_typed(slop_arena* arena, type_extract_TypeRegistry* types, context_TranspileContext* tctx);
void test_emit_emit(test_emit_EmitContext* ctx, slop_string line);
slop_list_string test_emit_emit_ctx_get_lines(test_emit_EmitContext* ctx);
types_SExpr* test_emit_build_call_sexpr(slop_arena* arena, slop_string fn_name, slop_list_types_SExpr_ptr args, uint8_t needs_arena, int64_t arena_pos);
slop_string test_emit_escape_string(slop_arena* arena, slop_string s);
slop_list_string test_emit_emit_test_harness_typed(slop_arena* arena, slop_list_extract_TestCase_ptr tests, slop_string module_prefix, type_extract_TypeRegistry* types, slop_list_type_extract_ImportEntry imports, context_TranspileContext* tctx);
uint8_t test_emit_any_test_needs_arena(slop_list_extract_TestCase_ptr tests);
void test_emit_emit_test_function_typed(test_emit_EmitContext* ctx, extract_TestCase tc, int64_t index, slop_string prefix, type_extract_TypeRegistry* types, context_TranspileContext* tctx);
void test_emit_emit_main_function(test_emit_EmitContext* ctx, int64_t test_count, uint8_t needs_arena);
slop_string test_emit_make_c_fn_name(slop_arena* arena, slop_string fn_name, slop_option_string module_name, slop_string prefix);
slop_string test_emit_build_args_display_typed(slop_arena* arena, slop_list_types_SExpr_ptr args, type_extract_TypeRegistry types);
test_emit_CompareInfo test_emit_build_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_option_string return_type, slop_string prefix, type_extract_TypeRegistry types, slop_option_string eq_fn, context_TranspileContext* tctx);
test_emit_CompareInfo test_emit_build_record_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types, context_TranspileContext* tctx);
test_emit_CompareInfo test_emit_build_record_comparison_inner(slop_arena* arena, type_extract_TypeRegistry types, slop_string record_name, slop_list_types_SExpr_ptr field_values, slop_string c_expected, slop_string decl_type);
slop_string test_emit_get_record_decl_type(slop_arena* arena, type_extract_TypeRegistry types, slop_string record_name);
slop_string test_emit_get_record_name_from_expr(types_SExpr* expr);
slop_list_types_SExpr_ptr test_emit_get_record_field_values(slop_arena* arena, types_SExpr* expr);
uint8_t test_emit_is_wildcard_expr(types_SExpr* expr);
slop_string test_emit_build_record_field_comparisons_with_values(slop_arena* arena, slop_list_type_extract_TstFieldEntry fields, slop_list_types_SExpr_ptr field_values, slop_string result_accessor, slop_string expected_var);
slop_string test_emit_build_single_field_comparison_with_accessor(slop_arena* arena, slop_string fname, slop_string ftype, slop_string result_accessor, slop_string expected_var);
uint8_t test_emit_is_likely_struct_type(slop_string type_name);
slop_string test_emit_get_first_symbol_name(types_SExpr* expr);
test_emit_CompareInfo test_emit_build_union_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types, slop_string ret_type_str, context_TranspileContext* tctx);
slop_string test_emit_build_union_payload_comparison(slop_arena* arena, slop_string payload_type, slop_string c_variant, slop_string expected_var, type_extract_TypeRegistry types);
slop_string test_emit_build_union_record_payload_comparison(slop_arena* arena, slop_list_type_extract_TstFieldEntry fields, slop_string c_variant, slop_string expected_var);
slop_string test_emit_build_union_field_comparison(slop_arena* arena, slop_string fname, slop_string ftype, slop_string c_variant, slop_string expected_var);
uint8_t test_emit_is_union_constructor_typed(types_SExpr* expr, type_extract_TypeRegistry types);
slop_string test_emit_get_union_variant_name(types_SExpr* expr);
uint8_t test_emit_is_enum_value_typed(types_SExpr* expr, type_extract_TypeRegistry types);
uint8_t test_emit_is_record_constructor_typed(types_SExpr* expr, type_extract_TypeRegistry types);
slop_string test_emit_emit_string_slice(slop_string s, int64_t start);
slop_string test_emit_get_some_inner_typed(slop_arena* arena, types_SExpr* expr, context_TranspileContext* tctx);
slop_string test_emit_get_ok_inner_typed(slop_arena* arena, types_SExpr* expr, context_TranspileContext* tctx);
slop_string test_emit_get_error_inner_typed(slop_arena* arena, types_SExpr* expr, context_TranspileContext* tctx);
types_SExpr* test_emit_get_some_inner_expr(types_SExpr* expected);
types_SExpr* test_emit_get_ok_inner_expr(types_SExpr* expected);
uint8_t test_emit_is_none_value(types_SExpr* expr);
uint8_t test_emit_is_some_value(types_SExpr* expr);
uint8_t test_emit_is_ok_value(types_SExpr* expr);
uint8_t test_emit_is_error_value(types_SExpr* expr);
slop_string test_emit_extract_list_element_type(slop_arena* arena, slop_string list_type_str);
slop_string test_emit_build_eq_function_name(slop_arena* arena, slop_string type_name, slop_string prefix, type_extract_TypeRegistry types);
test_emit_CompareInfo test_emit_build_list_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types, slop_string ret_type_str, slop_option_string eq_fn, context_TranspileContext* tctx);
context_TranspileContext* test_emit_init_transpile_context(slop_arena* arena, slop_list_types_SExpr_ptr ast, slop_string module_name);
void test_emit_init_transpile_context_for_imports(slop_arena* arena, context_TranspileContext* tctx, slop_list_types_SExpr_ptr import_ast, slop_string import_mod_name);
void test_emit_re_prescan_main_module(slop_arena* arena, context_TranspileContext* tctx, slop_list_types_SExpr_ptr ast);
void test_emit_register_all_field_types(context_TranspileContext* tctx, slop_list_types_SExpr_ptr body_forms);
void test_emit_register_type_fields(context_TranspileContext* tctx, types_SExpr* type_form);

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TEST_EMIT_EMITCONTEXT_DEFINED
#define SLOP_OPTION_TEST_EMIT_EMITCONTEXT_DEFINED
SLOP_OPTION_DEFINE(test_emit_EmitContext, slop_option_test_emit_EmitContext)
#endif

#ifndef SLOP_OPTION_TEST_EMIT_COMPAREINFO_DEFINED
#define SLOP_OPTION_TEST_EMIT_COMPAREINFO_DEFINED
SLOP_OPTION_DEFINE(test_emit_CompareInfo, slop_option_test_emit_CompareInfo)
#endif

#ifndef SLOP_OPTION_EXTRACT_TESTCASE_PTR_DEFINED
#define SLOP_OPTION_EXTRACT_TESTCASE_PTR_DEFINED
SLOP_OPTION_DEFINE(extract_TestCase*, slop_option_extract_TestCase_ptr)
#endif

#ifndef SLOP_OPTION_TYPE_EXTRACT_IMPORTENTRY_DEFINED
#define SLOP_OPTION_TYPE_EXTRACT_IMPORTENTRY_DEFINED
SLOP_OPTION_DEFINE(type_extract_ImportEntry, slop_option_type_extract_ImportEntry)
#endif

#ifndef SLOP_OPTION_TYPE_EXTRACT_TSTFIELDENTRY_DEFINED
#define SLOP_OPTION_TYPE_EXTRACT_TSTFIELDENTRY_DEFINED
SLOP_OPTION_DEFINE(type_extract_TstFieldEntry, slop_option_type_extract_TstFieldEntry)
#endif


#endif
