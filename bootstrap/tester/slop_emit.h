#ifndef SLOP_emit_H
#define SLOP_emit_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_types.h"
#include "slop_parser.h"
#include "slop_extract.h"
#include "slop_strlib.h"
#include "slop_type_extract.h"
#include "slop_ctype.h"
#include <string.h>

typedef struct emit_EmitContext emit_EmitContext;
typedef struct emit_CompareInfo emit_CompareInfo;

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

#ifndef SLOP_LIST_TYPE_EXTRACT_FIELDENTRY_DEFINED
#define SLOP_LIST_TYPE_EXTRACT_FIELDENTRY_DEFINED
SLOP_LIST_DEFINE(type_extract_FieldEntry, slop_list_type_extract_FieldEntry)
#endif

#ifndef SLOP_OPTION_TYPE_EXTRACT_IMPORTENTRY_DEFINED
#define SLOP_OPTION_TYPE_EXTRACT_IMPORTENTRY_DEFINED
SLOP_OPTION_DEFINE(type_extract_ImportEntry, slop_option_type_extract_ImportEntry)
#endif

#ifndef SLOP_OPTION_TYPE_EXTRACT_FIELDENTRY_DEFINED
#define SLOP_OPTION_TYPE_EXTRACT_FIELDENTRY_DEFINED
SLOP_OPTION_DEFINE(type_extract_FieldEntry, slop_option_type_extract_FieldEntry)
#endif

#ifndef SLOP_LIST_TYPE_EXTRACT_IMPORTENTRY_DEFINED
#define SLOP_LIST_TYPE_EXTRACT_IMPORTENTRY_DEFINED
SLOP_LIST_DEFINE(type_extract_ImportEntry, slop_list_type_extract_ImportEntry)
#endif

#ifndef SLOP_LIST_TYPE_EXTRACT_FIELDENTRY_DEFINED
#define SLOP_LIST_TYPE_EXTRACT_FIELDENTRY_DEFINED
SLOP_LIST_DEFINE(type_extract_FieldEntry, slop_list_type_extract_FieldEntry)
#endif

struct emit_EmitContext {
    slop_list_string lines;
    slop_arena* arena;
    type_extract_TypeRegistry* types;
    uint8_t has_types;
};
typedef struct emit_EmitContext emit_EmitContext;

#ifndef SLOP_OPTION_EMIT_EMITCONTEXT_DEFINED
#define SLOP_OPTION_EMIT_EMITCONTEXT_DEFINED
SLOP_OPTION_DEFINE(emit_EmitContext, slop_option_emit_EmitContext)
#endif

struct emit_CompareInfo {
    slop_string compare_expr;
    slop_string result_fmt;
    slop_string result_args;
    slop_string expected_fmt;
    slop_string expected_args;
};
typedef struct emit_CompareInfo emit_CompareInfo;

#ifndef SLOP_OPTION_EMIT_COMPAREINFO_DEFINED
#define SLOP_OPTION_EMIT_COMPAREINFO_DEFINED
SLOP_OPTION_DEFINE(emit_CompareInfo, slop_option_emit_CompareInfo)
#endif

slop_string emit_prefix_symbol(slop_arena* arena, slop_string name, slop_string prefix, type_extract_TypeRegistry types);
emit_EmitContext* emit_emit_ctx_new(slop_arena* arena);
emit_EmitContext* emit_emit_ctx_new_typed(slop_arena* arena, type_extract_TypeRegistry* types);
void emit_emit(emit_EmitContext* ctx, slop_string line);
slop_list_string emit_emit_ctx_get_lines(emit_EmitContext* ctx);
slop_string emit_sexpr_to_c_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_emit_union_literal_typed(slop_arena* arena, type_extract_TypeEntry* union_entry, slop_string variant_name, slop_list_types_SExpr_ptr items, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_emit_record_literal_typed(slop_arena* arena, type_extract_TypeEntry* record_entry, slop_list_types_SExpr_ptr items, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_emit_field_value_typed(slop_arena* arena, types_SExpr* item, slop_string field_type, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_emit_option_value_typed(slop_arena* arena, types_SExpr* item, slop_string opt_type, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_option_type_to_c(slop_arena* arena, slop_string opt_type, slop_string prefix);
slop_string emit_emit_binary_op_typed(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string c_op, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_emit_function_call_typed(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_emit_args_typed(slop_arena* arena, slop_list_types_SExpr_ptr items, int64_t start, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_emit_type_constructor_typed(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_sexpr_to_c(slop_arena* arena, types_SExpr* expr, slop_string prefix);
slop_string emit_emit_binary_op(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string c_op, slop_string prefix);
slop_string emit_emit_function_call(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string prefix);
slop_string emit_emit_args(slop_arena* arena, slop_list_types_SExpr_ptr items, int64_t start, slop_string prefix);
slop_string emit_emit_type_constructor(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string prefix);
slop_string emit_escape_string(slop_arena* arena, slop_string s);
slop_list_string emit_emit_test_harness_typed(slop_arena* arena, slop_list_extract_TestCase_ptr tests, slop_string module_prefix, type_extract_TypeRegistry* types, slop_list_type_extract_ImportEntry imports);
slop_list_string emit_emit_test_harness(slop_arena* arena, slop_list_extract_TestCase_ptr tests, slop_string module_prefix);
uint8_t emit_any_test_needs_arena(slop_list_extract_TestCase_ptr tests);
void emit_emit_test_function_typed(emit_EmitContext* ctx, extract_TestCase tc, int64_t index, slop_string prefix, type_extract_TypeRegistry* types);
uint8_t emit_is_none_or_some_form(types_SExpr* expr);
uint8_t emit_args_contain_complex_constructor(slop_list_types_SExpr_ptr args);
void emit_emit_test_function(emit_EmitContext* ctx, extract_TestCase tc, int64_t index, slop_string prefix);
void emit_emit_main_function(emit_EmitContext* ctx, int64_t test_count, uint8_t needs_arena);
slop_string emit_build_args_display_typed(slop_arena* arena, slop_list_types_SExpr_ptr args, type_extract_TypeRegistry types);
slop_string emit_build_call_args_typed(slop_arena* arena, slop_list_types_SExpr_ptr args, uint8_t needs_arena, int64_t arena_pos, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_make_c_fn_name(slop_arena* arena, slop_string fn_name, slop_option_string module_name, slop_string prefix);
slop_string emit_build_args_display(slop_arena* arena, slop_list_types_SExpr_ptr args);
slop_string emit_build_call_args(slop_arena* arena, slop_list_types_SExpr_ptr args, uint8_t needs_arena, int64_t arena_pos, slop_string prefix);
emit_CompareInfo emit_build_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_option_string return_type, slop_string prefix, type_extract_TypeRegistry types, slop_option_string eq_fn);
emit_CompareInfo emit_build_record_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_get_record_name_from_expr(types_SExpr* expr);
slop_list_types_SExpr_ptr emit_get_record_field_values(slop_arena* arena, types_SExpr* expr);
uint8_t emit_is_wildcard_expr(types_SExpr* expr);
slop_string emit_build_record_field_comparisons_with_values(slop_arena* arena, slop_list_type_extract_FieldEntry fields, slop_list_types_SExpr_ptr field_values, slop_string result_accessor, slop_string expected_var);
slop_string emit_build_single_field_comparison_with_accessor(slop_arena* arena, slop_string fname, slop_string ftype, slop_string result_accessor, slop_string expected_var);
slop_string emit_build_record_field_comparisons(slop_arena* arena, slop_list_type_extract_FieldEntry fields, slop_string prefix, slop_string expected_var);
slop_string emit_build_single_field_comparison(slop_arena* arena, slop_string fname, slop_string ftype, slop_string expected_var);
emit_CompareInfo emit_build_union_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types, slop_string ret_type_str);
slop_string emit_build_union_payload_comparison(slop_arena* arena, slop_string payload_type, slop_string c_variant, slop_string expected_var, type_extract_TypeRegistry types);
slop_string emit_build_union_record_payload_comparison(slop_arena* arena, slop_list_type_extract_FieldEntry fields, slop_string c_variant, slop_string expected_var);
slop_string emit_build_union_field_comparison(slop_arena* arena, slop_string fname, slop_string ftype, slop_string c_variant, slop_string expected_var);
uint8_t emit_is_union_constructor_typed(types_SExpr* expr, type_extract_TypeRegistry types);
slop_string emit_get_union_variant_name(types_SExpr* expr);
uint8_t emit_is_enum_value_typed(types_SExpr* expr, type_extract_TypeRegistry types);
uint8_t emit_is_record_constructor_typed(types_SExpr* expr, type_extract_TypeRegistry types);
slop_string emit_emit_string_slice(slop_string s, int64_t start);
slop_string emit_get_some_inner_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types);
slop_string emit_get_ok_inner_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types);
types_SExpr* emit_get_some_inner_expr(types_SExpr* expected);
slop_string emit_get_error_inner_typed(slop_arena* arena, types_SExpr* expr, slop_string prefix, type_extract_TypeRegistry types);
types_SExpr* emit_get_ok_inner_expr(types_SExpr* expected);
slop_string emit_extract_list_element_type(slop_arena* arena, slop_string list_type_str);
slop_string emit_build_eq_function_name(slop_arena* arena, slop_string type_name, slop_string prefix, type_extract_TypeRegistry types);
emit_CompareInfo emit_build_list_comparison_typed(slop_arena* arena, types_SExpr* expected, slop_string prefix, type_extract_TypeRegistry types, slop_string ret_type_str, slop_option_string eq_fn);
uint8_t emit_is_none_value(types_SExpr* expr);
uint8_t emit_is_some_value(types_SExpr* expr);
uint8_t emit_is_ok_value(types_SExpr* expr);
uint8_t emit_is_error_value(types_SExpr* expr);
slop_string emit_get_some_inner(slop_arena* arena, types_SExpr* expr, slop_string prefix);
slop_string emit_get_ok_inner(slop_arena* arena, types_SExpr* expr, slop_string prefix);
slop_string emit_get_error_inner(slop_arena* arena, types_SExpr* expr, slop_string prefix);
uint8_t emit_is_list_literal(types_SExpr* expr);
uint8_t emit_is_union_or_record_constructor(types_SExpr* expr);
emit_CompareInfo emit_build_comparison(slop_arena* arena, types_SExpr* expected, slop_option_string return_type, slop_string prefix);
emit_CompareInfo emit_build_list_comparison(slop_arena* arena, types_SExpr* expected, slop_string prefix);

#ifndef SLOP_OPTION_EMIT_EMITCONTEXT_DEFINED
#define SLOP_OPTION_EMIT_EMITCONTEXT_DEFINED
SLOP_OPTION_DEFINE(emit_EmitContext, slop_option_emit_EmitContext)
#endif

#ifndef SLOP_OPTION_EMIT_COMPAREINFO_DEFINED
#define SLOP_OPTION_EMIT_COMPAREINFO_DEFINED
SLOP_OPTION_DEFINE(emit_CompareInfo, slop_option_emit_CompareInfo)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_EXTRACT_TESTCASE_PTR_DEFINED
#define SLOP_OPTION_EXTRACT_TESTCASE_PTR_DEFINED
SLOP_OPTION_DEFINE(extract_TestCase*, slop_option_extract_TestCase_ptr)
#endif

#ifndef SLOP_OPTION_TYPE_EXTRACT_IMPORTENTRY_DEFINED
#define SLOP_OPTION_TYPE_EXTRACT_IMPORTENTRY_DEFINED
SLOP_OPTION_DEFINE(type_extract_ImportEntry, slop_option_type_extract_ImportEntry)
#endif

#ifndef SLOP_OPTION_TYPE_EXTRACT_FIELDENTRY_DEFINED
#define SLOP_OPTION_TYPE_EXTRACT_FIELDENTRY_DEFINED
SLOP_OPTION_DEFINE(type_extract_FieldEntry, slop_option_type_extract_FieldEntry)
#endif


#endif
