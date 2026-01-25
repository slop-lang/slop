#ifndef SLOP_extract_H
#define SLOP_extract_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_types.h"
#include "slop_parser.h"

typedef struct extract_TestCase extract_TestCase;

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

struct extract_TestCase {
    slop_string fn_name;
    slop_option_string module_name;
    slop_list_types_SExpr_ptr args;
    types_SExpr* expected;
    slop_option_string return_type;
    uint8_t needs_arena;
    int64_t arena_position;
};
typedef struct extract_TestCase extract_TestCase;

#ifndef SLOP_OPTION_EXTRACT_TESTCASE_DEFINED
#define SLOP_OPTION_EXTRACT_TESTCASE_DEFINED
SLOP_OPTION_DEFINE(extract_TestCase, slop_option_extract_TestCase)
#endif

extract_TestCase* extract_test_case_new(slop_arena* arena, slop_string fn_name, slop_option_string module_name, slop_list_types_SExpr_ptr args, types_SExpr* expected, slop_option_string return_type, uint8_t needs_arena, int64_t arena_position);
int64_t extract_find_arrow_separator(slop_list_types_SExpr_ptr items);
int64_t extract_detect_arena_param(types_SExpr* params);
slop_option_string extract_extract_return_type(slop_arena* arena, types_SExpr* spec_form);
slop_list_extract_TestCase_ptr extract_extract_fn_examples(slop_arena* arena, types_SExpr* fn_form, slop_option_string module_name);
slop_option_extract_TestCase_ptr extract_parse_example(slop_arena* arena, types_SExpr* example_form, slop_string fn_name, slop_option_string module_name, slop_option_string return_type, uint8_t needs_arena, int64_t arena_pos);
slop_list_types_SExpr_ptr extract_unpack_grouped_args(slop_arena* arena, slop_list_types_SExpr_ptr args);
slop_list_extract_TestCase_ptr extract_extract_examples_from_module(slop_arena* arena, types_SExpr* module_form);
slop_list_extract_TestCase_ptr extract_extract_examples_from_ast(slop_arena* arena, slop_list_types_SExpr_ptr ast);

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_EXTRACT_TESTCASE_DEFINED
#define SLOP_OPTION_EXTRACT_TESTCASE_DEFINED
SLOP_OPTION_DEFINE(extract_TestCase, slop_option_extract_TestCase)
#endif

#ifndef SLOP_OPTION_EXTRACT_TESTCASE_PTR_DEFINED
#define SLOP_OPTION_EXTRACT_TESTCASE_PTR_DEFINED
SLOP_OPTION_DEFINE(extract_TestCase*, slop_option_extract_TestCase_ptr)
#endif


#endif
