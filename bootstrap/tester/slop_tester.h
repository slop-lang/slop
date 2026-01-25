#ifndef SLOP_tester_H
#define SLOP_tester_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_types.h"
#include "slop_parser.h"
#include "slop_extract.h"
#include "slop_emit.h"
#include "slop_type_extract.h"
#include "slop_ctype.h"

typedef struct tester_TestResult tester_TestResult;

#ifndef SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
SLOP_LIST_DEFINE(types_SExpr*, slop_list_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

struct tester_TestResult {
    uint8_t success;
    slop_list_string test_harness;
    int64_t test_count;
    slop_string module_name;
    slop_string error_message;
};
typedef struct tester_TestResult tester_TestResult;

#ifndef SLOP_OPTION_TESTER_TESTRESULT_DEFINED
#define SLOP_OPTION_TESTER_TESTRESULT_DEFINED
SLOP_OPTION_DEFINE(tester_TestResult, slop_option_tester_TestResult)
#endif

slop_string tester_extract_module_name(slop_list_types_SExpr_ptr exprs);
slop_list_string tester_extract_imports(slop_arena* arena, slop_list_types_SExpr_ptr exprs);
tester_TestResult tester_generate_tests(slop_arena* arena, slop_string source);

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TESTER_TESTRESULT_DEFINED
#define SLOP_OPTION_TESTER_TESTRESULT_DEFINED
SLOP_OPTION_DEFINE(tester_TestResult, slop_option_tester_TestResult)
#endif


#endif
