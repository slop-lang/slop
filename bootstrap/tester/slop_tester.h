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

#ifndef SLOP_LIST_TYPE_EXTRACT_IMPORTENTRY_DEFINED
#define SLOP_LIST_TYPE_EXTRACT_IMPORTENTRY_DEFINED
SLOP_LIST_DEFINE(type_extract_ImportEntry, slop_list_type_extract_ImportEntry)
#endif

#ifndef SLOP_OPTION_TYPE_EXTRACT_IMPORTENTRY_DEFINED
#define SLOP_OPTION_TYPE_EXTRACT_IMPORTENTRY_DEFINED
SLOP_OPTION_DEFINE(type_extract_ImportEntry, slop_option_type_extract_ImportEntry)
#endif

#ifndef SLOP_LIST_TYPE_EXTRACT_IMPORTENTRY_DEFINED
#define SLOP_LIST_TYPE_EXTRACT_IMPORTENTRY_DEFINED
SLOP_LIST_DEFINE(type_extract_ImportEntry, slop_list_type_extract_ImportEntry)
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
slop_list_type_extract_ImportEntry tester_extract_imports(slop_arena* arena, slop_list_types_SExpr_ptr exprs);
tester_TestResult tester_generate_tests(slop_arena* arena, slop_string source);
tester_TestResult tester_generate_tests_with_imports(slop_arena* arena, slop_string source, slop_list_string import_sources);
void tester_extract_types_from_module_ast(slop_arena* arena, slop_list_types_SExpr_ptr ast, type_extract_TypeRegistry* types, slop_string prefix);
void tester_extract_types_from_module_form(slop_arena* arena, types_SExpr* module_form, type_extract_TypeRegistry* types, slop_string prefix);
void tester_extract_single_type_def(slop_arena* arena, types_SExpr* type_form, type_extract_TypeRegistry* types, slop_string prefix);
slop_string tester_make_prefixed_c_name(slop_arena* arena, slop_string prefix, slop_string name);
slop_string tester_convert_to_c_ident(slop_arena* arena, slop_string name);
type_extract_TypeEntry* tester_type_entry_new_local(slop_arena* arena, slop_string name, slop_string c_name, int64_t kind);
type_extract_TypeEntry* tester_extract_record_type_entry(slop_arena* arena, slop_string name, slop_string c_name, types_SExpr* def);
type_extract_TypeEntry* tester_extract_union_type_entry(slop_arena* arena, slop_string name, slop_string c_name, types_SExpr* def);
type_extract_TypeEntry* tester_extract_enum_type_entry(slop_arena* arena, slop_string name, slop_string c_name, types_SExpr* def);
slop_string tester_sexpr_to_string_simple(slop_arena* arena, types_SExpr* expr);

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPE_EXTRACT_IMPORTENTRY_DEFINED
#define SLOP_OPTION_TYPE_EXTRACT_IMPORTENTRY_DEFINED
SLOP_OPTION_DEFINE(type_extract_ImportEntry, slop_option_type_extract_ImportEntry)
#endif

#ifndef SLOP_OPTION_TESTER_TESTRESULT_DEFINED
#define SLOP_OPTION_TESTER_TESTRESULT_DEFINED
SLOP_OPTION_DEFINE(tester_TestResult, slop_option_tester_TestResult)
#endif


#endif
