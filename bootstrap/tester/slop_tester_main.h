#ifndef SLOP_tester_main_H
#define SLOP_tester_main_H

#include "../runtime/slop_runtime.h"
#ifndef SLOP_RUNTIME_ABI
#error "this module was generated for SLOP runtime ABI 2026-1 (SLOP_RUNTIME_ABI 202601), but slop_runtime.h predates runtime ABI versioning: use the slop_runtime.h of the SLOP release that generated this code"
#elif SLOP_RUNTIME_ABI != 202601
#error "this module was generated for SLOP runtime ABI 2026-1 (SLOP_RUNTIME_ABI 202601), which this slop_runtime.h does not provide (SLOP_RUNTIME_ABI differs): regenerate the C with the SLOP release that matches the runtime, or use the slop_runtime.h of the release that generated it"
#endif
#include <stdint.h>
#include <stdbool.h>
#include "slop_types.h"
#include "slop_tester.h"
#include "slop_strlib.h"
#include "slop_ctype.h"
#include <stdio.h>
#include <stdlib.h>

#ifndef SLOP_LIST_CTYPE_MODULEPACKAGE_DEFINED
#define SLOP_LIST_CTYPE_MODULEPACKAGE_DEFINED
#define SLOP_LIST_CTYPE_MODULEPACKAGE_IMPL_DEFINED
SLOP_LIST_DEFINE(ctype_ModulePackage, slop_list_ctype_ModulePackage)
#endif

#ifndef SLOP_OPTION_CTYPE_MODULEPACKAGE_DEFINED
#define SLOP_OPTION_CTYPE_MODULEPACKAGE_DEFINED
SLOP_OPTION_DEFINE(ctype_ModulePackage, slop_option_ctype_ModulePackage)
#endif

slop_option_string tester_main_read_file(slop_arena* arena, char* filename);
void tester_main_print_str(char* s);
void tester_main_print_string(slop_string s);
void tester_main_print_json_string(slop_string s);
slop_string tester_main_lines_to_string(slop_arena* arena, slop_list_string lines);
void tester_main_print_int(int64_t n);
slop_list_string tester_main_read_import_files(slop_arena* arena, uint8_t** argv, slop_list_int files);
uint8_t tester_main_collect_args(slop_arena* arena, int64_t argc, uint8_t** argv, slop_list_ctype_ModulePackage* packages, slop_list_int* files);
int main(int argc, char** _c_argv);

#ifndef SLOP_OPTION_CTYPE_MODULEPACKAGE_DEFINED
#define SLOP_OPTION_CTYPE_MODULEPACKAGE_DEFINED
SLOP_OPTION_DEFINE(ctype_ModulePackage, slop_option_ctype_ModulePackage)
#endif


#endif
