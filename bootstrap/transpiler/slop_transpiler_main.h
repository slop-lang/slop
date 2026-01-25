#ifndef SLOP_transpiler_main_H
#define SLOP_transpiler_main_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_types.h"
#include "slop_parser.h"
#include "slop_context.h"
#include "slop_transpiler.h"
#include "slop_strlib.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
SLOP_LIST_DEFINE(types_SExpr*, slop_list_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

slop_option_string transpiler_main_read_file(slop_arena* arena, char* filename);
void transpiler_main_print_str(char* s);
void transpiler_main_print_string(slop_string s);
void transpiler_main_print_json_string(slop_arena* arena, slop_string s);
slop_string transpiler_main_lines_to_string(slop_arena* arena, slop_list_string lines);
slop_string transpiler_main_extract_module_name(slop_list_types_SExpr_ptr exprs);
int main(int64_t argc, char** argv);
int64_t transpiler_main_transpile_single_file_with_ctx(context_TranspileContext* ctx, slop_string source, uint8_t first);
int64_t transpiler_main_transpile_single_file(slop_arena* arena, slop_string source, uint8_t first);
void transpiler_main_output_module_json(slop_arena* arena, context_TranspileContext* ctx, slop_string mod_name, uint8_t first);

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif


#endif
