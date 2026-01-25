#ifndef SLOP_parser_cli_H
#define SLOP_parser_cli_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_file.h"
#include "slop_types.h"
#include "slop_parser.h"
#include <string.h>

typedef enum {
    parser_cli_OutputFormat_fmt_sexp,
    parser_cli_OutputFormat_fmt_json
} parser_cli_OutputFormat;

#ifndef SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
SLOP_LIST_DEFINE(types_SExpr*, slop_list_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

slop_string parser_cli_argv_to_string(uint8_t** argv, int64_t index);
void parser_cli_print_json_array(slop_arena* arena, slop_list_types_SExpr_ptr exprs);
void parser_cli_print_sexp_list(slop_arena* arena, slop_list_types_SExpr_ptr exprs);
int main(int64_t argc, uint8_t** argv);

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif


#endif
