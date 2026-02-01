#ifndef SLOP_ctype_H
#define SLOP_ctype_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_types.h"
#include "slop_strlib.h"

#ifndef SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
SLOP_LIST_DEFINE(types_SExpr*, slop_list_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
#define SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
SLOP_OPTION_DEFINE(types_ResolvedType*, slop_option_types_ResolvedType_ptr)
#endif

uint8_t ctype_is_c_keyword(slop_string name);
uint8_t ctype_is_builtin_type(slop_string name);
uint8_t ctype_is_builtin_c_type(slop_string c_name);
uint8_t ctype_is_int_type(slop_string name);
uint8_t ctype_is_float_type(slop_string name);
uint8_t ctype_is_bool_type(slop_string name);
uint8_t ctype_is_numeric_type(slop_string name);
slop_option_string ctype_builtin_type_c(slop_arena* arena, slop_string name);
slop_string ctype_to_c_name(slop_arena* arena, slop_string name);
slop_string ctype_type_to_identifier(slop_arena* arena, slop_string c_type);
uint8_t ctype_is_type_variable(slop_string name);
slop_string ctype_to_c_type(slop_arena* arena, types_SExpr* expr);
slop_string ctype_to_c_type_compound(slop_arena* arena, slop_list_types_SExpr_ptr items);
slop_string ctype_build_fn_args_str(slop_arena* arena, types_SExpr* args_expr);
slop_string ctype_sexpr_to_type_string(slop_arena* arena, types_SExpr* expr);
slop_string ctype_range_type_to_c_type(slop_arena* arena, slop_list_types_SExpr_ptr items, int64_t len);
slop_option_types_ResolvedType_ptr ctype_get_node_resolved_type(types_SExpr* expr);
slop_string ctype_resolved_type_to_c(slop_arena* arena, types_ResolvedType* rt);

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
#define SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
SLOP_OPTION_DEFINE(types_ResolvedType*, slop_option_types_ResolvedType_ptr)
#endif


#endif
