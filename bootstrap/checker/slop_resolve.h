#ifndef SLOP_resolve_H
#define SLOP_resolve_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_parser.h"
#include "slop_types.h"
#include "slop_env.h"
#include "slop_path.h"
#include "slop_file.h"

#ifndef SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
SLOP_LIST_DEFINE(types_SExpr*, slop_list_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

void resolve_resolve_imports(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void resolve_resolve_module_imports(env_TypeEnv* env, types_SExpr* module_form);
void resolve_resolve_import_stmt(env_TypeEnv* env, types_SExpr* import_form);
uint8_t resolve_contains_slash(slop_string s);
slop_option_string resolve_resolve_module_file(slop_arena* arena, slop_string module_name, slop_option_string from_file);

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif


#endif
