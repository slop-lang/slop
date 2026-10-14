#ifndef SLOP_resolve_H
#define SLOP_resolve_H

#include "../runtime/slop_runtime.h"
#ifndef SLOP_RUNTIME_ABI
#error "this module was generated for SLOP runtime ABI 2026-1 (SLOP_RUNTIME_ABI 202601), but slop_runtime.h predates runtime ABI versioning: use the slop_runtime.h of the SLOP release that generated this code"
#elif SLOP_RUNTIME_ABI != 202601
#error "this module was generated for SLOP runtime ABI 2026-1 (SLOP_RUNTIME_ABI 202601), which this slop_runtime.h does not provide (SLOP_RUNTIME_ABI differs): regenerate the C with the SLOP release that matches the runtime, or use the slop_runtime.h of the release that generated it"
#endif
#include <stdint.h>
#include <stdbool.h>
#include "slop_parser.h"
#include "slop_types.h"
#include "slop_type_env.h"
#include "slop_strlib.h"
#include "slop_path.h"
#include "slop_file.h"

typedef struct resolve_ImportSite resolve_ImportSite;

#ifndef SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_IMPL_DEFINED
SLOP_LIST_DEFINE(types_SExpr*, slop_list_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

struct resolve_ImportSite {
    slop_string source;
    slop_string name;
    types_SExpr* name_expr;
};
typedef struct resolve_ImportSite resolve_ImportSite;

#ifndef SLOP_OPTION_RESOLVE_IMPORTSITE_DEFINED
#define SLOP_OPTION_RESOLVE_IMPORTSITE_DEFINED
SLOP_OPTION_DEFINE(resolve_ImportSite, slop_option_resolve_ImportSite)
#endif

#ifndef SLOP_LIST_RESOLVE_IMPORTSITE_DEFINED
#define SLOP_LIST_RESOLVE_IMPORTSITE_DEFINED
#define SLOP_LIST_RESOLVE_IMPORTSITE_IMPL_DEFINED
SLOP_LIST_DEFINE(resolve_ImportSite, slop_list_resolve_ImportSite)
#endif

void resolve_resolve_imports(type_env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void resolve_resolve_import_stmt(type_env_TypeEnv* env, types_SExpr* import_form);
slop_list_resolve_ImportSite resolve_collect_import_sites(slop_arena* arena, slop_list_types_SExpr_ptr ast);
slop_list_resolve_ImportSite resolve_push_import_sites(slop_arena* arena, slop_list_resolve_ImportSite sites, types_SExpr* import_form);
slop_option_string resolve_resolve_import_target(type_env_TypeEnv* env, slop_string src, slop_string name);
void resolve_resolve_import_name(type_env_TypeEnv* env, resolve_ImportSite site);
slop_string resolve_qualified_module_part(slop_arena* arena, slop_string qualified);
void resolve_check_import_shadowing(type_env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
uint8_t resolve_contains_slash(slop_string s);
slop_option_string resolve_resolve_module_file(slop_arena* arena, slop_string module_name, slop_option_string from_file);

#ifndef SLOP_OPTION_RESOLVE_IMPORTSITE_DEFINED
#define SLOP_OPTION_RESOLVE_IMPORTSITE_DEFINED
SLOP_OPTION_DEFINE(resolve_ImportSite, slop_option_resolve_ImportSite)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif


#endif
