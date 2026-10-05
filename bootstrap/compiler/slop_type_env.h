#ifndef SLOP_type_env_H
#define SLOP_type_env_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_strlib.h"
#include "slop_types.h"

typedef struct type_env_VarBinding type_env_VarBinding;
typedef struct type_env_ConstBinding type_env_ConstBinding;
typedef struct type_env_ImportEntry type_env_ImportEntry;
typedef struct type_env_ModuleImport type_env_ModuleImport;
typedef struct type_env_CheckerScope type_env_CheckerScope;
typedef struct type_env_VariantMapping type_env_VariantMapping;
typedef struct type_env_BindingAnnotation type_env_BindingAnnotation;
typedef struct type_env_TypeEnv type_env_TypeEnv;

#ifndef SLOP_LIST_TYPES_RESOLVEDTYPE_PTR_DEFINED
#define SLOP_LIST_TYPES_RESOLVEDTYPE_PTR_DEFINED
#define SLOP_LIST_TYPES_RESOLVEDTYPE_PTR_IMPL_DEFINED
SLOP_LIST_DEFINE(types_ResolvedType*, slop_list_types_ResolvedType_ptr)
#endif

#ifndef SLOP_LIST_TYPES_FNSIGNATURE_PTR_DEFINED
#define SLOP_LIST_TYPES_FNSIGNATURE_PTR_DEFINED
#define SLOP_LIST_TYPES_FNSIGNATURE_PTR_IMPL_DEFINED
SLOP_LIST_DEFINE(types_FnSignature*, slop_list_types_FnSignature_ptr)
#endif

#ifndef SLOP_LIST_TYPE_ENV_CHECKERSCOPE_PTR_DEFINED
#define SLOP_LIST_TYPE_ENV_CHECKERSCOPE_PTR_DEFINED
#define SLOP_LIST_TYPE_ENV_CHECKERSCOPE_PTR_IMPL_DEFINED
SLOP_LIST_DEFINE(type_env_CheckerScope*, slop_list_type_env_CheckerScope_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
#define SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
SLOP_OPTION_DEFINE(types_ResolvedType*, slop_option_types_ResolvedType_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_FNSIGNATURE_PTR_DEFINED
#define SLOP_OPTION_TYPES_FNSIGNATURE_PTR_DEFINED
SLOP_OPTION_DEFINE(types_FnSignature*, slop_option_types_FnSignature_ptr)
#endif

#ifndef SLOP_OPTION_TYPE_ENV_CHECKERSCOPE_PTR_DEFINED
#define SLOP_OPTION_TYPE_ENV_CHECKERSCOPE_PTR_DEFINED
SLOP_OPTION_DEFINE(type_env_CheckerScope*, slop_option_type_env_CheckerScope_ptr)
#endif

#ifndef SLOP_LIST_TYPES_DIAGNOSTIC_DEFINED
#define SLOP_LIST_TYPES_DIAGNOSTIC_DEFINED
#define SLOP_LIST_TYPES_DIAGNOSTIC_IMPL_DEFINED
SLOP_LIST_DEFINE(types_Diagnostic, slop_list_types_Diagnostic)
#endif

#ifndef SLOP_LIST_TYPES_PARAMINFO_DEFINED
#define SLOP_LIST_TYPES_PARAMINFO_DEFINED
#define SLOP_LIST_TYPES_PARAMINFO_IMPL_DEFINED
SLOP_LIST_DEFINE(types_ParamInfo, slop_list_types_ParamInfo)
#endif

#ifndef SLOP_OPTION_TYPES_DIAGNOSTIC_DEFINED
#define SLOP_OPTION_TYPES_DIAGNOSTIC_DEFINED
SLOP_OPTION_DEFINE(types_Diagnostic, slop_option_types_Diagnostic)
#endif

#ifndef SLOP_OPTION_TYPES_PARAMINFO_DEFINED
#define SLOP_OPTION_TYPES_PARAMINFO_DEFINED
SLOP_OPTION_DEFINE(types_ParamInfo, slop_option_types_ParamInfo)
#endif

#ifndef SLOP_OPTION_TYPES_RANGEBOUNDS_DEFINED
#define SLOP_OPTION_TYPES_RANGEBOUNDS_DEFINED
SLOP_OPTION_DEFINE(types_RangeBounds, slop_option_types_RangeBounds)
#endif

struct type_env_VarBinding {
    slop_string name;
    types_ResolvedType* var_type;
    uint8_t mutable;
    types_BindingOrigin origin;
};
typedef struct type_env_VarBinding type_env_VarBinding;

#ifndef SLOP_OPTION_TYPE_ENV_VARBINDING_DEFINED
#define SLOP_OPTION_TYPE_ENV_VARBINDING_DEFINED
SLOP_OPTION_DEFINE(type_env_VarBinding, slop_option_type_env_VarBinding)
#endif

#ifndef SLOP_LIST_TYPE_ENV_VARBINDING_DEFINED
#define SLOP_LIST_TYPE_ENV_VARBINDING_DEFINED
#define SLOP_LIST_TYPE_ENV_VARBINDING_IMPL_DEFINED
SLOP_LIST_DEFINE(type_env_VarBinding, slop_list_type_env_VarBinding)
#endif

struct type_env_ConstBinding {
    slop_string name;
    types_ResolvedType* const_type;
    slop_option_string module_name;
};
typedef struct type_env_ConstBinding type_env_ConstBinding;

#ifndef SLOP_OPTION_TYPE_ENV_CONSTBINDING_DEFINED
#define SLOP_OPTION_TYPE_ENV_CONSTBINDING_DEFINED
SLOP_OPTION_DEFINE(type_env_ConstBinding, slop_option_type_env_ConstBinding)
#endif

#ifndef SLOP_LIST_TYPE_ENV_CONSTBINDING_DEFINED
#define SLOP_LIST_TYPE_ENV_CONSTBINDING_DEFINED
#define SLOP_LIST_TYPE_ENV_CONSTBINDING_IMPL_DEFINED
SLOP_LIST_DEFINE(type_env_ConstBinding, slop_list_type_env_ConstBinding)
#endif

struct type_env_ImportEntry {
    slop_string local;
    slop_string qualified;
};
typedef struct type_env_ImportEntry type_env_ImportEntry;

#ifndef SLOP_OPTION_TYPE_ENV_IMPORTENTRY_DEFINED
#define SLOP_OPTION_TYPE_ENV_IMPORTENTRY_DEFINED
SLOP_OPTION_DEFINE(type_env_ImportEntry, slop_option_type_env_ImportEntry)
#endif

#ifndef SLOP_LIST_TYPE_ENV_IMPORTENTRY_DEFINED
#define SLOP_LIST_TYPE_ENV_IMPORTENTRY_DEFINED
#define SLOP_LIST_TYPE_ENV_IMPORTENTRY_IMPL_DEFINED
SLOP_LIST_DEFINE(type_env_ImportEntry, slop_list_type_env_ImportEntry)
#endif

struct type_env_ModuleImport {
    slop_string module;
    slop_string local;
    slop_string qualified;
};
typedef struct type_env_ModuleImport type_env_ModuleImport;

#ifndef SLOP_OPTION_TYPE_ENV_MODULEIMPORT_DEFINED
#define SLOP_OPTION_TYPE_ENV_MODULEIMPORT_DEFINED
SLOP_OPTION_DEFINE(type_env_ModuleImport, slop_option_type_env_ModuleImport)
#endif

#ifndef SLOP_LIST_TYPE_ENV_MODULEIMPORT_DEFINED
#define SLOP_LIST_TYPE_ENV_MODULEIMPORT_DEFINED
#define SLOP_LIST_TYPE_ENV_MODULEIMPORT_IMPL_DEFINED
SLOP_LIST_DEFINE(type_env_ModuleImport, slop_list_type_env_ModuleImport)
#endif

struct type_env_CheckerScope {
    slop_list_type_env_VarBinding bindings;
};
typedef struct type_env_CheckerScope type_env_CheckerScope;

#ifndef SLOP_OPTION_TYPE_ENV_CHECKERSCOPE_DEFINED
#define SLOP_OPTION_TYPE_ENV_CHECKERSCOPE_DEFINED
SLOP_OPTION_DEFINE(type_env_CheckerScope, slop_option_type_env_CheckerScope)
#endif

struct type_env_VariantMapping {
    slop_string variant_name;
    slop_string enum_name;
    types_ResolvedType* enum_type;
    slop_option_string module_name;
};
typedef struct type_env_VariantMapping type_env_VariantMapping;

#ifndef SLOP_OPTION_TYPE_ENV_VARIANTMAPPING_DEFINED
#define SLOP_OPTION_TYPE_ENV_VARIANTMAPPING_DEFINED
SLOP_OPTION_DEFINE(type_env_VariantMapping, slop_option_type_env_VariantMapping)
#endif

#ifndef SLOP_LIST_TYPE_ENV_VARIANTMAPPING_DEFINED
#define SLOP_LIST_TYPE_ENV_VARIANTMAPPING_DEFINED
#define SLOP_LIST_TYPE_ENV_VARIANTMAPPING_IMPL_DEFINED
SLOP_LIST_DEFINE(type_env_VariantMapping, slop_list_type_env_VariantMapping)
#endif

struct type_env_BindingAnnotation {
    slop_string name;
    int64_t line;
    int64_t col;
    slop_string slop_type;
};
typedef struct type_env_BindingAnnotation type_env_BindingAnnotation;

#ifndef SLOP_OPTION_TYPE_ENV_BINDINGANNOTATION_DEFINED
#define SLOP_OPTION_TYPE_ENV_BINDINGANNOTATION_DEFINED
SLOP_OPTION_DEFINE(type_env_BindingAnnotation, slop_option_type_env_BindingAnnotation)
#endif

#ifndef SLOP_LIST_TYPE_ENV_BINDINGANNOTATION_DEFINED
#define SLOP_LIST_TYPE_ENV_BINDINGANNOTATION_DEFINED
#define SLOP_LIST_TYPE_ENV_BINDINGANNOTATION_IMPL_DEFINED
SLOP_LIST_DEFINE(type_env_BindingAnnotation, slop_list_type_env_BindingAnnotation)
#endif

struct type_env_TypeEnv {
    slop_arena* arena;
    slop_list_types_ResolvedType_ptr types;
    slop_list_types_FnSignature_ptr functions;
    slop_list_type_env_ConstBinding constants;
    slop_list_type_env_ImportEntry imports;
    slop_list_type_env_VariantMapping enum_variants;
    slop_list_type_env_CheckerScope_ptr scopes;
    slop_option_string current_module;
    types_ResolvedType* int_type;
    types_ResolvedType* bool_type;
    types_ResolvedType* string_type;
    types_ResolvedType* float_type;
    types_ResolvedType* null_type;
    types_ResolvedType* unit_type;
    types_ResolvedType* arena_type;
    types_ResolvedType* unknown_type;
    slop_list_types_Diagnostic diagnostics;
    slop_list_type_env_BindingAnnotation binding_annotations;
    slop_option_string current_file;
    slop_list_string loaded_modules;
    types_ResolvedType* never_type;
    slop_list_string fn_type_params;
    slop_list_type_env_ModuleImport module_imports;
    slop_option_types_ResolvedType_ptr current_return;
};
typedef struct type_env_TypeEnv type_env_TypeEnv;

#ifndef SLOP_OPTION_TYPE_ENV_TYPEENV_DEFINED
#define SLOP_OPTION_TYPE_ENV_TYPEENV_DEFINED
SLOP_OPTION_DEFINE(type_env_TypeEnv, slop_option_type_env_TypeEnv)
#endif

type_env_TypeEnv* type_env_env_new(slop_arena* arena);
void type_env_env_register_builtin_fn(type_env_TypeEnv* env, slop_arena* arena, slop_string name, slop_string c_name, slop_list_types_ParamInfo params, types_ResolvedType* ret_type);
void type_env_register_builtin_functions(type_env_TypeEnv* env, slop_arena* arena, types_ResolvedType* int_t, types_ResolvedType* bool_t, types_ResolvedType* string_t, types_ResolvedType* arena_t, types_ResolvedType* u8_t, types_ResolvedType* unit_t);
slop_arena* type_env_env_arena(type_env_TypeEnv* env);
void type_env_env_push_scope(type_env_TypeEnv* env);
void type_env_env_pop_scope(type_env_TypeEnv* env);
void type_env_env_bind_var(type_env_TypeEnv* env, slop_string name, types_ResolvedType* var_type);
void type_env_env_bind_var_as(type_env_TypeEnv* env, slop_string name, types_ResolvedType* var_type, uint8_t mutable, types_BindingOrigin origin);
slop_option_type_env_VarBinding type_env_scope_lookup_binding(type_env_CheckerScope* scope_ptr, slop_string name);
slop_option_type_env_VarBinding type_env_env_lookup_binding(type_env_TypeEnv* env, slop_string name);
slop_option_types_ResolvedType_ptr type_env_scope_lookup_var(type_env_CheckerScope* scope_ptr, slop_string name);
slop_option_types_ResolvedType_ptr type_env_env_lookup_var(type_env_TypeEnv* env, slop_string name);
void type_env_env_register_constant(type_env_TypeEnv* env, slop_string name, types_ResolvedType* const_type);
uint8_t type_env_env_constant_matches_module(type_env_ConstBinding binding, slop_string mod_name);
uint8_t type_env_env_constant_is_builtin(type_env_ConstBinding binding);
uint8_t type_env_env_lookup_constant_in_module(type_env_TypeEnv* env, slop_string mod_name, slop_string const_name);
slop_option_types_ResolvedType_ptr type_env_env_lookup_constant(type_env_TypeEnv* env, slop_string name);
void type_env_env_register_type(type_env_TypeEnv* env, types_ResolvedType* t);
slop_option_types_ResolvedType_ptr type_env_env_lookup_type_direct(type_env_TypeEnv* env, slop_string name);
int64_t type_env_find_colon_pos(slop_string name);
slop_option_types_ResolvedType_ptr type_env_lookup_type_by_qualified_name(type_env_TypeEnv* env, slop_string qualified_name);
slop_option_types_ResolvedType_ptr type_env_env_lookup_type(type_env_TypeEnv* env, slop_string name);
slop_option_types_ResolvedType_ptr type_env_env_lookup_type_qualified(type_env_TypeEnv* env, slop_string module_name, slop_string type_name);
slop_option_types_ResolvedType_ptr type_env_env_lookup_own_type(type_env_TypeEnv* env, slop_string name);
slop_option_types_ResolvedType_ptr type_env_env_lookup_type_builtin(type_env_TypeEnv* env, slop_string name);
slop_option_types_ResolvedType_ptr type_env_env_lookup_type_elsewhere(type_env_TypeEnv* env, slop_string name);
uint8_t type_env_env_is_function_visible(type_env_TypeEnv* env, types_FnSignature* sig);
void type_env_env_register_function(type_env_TypeEnv* env, types_FnSignature* sig);
slop_option_types_FnSignature_ptr type_env_env_lookup_function_direct(type_env_TypeEnv* env, slop_string name);
slop_option_types_FnSignature_ptr type_env_env_lookup_function(type_env_TypeEnv* env, slop_string name);
void type_env_env_add_import(type_env_TypeEnv* env, slop_string local_name, slop_string qualified_name);
slop_option_string type_env_env_resolve_import(type_env_TypeEnv* env, slop_string local_name);
slop_option_string type_env_env_lookup_module_import(type_env_TypeEnv* env, slop_string mod_name, slop_string local_name);
void type_env_env_clear_imports(type_env_TypeEnv* env);
void type_env_env_register_variant(type_env_TypeEnv* env, slop_string variant_name, types_ResolvedType* enum_type);
uint8_t type_env_env_imports_variant_type(type_env_TypeEnv* env, type_env_VariantMapping v, slop_string vmod);
slop_option_types_ResolvedType_ptr type_env_env_lookup_variant(type_env_TypeEnv* env, slop_string variant_name, int64_t line, int64_t col);
void type_env_env_check_variant_collisions(type_env_TypeEnv* env);
uint8_t type_env_env_same_module_opt(slop_option_string a, slop_option_string b);
void type_env_env_set_module(type_env_TypeEnv* env, slop_option_string module_name);
slop_option_string type_env_env_get_module(type_env_TypeEnv* env);
types_ResolvedType* type_env_env_get_int_type(type_env_TypeEnv* env);
types_ResolvedType* type_env_env_get_bool_type(type_env_TypeEnv* env);
types_ResolvedType* type_env_env_get_string_type(type_env_TypeEnv* env);
types_ResolvedType* type_env_env_get_null_type(type_env_TypeEnv* env);
types_ResolvedType* type_env_env_get_float_type(type_env_TypeEnv* env);
types_ResolvedType* type_env_env_get_unit_type(type_env_TypeEnv* env);
types_ResolvedType* type_env_env_get_arena_type(type_env_TypeEnv* env);
types_ResolvedType* type_env_env_get_unknown_type(type_env_TypeEnv* env);
types_ResolvedType* type_env_env_get_never_type(type_env_TypeEnv* env);
types_ResolvedType* type_env_env_make_option_type(type_env_TypeEnv* env, types_ResolvedType* inner_type);
types_ResolvedType* type_env_env_make_ptr_type(type_env_TypeEnv* env, types_ResolvedType* inner_type);
types_ResolvedType* type_env_env_get_generic_type(type_env_TypeEnv* env);
types_ResolvedType* type_env_env_make_result_type(type_env_TypeEnv* env);
types_ResolvedType* type_env_env_make_fn_type(type_env_TypeEnv* env, types_FnSignature* sig);
void type_env_env_add_warning(type_env_TypeEnv* env, slop_string message, int64_t line, int64_t col);
void type_env_env_add_error(type_env_TypeEnv* env, slop_string message, int64_t line, int64_t col);
slop_option_types_RangeBounds type_env_env_type_range(types_ResolvedType* t);
slop_string type_env_env_range_label(type_env_TypeEnv* env, types_ResolvedType* t, types_RangeBounds bounds);
void type_env_env_check_range_narrowing(type_env_TypeEnv* env, slop_string context, types_ResolvedType* target, types_ResolvedType* value, int64_t line, int64_t col);
void type_env_env_set_current_return(type_env_TypeEnv* env, slop_option_types_ResolvedType_ptr ret);
slop_option_types_ResolvedType_ptr type_env_env_get_current_return(type_env_TypeEnv* env);
slop_list_types_Diagnostic type_env_env_get_diagnostics(type_env_TypeEnv* env);
void type_env_env_clear_diagnostics(type_env_TypeEnv* env);
void type_env_env_record_binding(type_env_TypeEnv* env, slop_string name, int64_t line, int64_t col, slop_string slop_type);
slop_list_type_env_BindingAnnotation type_env_env_get_binding_annotations(type_env_TypeEnv* env);
void type_env_env_set_current_file(type_env_TypeEnv* env, slop_option_string file_path);
slop_option_string type_env_env_get_current_file(type_env_TypeEnv* env);
void type_env_env_add_loaded_module(type_env_TypeEnv* env, slop_string module_path);
uint8_t type_env_env_is_module_loaded(type_env_TypeEnv* env, slop_string module_path);
void type_env_env_set_fn_type_params(type_env_TypeEnv* env, slop_list_string params);
slop_list_string type_env_env_get_fn_type_params(type_env_TypeEnv* env);
void type_env_env_clear_fn_type_params(type_env_TypeEnv* env);
uint8_t type_env_env_is_type_param(type_env_TypeEnv* env, slop_string name);

#ifndef SLOP_OPTION_TYPE_ENV_VARBINDING_DEFINED
#define SLOP_OPTION_TYPE_ENV_VARBINDING_DEFINED
SLOP_OPTION_DEFINE(type_env_VarBinding, slop_option_type_env_VarBinding)
#endif

#ifndef SLOP_OPTION_TYPE_ENV_CONSTBINDING_DEFINED
#define SLOP_OPTION_TYPE_ENV_CONSTBINDING_DEFINED
SLOP_OPTION_DEFINE(type_env_ConstBinding, slop_option_type_env_ConstBinding)
#endif

#ifndef SLOP_OPTION_TYPE_ENV_IMPORTENTRY_DEFINED
#define SLOP_OPTION_TYPE_ENV_IMPORTENTRY_DEFINED
SLOP_OPTION_DEFINE(type_env_ImportEntry, slop_option_type_env_ImportEntry)
#endif

#ifndef SLOP_OPTION_TYPE_ENV_MODULEIMPORT_DEFINED
#define SLOP_OPTION_TYPE_ENV_MODULEIMPORT_DEFINED
SLOP_OPTION_DEFINE(type_env_ModuleImport, slop_option_type_env_ModuleImport)
#endif

#ifndef SLOP_OPTION_TYPE_ENV_CHECKERSCOPE_DEFINED
#define SLOP_OPTION_TYPE_ENV_CHECKERSCOPE_DEFINED
SLOP_OPTION_DEFINE(type_env_CheckerScope, slop_option_type_env_CheckerScope)
#endif

#ifndef SLOP_OPTION_TYPE_ENV_VARIANTMAPPING_DEFINED
#define SLOP_OPTION_TYPE_ENV_VARIANTMAPPING_DEFINED
SLOP_OPTION_DEFINE(type_env_VariantMapping, slop_option_type_env_VariantMapping)
#endif

#ifndef SLOP_OPTION_TYPE_ENV_BINDINGANNOTATION_DEFINED
#define SLOP_OPTION_TYPE_ENV_BINDINGANNOTATION_DEFINED
SLOP_OPTION_DEFINE(type_env_BindingAnnotation, slop_option_type_env_BindingAnnotation)
#endif

#ifndef SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
#define SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
SLOP_OPTION_DEFINE(types_ResolvedType*, slop_option_types_ResolvedType_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_FNSIGNATURE_PTR_DEFINED
#define SLOP_OPTION_TYPES_FNSIGNATURE_PTR_DEFINED
SLOP_OPTION_DEFINE(types_FnSignature*, slop_option_types_FnSignature_ptr)
#endif

#ifndef SLOP_OPTION_TYPE_ENV_CHECKERSCOPE_PTR_DEFINED
#define SLOP_OPTION_TYPE_ENV_CHECKERSCOPE_PTR_DEFINED
SLOP_OPTION_DEFINE(type_env_CheckerScope*, slop_option_type_env_CheckerScope_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_DIAGNOSTIC_DEFINED
#define SLOP_OPTION_TYPES_DIAGNOSTIC_DEFINED
SLOP_OPTION_DEFINE(types_Diagnostic, slop_option_types_Diagnostic)
#endif

#ifndef SLOP_OPTION_TYPE_ENV_TYPEENV_DEFINED
#define SLOP_OPTION_TYPE_ENV_TYPEENV_DEFINED
SLOP_OPTION_DEFINE(type_env_TypeEnv, slop_option_type_env_TypeEnv)
#endif

#ifndef SLOP_OPTION_TYPES_PARAMINFO_DEFINED
#define SLOP_OPTION_TYPES_PARAMINFO_DEFINED
SLOP_OPTION_DEFINE(types_ParamInfo, slop_option_types_ParamInfo)
#endif

#ifndef SLOP_OPTION_TYPES_RANGEBOUNDS_DEFINED
#define SLOP_OPTION_TYPES_RANGEBOUNDS_DEFINED
SLOP_OPTION_DEFINE(types_RangeBounds, slop_option_types_RangeBounds)
#endif


#endif
