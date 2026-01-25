#ifndef SLOP_env_H
#define SLOP_env_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_types.h"

typedef struct env_VarBinding env_VarBinding;
typedef struct env_ConstBinding env_ConstBinding;
typedef struct env_ImportEntry env_ImportEntry;
typedef struct env_Scope env_Scope;
typedef struct env_VariantMapping env_VariantMapping;
typedef struct env_BindingAnnotation env_BindingAnnotation;
typedef struct env_TypeEnv env_TypeEnv;

#ifndef SLOP_LIST_TYPES_RESOLVEDTYPE_PTR_DEFINED
#define SLOP_LIST_TYPES_RESOLVEDTYPE_PTR_DEFINED
SLOP_LIST_DEFINE(types_ResolvedType*, slop_list_types_ResolvedType_ptr)
#endif

#ifndef SLOP_LIST_TYPES_FNSIGNATURE_PTR_DEFINED
#define SLOP_LIST_TYPES_FNSIGNATURE_PTR_DEFINED
SLOP_LIST_DEFINE(types_FnSignature*, slop_list_types_FnSignature_ptr)
#endif

#ifndef SLOP_LIST_ENV_SCOPE_PTR_DEFINED
#define SLOP_LIST_ENV_SCOPE_PTR_DEFINED
SLOP_LIST_DEFINE(env_Scope*, slop_list_env_Scope_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
#define SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
SLOP_OPTION_DEFINE(types_ResolvedType*, slop_option_types_ResolvedType_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_FNSIGNATURE_PTR_DEFINED
#define SLOP_OPTION_TYPES_FNSIGNATURE_PTR_DEFINED
SLOP_OPTION_DEFINE(types_FnSignature*, slop_option_types_FnSignature_ptr)
#endif

#ifndef SLOP_OPTION_ENV_SCOPE_PTR_DEFINED
#define SLOP_OPTION_ENV_SCOPE_PTR_DEFINED
SLOP_OPTION_DEFINE(env_Scope*, slop_option_env_Scope_ptr)
#endif

#ifndef SLOP_LIST_TYPES_DIAGNOSTIC_DEFINED
#define SLOP_LIST_TYPES_DIAGNOSTIC_DEFINED
SLOP_LIST_DEFINE(types_Diagnostic, slop_list_types_Diagnostic)
#endif

#ifndef SLOP_OPTION_TYPES_DIAGNOSTIC_DEFINED
#define SLOP_OPTION_TYPES_DIAGNOSTIC_DEFINED
SLOP_OPTION_DEFINE(types_Diagnostic, slop_option_types_Diagnostic)
#endif

#ifndef SLOP_LIST_TYPES_DIAGNOSTIC_DEFINED
#define SLOP_LIST_TYPES_DIAGNOSTIC_DEFINED
SLOP_LIST_DEFINE(types_Diagnostic, slop_list_types_Diagnostic)
#endif

struct env_VarBinding {
    slop_string name;
    types_ResolvedType* var_type;
};
typedef struct env_VarBinding env_VarBinding;

#ifndef SLOP_OPTION_ENV_VARBINDING_DEFINED
#define SLOP_OPTION_ENV_VARBINDING_DEFINED
SLOP_OPTION_DEFINE(env_VarBinding, slop_option_env_VarBinding)
#endif

#ifndef SLOP_LIST_ENV_VARBINDING_DEFINED
#define SLOP_LIST_ENV_VARBINDING_DEFINED
SLOP_LIST_DEFINE(env_VarBinding, slop_list_env_VarBinding)
#endif

struct env_ConstBinding {
    slop_string name;
    types_ResolvedType* const_type;
};
typedef struct env_ConstBinding env_ConstBinding;

#ifndef SLOP_OPTION_ENV_CONSTBINDING_DEFINED
#define SLOP_OPTION_ENV_CONSTBINDING_DEFINED
SLOP_OPTION_DEFINE(env_ConstBinding, slop_option_env_ConstBinding)
#endif

#ifndef SLOP_LIST_ENV_CONSTBINDING_DEFINED
#define SLOP_LIST_ENV_CONSTBINDING_DEFINED
SLOP_LIST_DEFINE(env_ConstBinding, slop_list_env_ConstBinding)
#endif

struct env_ImportEntry {
    slop_string local;
    slop_string qualified;
};
typedef struct env_ImportEntry env_ImportEntry;

#ifndef SLOP_OPTION_ENV_IMPORTENTRY_DEFINED
#define SLOP_OPTION_ENV_IMPORTENTRY_DEFINED
SLOP_OPTION_DEFINE(env_ImportEntry, slop_option_env_ImportEntry)
#endif

#ifndef SLOP_LIST_ENV_IMPORTENTRY_DEFINED
#define SLOP_LIST_ENV_IMPORTENTRY_DEFINED
SLOP_LIST_DEFINE(env_ImportEntry, slop_list_env_ImportEntry)
#endif

struct env_Scope {
    slop_list_env_VarBinding bindings;
};
typedef struct env_Scope env_Scope;

#ifndef SLOP_OPTION_ENV_SCOPE_DEFINED
#define SLOP_OPTION_ENV_SCOPE_DEFINED
SLOP_OPTION_DEFINE(env_Scope, slop_option_env_Scope)
#endif

struct env_VariantMapping {
    slop_string variant_name;
    slop_string enum_name;
};
typedef struct env_VariantMapping env_VariantMapping;

#ifndef SLOP_OPTION_ENV_VARIANTMAPPING_DEFINED
#define SLOP_OPTION_ENV_VARIANTMAPPING_DEFINED
SLOP_OPTION_DEFINE(env_VariantMapping, slop_option_env_VariantMapping)
#endif

#ifndef SLOP_LIST_ENV_VARIANTMAPPING_DEFINED
#define SLOP_LIST_ENV_VARIANTMAPPING_DEFINED
SLOP_LIST_DEFINE(env_VariantMapping, slop_list_env_VariantMapping)
#endif

struct env_BindingAnnotation {
    slop_string name;
    int64_t line;
    int64_t col;
    slop_string slop_type;
};
typedef struct env_BindingAnnotation env_BindingAnnotation;

#ifndef SLOP_OPTION_ENV_BINDINGANNOTATION_DEFINED
#define SLOP_OPTION_ENV_BINDINGANNOTATION_DEFINED
SLOP_OPTION_DEFINE(env_BindingAnnotation, slop_option_env_BindingAnnotation)
#endif

#ifndef SLOP_LIST_ENV_BINDINGANNOTATION_DEFINED
#define SLOP_LIST_ENV_BINDINGANNOTATION_DEFINED
SLOP_LIST_DEFINE(env_BindingAnnotation, slop_list_env_BindingAnnotation)
#endif

struct env_TypeEnv {
    slop_arena* arena;
    slop_list_types_ResolvedType_ptr types;
    slop_list_types_FnSignature_ptr functions;
    slop_list_env_ConstBinding constants;
    slop_list_env_ImportEntry imports;
    slop_list_env_VariantMapping enum_variants;
    slop_list_env_Scope_ptr scopes;
    slop_option_string current_module;
    types_ResolvedType* int_type;
    types_ResolvedType* bool_type;
    types_ResolvedType* string_type;
    types_ResolvedType* unit_type;
    types_ResolvedType* arena_type;
    types_ResolvedType* unknown_type;
    slop_list_types_Diagnostic diagnostics;
    slop_list_env_BindingAnnotation binding_annotations;
    slop_option_string current_file;
    slop_list_string loaded_modules;
};
typedef struct env_TypeEnv env_TypeEnv;

#ifndef SLOP_OPTION_ENV_TYPEENV_DEFINED
#define SLOP_OPTION_ENV_TYPEENV_DEFINED
SLOP_OPTION_DEFINE(env_TypeEnv, slop_option_env_TypeEnv)
#endif

env_TypeEnv* env_env_new(slop_arena* arena);
slop_arena* env_env_arena(env_TypeEnv* env);
void env_env_push_scope(env_TypeEnv* env);
void env_env_pop_scope(env_TypeEnv* env);
void env_env_bind_var(env_TypeEnv* env, slop_string name, types_ResolvedType* var_type);
slop_option_types_ResolvedType_ptr env_scope_lookup_var(env_Scope* scope_ptr, slop_string name);
slop_option_types_ResolvedType_ptr env_env_lookup_var(env_TypeEnv* env, slop_string name);
void env_env_register_constant(env_TypeEnv* env, slop_string name, types_ResolvedType* const_type);
slop_option_types_ResolvedType_ptr env_env_lookup_constant(env_TypeEnv* env, slop_string name);
void env_env_register_type(env_TypeEnv* env, types_ResolvedType* t);
slop_option_types_ResolvedType_ptr env_env_lookup_type_direct(env_TypeEnv* env, slop_string name);
slop_option_types_ResolvedType_ptr env_env_lookup_type(env_TypeEnv* env, slop_string name);
slop_option_types_ResolvedType_ptr env_env_lookup_type_qualified(env_TypeEnv* env, slop_string module_name, slop_string type_name);
void env_env_register_function(env_TypeEnv* env, types_FnSignature* sig);
slop_option_types_FnSignature_ptr env_env_lookup_function_direct(env_TypeEnv* env, slop_string name);
slop_option_types_FnSignature_ptr env_env_lookup_function(env_TypeEnv* env, slop_string name);
void env_env_add_import(env_TypeEnv* env, slop_string local_name, slop_string qualified_name);
slop_option_string env_env_resolve_import(env_TypeEnv* env, slop_string local_name);
void env_env_register_variant(env_TypeEnv* env, slop_string variant_name, slop_string enum_name);
slop_option_string env_env_lookup_variant(env_TypeEnv* env, slop_string variant_name);
void env_env_check_variant_collisions(env_TypeEnv* env);
void env_env_set_module(env_TypeEnv* env, slop_option_string module_name);
slop_option_string env_env_get_module(env_TypeEnv* env);
types_ResolvedType* env_env_get_int_type(env_TypeEnv* env);
types_ResolvedType* env_env_get_bool_type(env_TypeEnv* env);
types_ResolvedType* env_env_get_string_type(env_TypeEnv* env);
types_ResolvedType* env_env_get_unit_type(env_TypeEnv* env);
types_ResolvedType* env_env_get_arena_type(env_TypeEnv* env);
types_ResolvedType* env_env_get_unknown_type(env_TypeEnv* env);
types_ResolvedType* env_env_make_option_type(env_TypeEnv* env, types_ResolvedType* inner_type);
types_ResolvedType* env_env_make_ptr_type(env_TypeEnv* env, types_ResolvedType* inner_type);
types_ResolvedType* env_env_get_generic_type(env_TypeEnv* env);
types_ResolvedType* env_env_make_result_type(env_TypeEnv* env);
types_ResolvedType* env_env_make_fn_type(env_TypeEnv* env, types_FnSignature* sig);
void env_env_add_warning(env_TypeEnv* env, slop_string message, int64_t line, int64_t col);
void env_env_add_error(env_TypeEnv* env, slop_string message, int64_t line, int64_t col);
slop_list_types_Diagnostic env_env_get_diagnostics(env_TypeEnv* env);
void env_env_clear_diagnostics(env_TypeEnv* env);
void env_env_record_binding(env_TypeEnv* env, slop_string name, int64_t line, int64_t col, slop_string slop_type);
slop_list_env_BindingAnnotation env_env_get_binding_annotations(env_TypeEnv* env);
void env_env_set_current_file(env_TypeEnv* env, slop_option_string file_path);
slop_option_string env_env_get_current_file(env_TypeEnv* env);
void env_env_add_loaded_module(env_TypeEnv* env, slop_string module_path);
uint8_t env_env_is_module_loaded(env_TypeEnv* env, slop_string module_path);

#ifndef SLOP_OPTION_ENV_VARBINDING_DEFINED
#define SLOP_OPTION_ENV_VARBINDING_DEFINED
SLOP_OPTION_DEFINE(env_VarBinding, slop_option_env_VarBinding)
#endif

#ifndef SLOP_OPTION_ENV_CONSTBINDING_DEFINED
#define SLOP_OPTION_ENV_CONSTBINDING_DEFINED
SLOP_OPTION_DEFINE(env_ConstBinding, slop_option_env_ConstBinding)
#endif

#ifndef SLOP_OPTION_ENV_IMPORTENTRY_DEFINED
#define SLOP_OPTION_ENV_IMPORTENTRY_DEFINED
SLOP_OPTION_DEFINE(env_ImportEntry, slop_option_env_ImportEntry)
#endif

#ifndef SLOP_OPTION_ENV_SCOPE_DEFINED
#define SLOP_OPTION_ENV_SCOPE_DEFINED
SLOP_OPTION_DEFINE(env_Scope, slop_option_env_Scope)
#endif

#ifndef SLOP_OPTION_ENV_VARIANTMAPPING_DEFINED
#define SLOP_OPTION_ENV_VARIANTMAPPING_DEFINED
SLOP_OPTION_DEFINE(env_VariantMapping, slop_option_env_VariantMapping)
#endif

#ifndef SLOP_OPTION_ENV_BINDINGANNOTATION_DEFINED
#define SLOP_OPTION_ENV_BINDINGANNOTATION_DEFINED
SLOP_OPTION_DEFINE(env_BindingAnnotation, slop_option_env_BindingAnnotation)
#endif

#ifndef SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
#define SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
SLOP_OPTION_DEFINE(types_ResolvedType*, slop_option_types_ResolvedType_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_FNSIGNATURE_PTR_DEFINED
#define SLOP_OPTION_TYPES_FNSIGNATURE_PTR_DEFINED
SLOP_OPTION_DEFINE(types_FnSignature*, slop_option_types_FnSignature_ptr)
#endif

#ifndef SLOP_OPTION_ENV_SCOPE_PTR_DEFINED
#define SLOP_OPTION_ENV_SCOPE_PTR_DEFINED
SLOP_OPTION_DEFINE(env_Scope*, slop_option_env_Scope_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_DIAGNOSTIC_DEFINED
#define SLOP_OPTION_TYPES_DIAGNOSTIC_DEFINED
SLOP_OPTION_DEFINE(types_Diagnostic, slop_option_types_Diagnostic)
#endif

#ifndef SLOP_OPTION_ENV_TYPEENV_DEFINED
#define SLOP_OPTION_ENV_TYPEENV_DEFINED
SLOP_OPTION_DEFINE(env_TypeEnv, slop_option_env_TypeEnv)
#endif


#endif
