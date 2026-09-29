#ifndef SLOP_context_H
#define SLOP_context_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_types.h"
#include "slop_ctype.h"
#include "slop_strlib.h"
#include <stdio.h>
#include <stdlib.h>
#include <slop_runtime.h>

typedef struct context_TranspileError context_TranspileError;
typedef struct context_VarEntry context_VarEntry;
typedef struct context_TypeEntry context_TypeEntry;
typedef struct context_FuncParamType context_FuncParamType;
typedef struct context_FuncEntry context_FuncEntry;
typedef struct context_FieldEntry context_FieldEntry;
typedef struct context_Scope context_Scope;
typedef struct context_EnumVariant context_EnumVariant;
typedef struct context_UnionVariantEntry context_UnionVariantEntry;
typedef struct context_ResultType context_ResultType;
typedef struct context_OptionType context_OptionType;
typedef struct context_ListType context_ListType;
typedef struct context_ChanType context_ChanType;
typedef struct context_ThreadType context_ThreadType;
typedef struct context_ResultTypeAlias context_ResultTypeAlias;
typedef struct context_FuncCNameAlias context_FuncCNameAlias;
typedef struct context_ValueKeyType context_ValueKeyType;
typedef struct context_TypeAliasEntry context_TypeAliasEntry;
typedef struct context_InlineRecord context_InlineRecord;
typedef struct context_GenericFuncInstantiation context_GenericFuncInstantiation;
typedef struct context_TranspileContext context_TranspileContext;
typedef struct context_TypeLookup context_TypeLookup;
typedef struct context_VariantLookup context_VariantLookup;
typedef struct context_LastLambdaInfo context_LastLambdaInfo;

typedef enum {
    context_VariantScope_scope_own,
    context_VariantScope_scope_imported,
    context_VariantScope_scope_builtin
} context_VariantScope;

#ifndef SLOP_LIST_CONTEXT_FUNCPARAMTYPE_PTR_DEFINED
#define SLOP_LIST_CONTEXT_FUNCPARAMTYPE_PTR_DEFINED
#define SLOP_LIST_CONTEXT_FUNCPARAMTYPE_PTR_IMPL_DEFINED
SLOP_LIST_DEFINE(context_FuncParamType*, slop_list_context_FuncParamType_ptr)
#endif

#ifndef SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_IMPL_DEFINED
SLOP_LIST_DEFINE(types_SExpr*, slop_list_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_CONTEXT_FUNCPARAMTYPE_PTR_DEFINED
#define SLOP_OPTION_CONTEXT_FUNCPARAMTYPE_PTR_DEFINED
SLOP_OPTION_DEFINE(context_FuncParamType*, slop_option_context_FuncParamType_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_CONTEXT_SCOPE_PTR_DEFINED
#define SLOP_OPTION_CONTEXT_SCOPE_PTR_DEFINED
SLOP_OPTION_DEFINE(context_Scope*, slop_option_context_Scope_ptr)
#endif

struct context_TranspileError {
    slop_string message;
    int64_t line;
    int64_t col;
};
typedef struct context_TranspileError context_TranspileError;

#ifndef SLOP_OPTION_CONTEXT_TRANSPILEERROR_DEFINED
#define SLOP_OPTION_CONTEXT_TRANSPILEERROR_DEFINED
SLOP_OPTION_DEFINE(context_TranspileError, slop_option_context_TranspileError)
#endif

#ifndef SLOP_LIST_CONTEXT_TRANSPILEERROR_DEFINED
#define SLOP_LIST_CONTEXT_TRANSPILEERROR_DEFINED
#define SLOP_LIST_CONTEXT_TRANSPILEERROR_IMPL_DEFINED
SLOP_LIST_DEFINE(context_TranspileError, slop_list_context_TranspileError)
#endif

struct context_VarEntry {
    slop_string name;
    slop_string c_name;
    slop_string c_type;
    slop_string slop_type;
    uint8_t is_pointer;
    uint8_t is_mutable;
    uint8_t is_closure;
    slop_string closure_env_type;
    slop_string closure_lambda_name;
    types_BindingOrigin origin;
};
typedef struct context_VarEntry context_VarEntry;

#ifndef SLOP_OPTION_CONTEXT_VARENTRY_DEFINED
#define SLOP_OPTION_CONTEXT_VARENTRY_DEFINED
SLOP_OPTION_DEFINE(context_VarEntry, slop_option_context_VarEntry)
#endif

#ifndef SLOP_LIST_CONTEXT_VARENTRY_DEFINED
#define SLOP_LIST_CONTEXT_VARENTRY_DEFINED
#define SLOP_LIST_CONTEXT_VARENTRY_IMPL_DEFINED
SLOP_LIST_DEFINE(context_VarEntry, slop_list_context_VarEntry)
#endif

struct context_TypeEntry {
    slop_string name;
    slop_string c_name;
    slop_string c_type;
    uint8_t is_enum;
    uint8_t is_record;
    uint8_t is_union;
    slop_string owner_module;
    slop_string imported_from;
};
typedef struct context_TypeEntry context_TypeEntry;

#ifndef SLOP_OPTION_CONTEXT_TYPEENTRY_DEFINED
#define SLOP_OPTION_CONTEXT_TYPEENTRY_DEFINED
SLOP_OPTION_DEFINE(context_TypeEntry, slop_option_context_TypeEntry)
#endif

#ifndef SLOP_LIST_CONTEXT_TYPEENTRY_DEFINED
#define SLOP_LIST_CONTEXT_TYPEENTRY_DEFINED
#define SLOP_LIST_CONTEXT_TYPEENTRY_IMPL_DEFINED
SLOP_LIST_DEFINE(context_TypeEntry, slop_list_context_TypeEntry)
#endif

struct context_FuncParamType {
    slop_string c_type;
};
typedef struct context_FuncParamType context_FuncParamType;

#ifndef SLOP_OPTION_CONTEXT_FUNCPARAMTYPE_DEFINED
#define SLOP_OPTION_CONTEXT_FUNCPARAMTYPE_DEFINED
SLOP_OPTION_DEFINE(context_FuncParamType, slop_option_context_FuncParamType)
#endif

struct context_FuncEntry {
    slop_string name;
    slop_string c_name;
    slop_string return_type;
    slop_string slop_return_type;
    uint8_t returns_pointer;
    uint8_t returns_string;
    slop_list_context_FuncParamType_ptr param_types;
    uint8_t is_generic;
    slop_list_string type_params;
    slop_option_types_SExpr_ptr generic_source;
    slop_string owner_module;
    slop_string imported_from;
};
typedef struct context_FuncEntry context_FuncEntry;

#ifndef SLOP_OPTION_CONTEXT_FUNCENTRY_DEFINED
#define SLOP_OPTION_CONTEXT_FUNCENTRY_DEFINED
SLOP_OPTION_DEFINE(context_FuncEntry, slop_option_context_FuncEntry)
#endif

#ifndef SLOP_LIST_CONTEXT_FUNCENTRY_DEFINED
#define SLOP_LIST_CONTEXT_FUNCENTRY_DEFINED
#define SLOP_LIST_CONTEXT_FUNCENTRY_IMPL_DEFINED
SLOP_LIST_DEFINE(context_FuncEntry, slop_list_context_FuncEntry)
#endif

struct context_FieldEntry {
    slop_string type_name;
    slop_string field_name;
    slop_string c_type;
    slop_string slop_type;
    uint8_t is_pointer;
};
typedef struct context_FieldEntry context_FieldEntry;

#ifndef SLOP_OPTION_CONTEXT_FIELDENTRY_DEFINED
#define SLOP_OPTION_CONTEXT_FIELDENTRY_DEFINED
SLOP_OPTION_DEFINE(context_FieldEntry, slop_option_context_FieldEntry)
#endif

#ifndef SLOP_LIST_CONTEXT_FIELDENTRY_DEFINED
#define SLOP_LIST_CONTEXT_FIELDENTRY_DEFINED
#define SLOP_LIST_CONTEXT_FIELDENTRY_IMPL_DEFINED
SLOP_LIST_DEFINE(context_FieldEntry, slop_list_context_FieldEntry)
#endif

struct context_Scope {
    slop_list_context_VarEntry vars;
    slop_option_context_Scope_ptr parent;
};
typedef struct context_Scope context_Scope;

#ifndef SLOP_OPTION_CONTEXT_SCOPE_DEFINED
#define SLOP_OPTION_CONTEXT_SCOPE_DEFINED
SLOP_OPTION_DEFINE(context_Scope, slop_option_context_Scope)
#endif

struct context_EnumVariant {
    slop_string variant_name;
    slop_string enum_name;
    slop_string owner_module;
};
typedef struct context_EnumVariant context_EnumVariant;

#ifndef SLOP_OPTION_CONTEXT_ENUMVARIANT_DEFINED
#define SLOP_OPTION_CONTEXT_ENUMVARIANT_DEFINED
SLOP_OPTION_DEFINE(context_EnumVariant, slop_option_context_EnumVariant)
#endif

#ifndef SLOP_LIST_CONTEXT_ENUMVARIANT_DEFINED
#define SLOP_LIST_CONTEXT_ENUMVARIANT_DEFINED
#define SLOP_LIST_CONTEXT_ENUMVARIANT_IMPL_DEFINED
SLOP_LIST_DEFINE(context_EnumVariant, slop_list_context_EnumVariant)
#endif

struct context_UnionVariantEntry {
    slop_string variant_name;
    slop_string union_name;
    slop_string c_variant_name;
    slop_string slop_type;
    slop_string c_type;
};
typedef struct context_UnionVariantEntry context_UnionVariantEntry;

#ifndef SLOP_OPTION_CONTEXT_UNIONVARIANTENTRY_DEFINED
#define SLOP_OPTION_CONTEXT_UNIONVARIANTENTRY_DEFINED
SLOP_OPTION_DEFINE(context_UnionVariantEntry, slop_option_context_UnionVariantEntry)
#endif

#ifndef SLOP_LIST_CONTEXT_UNIONVARIANTENTRY_DEFINED
#define SLOP_LIST_CONTEXT_UNIONVARIANTENTRY_DEFINED
#define SLOP_LIST_CONTEXT_UNIONVARIANTENTRY_IMPL_DEFINED
SLOP_LIST_DEFINE(context_UnionVariantEntry, slop_list_context_UnionVariantEntry)
#endif

struct context_ResultType {
    slop_string ok_type;
    slop_string err_type;
    slop_string c_name;
};
typedef struct context_ResultType context_ResultType;

#ifndef SLOP_OPTION_CONTEXT_RESULTTYPE_DEFINED
#define SLOP_OPTION_CONTEXT_RESULTTYPE_DEFINED
SLOP_OPTION_DEFINE(context_ResultType, slop_option_context_ResultType)
#endif

#ifndef SLOP_LIST_CONTEXT_RESULTTYPE_DEFINED
#define SLOP_LIST_CONTEXT_RESULTTYPE_DEFINED
#define SLOP_LIST_CONTEXT_RESULTTYPE_IMPL_DEFINED
SLOP_LIST_DEFINE(context_ResultType, slop_list_context_ResultType)
#endif

struct context_OptionType {
    slop_string inner_type;
    slop_string c_name;
};
typedef struct context_OptionType context_OptionType;

#ifndef SLOP_OPTION_CONTEXT_OPTIONTYPE_DEFINED
#define SLOP_OPTION_CONTEXT_OPTIONTYPE_DEFINED
SLOP_OPTION_DEFINE(context_OptionType, slop_option_context_OptionType)
#endif

#ifndef SLOP_LIST_CONTEXT_OPTIONTYPE_DEFINED
#define SLOP_LIST_CONTEXT_OPTIONTYPE_DEFINED
#define SLOP_LIST_CONTEXT_OPTIONTYPE_IMPL_DEFINED
SLOP_LIST_DEFINE(context_OptionType, slop_list_context_OptionType)
#endif

struct context_ListType {
    slop_string elem_type;
    slop_string c_name;
};
typedef struct context_ListType context_ListType;

#ifndef SLOP_OPTION_CONTEXT_LISTTYPE_DEFINED
#define SLOP_OPTION_CONTEXT_LISTTYPE_DEFINED
SLOP_OPTION_DEFINE(context_ListType, slop_option_context_ListType)
#endif

#ifndef SLOP_LIST_CONTEXT_LISTTYPE_DEFINED
#define SLOP_LIST_CONTEXT_LISTTYPE_DEFINED
#define SLOP_LIST_CONTEXT_LISTTYPE_IMPL_DEFINED
SLOP_LIST_DEFINE(context_ListType, slop_list_context_ListType)
#endif

struct context_ChanType {
    slop_string elem_type;
    slop_string c_name;
};
typedef struct context_ChanType context_ChanType;

#ifndef SLOP_OPTION_CONTEXT_CHANTYPE_DEFINED
#define SLOP_OPTION_CONTEXT_CHANTYPE_DEFINED
SLOP_OPTION_DEFINE(context_ChanType, slop_option_context_ChanType)
#endif

#ifndef SLOP_LIST_CONTEXT_CHANTYPE_DEFINED
#define SLOP_LIST_CONTEXT_CHANTYPE_DEFINED
#define SLOP_LIST_CONTEXT_CHANTYPE_IMPL_DEFINED
SLOP_LIST_DEFINE(context_ChanType, slop_list_context_ChanType)
#endif

struct context_ThreadType {
    slop_string result_type;
    slop_string c_name;
};
typedef struct context_ThreadType context_ThreadType;

#ifndef SLOP_OPTION_CONTEXT_THREADTYPE_DEFINED
#define SLOP_OPTION_CONTEXT_THREADTYPE_DEFINED
SLOP_OPTION_DEFINE(context_ThreadType, slop_option_context_ThreadType)
#endif

#ifndef SLOP_LIST_CONTEXT_THREADTYPE_DEFINED
#define SLOP_LIST_CONTEXT_THREADTYPE_DEFINED
#define SLOP_LIST_CONTEXT_THREADTYPE_IMPL_DEFINED
SLOP_LIST_DEFINE(context_ThreadType, slop_list_context_ThreadType)
#endif

struct context_ResultTypeAlias {
    slop_string alias_name;
    slop_string c_name;
};
typedef struct context_ResultTypeAlias context_ResultTypeAlias;

#ifndef SLOP_OPTION_CONTEXT_RESULTTYPEALIAS_DEFINED
#define SLOP_OPTION_CONTEXT_RESULTTYPEALIAS_DEFINED
SLOP_OPTION_DEFINE(context_ResultTypeAlias, slop_option_context_ResultTypeAlias)
#endif

#ifndef SLOP_LIST_CONTEXT_RESULTTYPEALIAS_DEFINED
#define SLOP_LIST_CONTEXT_RESULTTYPEALIAS_DEFINED
#define SLOP_LIST_CONTEXT_RESULTTYPEALIAS_IMPL_DEFINED
SLOP_LIST_DEFINE(context_ResultTypeAlias, slop_list_context_ResultTypeAlias)
#endif

struct context_FuncCNameAlias {
    slop_string raw_name;
    slop_string mangled_name;
    slop_string clean_name;
};
typedef struct context_FuncCNameAlias context_FuncCNameAlias;

#ifndef SLOP_OPTION_CONTEXT_FUNCCNAMEALIAS_DEFINED
#define SLOP_OPTION_CONTEXT_FUNCCNAMEALIAS_DEFINED
SLOP_OPTION_DEFINE(context_FuncCNameAlias, slop_option_context_FuncCNameAlias)
#endif

#ifndef SLOP_LIST_CONTEXT_FUNCCNAMEALIAS_DEFINED
#define SLOP_LIST_CONTEXT_FUNCCNAMEALIAS_DEFINED
#define SLOP_LIST_CONTEXT_FUNCCNAMEALIAS_IMPL_DEFINED
SLOP_LIST_DEFINE(context_FuncCNameAlias, slop_list_context_FuncCNameAlias)
#endif

struct context_ValueKeyType {
    slop_string c_type;
    slop_string slop_type;
};
typedef struct context_ValueKeyType context_ValueKeyType;

#ifndef SLOP_OPTION_CONTEXT_VALUEKEYTYPE_DEFINED
#define SLOP_OPTION_CONTEXT_VALUEKEYTYPE_DEFINED
SLOP_OPTION_DEFINE(context_ValueKeyType, slop_option_context_ValueKeyType)
#endif

#ifndef SLOP_LIST_CONTEXT_VALUEKEYTYPE_DEFINED
#define SLOP_LIST_CONTEXT_VALUEKEYTYPE_DEFINED
#define SLOP_LIST_CONTEXT_VALUEKEYTYPE_IMPL_DEFINED
SLOP_LIST_DEFINE(context_ValueKeyType, slop_list_context_ValueKeyType)
#endif

struct context_TypeAliasEntry {
    slop_string name;
    slop_string slop_type;
};
typedef struct context_TypeAliasEntry context_TypeAliasEntry;

#ifndef SLOP_OPTION_CONTEXT_TYPEALIASENTRY_DEFINED
#define SLOP_OPTION_CONTEXT_TYPEALIASENTRY_DEFINED
SLOP_OPTION_DEFINE(context_TypeAliasEntry, slop_option_context_TypeAliasEntry)
#endif

#ifndef SLOP_LIST_CONTEXT_TYPEALIASENTRY_DEFINED
#define SLOP_LIST_CONTEXT_TYPEALIASENTRY_DEFINED
#define SLOP_LIST_CONTEXT_TYPEALIASENTRY_IMPL_DEFINED
SLOP_LIST_DEFINE(context_TypeAliasEntry, slop_list_context_TypeAliasEntry)
#endif

struct context_InlineRecord {
    slop_string type_name;
    slop_string field_body;
};
typedef struct context_InlineRecord context_InlineRecord;

#ifndef SLOP_OPTION_CONTEXT_INLINERECORD_DEFINED
#define SLOP_OPTION_CONTEXT_INLINERECORD_DEFINED
SLOP_OPTION_DEFINE(context_InlineRecord, slop_option_context_InlineRecord)
#endif

#ifndef SLOP_LIST_CONTEXT_INLINERECORD_DEFINED
#define SLOP_LIST_CONTEXT_INLINERECORD_DEFINED
#define SLOP_LIST_CONTEXT_INLINERECORD_IMPL_DEFINED
SLOP_LIST_DEFINE(context_InlineRecord, slop_list_context_InlineRecord)
#endif

struct context_GenericFuncInstantiation {
    slop_string fn_name;
    slop_string type_bindings;
    slop_string c_name;
    slop_string module_name;
};
typedef struct context_GenericFuncInstantiation context_GenericFuncInstantiation;

#ifndef SLOP_OPTION_CONTEXT_GENERICFUNCINSTANTIATION_DEFINED
#define SLOP_OPTION_CONTEXT_GENERICFUNCINSTANTIATION_DEFINED
SLOP_OPTION_DEFINE(context_GenericFuncInstantiation, slop_option_context_GenericFuncInstantiation)
#endif

#ifndef SLOP_LIST_CONTEXT_GENERICFUNCINSTANTIATION_DEFINED
#define SLOP_LIST_CONTEXT_GENERICFUNCINSTANTIATION_DEFINED
#define SLOP_LIST_CONTEXT_GENERICFUNCINSTANTIATION_IMPL_DEFINED
SLOP_LIST_DEFINE(context_GenericFuncInstantiation, slop_list_context_GenericFuncInstantiation)
#endif

struct context_TranspileContext {
    slop_arena* arena;
    slop_list_string output;
    slop_list_string header;
    int64_t indent;
    context_Scope* scope;
    slop_list_context_TypeEntry types;
    slop_list_context_FuncEntry funcs;
    slop_list_context_FieldEntry field_types;
    slop_list_string pointer_vars;
    slop_option_string current_module;
    uint8_t enable_prefixing;
    slop_list_string includes;
    slop_list_string emitted_types;
    slop_list_context_EnumVariant enum_variants;
    slop_list_context_UnionVariantEntry union_variants;
    slop_list_context_ResultType result_types;
    slop_option_string current_result_type;
    slop_option_string current_return_c_type;
    slop_list_string imported_modules;
    slop_list_context_OptionType option_types;
    slop_list_context_ListType list_types;
    slop_list_context_ChanType chan_types;
    slop_list_context_ThreadType thread_types;
    slop_list_context_ResultTypeAlias result_type_aliases;
    slop_list_context_InlineRecord inline_records;
    slop_list_context_FuncCNameAlias c_name_aliases;
    int64_t gensym_counter;
    uint8_t capture_to_retval;
    slop_list_string open_arenas;
    slop_list_string struct_key_types;
    slop_list_context_ValueKeyType value_key_types;
    slop_list_context_TypeAliasEntry type_aliases;
    slop_string current_file;
    slop_list_context_TranspileError errors;
    slop_list_context_TranspileError warnings;
    slop_list_string deferred_lambdas;
    slop_list_string fn_trampolines;
    slop_list_string function_output;
    uint8_t emit_to_function_buffer;
    uint8_t last_lambda_is_closure;
    slop_string last_lambda_env_type;
    slop_string last_lambda_name;
    slop_list_context_GenericFuncInstantiation generic_func_instantiations;
    uint8_t single_output_mode;
    uint8_t skip_trampoline_generation;
    uint8_t strict_unknown_symbols;
    slop_string current_fn_c_name;
    int64_t pos_line;
    int64_t pos_col;
    slop_list_string reported_ambiguities;
};
typedef struct context_TranspileContext context_TranspileContext;

#ifndef SLOP_OPTION_CONTEXT_TRANSPILECONTEXT_DEFINED
#define SLOP_OPTION_CONTEXT_TRANSPILECONTEXT_DEFINED
SLOP_OPTION_DEFINE(context_TranspileContext, slop_option_context_TranspileContext)
#endif

typedef enum {
    context_TypeLookup_type_found,
    context_TypeLookup_type_missing,
    context_TypeLookup_type_ambiguous
} context_TypeLookup_tag;

struct context_TypeLookup {
    context_TypeLookup_tag tag;
    union {
        context_TypeEntry type_found;
        slop_list_context_TypeEntry type_ambiguous;
    } data;
};
typedef struct context_TypeLookup context_TypeLookup;

#ifndef SLOP_OPTION_CONTEXT_TYPELOOKUP_DEFINED
#define SLOP_OPTION_CONTEXT_TYPELOOKUP_DEFINED
SLOP_OPTION_DEFINE(context_TypeLookup, slop_option_context_TypeLookup)
#endif

typedef enum {
    context_VariantLookup_variant_found,
    context_VariantLookup_variant_missing,
    context_VariantLookup_variant_ambiguous
} context_VariantLookup_tag;

struct context_VariantLookup {
    context_VariantLookup_tag tag;
    union {
        slop_string variant_found;
    } data;
};
typedef struct context_VariantLookup context_VariantLookup;

#ifndef SLOP_OPTION_CONTEXT_VARIANTLOOKUP_DEFINED
#define SLOP_OPTION_CONTEXT_VARIANTLOOKUP_DEFINED
SLOP_OPTION_DEFINE(context_VariantLookup, slop_option_context_VariantLookup)
#endif

struct context_LastLambdaInfo {
    uint8_t is_closure;
    slop_string env_type;
    slop_string lambda_name;
};
typedef struct context_LastLambdaInfo context_LastLambdaInfo;

#ifndef SLOP_OPTION_CONTEXT_LASTLAMBDAINFO_DEFINED
#define SLOP_OPTION_CONTEXT_LASTLAMBDAINFO_DEFINED
SLOP_OPTION_DEFINE(context_LastLambdaInfo, slop_option_context_LastLambdaInfo)
#endif

context_TranspileContext* context_context_new(slop_arena* arena);
void context_ctx_reset_for_new_module(context_TranspileContext* ctx, slop_string mod_name);
void context_ctx_emit(context_TranspileContext* ctx, slop_string line);
void context_ctx_emit_header(context_TranspileContext* ctx, slop_string line);
slop_list_string context_ctx_get_output(context_TranspileContext* ctx);
slop_list_string context_ctx_get_header(context_TranspileContext* ctx);
void context_ctx_indent(context_TranspileContext* ctx);
void context_ctx_dedent(context_TranspileContext* ctx);
void context_ctx_fail(context_TranspileContext* ctx, slop_string message);
void context_ctx_warn_fallback(context_TranspileContext* ctx, types_SExpr* expr, slop_string desc);
uint8_t context_fallback_warnings_enabled(void);
void context_print_string_stdout(slop_string s);
void context_print_string_stderr(slop_string s);
void context_ctx_set_file(context_TranspileContext* ctx, slop_string filename);
void context_ctx_add_error(context_TranspileContext* ctx, slop_string message);
void context_ctx_add_error_at(context_TranspileContext* ctx, slop_string message, int64_t line, int64_t col);
uint8_t context_ctx_has_errors(context_TranspileContext* ctx);
slop_list_context_TranspileError context_ctx_get_errors(context_TranspileContext* ctx);
int64_t context_ctx_report_errors(context_TranspileContext* ctx);
void context_ctx_add_warning(context_TranspileContext* ctx, slop_string message);
void context_ctx_add_warning_at(context_TranspileContext* ctx, slop_string message, int64_t line, int64_t col);
uint8_t context_ctx_has_warnings(context_TranspileContext* ctx);
int64_t context_ctx_report_warnings(context_TranspileContext* ctx);
int64_t context_ctx_sexpr_line(types_SExpr* expr);
int64_t context_ctx_sexpr_col(types_SExpr* expr);
int64_t context_ctx_list_first_line(slop_list_types_SExpr_ptr items);
int64_t context_ctx_list_first_col(slop_list_types_SExpr_ptr items);
void context_ctx_push_scope(context_TranspileContext* ctx);
void context_ctx_pop_scope(context_TranspileContext* ctx);
void context_ctx_bind_var(context_TranspileContext* ctx, context_VarEntry entry);
slop_option_context_VarEntry context_lookup_in_scope(context_Scope* scope, slop_string name);
slop_option_context_VarEntry context_ctx_lookup_var(context_TranspileContext* ctx, slop_string name);
slop_option_context_VarEntry context_lookup_var_in_scope_chain(context_Scope* scope, slop_string name);
slop_option_context_VarEntry context_find_arena_in_single_scope(context_Scope* scope);
slop_option_context_VarEntry context_ctx_find_arena_var(context_TranspileContext* ctx);
slop_option_context_VarEntry context_find_arena_in_scope_chain(context_Scope* scope);
void context_ctx_register_type(context_TranspileContext* ctx, context_TypeEntry entry);
slop_option_context_TypeEntry context_find_type_entry(context_TranspileContext* ctx, slop_string name, slop_string mod, uint8_t definition);
slop_option_context_TypeEntry context_ctx_find_type_binding(context_TranspileContext* ctx, slop_string name, slop_string mod);
slop_option_context_TypeEntry context_ctx_find_own_type(context_TranspileContext* ctx, slop_string name);
uint8_t context_ctx_module_defines_types(context_TranspileContext* ctx, slop_string mod);
slop_option_context_TypeEntry context_ctx_lookup_type_in_module(context_TranspileContext* ctx, slop_string name, slop_string mod);
context_TypeLookup context_ctx_resolve_type(context_TranspileContext* ctx, slop_string name);
uint8_t context_type_entries_have_c_name(slop_list_context_TypeEntry entries, slop_string c_name);
slop_option_context_TypeEntry context_ctx_resolve_type_at(context_TranspileContext* ctx, slop_string name, types_SExpr* at);
slop_option_context_TypeEntry context_ctx_lookup_type(context_TranspileContext* ctx, slop_string name);
uint8_t context_ctx_type_name_exists(context_TranspileContext* ctx, slop_string name);
void context_ctx_report_type_ambiguity(context_TranspileContext* ctx, slop_string name, slop_list_context_TypeEntry candidates, types_SExpr* at);
uint8_t context_list_has_string(slop_list_string items, slop_string s);
void context_ctx_set_pos(context_TranspileContext* ctx, types_SExpr* expr);
void context_ctx_register_func(context_TranspileContext* ctx, context_FuncEntry entry);
slop_string context_ctx_current_module_name(context_TranspileContext* ctx);
slop_option_context_FuncEntry context_ctx_lookup_func(context_TranspileContext* ctx, slop_string name);
slop_option_context_FuncEntry context_ctx_lookup_func_in_module(context_TranspileContext* ctx, slop_string name, slop_string mod);
slop_option_context_FuncEntry context_ctx_find_import_entry(context_TranspileContext* ctx, slop_string name, slop_string mod);
void context_ctx_register_field_type(context_TranspileContext* ctx, slop_string type_name, slop_string field_name, slop_string c_type, slop_string slop_type, uint8_t is_pointer);
slop_option_string context_ctx_lookup_field_type(context_TranspileContext* ctx, slop_string type_name, slop_string field_name);
slop_option_string context_ctx_lookup_field_slop_type(context_TranspileContext* ctx, slop_string type_name, slop_string field_name);
slop_option_string context_ctx_lookup_field_type_for_slop(context_TranspileContext* ctx, slop_string slop_name, slop_string field_name);
slop_option_string context_ctx_lookup_field_slop_type_for_slop(context_TranspileContext* ctx, slop_string slop_name, slop_string field_name);
slop_option_string context_ctx_lookup_field_type_by_index(context_TranspileContext* ctx, slop_string type_name, int64_t index);
slop_list_context_FieldEntry context_ctx_get_fields_for_type(context_TranspileContext* ctx, slop_string type_name);
void context_ctx_mark_pointer_var(context_TranspileContext* ctx, slop_string name);
uint8_t context_ctx_is_pointer_var(context_TranspileContext* ctx, slop_string name);
void context_ctx_set_module(context_TranspileContext* ctx, slop_option_string name);
slop_option_string context_ctx_get_module(context_TranspileContext* ctx);
void context_ctx_set_prefixing(context_TranspileContext* ctx, uint8_t enabled);
uint8_t context_ctx_prefixing_enabled(context_TranspileContext* ctx);
slop_string context_ctx_prefix_type(context_TranspileContext* ctx, slop_string type_name);
void context_ctx_add_include(context_TranspileContext* ctx, slop_string header);
slop_list_string context_ctx_get_includes(context_TranspileContext* ctx);
void context_ctx_mark_type_emitted(context_TranspileContext* ctx, slop_string type_name);
uint8_t context_ctx_is_type_emitted(context_TranspileContext* ctx, slop_string type_name);
void context_ctx_register_enum_variant(context_TranspileContext* ctx, slop_string variant_name, slop_string enum_name);
void context_ctx_register_enum_variant_in(context_TranspileContext* ctx, slop_string variant_name, slop_string enum_name, slop_string owner);
uint8_t context_variants_have_enum(slop_list_context_EnumVariant variants, slop_string enum_name);
slop_list_context_EnumVariant context_enum_variant_candidates(context_TranspileContext* ctx, slop_string variant_name);
uint8_t context_module_imports_type_c_name(context_TranspileContext* ctx, slop_string c_name, slop_string mod);
slop_list_context_EnumVariant context_select_variants(context_TranspileContext* ctx, slop_list_context_EnumVariant candidates, slop_string mod, context_VariantScope scope);
context_VariantLookup context_first_variant_type(slop_list_context_EnumVariant variants);
slop_string context_variant_type_slop_name(context_TranspileContext* ctx, context_EnumVariant v);
void context_report_variant_ambiguity(context_TranspileContext* ctx, slop_string variant_name, slop_list_context_EnumVariant candidates, uint8_t imported, types_SExpr* at);
context_VariantLookup context_resolve_visible_variant(context_TranspileContext* ctx, slop_string variant_name, types_SExpr* at);
slop_option_string context_ctx_resolve_any_enum_variant(context_TranspileContext* ctx, slop_string variant_name, types_SExpr* at);
slop_option_string context_ctx_resolve_enum_variant_at(context_TranspileContext* ctx, slop_string variant_name, types_SExpr* at);
slop_option_string context_ctx_lookup_enum_variant(context_TranspileContext* ctx, slop_string variant_name);
uint8_t context_ctx_enum_variant_known(context_TranspileContext* ctx, slop_string variant_name);
slop_option_string context_ctx_resolve_enum_variant_for(context_TranspileContext* ctx, slop_string variant_name, slop_string scrut_c_type, types_SExpr* at);
slop_option_string context_ctx_resolve_enum_variant_expecting(context_TranspileContext* ctx, slop_string variant_name, slop_string expected_c_type, types_SExpr* at);
slop_option_string context_ctx_resolve_callable_variant(context_TranspileContext* ctx, slop_string name, types_SExpr* at);
void context_ctx_register_union_variant(context_TranspileContext* ctx, slop_string variant_name, slop_string union_name, slop_string c_variant_name, slop_string slop_type, slop_string c_type);
slop_list_context_UnionVariantEntry context_ctx_get_union_variants(context_TranspileContext* ctx, slop_string union_name);
void context_ctx_register_result_type(context_TranspileContext* ctx, slop_string ok_type, slop_string err_type, slop_string c_name);
uint8_t context_ctx_has_result_type(context_TranspileContext* ctx, slop_string c_name);
slop_list_context_ResultType context_ctx_get_result_types(context_TranspileContext* ctx);
void context_ctx_set_current_result_type(context_TranspileContext* ctx, slop_string result_type);
slop_option_string context_ctx_get_current_result_type(context_TranspileContext* ctx);
void context_ctx_clear_current_result_type(context_TranspileContext* ctx);
void context_ctx_set_current_return_type(context_TranspileContext* ctx, slop_string c_type);
slop_option_string context_ctx_get_current_return_type(context_TranspileContext* ctx);
void context_ctx_clear_current_return_type(context_TranspileContext* ctx);
void context_ctx_set_capture_retval(context_TranspileContext* ctx, uint8_t enabled);
uint8_t context_ctx_is_capture_retval(context_TranspileContext* ctx);
void context_ctx_push_open_arena(context_TranspileContext* ctx, slop_string c_name);
void context_ctx_pop_open_arena(context_TranspileContext* ctx);
slop_list_string context_ctx_take_open_arenas(context_TranspileContext* ctx);
void context_ctx_restore_open_arenas(context_TranspileContext* ctx, slop_list_string saved);
slop_string context_ctx_open_arena_frees(context_TranspileContext* ctx);
void context_ctx_emit_return(context_TranspileContext* ctx, slop_string code);
void context_ctx_register_option_type(context_TranspileContext* ctx, slop_string inner_type, slop_string c_name);
uint8_t context_ctx_has_option_type(context_TranspileContext* ctx, slop_string c_name);
slop_list_context_OptionType context_ctx_get_option_types(context_TranspileContext* ctx);
void context_ctx_register_list_type(context_TranspileContext* ctx, slop_string elem_type, slop_string c_name);
uint8_t context_ctx_has_list_type(context_TranspileContext* ctx, slop_string c_name);
slop_list_context_ListType context_ctx_get_list_types(context_TranspileContext* ctx);
void context_ctx_register_chan_type(context_TranspileContext* ctx, slop_string elem_type, slop_string c_name);
uint8_t context_ctx_has_chan_type(context_TranspileContext* ctx, slop_string c_name);
slop_list_context_ChanType context_ctx_get_chan_types(context_TranspileContext* ctx);
void context_ctx_register_thread_type(context_TranspileContext* ctx, slop_string result_type, slop_string c_name);
uint8_t context_ctx_has_thread_type(context_TranspileContext* ctx, slop_string c_name);
slop_list_context_ThreadType context_ctx_get_thread_types(context_TranspileContext* ctx);
void context_ctx_register_result_type_alias(context_TranspileContext* ctx, slop_string alias_name, slop_string c_name);
slop_string context_alias_key_for_definition(context_TranspileContext* ctx, slop_string name);
slop_option_string context_find_result_type_alias(context_TranspileContext* ctx, slop_string key);
uint8_t context_type_candidates_have_alias(context_TranspileContext* ctx, slop_list_context_TypeEntry candidates, uint8_t result_alias);
slop_option_string context_ctx_lookup_result_type_alias(context_TranspileContext* ctx, slop_string alias_name);
void context_ctx_add_c_name_alias(context_TranspileContext* ctx, context_FuncCNameAlias alias);
slop_list_context_FuncCNameAlias context_ctx_get_c_name_aliases(context_TranspileContext* ctx);
slop_string context_extract_fn_c_name(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string default_name);
slop_string context_ctx_str(context_TranspileContext* ctx, slop_string a, slop_string b);
slop_string context_ctx_str3(context_TranspileContext* ctx, slop_string a, slop_string b, slop_string c);
slop_string context_ctx_str4(context_TranspileContext* ctx, slop_string a, slop_string b, slop_string c, slop_string d);
slop_string context_ctx_str5(context_TranspileContext* ctx, slop_string a, slop_string b, slop_string c, slop_string d, slop_string e);
uint8_t context_cond_paren_wrapped(slop_string s);
slop_string context_ctx_strip_cond_parens(context_TranspileContext* ctx, slop_string s);
void context_ctx_add_import(context_TranspileContext* ctx, slop_string mod_name);
slop_list_string context_ctx_get_imports(context_TranspileContext* ctx);
void context_ctx_register_inline_record(context_TranspileContext* ctx, slop_string type_name, slop_string field_body);
slop_list_context_InlineRecord context_ctx_get_inline_records(context_TranspileContext* ctx);
slop_string context_simple_hash(slop_arena* arena, slop_string s);
slop_string context_to_c_type_prefixed(context_TranspileContext* ctx, types_SExpr* type_expr);
slop_option_string context_get_array_pointer_type(context_TranspileContext* ctx, types_SExpr* expr);
uint8_t context_ends_with_star(slop_string s);
slop_string context_string_concat_ctx(context_TranspileContext* ctx, slop_string a, slop_string b);
slop_string context_to_c_type_prefixed_compound(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string context_build_fn_args_str_prefixed(context_TranspileContext* ctx, types_SExpr* args_expr);
slop_string context_ctx_gensym(context_TranspileContext* ctx, slop_string prefix);
void context_ctx_register_struct_key_type(context_TranspileContext* ctx, slop_string c_type);
uint8_t context_ctx_has_struct_key_type(context_TranspileContext* ctx, slop_string c_type);
slop_list_string context_ctx_get_struct_key_types(context_TranspileContext* ctx);
slop_option_string context_ctx_lookup_value_key_type(context_TranspileContext* ctx, slop_string c_type);
void context_ctx_register_value_key_type(context_TranspileContext* ctx, slop_string c_type, slop_string slop_type);
void context_ctx_register_type_alias(context_TranspileContext* ctx, slop_string name, slop_string slop_type);
uint8_t context_ctx_is_option_c_type(context_TranspileContext* ctx, slop_string c_type);
slop_option_string context_ctx_lookup_type_alias(context_TranspileContext* ctx, slop_string name);
slop_option_string context_find_type_alias(context_TranspileContext* ctx, slop_string key);
void context_ctx_add_deferred_lambda(context_TranspileContext* ctx, slop_string lambda_code);
slop_list_string context_ctx_get_deferred_lambdas(context_TranspileContext* ctx);
void context_ctx_clear_deferred_lambdas(context_TranspileContext* ctx);
uint8_t context_ctx_has_trampoline(context_TranspileContext* ctx, slop_string fn_c_name);
void context_ctx_add_trampoline(context_TranspileContext* ctx, slop_string fn_c_name);
void context_ctx_set_single_output_mode(context_TranspileContext* ctx, uint8_t enabled);
void context_ctx_set_skip_trampoline_generation(context_TranspileContext* ctx, uint8_t skip);
uint8_t context_ctx_skip_trampoline_generation(context_TranspileContext* ctx);
void context_ctx_set_strict_unknown_symbols(context_TranspileContext* ctx, uint8_t enabled);
uint8_t context_ctx_strict_unknown_symbols(context_TranspileContext* ctx);
void context_ctx_set_current_fn_c_name(context_TranspileContext* ctx, slop_string name);
void context_ctx_clear_current_fn_c_name(context_TranspileContext* ctx);
void context_ctx_set_last_lambda_info(context_TranspileContext* ctx, uint8_t is_closure, slop_string env_type, slop_string lambda_name);
context_LastLambdaInfo context_ctx_get_last_lambda_info(context_TranspileContext* ctx);
void context_ctx_clear_last_lambda_info(context_TranspileContext* ctx);
void context_ctx_start_function_buffer(context_TranspileContext* ctx);
void context_ctx_stop_function_buffer(context_TranspileContext* ctx);
void context_ctx_flush_function_buffer(context_TranspileContext* ctx);
void context_ctx_register_generic_instantiation(context_TranspileContext* ctx, slop_string fn_name, slop_string type_bindings, slop_string c_name, slop_string module_name);
uint8_t context_ctx_has_generic_instantiation(context_TranspileContext* ctx, slop_string fn_name, slop_string type_bindings);
slop_list_context_GenericFuncInstantiation context_ctx_get_generic_instantiations(context_TranspileContext* ctx);
slop_string context_mangle_generic_fn_name(context_TranspileContext* ctx, slop_string base_c_name, slop_string type_binding);

#ifndef SLOP_OPTION_CONTEXT_TRANSPILEERROR_DEFINED
#define SLOP_OPTION_CONTEXT_TRANSPILEERROR_DEFINED
SLOP_OPTION_DEFINE(context_TranspileError, slop_option_context_TranspileError)
#endif

#ifndef SLOP_OPTION_CONTEXT_VARENTRY_DEFINED
#define SLOP_OPTION_CONTEXT_VARENTRY_DEFINED
SLOP_OPTION_DEFINE(context_VarEntry, slop_option_context_VarEntry)
#endif

#ifndef SLOP_OPTION_CONTEXT_TYPEENTRY_DEFINED
#define SLOP_OPTION_CONTEXT_TYPEENTRY_DEFINED
SLOP_OPTION_DEFINE(context_TypeEntry, slop_option_context_TypeEntry)
#endif

#ifndef SLOP_OPTION_CONTEXT_FUNCPARAMTYPE_DEFINED
#define SLOP_OPTION_CONTEXT_FUNCPARAMTYPE_DEFINED
SLOP_OPTION_DEFINE(context_FuncParamType, slop_option_context_FuncParamType)
#endif

#ifndef SLOP_OPTION_CONTEXT_FUNCPARAMTYPE_PTR_DEFINED
#define SLOP_OPTION_CONTEXT_FUNCPARAMTYPE_PTR_DEFINED
SLOP_OPTION_DEFINE(context_FuncParamType*, slop_option_context_FuncParamType_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_CONTEXT_FUNCENTRY_DEFINED
#define SLOP_OPTION_CONTEXT_FUNCENTRY_DEFINED
SLOP_OPTION_DEFINE(context_FuncEntry, slop_option_context_FuncEntry)
#endif

#ifndef SLOP_OPTION_CONTEXT_FIELDENTRY_DEFINED
#define SLOP_OPTION_CONTEXT_FIELDENTRY_DEFINED
SLOP_OPTION_DEFINE(context_FieldEntry, slop_option_context_FieldEntry)
#endif

#ifndef SLOP_OPTION_CONTEXT_SCOPE_PTR_DEFINED
#define SLOP_OPTION_CONTEXT_SCOPE_PTR_DEFINED
SLOP_OPTION_DEFINE(context_Scope*, slop_option_context_Scope_ptr)
#endif

#ifndef SLOP_OPTION_CONTEXT_SCOPE_DEFINED
#define SLOP_OPTION_CONTEXT_SCOPE_DEFINED
SLOP_OPTION_DEFINE(context_Scope, slop_option_context_Scope)
#endif

#ifndef SLOP_OPTION_CONTEXT_ENUMVARIANT_DEFINED
#define SLOP_OPTION_CONTEXT_ENUMVARIANT_DEFINED
SLOP_OPTION_DEFINE(context_EnumVariant, slop_option_context_EnumVariant)
#endif

#ifndef SLOP_OPTION_CONTEXT_UNIONVARIANTENTRY_DEFINED
#define SLOP_OPTION_CONTEXT_UNIONVARIANTENTRY_DEFINED
SLOP_OPTION_DEFINE(context_UnionVariantEntry, slop_option_context_UnionVariantEntry)
#endif

#ifndef SLOP_OPTION_CONTEXT_RESULTTYPE_DEFINED
#define SLOP_OPTION_CONTEXT_RESULTTYPE_DEFINED
SLOP_OPTION_DEFINE(context_ResultType, slop_option_context_ResultType)
#endif

#ifndef SLOP_OPTION_CONTEXT_OPTIONTYPE_DEFINED
#define SLOP_OPTION_CONTEXT_OPTIONTYPE_DEFINED
SLOP_OPTION_DEFINE(context_OptionType, slop_option_context_OptionType)
#endif

#ifndef SLOP_OPTION_CONTEXT_LISTTYPE_DEFINED
#define SLOP_OPTION_CONTEXT_LISTTYPE_DEFINED
SLOP_OPTION_DEFINE(context_ListType, slop_option_context_ListType)
#endif

#ifndef SLOP_OPTION_CONTEXT_CHANTYPE_DEFINED
#define SLOP_OPTION_CONTEXT_CHANTYPE_DEFINED
SLOP_OPTION_DEFINE(context_ChanType, slop_option_context_ChanType)
#endif

#ifndef SLOP_OPTION_CONTEXT_THREADTYPE_DEFINED
#define SLOP_OPTION_CONTEXT_THREADTYPE_DEFINED
SLOP_OPTION_DEFINE(context_ThreadType, slop_option_context_ThreadType)
#endif

#ifndef SLOP_OPTION_CONTEXT_RESULTTYPEALIAS_DEFINED
#define SLOP_OPTION_CONTEXT_RESULTTYPEALIAS_DEFINED
SLOP_OPTION_DEFINE(context_ResultTypeAlias, slop_option_context_ResultTypeAlias)
#endif

#ifndef SLOP_OPTION_CONTEXT_FUNCCNAMEALIAS_DEFINED
#define SLOP_OPTION_CONTEXT_FUNCCNAMEALIAS_DEFINED
SLOP_OPTION_DEFINE(context_FuncCNameAlias, slop_option_context_FuncCNameAlias)
#endif

#ifndef SLOP_OPTION_CONTEXT_VALUEKEYTYPE_DEFINED
#define SLOP_OPTION_CONTEXT_VALUEKEYTYPE_DEFINED
SLOP_OPTION_DEFINE(context_ValueKeyType, slop_option_context_ValueKeyType)
#endif

#ifndef SLOP_OPTION_CONTEXT_TYPEALIASENTRY_DEFINED
#define SLOP_OPTION_CONTEXT_TYPEALIASENTRY_DEFINED
SLOP_OPTION_DEFINE(context_TypeAliasEntry, slop_option_context_TypeAliasEntry)
#endif

#ifndef SLOP_OPTION_CONTEXT_INLINERECORD_DEFINED
#define SLOP_OPTION_CONTEXT_INLINERECORD_DEFINED
SLOP_OPTION_DEFINE(context_InlineRecord, slop_option_context_InlineRecord)
#endif

#ifndef SLOP_OPTION_CONTEXT_GENERICFUNCINSTANTIATION_DEFINED
#define SLOP_OPTION_CONTEXT_GENERICFUNCINSTANTIATION_DEFINED
SLOP_OPTION_DEFINE(context_GenericFuncInstantiation, slop_option_context_GenericFuncInstantiation)
#endif

#ifndef SLOP_OPTION_CONTEXT_TRANSPILECONTEXT_DEFINED
#define SLOP_OPTION_CONTEXT_TRANSPILECONTEXT_DEFINED
SLOP_OPTION_DEFINE(context_TranspileContext, slop_option_context_TranspileContext)
#endif

#ifndef SLOP_OPTION_CONTEXT_TYPELOOKUP_DEFINED
#define SLOP_OPTION_CONTEXT_TYPELOOKUP_DEFINED
SLOP_OPTION_DEFINE(context_TypeLookup, slop_option_context_TypeLookup)
#endif

#ifndef SLOP_OPTION_CONTEXT_VARIANTLOOKUP_DEFINED
#define SLOP_OPTION_CONTEXT_VARIANTLOOKUP_DEFINED
SLOP_OPTION_DEFINE(context_VariantLookup, slop_option_context_VariantLookup)
#endif

#ifndef SLOP_OPTION_CONTEXT_LASTLAMBDAINFO_DEFINED
#define SLOP_OPTION_CONTEXT_LASTLAMBDAINFO_DEFINED
SLOP_OPTION_DEFINE(context_LastLambdaInfo, slop_option_context_LastLambdaInfo)
#endif


#endif
