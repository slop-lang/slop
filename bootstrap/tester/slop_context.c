#include "../runtime/slop_runtime.h"
#include "slop_context.h"

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
void context_print_string_stdout(slop_string s);
void context_print_string_stderr(slop_string s);
void context_ctx_set_file(context_TranspileContext* ctx, slop_string filename);
void context_ctx_add_error(context_TranspileContext* ctx, slop_string message);
void context_ctx_add_error_at(context_TranspileContext* ctx, slop_string message, int64_t line, int64_t col);
uint8_t context_ctx_has_errors(context_TranspileContext* ctx);
slop_list_context_TranspileError context_ctx_get_errors(context_TranspileContext* ctx);
int64_t context_ctx_report_errors(context_TranspileContext* ctx);
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
void context_ctx_register_type(context_TranspileContext* ctx, context_TypeEntry entry);
slop_option_context_TypeEntry context_ctx_lookup_type(context_TranspileContext* ctx, slop_string name);
void context_ctx_register_func(context_TranspileContext* ctx, context_FuncEntry entry);
slop_option_context_FuncEntry context_ctx_lookup_func(context_TranspileContext* ctx, slop_string name);
void context_ctx_register_field_type(context_TranspileContext* ctx, slop_string type_name, slop_string field_name, slop_string c_type, slop_string slop_type, uint8_t is_pointer);
slop_option_string context_ctx_lookup_field_type(context_TranspileContext* ctx, slop_string type_name, slop_string field_name);
slop_string context_strip_module_prefix(slop_arena* arena, slop_string type_name);
slop_option_string context_ctx_lookup_field_slop_type(context_TranspileContext* ctx, slop_string type_name, slop_string field_name);
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
slop_option_string context_ctx_lookup_enum_variant(context_TranspileContext* ctx, slop_string variant_name);
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
slop_option_string context_ctx_lookup_result_type_alias(context_TranspileContext* ctx, slop_string alias_name);
void context_ctx_add_c_name_alias(context_TranspileContext* ctx, context_FuncCNameAlias alias);
slop_list_context_FuncCNameAlias context_ctx_get_c_name_aliases(context_TranspileContext* ctx);
slop_string context_extract_fn_c_name(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string default_name);
slop_string context_ctx_str(context_TranspileContext* ctx, slop_string a, slop_string b);
slop_string context_ctx_str3(context_TranspileContext* ctx, slop_string a, slop_string b, slop_string c);
slop_string context_ctx_str4(context_TranspileContext* ctx, slop_string a, slop_string b, slop_string c, slop_string d);
slop_string context_ctx_str5(context_TranspileContext* ctx, slop_string a, slop_string b, slop_string c, slop_string d, slop_string e);
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
void context_ctx_register_type_alias(context_TranspileContext* ctx, slop_string name, slop_string slop_type);
slop_option_string context_ctx_lookup_type_alias(context_TranspileContext* ctx, slop_string name);
void context_ctx_add_deferred_lambda(context_TranspileContext* ctx, slop_string lambda_code);
slop_list_string context_ctx_get_deferred_lambdas(context_TranspileContext* ctx);
void context_ctx_clear_deferred_lambdas(context_TranspileContext* ctx);
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

context_TranspileContext* context_context_new(slop_arena* arena) {
    {
        __auto_type ctx = ((context_TranspileContext*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 1024); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        __auto_type initial_scope = ((context_Scope*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 64); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        slop_option_context_Scope_ptr no_parent = (slop_option_context_Scope_ptr){.has_value = false};
        slop_option_string no_module = (slop_option_string){.has_value = false};
        (*initial_scope).vars = ((slop_list_context_VarEntry){ .data = (context_VarEntry*)slop_arena_alloc(arena, 16 * sizeof(context_VarEntry)), .len = 0, .cap = 16 });
        (*initial_scope).parent = no_parent;
        (*ctx).arena = arena;
        (*ctx).output = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).header = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).indent = 0;
        (*ctx).scope = initial_scope;
        (*ctx).types = ((slop_list_context_TypeEntry){ .data = (context_TypeEntry*)slop_arena_alloc(arena, 16 * sizeof(context_TypeEntry)), .len = 0, .cap = 16 });
        (*ctx).funcs = ((slop_list_context_FuncEntry){ .data = (context_FuncEntry*)slop_arena_alloc(arena, 16 * sizeof(context_FuncEntry)), .len = 0, .cap = 16 });
        (*ctx).field_types = ((slop_list_context_FieldEntry){ .data = (context_FieldEntry*)slop_arena_alloc(arena, 16 * sizeof(context_FieldEntry)), .len = 0, .cap = 16 });
        (*ctx).pointer_vars = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).current_module = no_module;
        (*ctx).enable_prefixing = 0;
        (*ctx).includes = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).emitted_types = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).enum_variants = ((slop_list_context_EnumVariant){ .data = (context_EnumVariant*)slop_arena_alloc(arena, 16 * sizeof(context_EnumVariant)), .len = 0, .cap = 16 });
        (*ctx).union_variants = ((slop_list_context_UnionVariantEntry){ .data = (context_UnionVariantEntry*)slop_arena_alloc(arena, 16 * sizeof(context_UnionVariantEntry)), .len = 0, .cap = 16 });
        (*ctx).result_types = ((slop_list_context_ResultType){ .data = (context_ResultType*)slop_arena_alloc(arena, 16 * sizeof(context_ResultType)), .len = 0, .cap = 16 });
        (*ctx).current_result_type = (slop_option_string){.has_value = false};
        (*ctx).current_return_c_type = (slop_option_string){.has_value = false};
        (*ctx).imported_modules = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).option_types = ((slop_list_context_OptionType){ .data = (context_OptionType*)slop_arena_alloc(arena, 16 * sizeof(context_OptionType)), .len = 0, .cap = 16 });
        (*ctx).list_types = ((slop_list_context_ListType){ .data = (context_ListType*)slop_arena_alloc(arena, 16 * sizeof(context_ListType)), .len = 0, .cap = 16 });
        (*ctx).chan_types = ((slop_list_context_ChanType){ .data = (context_ChanType*)slop_arena_alloc(arena, 16 * sizeof(context_ChanType)), .len = 0, .cap = 16 });
        (*ctx).thread_types = ((slop_list_context_ThreadType){ .data = (context_ThreadType*)slop_arena_alloc(arena, 16 * sizeof(context_ThreadType)), .len = 0, .cap = 16 });
        (*ctx).result_type_aliases = ((slop_list_context_ResultTypeAlias){ .data = (context_ResultTypeAlias*)slop_arena_alloc(arena, 16 * sizeof(context_ResultTypeAlias)), .len = 0, .cap = 16 });
        (*ctx).inline_records = ((slop_list_context_InlineRecord){ .data = (context_InlineRecord*)slop_arena_alloc(arena, 16 * sizeof(context_InlineRecord)), .len = 0, .cap = 16 });
        (*ctx).c_name_aliases = ((slop_list_context_FuncCNameAlias){ .data = (context_FuncCNameAlias*)slop_arena_alloc(arena, 16 * sizeof(context_FuncCNameAlias)), .len = 0, .cap = 16 });
        (*ctx).gensym_counter = 0;
        (*ctx).capture_to_retval = 0;
        (*ctx).struct_key_types = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).type_aliases = ((slop_list_context_TypeAliasEntry){ .data = (context_TypeAliasEntry*)slop_arena_alloc(arena, 16 * sizeof(context_TypeAliasEntry)), .len = 0, .cap = 16 });
        (*ctx).current_file = SLOP_STR("");
        (*ctx).errors = ((slop_list_context_TranspileError){ .data = (context_TranspileError*)slop_arena_alloc(arena, 16 * sizeof(context_TranspileError)), .len = 0, .cap = 16 });
        (*ctx).deferred_lambdas = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).function_output = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).emit_to_function_buffer = 0;
        (*ctx).last_lambda_is_closure = 0;
        (*ctx).last_lambda_env_type = SLOP_STR("");
        (*ctx).last_lambda_name = SLOP_STR("");
        (*ctx).generic_func_instantiations = ((slop_list_context_GenericFuncInstantiation){ .data = (context_GenericFuncInstantiation*)slop_arena_alloc(arena, 16 * sizeof(context_GenericFuncInstantiation)), .len = 0, .cap = 16 });
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("Int"), SLOP_STR("int64_t"), SLOP_STR("int64_t"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("I8"), SLOP_STR("int8_t"), SLOP_STR("int8_t"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("I16"), SLOP_STR("int16_t"), SLOP_STR("int16_t"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("I32"), SLOP_STR("int32_t"), SLOP_STR("int32_t"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("I64"), SLOP_STR("int64_t"), SLOP_STR("int64_t"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("U8"), SLOP_STR("uint8_t"), SLOP_STR("uint8_t"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("U16"), SLOP_STR("uint16_t"), SLOP_STR("uint16_t"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("U32"), SLOP_STR("uint32_t"), SLOP_STR("uint32_t"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("U64"), SLOP_STR("uint64_t"), SLOP_STR("uint64_t"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("Char"), SLOP_STR("char"), SLOP_STR("char"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("Float"), SLOP_STR("double"), SLOP_STR("double"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("F32"), SLOP_STR("float"), SLOP_STR("float"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("Bool"), SLOP_STR("uint8_t"), SLOP_STR("uint8_t"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("String"), SLOP_STR("slop_string"), SLOP_STR("slop_string"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("Bytes"), SLOP_STR("slop_bytes"), SLOP_STR("slop_bytes"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("Unit"), SLOP_STR("void"), SLOP_STR("void"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("Void"), SLOP_STR("void"), SLOP_STR("void"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("Arena"), SLOP_STR("slop_arena*"), SLOP_STR("slop_arena*"), 0, 0, 0});
        context_ctx_register_type(ctx, (context_TypeEntry){SLOP_STR("Milliseconds"), SLOP_STR("int64_t"), SLOP_STR("int64_t"), 0, 0, 0});
        return ctx;
    }
}

void context_ctx_reset_for_new_module(context_TranspileContext* ctx, slop_string mod_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type fresh_scope = ((context_Scope*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 64); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        slop_option_context_Scope_ptr no_parent = (slop_option_context_Scope_ptr){.has_value = false};
        (*fresh_scope).vars = ((slop_list_context_VarEntry){ .data = (context_VarEntry*)slop_arena_alloc(arena, 16 * sizeof(context_VarEntry)), .len = 0, .cap = 16 });
        (*fresh_scope).parent = no_parent;
        (*ctx).output = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).header = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).indent = 0;
        (*ctx).scope = fresh_scope;
        (*ctx).current_result_type = (slop_option_string){.has_value = false};
        (*ctx).current_return_c_type = (slop_option_string){.has_value = false};
        (*ctx).includes = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).emitted_types = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).imported_modules = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).result_types = ((slop_list_context_ResultType){ .data = (context_ResultType*)slop_arena_alloc(arena, 16 * sizeof(context_ResultType)), .len = 0, .cap = 16 });
        (*ctx).option_types = ((slop_list_context_OptionType){ .data = (context_OptionType*)slop_arena_alloc(arena, 16 * sizeof(context_OptionType)), .len = 0, .cap = 16 });
        (*ctx).list_types = ((slop_list_context_ListType){ .data = (context_ListType*)slop_arena_alloc(arena, 16 * sizeof(context_ListType)), .len = 0, .cap = 16 });
        (*ctx).chan_types = ((slop_list_context_ChanType){ .data = (context_ChanType*)slop_arena_alloc(arena, 16 * sizeof(context_ChanType)), .len = 0, .cap = 16 });
        (*ctx).thread_types = ((slop_list_context_ThreadType){ .data = (context_ThreadType*)slop_arena_alloc(arena, 16 * sizeof(context_ThreadType)), .len = 0, .cap = 16 });
        (*ctx).inline_records = ((slop_list_context_InlineRecord){ .data = (context_InlineRecord*)slop_arena_alloc(arena, 16 * sizeof(context_InlineRecord)), .len = 0, .cap = 16 });
        (*ctx).c_name_aliases = ((slop_list_context_FuncCNameAlias){ .data = (context_FuncCNameAlias*)slop_arena_alloc(arena, 16 * sizeof(context_FuncCNameAlias)), .len = 0, .cap = 16 });
        (*ctx).struct_key_types = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).deferred_lambdas = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).function_output = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        (*ctx).emit_to_function_buffer = 0;
        (*ctx).generic_func_instantiations = ((slop_list_context_GenericFuncInstantiation){ .data = (context_GenericFuncInstantiation*)slop_arena_alloc(arena, 16 * sizeof(context_GenericFuncInstantiation)), .len = 0, .cap = 16 });
        (*ctx).current_module = (slop_option_string){.has_value = 1, .value = mod_name};
    }
}

void context_ctx_emit(context_TranspileContext* ctx, slop_string line) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type indent_level = (*ctx).indent;
        __auto_type to_fn_buffer = (*ctx).emit_to_function_buffer;
        {
            __auto_type indented = line;
            __auto_type i = 0;
            while ((i < indent_level)) {
                indented = string_concat(arena, SLOP_STR("    "), indented);
                i = (i + 1);
            }
            if (to_fn_buffer) {
                ({ __auto_type _lst_p = &((*ctx).function_output); __auto_type _item = (indented); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            } else {
                ({ __auto_type _lst_p = &((*ctx).output); __auto_type _item = (indented); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            }
        }
    }
}

void context_ctx_emit_header(context_TranspileContext* ctx, slop_string line) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    ({ __auto_type _lst_p = &((*ctx).header); __auto_type _item = (line); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_list_string context_ctx_get_output(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).output;
}

slop_list_string context_ctx_get_header(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).header;
}

void context_ctx_indent(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    (*ctx).indent = ((*ctx).indent + 1);
}

void context_ctx_dedent(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE((((*ctx).indent > 0)), "(> (. (deref ctx) indent) 0)");
    (*ctx).indent = ((*ctx).indent - 1);
}

void context_ctx_fail(context_TranspileContext* ctx, slop_string message) {
    slop_eprint(((char*)(SLOP_STR("Transpiler error: ").data)));
    context_print_string_stderr(message);
    slop_eputc(10);
    exit(1);
}

void context_ctx_warn_fallback(context_TranspileContext* ctx, types_SExpr* expr, slop_string desc) {
    {
        __auto_type arena = (*ctx).arena;
        __auto_type line = context_ctx_sexpr_line(expr);
        __auto_type col = context_ctx_sexpr_col(expr);
        __auto_type mod_name = context_ctx_get_module(ctx);
        __auto_type expr_head = (((expr == NULL)) ? SLOP_STR("<?>") : ({ __auto_type _mv = (*expr); slop_string _mr = {0}; switch (_mv.tag) { case types_SExpr_sym: { __auto_type s = _mv.data.sym; _mr = s.name; break; } case types_SExpr_str: { __auto_type s = _mv.data.str; _mr = SLOP_STR("<literal>"); break; } case types_SExpr_num: { __auto_type n = _mv.data.num; _mr = SLOP_STR("<literal>"); break; } case types_SExpr_lst: { __auto_type l = _mv.data.lst; _mr = ({ __auto_type items = l.items; ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type first = _mv.value; ({ __auto_type _mv = (*first); slop_string _mr = {0}; switch (_mv.tag) { case types_SExpr_sym: { __auto_type s = _mv.data.sym; _mr = s.name; break; } case types_SExpr_str: { __auto_type s = _mv.data.str; _mr = SLOP_STR("<str>"); break; } case types_SExpr_num: { __auto_type n = _mv.data.num; _mr = SLOP_STR("<num>"); break; } case types_SExpr_lst: { __auto_type l2 = _mv.data.lst; _mr = SLOP_STR("<list>"); break; }  } _mr; }); }) : (SLOP_STR("<empty-list>")); }); }); break; }  } _mr; }));
        slop_eprint(((char*)(SLOP_STR("warning: type inference fallback in ").data)));
        __auto_type _mv_47 = mod_name;
        if (_mv_47.has_value) {
            __auto_type m = _mv_47.value;
            context_print_string_stderr(m);
        } else if (!_mv_47.has_value) {
            slop_eprint(((char*)(SLOP_STR("<unknown>").data)));
        }
        slop_eprint(((char*)(SLOP_STR(" at ").data)));
        context_print_string_stderr(int_to_string(arena, line));
        slop_eputc(58);
        context_print_string_stderr(int_to_string(arena, col));
        slop_eprint(((char*)(SLOP_STR(" (").data)));
        context_print_string_stderr(expr_head);
        slop_eprint(((char*)(SLOP_STR(") for ").data)));
        context_print_string_stderr(desc);
        slop_eputc(10);
    }
}

void context_print_string_stdout(slop_string s) {
    {
        __auto_type len = ((int64_t)(s.len));
        __auto_type data = s.data;
        __auto_type i = 0;
        while ((i < len)) {
            putchar(((int64_t)(data[i])));
            i = (i + 1);
        }
    }
}

void context_print_string_stderr(slop_string s) {
    {
        __auto_type len = ((int64_t)(s.len));
        __auto_type data = s.data;
        __auto_type i = 0;
        while ((i < len)) {
            slop_eputc(((int64_t)(data[i])));
            i = (i + 1);
        }
    }
}

void context_ctx_set_file(context_TranspileContext* ctx, slop_string filename) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    (*ctx).current_file = filename;
}

void context_ctx_add_error(context_TranspileContext* ctx, slop_string message) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    ({ __auto_type _lst_p = &((*ctx).errors); __auto_type _item = ((context_TranspileError){message, 0, 0}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

void context_ctx_add_error_at(context_TranspileContext* ctx, slop_string message, int64_t line, int64_t col) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    ({ __auto_type _lst_p = &((*ctx).errors); __auto_type _item = ((context_TranspileError){message, line, col}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

uint8_t context_ctx_has_errors(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (((int64_t)(((*ctx).errors).len)) > 0);
}

slop_list_context_TranspileError context_ctx_get_errors(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).errors;
}

int64_t context_ctx_report_errors(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type errors = (*ctx).errors;
        __auto_type count = ((int64_t)((errors).len));
        __auto_type arena = (*ctx).arena;
        __auto_type current_file = (*ctx).current_file;
        __auto_type i = 0;
        while ((i < count)) {
            __auto_type _mv_48 = ({ __auto_type _lst = errors; size_t _idx = (size_t)i; slop_option_context_TranspileError _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_48.has_value) {
                __auto_type err = _mv_48.value;
                ((void)(({ __auto_type line = err.line; __auto_type col = err.col; ({ (((string_len(current_file) > 0)) ? ({ context_print_string_stderr(current_file); }) : ({ slop_eprint(((char*)(SLOP_STR("<unknown>").data))); })); slop_eputc(58); context_print_string_stderr(int_to_string(arena, line)); slop_eputc(58); context_print_string_stderr(int_to_string(arena, col)); slop_eprint(((char*)(SLOP_STR(": error: ").data))); context_print_string_stderr(err.message); slop_eputc(10); }); })));
            } else if (!_mv_48.has_value) {
            }
            i = (i + 1);
        }
        return ((int64_t)(count));
    }
}

int64_t context_ctx_sexpr_line(types_SExpr* expr) {
    if ((expr == NULL)) {
        return 0;
    } else {
        __auto_type _mv_49 = (*expr);
        switch (_mv_49.tag) {
            case types_SExpr_sym:
            {
                __auto_type s = _mv_49.data.sym;
                return ((int64_t)(s.line));
            }
            case types_SExpr_str:
            {
                __auto_type s = _mv_49.data.str;
                return ((int64_t)(s.line));
            }
            case types_SExpr_num:
            {
                __auto_type n = _mv_49.data.num;
                return ((int64_t)(n.line));
            }
            case types_SExpr_lst:
            {
                __auto_type l = _mv_49.data.lst;
                return ((int64_t)(l.line));
            }
        }
    }
}

int64_t context_ctx_sexpr_col(types_SExpr* expr) {
    if ((expr == NULL)) {
        return 0;
    } else {
        __auto_type _mv_50 = (*expr);
        switch (_mv_50.tag) {
            case types_SExpr_sym:
            {
                __auto_type s = _mv_50.data.sym;
                return ((int64_t)(s.col));
            }
            case types_SExpr_str:
            {
                __auto_type s = _mv_50.data.str;
                return ((int64_t)(s.col));
            }
            case types_SExpr_num:
            {
                __auto_type n = _mv_50.data.num;
                return ((int64_t)(n.col));
            }
            case types_SExpr_lst:
            {
                __auto_type l = _mv_50.data.lst;
                return ((int64_t)(l.col));
            }
        }
    }
}

int64_t context_ctx_list_first_line(slop_list_types_SExpr_ptr items) {
    __auto_type _mv_51 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
    if (_mv_51.has_value) {
        __auto_type first_expr = _mv_51.value;
        return context_ctx_sexpr_line(first_expr);
    } else if (!_mv_51.has_value) {
        return 0;
    }
}

int64_t context_ctx_list_first_col(slop_list_types_SExpr_ptr items) {
    __auto_type _mv_52 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
    if (_mv_52.has_value) {
        __auto_type first_expr = _mv_52.value;
        return context_ctx_sexpr_col(first_expr);
    } else if (!_mv_52.has_value) {
        return 0;
    }
}

void context_ctx_push_scope(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type new_scope = ((context_Scope*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 64); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        __auto_type current = (*ctx).scope;
        slop_option_context_Scope_ptr parent_opt = (slop_option_context_Scope_ptr){.has_value = 1, .value = current};
        (*new_scope).vars = ((slop_list_context_VarEntry){ .data = (context_VarEntry*)slop_arena_alloc(arena, 16 * sizeof(context_VarEntry)), .len = 0, .cap = 16 });
        (*new_scope).parent = parent_opt;
        (*ctx).scope = new_scope;
    }
}

void context_ctx_pop_scope(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    __auto_type _mv_53 = (*(*ctx).scope).parent;
    if (_mv_53.has_value) {
        __auto_type parent_scope = _mv_53.value;
        (*ctx).scope = parent_scope;
    } else if (!_mv_53.has_value) {
    }
}

void context_ctx_bind_var(context_TranspileContext* ctx, context_VarEntry entry) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type scope = (*ctx).scope;
        ({ __auto_type _lst_p = &((*scope).vars); __auto_type _item = (entry); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
        if (entry.is_pointer) {
            ({ __auto_type _lst_p = &((*ctx).pointer_vars); __auto_type _item = (entry.name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
        }
    }
}

slop_option_context_VarEntry context_lookup_in_scope(context_Scope* scope, slop_string name) {
    if ((scope == NULL)) {
        return (slop_option_context_VarEntry){.has_value = false};
    } else {
        {
            __auto_type len = ((int64_t)(((*scope).vars).len));
            __auto_type i = 0;
            slop_option_context_VarEntry result = (slop_option_context_VarEntry){.has_value = false};
            while (((i < len) && ({ __auto_type _mv = result; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); }))) {
                __auto_type _mv_54 = ({ __auto_type _lst = (*scope).vars; size_t _idx = (size_t)i; slop_option_context_VarEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_54.has_value) {
                    __auto_type entry = _mv_54.value;
                    if (string_eq(entry.name, name)) {
                        result = (slop_option_context_VarEntry){.has_value = 1, .value = entry};
                    }
                } else if (!_mv_54.has_value) {
                }
                i = (i + 1);
            }
            return result;
        }
    }
}

slop_option_context_VarEntry context_ctx_lookup_var(context_TranspileContext* ctx, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return context_lookup_var_in_scope_chain((*ctx).scope, name);
}

slop_option_context_VarEntry context_lookup_var_in_scope_chain(context_Scope* scope, slop_string name) {
    if ((scope == NULL)) {
        return (slop_option_context_VarEntry){.has_value = false};
    } else {
        {
            __auto_type result = context_lookup_in_scope(scope, name);
            __auto_type _mv_55 = result;
            if (_mv_55.has_value) {
                __auto_type _ = _mv_55.value;
                return result;
            } else if (!_mv_55.has_value) {
                __auto_type _mv_56 = (*scope).parent;
                if (_mv_56.has_value) {
                    __auto_type parent_scope = _mv_56.value;
                    return context_lookup_var_in_scope_chain(parent_scope, name);
                } else if (!_mv_56.has_value) {
                    return (slop_option_context_VarEntry){.has_value = false};
                }
            }
        }
    }
}

void context_ctx_register_type(context_TranspileContext* ctx, context_TypeEntry entry) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    ({ __auto_type _lst_p = &((*ctx).types); __auto_type _item = (entry); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_option_context_TypeEntry context_ctx_lookup_type(context_TranspileContext* ctx, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type types = (*ctx).types;
        __auto_type len = ((int64_t)((types).len));
        slop_option_context_TypeEntry result = (slop_option_context_TypeEntry){.has_value = false};
        if ((len > 0)) {
            {
                __auto_type i = (((int64_t)(len)) - 1);
                while (((i >= 0) && ({ __auto_type _mv = result; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); }))) {
                    __auto_type _mv_57 = ({ __auto_type _lst = types; size_t _idx = (size_t)((int64_t)(i)); slop_option_context_TypeEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_57.has_value) {
                        __auto_type entry = _mv_57.value;
                        if (string_eq(entry.name, name)) {
                            result = (slop_option_context_TypeEntry){.has_value = 1, .value = entry};
                        }
                    } else if (!_mv_57.has_value) {
                    }
                    i = (i - 1);
                }
            }
        }
        return result;
    }
}

void context_ctx_register_func(context_TranspileContext* ctx, context_FuncEntry entry) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    ({ __auto_type _lst_p = &((*ctx).funcs); __auto_type _item = (entry); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_option_context_FuncEntry context_ctx_lookup_func(context_TranspileContext* ctx, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type funcs = (*ctx).funcs;
        __auto_type len = ((int64_t)((funcs).len));
        __auto_type i = (len - 1);
        slop_option_context_FuncEntry result = (slop_option_context_FuncEntry){.has_value = false};
        while (((i >= 0) && ({ __auto_type _mv = result; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); }))) {
            __auto_type _mv_58 = ({ __auto_type _lst = funcs; size_t _idx = (size_t)i; slop_option_context_FuncEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_58.has_value) {
                __auto_type entry = _mv_58.value;
                if (string_eq(entry.name, name)) {
                    result = (slop_option_context_FuncEntry){.has_value = 1, .value = entry};
                }
            } else if (!_mv_58.has_value) {
            }
            i = (i - 1);
        }
        return result;
    }
}

void context_ctx_register_field_type(context_TranspileContext* ctx, slop_string type_name, slop_string field_name, slop_string c_type, slop_string slop_type, uint8_t is_pointer) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    ({ __auto_type _lst_p = &((*ctx).field_types); __auto_type _item = ((context_FieldEntry){type_name, field_name, c_type, slop_type, is_pointer}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_option_string context_ctx_lookup_field_type(context_TranspileContext* ctx, slop_string type_name, slop_string field_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type fields = (*ctx).field_types;
        __auto_type len = ((int64_t)((fields).len));
        __auto_type i = 0;
        slop_option_string result = (slop_option_string){.has_value = false};
        while (((i < len) && ({ __auto_type _mv = result; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); }))) {
            __auto_type _mv_59 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_context_FieldEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_59.has_value) {
                __auto_type entry = _mv_59.value;
                if ((string_eq(entry.type_name, type_name) && string_eq(entry.field_name, field_name))) {
                    result = (slop_option_string){.has_value = 1, .value = entry.c_type};
                }
            } else if (!_mv_59.has_value) {
            }
            i = (i + 1);
        }
        if (({ __auto_type _mv = result; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); })) {
            {
                __auto_type stripped = context_strip_module_prefix(arena, type_name);
                if (!(string_eq(stripped, type_name))) {
                    i = 0;
                    while (((i < len) && ({ __auto_type _mv = result; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); }))) {
                        __auto_type _mv_60 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_context_FieldEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_60.has_value) {
                            __auto_type entry = _mv_60.value;
                            if ((string_eq(entry.type_name, stripped) && string_eq(entry.field_name, field_name))) {
                                result = (slop_option_string){.has_value = 1, .value = entry.c_type};
                            }
                        } else if (!_mv_60.has_value) {
                        }
                        i = (i + 1);
                    }
                }
            }
        }
        return result;
    }
}

slop_string context_strip_module_prefix(slop_arena* arena, slop_string type_name) {
    __auto_type _mv_61 = strlib_index_of(type_name, SLOP_STR("_"));
    if (_mv_61.has_value) {
        __auto_type pos = _mv_61.value;
        {
            __auto_type start = (((int64_t)(pos)) + 1);
            __auto_type len = (string_len(type_name) - start);
            if ((len > 0)) {
                return strlib_substring(arena, type_name, ((int64_t)(start)), ((int64_t)(len)));
            } else {
                return type_name;
            }
        }
    } else if (!_mv_61.has_value) {
        return type_name;
    }
}

slop_option_string context_ctx_lookup_field_slop_type(context_TranspileContext* ctx, slop_string type_name, slop_string field_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type fields = (*ctx).field_types;
        __auto_type len = ((int64_t)((fields).len));
        __auto_type i = 0;
        slop_option_string result = (slop_option_string){.has_value = false};
        while (((i < len) && ({ __auto_type _mv = result; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); }))) {
            __auto_type _mv_62 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_context_FieldEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_62.has_value) {
                __auto_type entry = _mv_62.value;
                if ((string_eq(entry.type_name, type_name) && string_eq(entry.field_name, field_name))) {
                    result = (slop_option_string){.has_value = 1, .value = entry.slop_type};
                }
            } else if (!_mv_62.has_value) {
            }
            i = (i + 1);
        }
        if (({ __auto_type _mv = result; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); })) {
            {
                __auto_type stripped = context_strip_module_prefix(arena, type_name);
                if (!(string_eq(stripped, type_name))) {
                    i = 0;
                    while (((i < len) && ({ __auto_type _mv = result; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); }))) {
                        __auto_type _mv_63 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_context_FieldEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_63.has_value) {
                            __auto_type entry = _mv_63.value;
                            if ((string_eq(entry.type_name, stripped) && string_eq(entry.field_name, field_name))) {
                                result = (slop_option_string){.has_value = 1, .value = entry.slop_type};
                            }
                        } else if (!_mv_63.has_value) {
                        }
                        i = (i + 1);
                    }
                }
            }
        }
        return result;
    }
}

slop_option_string context_ctx_lookup_field_type_by_index(context_TranspileContext* ctx, slop_string type_name, int64_t index) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((index >= 0)), "(>= index 0)");
    {
        __auto_type fields = (*ctx).field_types;
        __auto_type len = ((int64_t)((fields).len));
        __auto_type field_idx = 0;
        __auto_type i = 0;
        slop_option_string result = (slop_option_string){.has_value = false};
        while (((i < len) && ({ __auto_type _mv = result; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); }))) {
            __auto_type _mv_64 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_context_FieldEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_64.has_value) {
                __auto_type entry = _mv_64.value;
                if (string_eq(entry.type_name, type_name)) {
                    if ((field_idx == index)) {
                        result = (slop_option_string){.has_value = 1, .value = entry.c_type};
                    } else {
                        field_idx = (field_idx + 1);
                    }
                }
            } else if (!_mv_64.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_list_context_FieldEntry context_ctx_get_fields_for_type(context_TranspileContext* ctx, slop_string type_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type all_fields = (*ctx).field_types;
        __auto_type result = ((slop_list_context_FieldEntry){ .data = (context_FieldEntry*)slop_arena_alloc(arena, 16 * sizeof(context_FieldEntry)), .len = 0, .cap = 16 });
        __auto_type len = ((int64_t)((all_fields).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_65 = ({ __auto_type _lst = all_fields; size_t _idx = (size_t)i; slop_option_context_FieldEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_65.has_value) {
                __auto_type entry = _mv_65.value;
                if (string_eq(entry.type_name, type_name)) {
                    ({ __auto_type _lst_p = &(result); __auto_type _item = (entry); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                }
            } else if (!_mv_65.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

void context_ctx_mark_pointer_var(context_TranspileContext* ctx, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    ({ __auto_type _lst_p = &((*ctx).pointer_vars); __auto_type _item = (name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

uint8_t context_ctx_is_pointer_var(context_TranspileContext* ctx, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type vars = (*ctx).pointer_vars;
        __auto_type len = ((int64_t)((vars).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_66 = ({ __auto_type _lst = vars; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_66.has_value) {
                __auto_type v = _mv_66.value;
                if (string_eq(v, name)) {
                    found = 1;
                }
            } else if (!_mv_66.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

void context_ctx_set_module(context_TranspileContext* ctx, slop_option_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    (*ctx).current_module = name;
}

slop_option_string context_ctx_get_module(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).current_module;
}

void context_ctx_set_prefixing(context_TranspileContext* ctx, uint8_t enabled) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    (*ctx).enable_prefixing = enabled;
}

uint8_t context_ctx_prefixing_enabled(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).enable_prefixing;
}

slop_string context_ctx_prefix_type(context_TranspileContext* ctx, slop_string type_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (context_ctx_prefixing_enabled(ctx)) {
            __auto_type _mv_67 = context_ctx_get_module(ctx);
            if (_mv_67.has_value) {
                __auto_type mod_name = _mv_67.value;
                {
                    __auto_type c_mod_name = ctype_to_c_name(arena, mod_name);
                    return context_ctx_str(ctx, c_mod_name, context_ctx_str(ctx, SLOP_STR("_"), type_name));
                }
            } else if (!_mv_67.has_value) {
                return type_name;
            }
        } else {
            return type_name;
        }
    }
}

void context_ctx_add_include(context_TranspileContext* ctx, slop_string header) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)(((*ctx).includes).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_68 = ({ __auto_type _lst = (*ctx).includes; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_68.has_value) {
                __auto_type h = _mv_68.value;
                if (string_eq(h, header)) {
                    found = 1;
                }
            } else if (!_mv_68.has_value) {
            }
            i = (i + 1);
        }
        if (!(found)) {
            ({ __auto_type _lst_p = &((*ctx).includes); __auto_type _item = (header); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
        }
    }
}

slop_list_string context_ctx_get_includes(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).includes;
}

void context_ctx_mark_type_emitted(context_TranspileContext* ctx, slop_string type_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    ({ __auto_type _lst_p = &((*ctx).emitted_types); __auto_type _item = (type_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

uint8_t context_ctx_is_type_emitted(context_TranspileContext* ctx, slop_string type_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type types = (*ctx).emitted_types;
        __auto_type len = ((int64_t)((types).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_69 = ({ __auto_type _lst = types; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_69.has_value) {
                __auto_type t = _mv_69.value;
                if (string_eq(t, type_name)) {
                    found = 1;
                }
            } else if (!_mv_69.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

void context_ctx_register_enum_variant(context_TranspileContext* ctx, slop_string variant_name, slop_string enum_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    ({ __auto_type _lst_p = &((*ctx).enum_variants); __auto_type _item = ((context_EnumVariant){variant_name, enum_name}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_option_string context_ctx_lookup_enum_variant(context_TranspileContext* ctx, slop_string variant_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type variants = (*ctx).enum_variants;
        __auto_type len = ((int64_t)((variants).len));
        __auto_type i = 0;
        slop_option_string result = (slop_option_string){.has_value = false};
        while (((i < len) && ({ __auto_type _mv = result; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); }))) {
            __auto_type _mv_70 = ({ __auto_type _lst = variants; size_t _idx = (size_t)i; slop_option_context_EnumVariant _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_70.has_value) {
                __auto_type entry = _mv_70.value;
                if (string_eq(entry.variant_name, variant_name)) {
                    result = (slop_option_string){.has_value = 1, .value = entry.enum_name};
                }
            } else if (!_mv_70.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

void context_ctx_register_union_variant(context_TranspileContext* ctx, slop_string variant_name, slop_string union_name, slop_string c_variant_name, slop_string slop_type, slop_string c_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    ({ __auto_type _lst_p = &((*ctx).union_variants); __auto_type _item = ((context_UnionVariantEntry){variant_name, union_name, c_variant_name, slop_type, c_type}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_list_context_UnionVariantEntry context_ctx_get_union_variants(context_TranspileContext* ctx, slop_string union_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type all_variants = (*ctx).union_variants;
        __auto_type result = ((slop_list_context_UnionVariantEntry){ .data = (context_UnionVariantEntry*)slop_arena_alloc(arena, 16 * sizeof(context_UnionVariantEntry)), .len = 0, .cap = 16 });
        __auto_type len = ((int64_t)((all_variants).len));
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_71 = ({ __auto_type _lst = all_variants; size_t _idx = (size_t)i; slop_option_context_UnionVariantEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_71.has_value) {
                __auto_type entry = _mv_71.value;
                if (string_eq(entry.union_name, union_name)) {
                    ({ __auto_type _lst_p = &(result); __auto_type _item = (entry); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                }
            } else if (!_mv_71.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

void context_ctx_register_result_type(context_TranspileContext* ctx, slop_string ok_type, slop_string err_type, slop_string c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (!(context_ctx_has_result_type(ctx, c_name))) {
        ({ __auto_type _lst_p = &((*ctx).result_types); __auto_type _item = ((context_ResultType){ok_type, err_type, c_name}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
    }
}

uint8_t context_ctx_has_result_type(context_TranspileContext* ctx, slop_string c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type types = (*ctx).result_types;
        __auto_type len = ((int64_t)((types).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_72 = ({ __auto_type _lst = types; size_t _idx = (size_t)i; slop_option_context_ResultType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_72.has_value) {
                __auto_type entry = _mv_72.value;
                if (string_eq(entry.c_name, c_name)) {
                    found = 1;
                }
            } else if (!_mv_72.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

slop_list_context_ResultType context_ctx_get_result_types(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).result_types;
}

void context_ctx_set_current_result_type(context_TranspileContext* ctx, slop_string result_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        slop_option_string opt = (slop_option_string){.has_value = 1, .value = result_type};
        (*ctx).current_result_type = opt;
    }
}

slop_option_string context_ctx_get_current_result_type(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).current_result_type;
}

void context_ctx_clear_current_result_type(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    (*ctx).current_result_type = (slop_option_string){.has_value = false};
}

void context_ctx_set_current_return_type(context_TranspileContext* ctx, slop_string c_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        slop_option_string opt = (slop_option_string){.has_value = 1, .value = c_type};
        (*ctx).current_return_c_type = opt;
    }
}

slop_option_string context_ctx_get_current_return_type(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).current_return_c_type;
}

void context_ctx_clear_current_return_type(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    (*ctx).current_return_c_type = (slop_option_string){.has_value = false};
}

void context_ctx_set_capture_retval(context_TranspileContext* ctx, uint8_t enabled) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    (*ctx).capture_to_retval = enabled;
}

uint8_t context_ctx_is_capture_retval(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).capture_to_retval;
}

void context_ctx_register_option_type(context_TranspileContext* ctx, slop_string inner_type, slop_string c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (!(context_ctx_has_option_type(ctx, c_name))) {
        ({ __auto_type _lst_p = &((*ctx).option_types); __auto_type _item = ((context_OptionType){inner_type, c_name}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
    }
}

uint8_t context_ctx_has_option_type(context_TranspileContext* ctx, slop_string c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type types = (*ctx).option_types;
        __auto_type len = ((int64_t)((types).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_73 = ({ __auto_type _lst = types; size_t _idx = (size_t)i; slop_option_context_OptionType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_73.has_value) {
                __auto_type entry = _mv_73.value;
                if (string_eq(entry.c_name, c_name)) {
                    found = 1;
                }
            } else if (!_mv_73.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

slop_list_context_OptionType context_ctx_get_option_types(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).option_types;
}

void context_ctx_register_list_type(context_TranspileContext* ctx, slop_string elem_type, slop_string c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (!(context_ctx_has_list_type(ctx, c_name))) {
        ({ __auto_type _lst_p = &((*ctx).list_types); __auto_type _item = ((context_ListType){elem_type, c_name}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
    }
}

uint8_t context_ctx_has_list_type(context_TranspileContext* ctx, slop_string c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type types = (*ctx).list_types;
        __auto_type len = ((int64_t)((types).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_74 = ({ __auto_type _lst = types; size_t _idx = (size_t)i; slop_option_context_ListType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_74.has_value) {
                __auto_type entry = _mv_74.value;
                if (string_eq(entry.c_name, c_name)) {
                    found = 1;
                }
            } else if (!_mv_74.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

slop_list_context_ListType context_ctx_get_list_types(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).list_types;
}

void context_ctx_register_chan_type(context_TranspileContext* ctx, slop_string elem_type, slop_string c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (!(context_ctx_has_chan_type(ctx, c_name))) {
        ({ __auto_type _lst_p = &((*ctx).chan_types); __auto_type _item = ((context_ChanType){elem_type, c_name}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
    }
}

uint8_t context_ctx_has_chan_type(context_TranspileContext* ctx, slop_string c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type types = (*ctx).chan_types;
        __auto_type len = ((int64_t)((types).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_75 = ({ __auto_type _lst = types; size_t _idx = (size_t)i; slop_option_context_ChanType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_75.has_value) {
                __auto_type entry = _mv_75.value;
                if (string_eq(entry.c_name, c_name)) {
                    found = 1;
                }
            } else if (!_mv_75.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

slop_list_context_ChanType context_ctx_get_chan_types(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).chan_types;
}

void context_ctx_register_thread_type(context_TranspileContext* ctx, slop_string result_type, slop_string c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (!(context_ctx_has_thread_type(ctx, c_name))) {
        ({ __auto_type _lst_p = &((*ctx).thread_types); __auto_type _item = ((context_ThreadType){result_type, c_name}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
    }
}

uint8_t context_ctx_has_thread_type(context_TranspileContext* ctx, slop_string c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type types = (*ctx).thread_types;
        __auto_type len = ((int64_t)((types).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_76 = ({ __auto_type _lst = types; size_t _idx = (size_t)i; slop_option_context_ThreadType _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_76.has_value) {
                __auto_type entry = _mv_76.value;
                if (string_eq(entry.c_name, c_name)) {
                    found = 1;
                }
            } else if (!_mv_76.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

slop_list_context_ThreadType context_ctx_get_thread_types(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).thread_types;
}

void context_ctx_register_result_type_alias(context_TranspileContext* ctx, slop_string alias_name, slop_string c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    ({ __auto_type _lst_p = &((*ctx).result_type_aliases); __auto_type _item = ((context_ResultTypeAlias){alias_name, c_name}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_option_string context_ctx_lookup_result_type_alias(context_TranspileContext* ctx, slop_string alias_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type aliases = (*ctx).result_type_aliases;
        __auto_type len = ((int64_t)((aliases).len));
        __auto_type i = 0;
        slop_option_string result = (slop_option_string){.has_value = false};
        while (((i < len) && ({ __auto_type _mv = result; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); }))) {
            __auto_type _mv_77 = ({ __auto_type _lst = aliases; size_t _idx = (size_t)i; slop_option_context_ResultTypeAlias _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_77.has_value) {
                __auto_type entry = _mv_77.value;
                if (string_eq(entry.alias_name, alias_name)) {
                    result = (slop_option_string){.has_value = 1, .value = entry.c_name};
                }
            } else if (!_mv_77.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

void context_ctx_add_c_name_alias(context_TranspileContext* ctx, context_FuncCNameAlias alias) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    ({ __auto_type _lst_p = &((*ctx).c_name_aliases); __auto_type _item = (alias); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_list_context_FuncCNameAlias context_ctx_get_c_name_aliases(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).c_name_aliases;
}

slop_string context_extract_fn_c_name(slop_arena* arena, slop_list_types_SExpr_ptr items, slop_string default_name) {
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 3;
        __auto_type found_c_name = 0;
        __auto_type c_name = SLOP_STR("");
        while ((i < len)) {
            __auto_type _mv_78 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_78.has_value) {
                __auto_type item_expr = _mv_78.value;
                __auto_type _mv_79 = (*item_expr);
                switch (_mv_79.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_79.data.sym;
                        if (string_eq(sym.name, SLOP_STR(":c-name"))) {
                            __auto_type _mv_80 = ({ __auto_type _lst = items; size_t _idx = (size_t)(i + 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_80.has_value) {
                                __auto_type c_name_expr = _mv_80.value;
                                __auto_type _mv_81 = (*c_name_expr);
                                switch (_mv_81.tag) {
                                    case types_SExpr_str:
                                    {
                                        __auto_type str = _mv_81.data.str;
                                        c_name = str.value;
                                        found_c_name = 1;
                                        break;
                                    }
                                    default: {
                                        break;
                                    }
                                }
                            } else if (!_mv_80.has_value) {
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_78.has_value) {
            }
            i = (i + 1);
        }
        if (found_c_name) {
            return c_name;
        } else {
            return default_name;
        }
    }
}

slop_string context_ctx_str(context_TranspileContext* ctx, slop_string a, slop_string b) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return string_concat((*ctx).arena, a, b);
}

slop_string context_ctx_str3(context_TranspileContext* ctx, slop_string a, slop_string b, slop_string c) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        return string_concat(arena, string_concat(arena, a, b), c);
    }
}

slop_string context_ctx_str4(context_TranspileContext* ctx, slop_string a, slop_string b, slop_string c, slop_string d) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        return string_concat(arena, string_concat(arena, string_concat(arena, a, b), c), d);
    }
}

slop_string context_ctx_str5(context_TranspileContext* ctx, slop_string a, slop_string b, slop_string c, slop_string d, slop_string e) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        return string_concat(arena, string_concat(arena, string_concat(arena, string_concat(arena, a, b), c), d), e);
    }
}

void context_ctx_add_import(context_TranspileContext* ctx, slop_string mod_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type imports = (*ctx).imported_modules;
        __auto_type len = ((int64_t)((imports).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_82 = ({ __auto_type _lst = imports; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_82.has_value) {
                __auto_type m = _mv_82.value;
                if (string_eq(m, mod_name)) {
                    found = 1;
                }
            } else if (!_mv_82.has_value) {
            }
            i = (i + 1);
        }
        if (!(found)) {
            ({ __auto_type _lst_p = &((*ctx).imported_modules); __auto_type _item = (mod_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
        }
    }
}

slop_list_string context_ctx_get_imports(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).imported_modules;
}

void context_ctx_register_inline_record(context_TranspileContext* ctx, slop_string type_name, slop_string field_body) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type records = (*ctx).inline_records;
        __auto_type len = ((int64_t)((records).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_83 = ({ __auto_type _lst = records; size_t _idx = (size_t)i; slop_option_context_InlineRecord _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_83.has_value) {
                __auto_type r = _mv_83.value;
                if (string_eq(r.type_name, type_name)) {
                    found = 1;
                }
            } else if (!_mv_83.has_value) {
            }
            i = (i + 1);
        }
        if (!(found)) {
            ({ __auto_type _lst_p = &((*ctx).inline_records); __auto_type _item = ((context_InlineRecord){type_name, field_body}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
        }
    }
}

slop_list_context_InlineRecord context_ctx_get_inline_records(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).inline_records;
}

slop_string context_simple_hash(slop_arena* arena, slop_string s) {
    {
        __auto_type hash = 5381;
        __auto_type len = ((int64_t)(string_len(s)));
        __auto_type i = 0;
        while ((i < len)) {
            {
                __auto_type c = ((int64_t)(s.data[i]));
                hash = ((hash * 33) + c);
            }
            i = (i + 1);
        }
        {
            __auto_type positive_hash = ((((hash < 0)) ? (0 - hash) : hash) % 999999999);
            return int_to_string(arena, positive_hash);
        }
    }
}

slop_string context_to_c_type_prefixed(context_TranspileContext* ctx, types_SExpr* type_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_84 = (*type_expr);
        switch (_mv_84.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_84.data.sym;
                {
                    __auto_type name = sym.name;
                    __auto_type base_c_type = ctype_to_c_type(arena, type_expr);
                    if (ctype_is_builtin_c_type(base_c_type)) {
                        return base_c_type;
                    } else {
                        __auto_type _mv_85 = context_ctx_lookup_type(ctx, name);
                        if (_mv_85.has_value) {
                            __auto_type entry = _mv_85.value;
                            return entry.c_name;
                        } else if (!_mv_85.has_value) {
                            return context_ctx_prefix_type(ctx, base_c_type);
                        }
                    }
                }
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_84.data.lst;
                return context_to_c_type_prefixed_compound(ctx, lst.items);
            }
            case types_SExpr_str:
            {
                __auto_type _ = _mv_84.data.str;
                return SLOP_STR("void*");
            }
            case types_SExpr_num:
            {
                __auto_type _ = _mv_84.data.num;
                return SLOP_STR("void*");
            }
        }
    }
}

slop_option_string context_get_array_pointer_type(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_86 = (*expr);
    switch (_mv_86.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_86.data.sym;
            {
                __auto_type type_name = sym.name;
                __auto_type _mv_87 = context_ctx_lookup_type(ctx, type_name);
                if (_mv_87.has_value) {
                    __auto_type entry = _mv_87.value;
                    {
                        __auto_type c_name = entry.c_name;
                        __auto_type c_type = entry.c_type;
                        if ((context_ends_with_star(c_type) && !(string_eq(c_type, context_string_concat_ctx(ctx, c_name, SLOP_STR("*")))))) {
                            return (slop_option_string){.has_value = 1, .value = c_type};
                        } else {
                            return (slop_option_string){.has_value = false};
                        }
                    }
                } else if (!_mv_87.has_value) {
                    return (slop_option_string){.has_value = false};
                }
            }
        }
        default: {
            return (slop_option_string){.has_value = false};
        }
    }
}

uint8_t context_ends_with_star(slop_string s) {
    {
        __auto_type len = string_len(s);
        if ((len < 1)) {
            return 0;
        } else {
            return (s.data[(((int64_t)(len)) - 1)] == 42);
        }
    }
}

slop_string context_string_concat_ctx(context_TranspileContext* ctx, slop_string a, slop_string b) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        return string_concat(arena, a, b);
    }
}

slop_string context_to_c_type_prefixed_compound(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result = SLOP_STR("void*");
        if ((len >= 1)) {
            __auto_type _mv_88 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_88.has_value) {
                __auto_type first_expr = _mv_88.value;
                __auto_type _mv_89 = (*first_expr);
                switch (_mv_89.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type head_sym = _mv_89.data.sym;
                        {
                            __auto_type head = head_sym.name;
                            if (string_eq(head, SLOP_STR("Ptr"))) {
                                if ((len >= 2)) {
                                    __auto_type _mv_90 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_90.has_value) {
                                        __auto_type inner = _mv_90.value;
                                        __auto_type _mv_91 = context_get_array_pointer_type(ctx, inner);
                                        if (_mv_91.has_value) {
                                            __auto_type ptr_type = _mv_91.value;
                                            result = ptr_type;
                                        } else if (!_mv_91.has_value) {
                                            result = context_ctx_str(ctx, context_to_c_type_prefixed(ctx, inner), SLOP_STR("*"));
                                        }
                                    } else if (!_mv_90.has_value) {
                                    }
                                } else {
                                }
                            } else if (string_eq(head, SLOP_STR("ScopedPtr"))) {
                                if ((len >= 2)) {
                                    __auto_type _mv_92 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_92.has_value) {
                                        __auto_type inner = _mv_92.value;
                                        result = context_ctx_str(ctx, context_to_c_type_prefixed(ctx, inner), SLOP_STR("*"));
                                    } else if (!_mv_92.has_value) {
                                    }
                                } else {
                                }
                            } else if (string_eq(head, SLOP_STR("Option"))) {
                                result = SLOP_STR("__option_type_error__");
                                if ((len >= 2)) {
                                    __auto_type _mv_93 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_93.has_value) {
                                        __auto_type inner = _mv_93.value;
                                        {
                                            __auto_type inner_c = context_to_c_type_prefixed(ctx, inner);
                                            __auto_type inner_id = ctype_type_to_identifier(arena, inner_c);
                                            result = context_ctx_str(ctx, SLOP_STR("slop_option_"), inner_id);
                                        }
                                    } else if (!_mv_93.has_value) {
                                    }
                                }
                            } else if (string_eq(head, SLOP_STR("Result"))) {
                                {
                                    __auto_type ok_id = SLOP_STR("void");
                                    __auto_type err_id = SLOP_STR("slop_error");
                                    if ((len >= 2)) {
                                        __auto_type _mv_94 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_94.has_value) {
                                            __auto_type ok_expr = _mv_94.value;
                                            ok_id = ctype_type_to_identifier(arena, context_to_c_type_prefixed(ctx, ok_expr));
                                        } else if (!_mv_94.has_value) {
                                        }
                                    }
                                    if ((len >= 3)) {
                                        __auto_type _mv_95 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_95.has_value) {
                                            __auto_type err_expr = _mv_95.value;
                                            err_id = ctype_type_to_identifier(arena, context_to_c_type_prefixed(ctx, err_expr));
                                        } else if (!_mv_95.has_value) {
                                        }
                                    }
                                    result = context_ctx_str(ctx, context_ctx_str(ctx, SLOP_STR("slop_result_"), ok_id), context_ctx_str(ctx, SLOP_STR("_"), err_id));
                                }
                            } else if (string_eq(head, SLOP_STR("List"))) {
                                result = SLOP_STR("slop_list_void");
                                if ((len >= 2)) {
                                    __auto_type _mv_96 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_96.has_value) {
                                        __auto_type inner = _mv_96.value;
                                        {
                                            __auto_type inner_c = context_to_c_type_prefixed(ctx, inner);
                                            __auto_type inner_id = ctype_type_to_identifier(arena, inner_c);
                                            result = context_ctx_str(ctx, SLOP_STR("slop_list_"), inner_id);
                                        }
                                    } else if (!_mv_96.has_value) {
                                    }
                                }
                            } else if (string_eq(head, SLOP_STR("Map"))) {
                                result = SLOP_STR("slop_map*");
                            } else if (string_eq(head, SLOP_STR("Set"))) {
                                result = SLOP_STR("slop_map*");
                            } else if (string_eq(head, SLOP_STR("Array"))) {
                                if ((len >= 2)) {
                                    __auto_type _mv_97 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_97.has_value) {
                                        __auto_type inner = _mv_97.value;
                                        result = context_ctx_str(ctx, context_to_c_type_prefixed(ctx, inner), SLOP_STR("*"));
                                    } else if (!_mv_97.has_value) {
                                    }
                                }
                            } else if (string_eq(head, SLOP_STR("Chan"))) {
                                result = SLOP_STR("slop_chan_void");
                                if ((len >= 2)) {
                                    __auto_type _mv_98 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_98.has_value) {
                                        __auto_type inner = _mv_98.value;
                                        {
                                            __auto_type inner_c = context_to_c_type_prefixed(ctx, inner);
                                            __auto_type inner_id = ctype_type_to_identifier(arena, inner_c);
                                            result = context_ctx_str(ctx, SLOP_STR("slop_chan_"), inner_id);
                                        }
                                    } else if (!_mv_98.has_value) {
                                    }
                                }
                            } else if (string_eq(head, SLOP_STR("Thread"))) {
                                result = SLOP_STR("slop_thread_int");
                                if ((len >= 2)) {
                                    __auto_type _mv_99 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_99.has_value) {
                                        __auto_type inner = _mv_99.value;
                                        {
                                            __auto_type inner_c = context_to_c_type_prefixed(ctx, inner);
                                            if (string_eq(inner_c, SLOP_STR("void"))) {
                                                result = SLOP_STR("slop_thread_int");
                                            } else {
                                                {
                                                    __auto_type inner_id = ctype_type_to_identifier(arena, inner_c);
                                                    result = context_ctx_str(ctx, SLOP_STR("slop_thread_"), inner_id);
                                                }
                                            }
                                        }
                                    } else if (!_mv_99.has_value) {
                                    }
                                }
                            } else if (string_eq(head, SLOP_STR("record"))) {
                                {
                                    __auto_type field_str = SLOP_STR("");
                                    __auto_type i = 1;
                                    while ((i < len)) {
                                        __auto_type _mv_100 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_100.has_value) {
                                            __auto_type field_expr = _mv_100.value;
                                            __auto_type _mv_101 = (*field_expr);
                                            switch (_mv_101.tag) {
                                                case types_SExpr_lst:
                                                {
                                                    __auto_type field_lst = _mv_101.data.lst;
                                                    {
                                                        __auto_type field_items = field_lst.items;
                                                        if ((((int64_t)((field_items).len)) >= 2)) {
                                                            __auto_type _mv_102 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_102.has_value) {
                                                                __auto_type name_expr = _mv_102.value;
                                                                __auto_type _mv_103 = (*name_expr);
                                                                switch (_mv_103.tag) {
                                                                    case types_SExpr_sym:
                                                                    {
                                                                        __auto_type name_sym = _mv_103.data.sym;
                                                                        __auto_type _mv_104 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                        if (_mv_104.has_value) {
                                                                            __auto_type type_expr = _mv_104.value;
                                                                            {
                                                                                __auto_type field_name = ctype_to_c_name(arena, name_sym.name);
                                                                                __auto_type field_type = context_to_c_type_prefixed(ctx, type_expr);
                                                                                field_str = context_ctx_str(ctx, field_str, context_ctx_str(ctx, field_type, context_ctx_str(ctx, SLOP_STR(" "), context_ctx_str(ctx, field_name, SLOP_STR("; ")))));
                                                                            }
                                                                        } else if (!_mv_104.has_value) {
                                                                        }
                                                                        break;
                                                                    }
                                                                    default: {
                                                                        break;
                                                                    }
                                                                }
                                                            } else if (!_mv_102.has_value) {
                                                            }
                                                        }
                                                    }
                                                    break;
                                                }
                                                default: {
                                                    break;
                                                }
                                            }
                                        } else if (!_mv_100.has_value) {
                                        }
                                        i = (i + 1);
                                    }
                                    {
                                        __auto_type type_name = context_ctx_str(ctx, SLOP_STR("_anon_record_"), context_simple_hash(arena, field_str));
                                        context_ctx_register_inline_record(ctx, type_name, field_str);
                                        result = type_name;
                                    }
                                }
                            } else if (string_eq(head, SLOP_STR("Fn"))) {
                                result = SLOP_STR("slop_closure_t");
                            } else if (string_eq(head, SLOP_STR("Int"))) {
                                result = ctype_range_type_to_c_type(arena, items, len);
                            } else {
                                {
                                    __auto_type base_c_type = ctype_to_c_type(arena, first_expr);
                                    if (ctype_is_builtin_c_type(base_c_type)) {
                                        result = base_c_type;
                                    } else {
                                        __auto_type _mv_105 = context_ctx_lookup_type(ctx, head);
                                        if (_mv_105.has_value) {
                                            __auto_type entry = _mv_105.value;
                                            result = entry.c_name;
                                        } else if (!_mv_105.has_value) {
                                            result = context_ctx_prefix_type(ctx, base_c_type);
                                        }
                                    }
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_88.has_value) {
            }
        }
        return result;
    }
}

slop_string context_build_fn_args_str_prefixed(context_TranspileContext* ctx, types_SExpr* args_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_106 = (*args_expr);
        switch (_mv_106.tag) {
            case types_SExpr_lst:
            {
                __auto_type args_list = _mv_106.data.lst;
                {
                    __auto_type arg_items = args_list.items;
                    __auto_type arg_count = ((int64_t)((arg_items).len));
                    if ((arg_count == 0)) {
                        return SLOP_STR("(void)");
                    } else {
                        {
                            __auto_type result = SLOP_STR("(");
                            __auto_type i = 0;
                            while ((i < arg_count)) {
                                __auto_type _mv_107 = ({ __auto_type _lst = arg_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_107.has_value) {
                                    __auto_type arg_expr = _mv_107.value;
                                    {
                                        __auto_type arg_type = context_to_c_type_prefixed(ctx, arg_expr);
                                        if ((i > 0)) {
                                            result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR(", "), arg_type));
                                        } else {
                                            result = context_ctx_str(ctx, result, arg_type);
                                        }
                                    }
                                } else if (!_mv_107.has_value) {
                                    /* empty list */;
                                }
                                i = (i + 1);
                            }
                            return context_ctx_str(ctx, result, SLOP_STR(")"));
                        }
                    }
                }
            }
            default: {
                return SLOP_STR("(void)");
            }
        }
    }
}

slop_string context_ctx_gensym(context_TranspileContext* ctx, slop_string prefix) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type counter = (*ctx).gensym_counter;
        (*ctx).gensym_counter = (counter + 1);
        return context_ctx_str3(ctx, prefix, SLOP_STR("_"), int_to_string(arena, counter));
    }
}

void context_ctx_register_struct_key_type(context_TranspileContext* ctx, slop_string c_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type types = (*ctx).struct_key_types;
        __auto_type len = ((int64_t)((types).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_108 = ({ __auto_type _lst = types; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_108.has_value) {
                __auto_type existing = _mv_108.value;
                if (string_eq(existing, c_type)) {
                    found = 1;
                }
            } else if (!_mv_108.has_value) {
            }
            i = (i + 1);
        }
        if (!(found)) {
            ({ __auto_type _lst_p = &((*ctx).struct_key_types); __auto_type _item = (c_type); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
        }
    }
}

uint8_t context_ctx_has_struct_key_type(context_TranspileContext* ctx, slop_string c_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type types = (*ctx).struct_key_types;
        __auto_type len = ((int64_t)((types).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_109 = ({ __auto_type _lst = types; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_109.has_value) {
                __auto_type existing = _mv_109.value;
                if (string_eq(existing, c_type)) {
                    found = 1;
                }
            } else if (!_mv_109.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

slop_list_string context_ctx_get_struct_key_types(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).struct_key_types;
}

void context_ctx_register_type_alias(context_TranspileContext* ctx, slop_string name, slop_string slop_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    ({ __auto_type _lst_p = &((*ctx).type_aliases); __auto_type _item = ((context_TypeAliasEntry){name, slop_type}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_option_string context_ctx_lookup_type_alias(context_TranspileContext* ctx, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type aliases = (*ctx).type_aliases;
        __auto_type len = ((int64_t)((aliases).len));
        __auto_type i = 0;
        slop_option_string result = (slop_option_string){.has_value = false};
        while (((i < len) && ({ __auto_type _mv = result; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); }))) {
            __auto_type _mv_110 = ({ __auto_type _lst = aliases; size_t _idx = (size_t)i; slop_option_context_TypeAliasEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_110.has_value) {
                __auto_type entry = _mv_110.value;
                if (string_eq(entry.name, name)) {
                    result = (slop_option_string){.has_value = 1, .value = entry.slop_type};
                }
            } else if (!_mv_110.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

void context_ctx_add_deferred_lambda(context_TranspileContext* ctx, slop_string lambda_code) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    ({ __auto_type _lst_p = &((*ctx).deferred_lambdas); __auto_type _item = (lambda_code); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_list_string context_ctx_get_deferred_lambdas(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).deferred_lambdas;
}

void context_ctx_clear_deferred_lambdas(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        (*ctx).deferred_lambdas = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
    }
}

void context_ctx_set_last_lambda_info(context_TranspileContext* ctx, uint8_t is_closure, slop_string env_type, slop_string lambda_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    (*ctx).last_lambda_is_closure = is_closure;
    (*ctx).last_lambda_env_type = env_type;
    (*ctx).last_lambda_name = lambda_name;
}

context_LastLambdaInfo context_ctx_get_last_lambda_info(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (context_LastLambdaInfo){(*ctx).last_lambda_is_closure, (*ctx).last_lambda_env_type, (*ctx).last_lambda_name};
}

void context_ctx_clear_last_lambda_info(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    (*ctx).last_lambda_is_closure = 0;
    (*ctx).last_lambda_env_type = SLOP_STR("");
    (*ctx).last_lambda_name = SLOP_STR("");
}

void context_ctx_start_function_buffer(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    (*ctx).emit_to_function_buffer = 1;
}

void context_ctx_stop_function_buffer(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    (*ctx).emit_to_function_buffer = 0;
}

void context_ctx_flush_function_buffer(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type fn_output = (*ctx).function_output;
        __auto_type count = ((int64_t)((fn_output).len));
        __auto_type i = 0;
        while ((i < count)) {
            __auto_type _mv_111 = ({ __auto_type _lst = fn_output; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_111.has_value) {
                __auto_type line = _mv_111.value;
                ({ __auto_type _lst_p = &((*ctx).output); __auto_type _item = (line); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            } else if (!_mv_111.has_value) {
            }
            i = (i + 1);
        }
        {
            __auto_type arena = (*ctx).arena;
            (*ctx).function_output = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        }
    }
}

void context_ctx_register_generic_instantiation(context_TranspileContext* ctx, slop_string fn_name, slop_string type_bindings, slop_string c_name, slop_string module_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    ({ __auto_type _lst_p = &((*ctx).generic_func_instantiations); __auto_type _item = ((context_GenericFuncInstantiation){fn_name, type_bindings, c_name, module_name}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

uint8_t context_ctx_has_generic_instantiation(context_TranspileContext* ctx, slop_string fn_name, slop_string type_bindings) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type instances = (*ctx).generic_func_instantiations;
        __auto_type len = ((int64_t)((instances).len));
        __auto_type i = 0;
        __auto_type found = 0;
        while (((i < len) && !(found))) {
            __auto_type _mv_112 = ({ __auto_type _lst = instances; size_t _idx = (size_t)i; slop_option_context_GenericFuncInstantiation _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_112.has_value) {
                __auto_type inst = _mv_112.value;
                if ((string_eq(inst.fn_name, fn_name) && string_eq(inst.type_bindings, type_bindings))) {
                    found = 1;
                }
            } else if (!_mv_112.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

slop_list_context_GenericFuncInstantiation context_ctx_get_generic_instantiations(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (*ctx).generic_func_instantiations;
}

slop_string context_mangle_generic_fn_name(context_TranspileContext* ctx, slop_string base_c_name, slop_string type_binding) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return context_ctx_str3(ctx, base_c_name, SLOP_STR("_"), type_binding);
}

