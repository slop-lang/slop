#include "../runtime/slop_runtime.h"
#include "slop_expr.h"

slop_string expr_escape_c_string(context_TranspileContext* ctx, slop_string s);
slop_string expr_wrap_arena_alloc_checked(context_TranspileContext* ctx, slop_string alloc_expr);
uint8_t expr_is_binop(slop_string op);
uint8_t expr_is_comparison_op(slop_string op);
uint8_t expr_is_equality_op(slop_string op);
uint8_t expr_is_unop(slop_string op);
slop_option_string expr_extract_symbol_name(types_SExpr* expr);
slop_string expr_transpile_literal(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_transpile_symbol(context_TranspileContext* ctx, slop_string name);
slop_string expr_get_prefixed_enum_value(context_TranspileContext* ctx, slop_string enum_name, slop_string variant_name);
slop_string expr_binop_to_c(slop_string op);
slop_string expr_transpile_binop(context_TranspileContext* ctx, slop_string op, slop_string left, slop_string right);
uint8_t expr_is_aggregate_c_type(context_TranspileContext* ctx, slop_string c_type);
slop_string expr_record_container_field(context_TranspileContext* ctx, slop_string c_type);
slop_string expr_transpile_aggregate_eq(context_TranspileContext* ctx, slop_string op, slop_string left_c, slop_string right_c, slop_string c_type, types_SExpr* site);
slop_string expr_transpile_variadic_binop(context_TranspileContext* ctx, slop_string op, slop_list_types_SExpr_ptr items, int64_t start_idx);
slop_string expr_get_builtin_type_c_name(slop_string type_name);
uint8_t expr_is_pointer_type_expr(types_SExpr* type_expr);
uint8_t expr_is_string_literal(types_SExpr* expr);
uint8_t expr_is_fn_type_expr(types_SExpr* type_expr);
uint8_t expr_is_ptr_void_type(types_SExpr* type_expr);
uint8_t expr_is_closure_typed_expr(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_fn_type_to_c_fn_ptr(context_TranspileContext* ctx, types_SExpr* fn_expr);
slop_string expr_build_fn_ptr_args_from_list(context_TranspileContext* ctx, types_SExpr* args_expr);
slop_string expr_transpile_builtin_constructor(context_TranspileContext* ctx, slop_string type_name, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_call(context_TranspileContext* ctx, slop_string fn_name, slop_string args);
slop_string expr_emit_generic_closure_call(context_TranspileContext* ctx, slop_string var_c_name, slop_string slop_type, slop_string args);
slop_string expr_build_closure_fn_cast(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_fn_type_args_c(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
uint8_t expr_is_fn_type_shape(slop_list_types_SExpr_ptr items);
uint8_t expr_fn_type_arg_list_ok(slop_list_types_SExpr_ptr items);
slop_string expr_closure_cast_error(context_TranspileContext* ctx, slop_string slop_type, slop_string why);
types_SExpr* expr_parse_type_string(slop_arena* arena, slop_string s);
uint8_t expr_type_form_is_wrapped(slop_string s);
slop_list_string expr_split_top_level_types(slop_arena* arena, slop_string s);
uint8_t expr_type_token_is_number(slop_string s);
int64_t expr_type_token_to_int(slop_string s);
slop_string expr_get_base_function_name(slop_arena* arena, slop_string fn_name);
slop_string expr_get_module_from_qualified_name(slop_arena* arena, slop_string fn_name);
slop_string expr_get_runtime_function_name(slop_string fn_name);
slop_string expr_transpile_enum_variant(context_TranspileContext* ctx, slop_string variant_name);
slop_string expr_transpile_ok(context_TranspileContext* ctx, slop_string value_c);
slop_string expr_transpile_error(context_TranspileContext* ctx, slop_string value_c);
slop_string expr_infer_option_type(context_TranspileContext* ctx, types_SExpr* val_expr);
slop_string expr_c_type_to_option_type_name(context_TranspileContext* ctx, slop_string c_type);
slop_string expr_infer_field_c_type_from_items(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_infer_list_expr_option_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_strip_pointer_suffix(slop_arena* arena, slop_string s);
slop_string expr_extract_chan_elem_type(context_TranspileContext* ctx, slop_string chan_type);
slop_string expr_infer_list_element_option_type(context_TranspileContext* ctx, types_SExpr* list_expr);
slop_string expr_infer_list_element_option_type_fallback(context_TranspileContext* ctx, types_SExpr* list_expr);
slop_string expr_infer_field_access_list_type(context_TranspileContext* ctx, types_SExpr* field_expr);
slop_string expr_list_type_to_option_type(context_TranspileContext* ctx, slop_string c_type);
slop_string expr_prefix_list_element_type(context_TranspileContext* ctx, slop_string elem_type);
slop_string expr_substring_after_prefix(slop_arena* arena, slop_string s, slop_string prefix);
slop_string expr_extract_map_value_from_slop_type(slop_arena* arena, slop_string raw_slop_type);
slop_string expr_slop_value_type_to_c_type(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_get_var_name_from_expr(types_SExpr* expr);
slop_string expr_extract_map_key_from_slop_type(slop_arena* arena, slop_string raw_slop_type);
slop_string expr_resolve_type_alias(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_infer_expr_slop_type(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_infer_map_key_c_type_from_slop_type(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_infer_set_elem_c_type_from_slop_type(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_extract_map_value_from_inferred(context_TranspileContext* ctx, types_SExpr* map_expr);
slop_string expr_extract_list_elem_from_inferred(context_TranspileContext* ctx, types_SExpr* list_expr);
slop_string expr_infer_map_key_c_type(context_TranspileContext* ctx, types_SExpr* map_expr);
uint8_t expr_is_set_type(slop_string slop_type);
uint8_t expr_is_map_type(slop_string slop_type);
slop_string expr_extract_set_elem_from_slop_type(slop_arena* arena, slop_string raw_slop_type);
slop_string expr_infer_set_elem_c_type(context_TranspileContext* ctx, types_SExpr* set_expr);
slop_string expr_compound_slop_type_to_id(slop_arena* arena, slop_string slop_type);
slop_string expr_slop_value_type_to_option_id(slop_arena* arena, slop_string slop_type);
slop_string expr_infer_map_value_option_type(context_TranspileContext* ctx, types_SExpr* map_expr);
slop_string expr_option_type_to_value_c_type(slop_arena* arena, slop_string option_type);
slop_string expr_infer_option_inner_slop_type(context_TranspileContext* ctx, types_SExpr* scrutinee);
slop_string expr_fix_ternary_none(context_TranspileContext* ctx, types_SExpr* other_expr, slop_string other_branch, slop_string this_branch);
slop_option_string expr_extract_option_type(slop_arena* arena, slop_string s);
slop_string expr_transpile_array_index(context_TranspileContext* ctx, types_SExpr* arr_expr, slop_string arr_c, slop_string idx_c);
uint8_t expr_is_pointer_expr(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_extract_sizeof_type(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_transpile_expr(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_transpile_list_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_fn_call(context_TranspileContext* ctx, slop_string fn_name, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_print(context_TranspileContext* ctx, types_SExpr* arg, uint8_t newline);
slop_string expr_transpile_print_string(context_TranspileContext* ctx, slop_string arg_c, slop_string nl);
slop_string expr_transpile_printf_call(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_raw_string_fn_call(context_TranspileContext* ctx, slop_string fn_name, slop_list_types_SExpr_ptr items);
uint8_t expr_string_contains(slop_string s, slop_string substr);
slop_option_string expr_get_expr_type_hint(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_transpile_union_constructor(context_TranspileContext* ctx, slop_string type_name, slop_string c_type_name, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_cond_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_match_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_list_types_SExpr_ptr expr_collect_match_patterns(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_get_expr_pattern_tag(types_SExpr* pat_expr);
uint8_t expr_is_option_patterns(slop_list_types_SExpr_ptr patterns);
uint8_t expr_is_result_patterns(slop_list_types_SExpr_ptr patterns);
uint8_t expr_is_enum_expr_patterns(context_TranspileContext* ctx, slop_list_types_SExpr_ptr patterns);
uint8_t expr_is_union_expr_patterns(context_TranspileContext* ctx, slop_list_types_SExpr_ptr patterns);
slop_option_string expr_get_expr_binding_name(types_SExpr* pat_expr);
slop_string expr_get_match_branch_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr branch_items);
slop_string expr_transpile_branch_body_with_binding(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_list_types_SExpr_ptr branch_items, slop_string binding_name);
slop_string expr_build_option_match_expr(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_string scrutinee_c, slop_list_types_SExpr_ptr items);
slop_string expr_build_option_match_no_binding(context_TranspileContext* ctx, slop_string scrutinee_c, slop_string some_body, slop_string none_body, slop_string result_type);
slop_string expr_build_option_match_with_binding(context_TranspileContext* ctx, slop_arena* arena, slop_string scrutinee_c, slop_string binding, slop_string some_body, slop_string none_body, slop_string result_type);
slop_string expr_infer_cond_result_c_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_infer_match_branch_body_type(context_TranspileContext* ctx, types_SExpr* branch);
slop_string expr_infer_match_result_c_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_slop_type_to_c_type(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_infer_expr_c_type(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_build_result_match_expr(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_string scrutinee_c, slop_list_types_SExpr_ptr items);
slop_string expr_build_enum_match_expr(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr items);
slop_string expr_build_enum_case_expr(context_TranspileContext* ctx, slop_arena* arena, slop_string cases, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, slop_string result_type);
slop_string expr_build_union_match_expr(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_string scrutinee_c, slop_list_types_SExpr_ptr items);
slop_string expr_typed_none(context_TranspileContext* ctx, slop_string result_type, slop_string body);
slop_string expr_typed_none_arg(context_TranspileContext* ctx, slop_string expected_type, slop_string arg_c);
slop_string expr_wrap_fn_ref_as_closure(context_TranspileContext* ctx, slop_string expected_type, slop_string arg_c, types_SExpr* arg_expr);
slop_string expr_generate_fn_trampoline(context_TranspileContext* ctx, slop_string fn_c_name, context_FuncEntry func_entry);
slop_string expr_build_union_case_expr(context_TranspileContext* ctx, slop_arena* arena, slop_string cases, types_SExpr* scrutinee, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, slop_string result_type);
slop_string expr_build_ternary_match_expr(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr items);
uint8_t expr_discard_needs_void(types_SExpr* e);
slop_string expr_transpile_discarded_expr(context_TranspileContext* ctx, types_SExpr* e);
slop_string expr_transpile_let_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void expr_register_let_binding_in_context(context_TranspileContext* ctx, types_SExpr* binding);
slop_string expr_transpile_binding_expr(context_TranspileContext* ctx, types_SExpr* binding);
uint8_t expr_binding_has_mut(slop_list_types_SExpr_ptr items);
slop_string expr_transpile_typed_init(context_TranspileContext* ctx, types_SExpr* init_expr, slop_string target_type);
slop_string expr_transpile_while_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_do_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_when_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
uint8_t expr_set_is_self_assign(slop_list_types_SExpr_ptr items);
slop_string expr_transpile_set_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_resolve_arena_c_name(context_TranspileContext* ctx, slop_string op, slop_list_types_SExpr_ptr items);
uint8_t expr_local_callable_shadows(context_TranspileContext* ctx, slop_string name);
slop_string expr_get_arena_for_list_push_expr(context_TranspileContext* ctx, types_SExpr* list_expr, slop_string list_c);
slop_string expr_get_arena_from_field_access(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_get_arena_from_base(context_TranspileContext* ctx, types_SExpr* base_expr);
slop_string expr_get_arena_for_list_push(context_TranspileContext* ctx, slop_string list_c);
uint8_t expr_is_ptr_to_ptr_map(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_deref_container_c(context_TranspileContext* ctx, slop_string container_c, slop_string slop_type);
slop_string expr_resolve_container_c(context_TranspileContext* ctx, types_SExpr* container_expr);
slop_string expr_transpile_record_new(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_record_fields(context_TranspileContext* ctx, slop_string type_name, slop_list_types_SExpr_ptr items, int64_t start_idx);
slop_string expr_build_inline_struct_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr type_items);
slop_string expr_transpile_inline_record_fields(context_TranspileContext* ctx, slop_string struct_def, slop_list_types_SExpr_ptr items, int64_t start_idx);
slop_string expr_transpile_list_literal(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_build_struct_key_info(context_TranspileContext* ctx, slop_string c_name);
slop_string expr_get_map_key_c_info(context_TranspileContext* ctx, types_SExpr* key_type_expr);
slop_string expr_get_struct_key_info_by_name(context_TranspileContext* ctx, slop_string name);
slop_string expr_transpile_map_new(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
uint8_t expr_is_c_primitive_type(slop_string t);
slop_string expr_map_key_c_type(context_TranspileContext* ctx, types_SExpr* key_expr, types_SExpr* container_expr);
slop_string expr_wrap_map_key_as_ptr(context_TranspileContext* ctx, slop_string key_c, types_SExpr* key_expr, types_SExpr* container_expr);
uint8_t expr_key_expr_is_addressable(types_SExpr* key_expr);
slop_string expr_with_map_key(context_TranspileContext* ctx, slop_string key_c, types_SExpr* key_expr, types_SExpr* container_expr, slop_string prefix, slop_string suffix);
uint8_t expr_map_key_needs_temp(context_TranspileContext* ctx, types_SExpr* key_expr, types_SExpr* container_expr);
slop_string expr_map_key_temp_decl(context_TranspileContext* ctx, slop_string key_c, types_SExpr* key_expr, types_SExpr* container_expr, slop_string temp);
slop_string expr_map_key_ptr(context_TranspileContext* ctx, slop_string key_c, types_SExpr* key_expr, types_SExpr* container_expr, slop_string temp);
slop_string expr_map_put_value_decl_type(context_TranspileContext* ctx, types_SExpr* map_expr);
slop_string expr_transpile_map_put(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_map_get(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_map_has(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_map_remove(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_map_keys(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_set_new(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_set_put(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_set_has(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_set_remove(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_set_elements(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_set_literal(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_for_as_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_for_each_as_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_for_each_list_as_expr(context_TranspileContext* ctx, slop_string var_name, types_SExprSymbol var_sym, types_SExpr* coll_expr, slop_list_types_SExpr_ptr items, int64_t len);
slop_string expr_transpile_for_each_set_as_expr(context_TranspileContext* ctx, slop_string var_name, types_SExprSymbol var_sym, types_SExpr* coll_expr, slop_string resolved_type, slop_list_types_SExpr_ptr items, int64_t len);
slop_string expr_transpile_for_each_map_keys_as_expr(context_TranspileContext* ctx, slop_string var_name, types_SExprSymbol var_sym, types_SExpr* coll_expr, slop_string resolved_type, slop_list_types_SExpr_ptr items, int64_t len);
slop_string expr_transpile_for_each_map_kv_as_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr binding_items, slop_list_types_SExpr_ptr items, int64_t len);
slop_string expr_transpile_with_arena_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_lambda_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_lambda_with_params(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, slop_list_types_SExpr_ptr params);
slop_list_string expr_extract_param_names(slop_arena* arena, slop_list_types_SExpr_ptr params);
slop_string expr_infer_lambda_return_type(context_TranspileContext* ctx, types_SExpr* body);
slop_string expr_transpile_simple_lambda(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, slop_list_types_SExpr_ptr params, slop_string lambda_name);
slop_string expr_transpile_closure(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, slop_list_types_SExpr_ptr params, slop_list_string param_names, slop_list_string free_vars, slop_string lambda_name);
slop_string expr_build_closure_struct(context_TranspileContext* ctx, slop_string env_type, slop_list_string free_vars);
slop_string expr_build_closure_params(context_TranspileContext* ctx, slop_list_types_SExpr_ptr params);
void expr_bind_closure_captures(context_TranspileContext* ctx, slop_list_string free_vars);
slop_list_string expr_capture_free_var_accesses(context_TranspileContext* ctx, slop_list_string free_vars);
slop_string expr_build_closure_function(context_TranspileContext* ctx, slop_string name, slop_string env_type, slop_string ret_type, slop_string params, slop_string body, slop_list_string free_vars);
slop_string expr_trim_parens(slop_arena* arena, slop_string s);
slop_string expr_find_arena_ptr_expr(context_TranspileContext* ctx);
slop_string expr_build_closure_instance(context_TranspileContext* ctx, slop_string lambda_name, slop_string env_name, slop_string env_type, slop_list_string free_vars, slop_list_string captured_accesses);
slop_string expr_build_env_initializer(context_TranspileContext* ctx, slop_list_string free_vars, slop_list_string captured_accesses);
slop_string expr_build_lambda_params(context_TranspileContext* ctx, slop_list_types_SExpr_ptr params);
void expr_bind_lambda_params(context_TranspileContext* ctx, slop_list_types_SExpr_ptr params);
uint8_t expr_is_pointer_type_sexpr(types_SExpr* type_expr);
slop_string expr_transpile_lambda_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start, slop_string return_type);
slop_string expr_build_lambda_function(context_TranspileContext* ctx, slop_string name, slop_string ret_type, slop_string params, slop_string body);
uint8_t expr_is_capturing_lambda(types_SExpr* expr);
slop_string expr_transpile_spawn_closure(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, types_SExpr* fn_expr);
uint8_t expr_lambda_has_captures(context_TranspileContext* ctx, types_SExpr* fn_expr);
slop_string expr_transpile_regular_fn_call(context_TranspileContext* ctx, slop_string fn_name, slop_list_types_SExpr_ptr items);
slop_string expr_infer_generic_type_binding(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_extract_type_binding_from_slop_type(slop_arena* arena, slop_string slop_type);
slop_string expr_extract_type_binding_from_c_type(slop_arena* arena, slop_string c_type);
slop_string expr_slop_type_to_c_identifier(slop_arena* arena, slop_string slop_type);
int64_t expr_find_matching_paren(slop_string s, int64_t start);
slop_list_string expr_find_free_vars(context_TranspileContext* ctx, slop_list_string param_names, slop_list_types_SExpr_ptr body_items, int64_t start, slop_list_string pending);
void expr_collect_symbols_in_expr(context_TranspileContext* ctx, slop_list_string* symbols, slop_list_string pending, types_SExpr* expr);
void expr_collect_symbols_in_list(context_TranspileContext* ctx, slop_list_string* symbols, slop_list_string pending, slop_list_types_SExpr_ptr items, int64_t start);
void expr_collect_symbols_in_let(context_TranspileContext* ctx, slop_list_string* symbols, slop_list_string pending, slop_list_types_SExpr_ptr items);
uint8_t expr_is_mut_binding(slop_list_types_SExpr_ptr items);
slop_list_string expr_extract_let_binding_names(slop_arena* arena, types_SExpr* bindings_expr);
void expr_collect_symbols_in_match(context_TranspileContext* ctx, slop_list_string* symbols, slop_list_string pending, slop_list_types_SExpr_ptr items);
void expr_collect_symbols_in_for(context_TranspileContext* ctx, slop_list_string* symbols, slop_list_string pending, slop_list_types_SExpr_ptr items);
slop_list_string expr_extract_for_loop_var_pending(slop_arena* arena, slop_list_string pending, slop_list_types_SExpr_ptr bind_items);
void expr_collect_symbols_in_with_arena(context_TranspileContext* ctx, slop_list_string* symbols, slop_list_string pending, slop_list_types_SExpr_ptr items);
void expr_collect_nested_lambda_free_vars(context_TranspileContext* ctx, slop_list_string* symbols, slop_list_string pending, slop_list_types_SExpr_ptr items);
uint8_t expr_is_special_keyword(slop_string name);
uint8_t expr_is_free_var(context_TranspileContext* ctx, slop_list_string param_names, slop_list_string pending, slop_string sym_name);
uint8_t expr_is_builtin_op(slop_string name);
uint8_t expr_list_contains_string(slop_list_string lst, slop_string needle);
slop_list_string expr_list_concat(slop_arena* arena, slop_list_string a, slop_list_string b);
slop_string expr_extract_first_type_arg(slop_arena* arena, slop_string slop_type, int64_t start);
slop_string expr_extract_second_type_arg(slop_arena* arena, slop_string slop_type, int64_t start);
slop_string expr_infer_result_ok_slop_type(context_TranspileContext* ctx, types_SExpr* scrutinee);
slop_string expr_infer_result_err_slop_type(context_TranspileContext* ctx, types_SExpr* scrutinee);
slop_string expr_infer_collection_element_slop_type(context_TranspileContext* ctx, types_SExpr* coll_expr);
slop_string expr_infer_elem_from_type(context_TranspileContext* ctx, types_SExpr* expr);

slop_string expr_escape_c_string(context_TranspileContext* ctx, slop_string s) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)(s.len));
        __auto_type data = s.data;
        {
            __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, ((len * 2) + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
            int64_t out_pos = 0;
            int64_t in_pos = 0;
            while (in_pos < len) {
                {
                    __auto_type c = ((int64_t)(data[in_pos]));
                    if (c == 10) {
                        buf[out_pos] = 92;
                        out_pos = (out_pos + 1);
                        buf[out_pos] = 110;
                        out_pos = (out_pos + 1);
                    } else if (c == 13) {
                        buf[out_pos] = 92;
                        out_pos = (out_pos + 1);
                        buf[out_pos] = 114;
                        out_pos = (out_pos + 1);
                    } else if (c == 9) {
                        buf[out_pos] = 92;
                        out_pos = (out_pos + 1);
                        buf[out_pos] = 116;
                        out_pos = (out_pos + 1);
                    } else if (c == 92) {
                        buf[out_pos] = 92;
                        out_pos = (out_pos + 1);
                        buf[out_pos] = 92;
                        out_pos = (out_pos + 1);
                    } else if (c == 34) {
                        buf[out_pos] = 92;
                        out_pos = (out_pos + 1);
                        buf[out_pos] = 34;
                        out_pos = (out_pos + 1);
                    } else {
                        buf[out_pos] = ((uint8_t)(c));
                        out_pos = (out_pos + 1);
                    }
                }
                in_pos = (in_pos + 1);
            }
            buf[out_pos] = 0;
            return (slop_string){.len = ((uint64_t)(out_pos)), .data = buf};
        }
    }
}

slop_string expr_wrap_arena_alloc_checked(context_TranspileContext* ctx, slop_string alloc_expr) {
    {
        __auto_type prefix = context_ctx_str(ctx, SLOP_STR("({ __auto_type _alloc = "), alloc_expr);
        __auto_type suffix = SLOP_STR("; if (_alloc == NULL) { fprintf(stderr, \"SLOP: arena alloc failed at %s:%d\\n\", __FILE__, __LINE__); abort(); } _alloc; })");
        return context_ctx_str(ctx, prefix, suffix);
    }
}

uint8_t expr_is_binop(slop_string op) {
    return ((string_eq(op, SLOP_STR("+"))) || (string_eq(op, SLOP_STR("-"))) || (string_eq(op, SLOP_STR("*"))) || (string_eq(op, SLOP_STR("/"))) || (string_eq(op, SLOP_STR("%"))) || (string_eq(op, SLOP_STR("and"))) || (string_eq(op, SLOP_STR("or"))) || (string_eq(op, SLOP_STR("bit-and"))) || (string_eq(op, SLOP_STR("bit-or"))) || (string_eq(op, SLOP_STR("bit-xor"))) || (string_eq(op, SLOP_STR("&"))) || (string_eq(op, SLOP_STR("|"))) || (string_eq(op, SLOP_STR("^"))) || (string_eq(op, SLOP_STR("<<"))) || (string_eq(op, SLOP_STR(">>"))));
}

uint8_t expr_is_comparison_op(slop_string op) {
    return ((string_eq(op, SLOP_STR("=="))) || (string_eq(op, SLOP_STR("="))) || (string_eq(op, SLOP_STR("!="))) || (string_eq(op, SLOP_STR("<"))) || (string_eq(op, SLOP_STR(">"))) || (string_eq(op, SLOP_STR("<="))) || (string_eq(op, SLOP_STR(">="))));
}

uint8_t expr_is_equality_op(slop_string op) {
    return ((string_eq(op, SLOP_STR("=="))) || (string_eq(op, SLOP_STR("="))) || (string_eq(op, SLOP_STR("!="))));
}

uint8_t expr_is_unop(slop_string op) {
    return ((string_eq(op, SLOP_STR("not"))) || (string_eq(op, SLOP_STR("bit-not"))) || (string_eq(op, SLOP_STR("-"))));
}

slop_option_string expr_extract_symbol_name(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_122 = (*expr);
    switch (_mv_122.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_122.data.sym;
            return (slop_option_string){.has_value = 1, .value = sym.name};
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_122.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 2) {
                    return (slop_option_string){.has_value = false};
                } else {
                    __auto_type _mv_123 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_123.has_value) {
                        __auto_type head = _mv_123.value;
                        __auto_type _mv_124 = (*head);
                        switch (_mv_124.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type head_sym = _mv_124.data.sym;
                                if (string_eq(head_sym.name, SLOP_STR("quote"))) {
                                    __auto_type _mv_125 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_125.has_value) {
                                        __auto_type inner = _mv_125.value;
                                        __auto_type _mv_126 = (*inner);
                                        switch (_mv_126.tag) {
                                            case types_SExpr_sym:
                                            {
                                                __auto_type inner_sym = _mv_126.data.sym;
                                                return (slop_option_string){.has_value = 1, .value = inner_sym.name};
                                            }
                                            default: {
                                                return (slop_option_string){.has_value = false};
                                            }
                                        }
                                    } else if (!_mv_125.has_value) {
                                        return (slop_option_string){.has_value = false};
                                    }
                                    SLOP_UNREACHABLE();
                                } else {
                                    return (slop_option_string){.has_value = false};
                                }
                            }
                            default: {
                                return (slop_option_string){.has_value = false};
                            }
                        }
                    } else if (!_mv_123.has_value) {
                        return (slop_option_string){.has_value = false};
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        default: {
            return (slop_option_string){.has_value = false};
        }
    }
}

slop_string expr_transpile_literal(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_127 = (*expr);
    switch (_mv_127.tag) {
        case types_SExpr_num:
        {
            __auto_type num = _mv_127.data.num;
            if (num.is_float) {
                return num.raw;
            } else {
                return num.raw;
            }
        }
        case types_SExpr_str:
        {
            __auto_type str = _mv_127.data.str;
            return context_ctx_str3(ctx, SLOP_STR("SLOP_STR(\""), expr_escape_c_string(ctx, str.value), SLOP_STR("\")"));
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_127.data.sym;
            return expr_transpile_symbol(ctx, sym.name);
        }
        case types_SExpr_lst:
        {
            __auto_type _ = _mv_127.data.lst;
            return SLOP_STR("/* error: list is not a literal */");
        }
    }
    SLOP_UNREACHABLE();
}

slop_string expr_transpile_symbol(context_TranspileContext* ctx, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (string_eq(name, SLOP_STR("true"))) {
            return SLOP_STR("1");
        } else if (string_eq(name, SLOP_STR("false"))) {
            return SLOP_STR("0");
        } else if (string_eq(name, SLOP_STR("nil"))) {
            return SLOP_STR("NULL");
        } else if (string_eq(name, SLOP_STR("none"))) {
            return SLOP_STR("none");
        } else if (string_eq(name, SLOP_STR("unit"))) {
            return SLOP_STR("0");
        } else if (strlib_starts_with(name, SLOP_STR("'"))) {
            {
                __auto_type name_len = string_len(name);
                __auto_type variant_name = strlib_substring(arena, name, 1, ((int64_t)((name_len - 1))));
                __auto_type _mv_128 = context_ctx_lookup_enum_variant(ctx, variant_name);
                if (_mv_128.has_value) {
                    __auto_type enum_name = _mv_128.value;
                    return expr_get_prefixed_enum_value(ctx, enum_name, variant_name);
                } else if (!_mv_128.has_value) {
                    return ctype_to_c_name(arena, variant_name);
                }
                SLOP_UNREACHABLE();
            }
        } else if (strlib_contains(name, SLOP_STR("."))) {
            __auto_type _mv_129 = strlib_index_of(name, SLOP_STR("."));
            if (_mv_129.has_value) {
                __auto_type dot_pos = _mv_129.value;
                {
                    __auto_type base_name = strlib_substring(arena, name, 0, dot_pos);
                    __auto_type rest_len = ((int64_t)((string_len(name) - (dot_pos + 1))));
                    __auto_type rest_name = strlib_substring(arena, name, (dot_pos + 1), rest_len);
                    __auto_type c_rest = ctype_to_c_name(arena, rest_name);
                    __auto_type _mv_130 = context_ctx_lookup_var(ctx, base_name);
                    if (_mv_130.has_value) {
                        __auto_type var_entry = _mv_130.value;
                        {
                            __auto_type c_base = var_entry.c_name;
                            __auto_type is_ptr = var_entry.is_pointer;
                            __auto_type accessor = ((is_ptr) ? SLOP_STR("->") : SLOP_STR("."));
                            return context_ctx_str3(ctx, c_base, accessor, c_rest);
                        }
                    } else if (!_mv_130.has_value) {
                        __auto_type _mv_131 = context_ctx_lookup_type(ctx, base_name);
                        if (_mv_131.has_value) {
                            __auto_type type_info = _mv_131.value;
                            return expr_get_prefixed_enum_value(ctx, type_info.c_name, rest_name);
                        } else if (!_mv_131.has_value) {
                            return context_ctx_str3(ctx, base_name, SLOP_STR("_"), c_rest);
                        }
                        SLOP_UNREACHABLE();
                    }
                    SLOP_UNREACHABLE();
                }
            } else if (!_mv_129.has_value) {
                return ctype_to_c_name(arena, name);
            }
            SLOP_UNREACHABLE();
        } else {
            __auto_type _mv_132 = context_ctx_lookup_var(ctx, name);
            if (_mv_132.has_value) {
                __auto_type entry = _mv_132.value;
                return entry.c_name;
            } else if (!_mv_132.has_value) {
                __auto_type _mv_133 = context_ctx_lookup_enum_variant(ctx, name);
                if (_mv_133.has_value) {
                    __auto_type enum_name = _mv_133.value;
                    return expr_get_prefixed_enum_value(ctx, enum_name, name);
                } else if (!_mv_133.has_value) {
                    {
                        __auto_type c_name = ctype_to_c_name(arena, name);
                        __auto_type _mv_134 = context_ctx_lookup_func(ctx, name);
                        if (_mv_134.has_value) {
                            __auto_type func_entry = _mv_134.value;
                            return func_entry.c_name;
                        } else if (!_mv_134.has_value) {
                            if (context_ctx_strict_unknown_symbols(ctx)) {
                                context_ctx_add_error(ctx, context_ctx_str3(ctx, SLOP_STR("unknown symbol '"), name, SLOP_STR("'")));
                            }
                            return c_name;
                        }
                        SLOP_UNREACHABLE();
                    }
                }
                SLOP_UNREACHABLE();
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_get_prefixed_enum_value(context_TranspileContext* ctx, slop_string enum_name, slop_string variant_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        return context_ctx_str3(ctx, enum_name, SLOP_STR("_"), ctype_to_c_name(arena, variant_name));
    }
}

slop_string expr_binop_to_c(slop_string op) {
    if (string_eq(op, SLOP_STR("+"))) {
        return SLOP_STR("+");
    } else if (string_eq(op, SLOP_STR("-"))) {
        return SLOP_STR("-");
    } else if (string_eq(op, SLOP_STR("*"))) {
        return SLOP_STR("*");
    } else if (string_eq(op, SLOP_STR("/"))) {
        return SLOP_STR("/");
    } else if (string_eq(op, SLOP_STR("%"))) {
        return SLOP_STR("%");
    } else if (string_eq(op, SLOP_STR("=="))) {
        return SLOP_STR("==");
    } else if (string_eq(op, SLOP_STR("="))) {
        return SLOP_STR("==");
    } else if (string_eq(op, SLOP_STR("!="))) {
        return SLOP_STR("!=");
    } else if (string_eq(op, SLOP_STR("<"))) {
        return SLOP_STR("<");
    } else if (string_eq(op, SLOP_STR(">"))) {
        return SLOP_STR(">");
    } else if (string_eq(op, SLOP_STR("<="))) {
        return SLOP_STR("<=");
    } else if (string_eq(op, SLOP_STR(">="))) {
        return SLOP_STR(">=");
    } else if (string_eq(op, SLOP_STR("and"))) {
        return SLOP_STR("&&");
    } else if (string_eq(op, SLOP_STR("or"))) {
        return SLOP_STR("||");
    } else if (string_eq(op, SLOP_STR("bit-and"))) {
        return SLOP_STR("&");
    } else if (string_eq(op, SLOP_STR("bit-or"))) {
        return SLOP_STR("|");
    } else if (string_eq(op, SLOP_STR("bit-xor"))) {
        return SLOP_STR("^");
    } else if (string_eq(op, SLOP_STR("&"))) {
        return SLOP_STR("&");
    } else if (string_eq(op, SLOP_STR("|"))) {
        return SLOP_STR("|");
    } else if (string_eq(op, SLOP_STR("^"))) {
        return SLOP_STR("^");
    } else if (string_eq(op, SLOP_STR("<<"))) {
        return SLOP_STR("<<");
    } else if (string_eq(op, SLOP_STR(">>"))) {
        return SLOP_STR(">>");
    } else {
        return op;
    }
}

slop_string expr_transpile_binop(context_TranspileContext* ctx, slop_string op, slop_string left, slop_string right) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type c_op = expr_binop_to_c(op);
        return context_ctx_str5(ctx, SLOP_STR("("), left, SLOP_STR(" "), c_op, context_ctx_str3(ctx, SLOP_STR(" "), right, SLOP_STR(")")));
    }
}

uint8_t expr_is_aggregate_c_type(context_TranspileContext* ctx, slop_string c_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return (!(strlib_ends_with(c_type, SLOP_STR("*"))) && ((((int64_t)((context_ctx_get_union_variants(ctx, c_type)).len)) > 0) || (((int64_t)((context_ctx_get_fields_for_type(ctx, c_type)).len)) > 0)));
}

slop_string expr_record_container_field(context_TranspileContext* ctx, slop_string c_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type fields = context_ctx_get_fields_for_type(ctx, c_type);
        __auto_type len = ((int64_t)((fields).len));
        int64_t i = 0;
        __auto_type found = SLOP_STR("");
        while ((i < len) && string_eq(found, SLOP_STR(""))) {
            __auto_type _mv_135 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_context_FieldEntry _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_135.has_value) {
                __auto_type field = _mv_135.value;
                {
                    __auto_type st = field.slop_type;
                    if ((strlib_starts_with(st, SLOP_STR("(List"))) || (strlib_starts_with(st, SLOP_STR("(Map"))) || (strlib_starts_with(st, SLOP_STR("(Set"))) || (strlib_starts_with(st, SLOP_STR("(Option"))) || (strlib_starts_with(st, SLOP_STR("(Result")))) {
                        found = field.field_name;
                    }
                }
            } else if (!_mv_135.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

slop_string expr_transpile_aggregate_eq(context_TranspileContext* ctx, slop_string op, slop_string left_c, slop_string right_c, slop_string c_type, types_SExpr* site) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((site != NULL)), "(!= site nil)");
    {
        __auto_type l = context_ctx_gensym(ctx, SLOP_STR("_eq_l"));
        __auto_type r = context_ctx_gensym(ctx, SLOP_STR("_eq_r"));
        __auto_type container_field = expr_record_container_field(ctx, c_type);
        context_ctx_register_struct_key_type(ctx, c_type);
        if (!(string_eq(container_field, SLOP_STR("")))) {
            context_ctx_add_warning_at(ctx, context_ctx_str5(ctx, SLOP_STR("== on '"), c_type, SLOP_STR("' compares field '"), container_field, SLOP_STR("' by identity, not contents")), context_ctx_sexpr_line(site), context_ctx_sexpr_col(site));
        }
        {
            __auto_type decl_l = context_ctx_str5(ctx, c_type, SLOP_STR(" "), l, SLOP_STR(" = ("), context_ctx_str(ctx, left_c, SLOP_STR("); ")));
            __auto_type decl_r = context_ctx_str5(ctx, c_type, SLOP_STR(" "), r, SLOP_STR(" = ("), context_ctx_str(ctx, right_c, SLOP_STR("); ")));
            __auto_type call = context_ctx_str5(ctx, SLOP_STR("slop_eq_"), c_type, SLOP_STR("(&"), l, context_ctx_str3(ctx, SLOP_STR(", &"), r, SLOP_STR("); })")));
            {
                __auto_type stmt_expr = context_ctx_str4(ctx, SLOP_STR("({ "), decl_l, decl_r, call);
                if (string_eq(op, SLOP_STR("!="))) {
                    return context_ctx_str3(ctx, SLOP_STR("(!"), stmt_expr, SLOP_STR(")"));
                } else {
                    return stmt_expr;
                }
            }
        }
    }
}

slop_string expr_transpile_variadic_binop(context_TranspileContext* ctx, slop_string op, slop_list_types_SExpr_ptr items, int64_t start_idx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type c_op = expr_binop_to_c(op);
        __auto_type len = ((int64_t)(((int64_t)((items).len))));
        if (len <= (start_idx + 1)) {
            context_ctx_add_error_at(ctx, SLOP_STR("not enough operands"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("0");
        } else {
            {
                __auto_type result = SLOP_STR("(");
                __auto_type _mv_136 = ({ __auto_type _lst = items; size_t _idx = (size_t)start_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_136.has_value) {
                    __auto_type first_arg = _mv_136.value;
                    result = context_ctx_str4(ctx, result, SLOP_STR("("), expr_transpile_expr(ctx, first_arg), SLOP_STR(")"));
                } else if (!_mv_136.has_value) {
                }
                {
                    int64_t i = (start_idx + 1);
                    while (i < len) {
                        __auto_type _mv_137 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_137.has_value) {
                            __auto_type arg = _mv_137.value;
                            {
                                __auto_type arg_str = context_ctx_str3(ctx, SLOP_STR(" ("), expr_transpile_expr(ctx, arg), SLOP_STR(")"));
                                result = context_ctx_str4(ctx, result, SLOP_STR(" "), c_op, arg_str);
                            }
                        } else if (!_mv_137.has_value) {
                        }
                        i = (i + 1);
                    }
                }
                return context_ctx_str(ctx, result, SLOP_STR(")"));
            }
        }
    }
}

slop_string expr_get_builtin_type_c_name(slop_string type_name) {
    if (string_eq(type_name, SLOP_STR("Bytes"))) {
        return SLOP_STR("slop_bytes");
    } else if (string_eq(type_name, SLOP_STR("String"))) {
        return SLOP_STR("slop_string");
    } else {
        return SLOP_STR("");
    }
}

uint8_t expr_is_pointer_type_expr(types_SExpr* type_expr) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_138 = (*type_expr);
    switch (_mv_138.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_138.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_139 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_139.has_value) {
                        __auto_type head = _mv_139.value;
                        __auto_type _mv_140 = (*head);
                        switch (_mv_140.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_140.data.sym;
                                return (string_eq(sym.name, SLOP_STR("Ptr")) || string_eq(sym.name, SLOP_STR("ScopedPtr")));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_139.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        default: {
            return 0;
        }
    }
}

uint8_t expr_is_string_literal(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_141 = (*expr);
    switch (_mv_141.tag) {
        case types_SExpr_str:
        {
            __auto_type _ = _mv_141.data.str;
            return 1;
        }
        default: {
            return 0;
        }
    }
}

uint8_t expr_is_fn_type_expr(types_SExpr* type_expr) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_142 = (*type_expr);
    switch (_mv_142.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_142.data.lst;
            __auto_type _mv_143 = ({ __auto_type _lst = lst.items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_143.has_value) {
                __auto_type head = _mv_143.value;
                __auto_type _mv_144 = (*head);
                switch (_mv_144.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_144.data.sym;
                        return string_eq(sym.name, SLOP_STR("Fn"));
                    }
                    default: {
                        return 0;
                    }
                }
            } else if (!_mv_143.has_value) {
                return 0;
            }
            SLOP_UNREACHABLE();
        }
        default: {
            return 0;
        }
    }
}

uint8_t expr_is_ptr_void_type(types_SExpr* type_expr) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_145 = (*type_expr);
    switch (_mv_145.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_145.data.lst;
            {
                __auto_type items = lst.items;
                return (((((int64_t)((items).len)) == 2)) && (({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type head = _mv.value; ({ __auto_type _mv = (*head); uint8_t _mr = {0}; switch (_mv.tag) { case types_SExpr_sym: { __auto_type s = _mv.data.sym; _mr = string_eq(s.name, SLOP_STR("Ptr")); break; } default: { _mr = 0; break; }  } _mr; }); }) : (0); })) && (({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner = _mv.value; ({ __auto_type _mv = (*inner); uint8_t _mr = {0}; switch (_mv.tag) { case types_SExpr_sym: { __auto_type s = _mv.data.sym; _mr = string_eq(s.name, SLOP_STR("Void")); break; } default: { _mr = 0; break; }  } _mr; }); }) : (0); })));
            }
        }
        default: {
            return 0;
        }
    }
}

uint8_t expr_is_closure_typed_expr(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_146 = (*expr);
    switch (_mv_146.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_146.data.sym;
            __auto_type _mv_147 = context_ctx_lookup_var(ctx, sym.name);
            if (_mv_147.has_value) {
                __auto_type entry = _mv_147.value;
                return string_eq(entry.c_type, SLOP_STR("slop_closure_t"));
            } else if (!_mv_147.has_value) {
                return 0;
            }
            SLOP_UNREACHABLE();
        }
        default: {
            return 0;
        }
    }
}

slop_string expr_fn_type_to_c_fn_ptr(context_TranspileContext* ctx, types_SExpr* fn_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((fn_expr != NULL)), "(!= fn-expr nil)");
    __auto_type _mv_148 = (*fn_expr);
    switch (_mv_148.tag) {
        case types_SExpr_lst:
        {
            __auto_type l = _mv_148.data.lst;
            {
                __auto_type items = l.items;
                if (((int64_t)((items).len)) < 3) {
                    return SLOP_STR("void*");
                } else {
                    {
                        __auto_type args_expr = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type e = _mv.value; e; }) : (fn_expr); });
                        __auto_type ret_expr = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type e = _mv.value; e; }) : (fn_expr); });
                        __auto_type ret_c = context_to_c_type_prefixed(ctx, ret_expr);
                        __auto_type args_c = expr_build_fn_ptr_args_from_list(ctx, args_expr);
                        if (string_eq(args_c, SLOP_STR(""))) {
                            return context_ctx_str(ctx, ret_c, SLOP_STR("(*)(void)"));
                        } else {
                            return context_ctx_str(ctx, ret_c, context_ctx_str(ctx, SLOP_STR("(*)("), context_ctx_str(ctx, args_c, SLOP_STR(")"))));
                        }
                    }
                }
            }
        }
        default: {
            return SLOP_STR("void*");
        }
    }
}

slop_string expr_build_fn_ptr_args_from_list(context_TranspileContext* ctx, types_SExpr* args_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((args_expr != NULL)), "(!= args-expr nil)");
    __auto_type _mv_149 = (*args_expr);
    switch (_mv_149.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_149.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type count = ((int64_t)((items).len));
                __auto_type result = SLOP_STR("");
                __auto_type i = 0;
                while (i < count) {
                    __auto_type _mv_150 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_150.has_value) {
                        __auto_type arg_type = _mv_150.value;
                        {
                            __auto_type c_type = context_to_c_type_prefixed(ctx, arg_type);
                            result = (((i == 0)) ? c_type : context_ctx_str3(ctx, result, SLOP_STR(", "), c_type));
                        }
                    } else if (!_mv_150.has_value) {
                    }
                    i = (i + 1);
                }
                return result;
            }
        }
        default: {
            return SLOP_STR("");
        }
    }
}

slop_string expr_transpile_builtin_constructor(context_TranspileContext* ctx, slop_string type_name, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (string_eq(type_name, SLOP_STR("Bytes"))) {
            if (len < 4) {
                return SLOP_STR("(slop_bytes){0}");
            } else {
                {
                    __auto_type data_c = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type e = _mv.value; expr_transpile_expr(ctx, e); }) : (SLOP_STR("NULL")); });
                    __auto_type len_c = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type e = _mv.value; expr_transpile_expr(ctx, e); }) : (SLOP_STR("0")); });
                    __auto_type cap_c = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type e = _mv.value; expr_transpile_expr(ctx, e); }) : (SLOP_STR("0")); });
                    return context_ctx_str(ctx, SLOP_STR("(slop_bytes){.len = "), context_ctx_str(ctx, len_c, context_ctx_str(ctx, SLOP_STR(", .cap = "), context_ctx_str(ctx, cap_c, context_ctx_str(ctx, SLOP_STR(", .data = "), context_ctx_str(ctx, data_c, SLOP_STR("}")))))));
                }
            }
        } else if (string_eq(type_name, SLOP_STR("String"))) {
            if (len < 3) {
                return SLOP_STR("(slop_string){0}");
            } else {
                {
                    __auto_type data_c = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type e = _mv.value; expr_transpile_expr(ctx, e); }) : (SLOP_STR("NULL")); });
                    __auto_type len_c = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type e = _mv.value; expr_transpile_expr(ctx, e); }) : (SLOP_STR("0")); });
                    return context_ctx_str(ctx, SLOP_STR("(slop_string){.len = "), context_ctx_str(ctx, len_c, context_ctx_str(ctx, SLOP_STR(", .data = "), context_ctx_str(ctx, data_c, SLOP_STR("}")))));
                }
            }
        } else {
            return SLOP_STR("(/* unknown builtin */)");
        }
    }
}

slop_string expr_transpile_call(context_TranspileContext* ctx, slop_string fn_name, slop_string args) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        {
            __auto_type runtime_name = expr_get_runtime_function_name(fn_name);
            if (string_len(runtime_name) > 0) {
                return context_ctx_str4(ctx, runtime_name, SLOP_STR("("), args, SLOP_STR(")"));
            } else {
                {
                    __auto_type base_name = expr_get_base_function_name(arena, fn_name);
                    __auto_type mod_name = expr_get_module_from_qualified_name(arena, fn_name);
                    __auto_type _mv_151 = context_ctx_lookup_var(ctx, fn_name);
                    if (_mv_151.has_value) {
                        __auto_type var_entry = _mv_151.value;
                        if (var_entry.is_closure) {
                            {
                                __auto_type lambda_name = var_entry.closure_lambda_name;
                                __auto_type env_type = var_entry.closure_env_type;
                                __auto_type var_c_name = var_entry.c_name;
                                __auto_type slop_type = var_entry.slop_type;
                                if (string_len(lambda_name) > 0) {
                                    if (string_len(args) > 0) {
                                        {
                                            __auto_type s1 = context_ctx_str(ctx, lambda_name, SLOP_STR("(("));
                                            __auto_type s2 = context_ctx_str(ctx, s1, env_type);
                                            __auto_type s3 = context_ctx_str(ctx, s2, SLOP_STR("*)"));
                                            __auto_type s4 = context_ctx_str(ctx, s3, var_c_name);
                                            __auto_type s5 = context_ctx_str(ctx, s4, SLOP_STR(".env, "));
                                            __auto_type s6 = context_ctx_str(ctx, s5, args);
                                            return context_ctx_str(ctx, s6, SLOP_STR(")"));
                                        }
                                    } else {
                                        {
                                            __auto_type s1 = context_ctx_str(ctx, lambda_name, SLOP_STR("(("));
                                            __auto_type s2 = context_ctx_str(ctx, s1, env_type);
                                            __auto_type s3 = context_ctx_str(ctx, s2, SLOP_STR("*)"));
                                            __auto_type s4 = context_ctx_str(ctx, s3, var_c_name);
                                            return context_ctx_str(ctx, s4, SLOP_STR(".env)"));
                                        }
                                    }
                                } else {
                                    return expr_emit_generic_closure_call(ctx, var_c_name, slop_type, args);
                                }
                            }
                        } else {
                            return context_ctx_str4(ctx, var_entry.c_name, SLOP_STR("("), args, SLOP_STR(")"));
                        }
                    } else if (!_mv_151.has_value) {
                        {
                            __auto_type c_name = ({ __auto_type _mv = context_ctx_lookup_func(ctx, base_name); _mv.has_value ? ({ __auto_type func_entry = _mv.value; func_entry.c_name; }) : ((((string_len(mod_name) > 0)) ? ctype_to_c_name(arena, fn_name) : context_ctx_prefix_type(ctx, ctype_to_c_name(arena, fn_name)))); });
                            return context_ctx_str4(ctx, c_name, SLOP_STR("("), args, SLOP_STR(")"));
                        }
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
    }
}

slop_string expr_emit_generic_closure_call(context_TranspileContext* ctx, slop_string var_c_name, slop_string slop_type, slop_string args) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type fn_cast = expr_build_closure_fn_cast(ctx, slop_type);
        __auto_type fn_ptr = context_ctx_str(ctx, var_c_name, SLOP_STR(".fn"));
        __auto_type env_ptr = context_ctx_str(ctx, var_c_name, SLOP_STR(".env"));
        {
            __auto_type cast_expr = context_ctx_str4(ctx, SLOP_STR("(("), fn_cast, SLOP_STR(")"), fn_ptr);
            __auto_type call_open = context_ctx_str(ctx, cast_expr, SLOP_STR(")("));
            if (string_len(args) > 0) {
                return context_ctx_str4(ctx, call_open, env_ptr, SLOP_STR(", "), context_ctx_str(ctx, args, SLOP_STR(")")));
            } else {
                return context_ctx_str(ctx, call_open, context_ctx_str(ctx, env_ptr, SLOP_STR(")")));
            }
        }
    }
}

slop_string expr_build_closure_fn_cast(context_TranspileContext* ctx, slop_string slop_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        {
            __auto_type type_expr = expr_parse_type_string(arena, slop_type);
            if (type_expr == NULL) {
                return expr_closure_cast_error(ctx, slop_type, SLOP_STR("type is not a balanced s-expression"));
            } else {
                __auto_type _mv_152 = (*type_expr);
                switch (_mv_152.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type l = _mv_152.data.lst;
                        {
                            __auto_type items = l.items;
                            if (!(expr_is_fn_type_shape(items))) {
                                return expr_closure_cast_error(ctx, slop_type, SLOP_STR("expected (Fn (arg-types) return-type)"));
                            } else {
                                {
                                    __auto_type ret_expr = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)(((int64_t)((items).len)) - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type e = _mv.value; e; }) : (type_expr); });
                                    __auto_type args_c = expr_fn_type_args_c(ctx, items);
                                    {
                                        __auto_type ret_c = context_to_c_type_prefixed(ctx, ret_expr);
                                        if (string_eq(args_c, SLOP_STR(""))) {
                                            return context_ctx_str(ctx, ret_c, SLOP_STR("(*)(void*)"));
                                        } else {
                                            return context_ctx_str(ctx, ret_c, context_ctx_str(ctx, SLOP_STR("(*)(void*, "), context_ctx_str(ctx, args_c, SLOP_STR(")"))));
                                        }
                                    }
                                }
                            }
                        }
                    }
                    default: {
                        return expr_closure_cast_error(ctx, slop_type, SLOP_STR("expected (Fn (arg-types) return-type)"));
                    }
                }
            }
        }
    }
}

slop_string expr_fn_type_args_c(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (((int64_t)((items).len)) == 2) {
        return SLOP_STR("");
    } else {
        __auto_type _mv_153 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_153.has_value) {
            __auto_type args_expr = _mv_153.value;
            return expr_build_fn_ptr_args_from_list(ctx, args_expr);
        } else if (!_mv_153.has_value) {
            return SLOP_STR("");
        }
        SLOP_UNREACHABLE();
    }
}

uint8_t expr_is_fn_type_shape(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        if (len == 2) {
            return 1;
        } else if (len == 3) {
            return expr_fn_type_arg_list_ok(items);
        } else if (len == 4) {
            return (expr_fn_type_arg_list_ok(items) && ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type arrow = _mv.value; ({ __auto_type _mv = (*arrow); uint8_t _mr = {0}; switch (_mv.tag) { case types_SExpr_sym: { __auto_type s = _mv.data.sym; _mr = string_eq(s.name, SLOP_STR("->")); break; } default: { _mr = 0; break; }  } _mr; }); }) : (0); }));
        } else {
            return 0;
        }
    }
}

uint8_t expr_fn_type_arg_list_ok(slop_list_types_SExpr_ptr items) {
    __auto_type _mv_154 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
    if (_mv_154.has_value) {
        __auto_type args_expr = _mv_154.value;
        __auto_type _mv_155 = (*args_expr);
        switch (_mv_155.tag) {
            case types_SExpr_lst:
            {
                __auto_type _ = _mv_155.data.lst;
                return 1;
            }
            default: {
                return 0;
            }
        }
    } else if (!_mv_154.has_value) {
        return 0;
    }
    SLOP_UNREACHABLE();
}

slop_string expr_closure_cast_error(context_TranspileContext* ctx, slop_string slop_type, slop_string why) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_add_error(ctx, context_ctx_str4(ctx, SLOP_STR("cannot build a closure call cast for type '"), slop_type, SLOP_STR("': "), why));
    return SLOP_STR("void(*)(void*)");
}

types_SExpr* expr_parse_type_string(slop_arena* arena, slop_string s) {
    {
        __auto_type len = ((int64_t)(string_len(s)));
        if (len == 0) {
            return NULL;
        } else if (strlib_starts_with(s, SLOP_STR("("))) {
            if (!(expr_type_form_is_wrapped(s))) {
                return NULL;
            } else {
                {
                    __auto_type inner = strlib_substring(arena, s, 1, ((0) > ((len - 2)) ? (0) : ((len - 2))));
                    __auto_type items = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
                    uint8_t failed = 0;
                    int64_t i = 0;
                    {
                        __auto_type parts = expr_split_top_level_types(arena, inner);
                        {
                            __auto_type count = ((int64_t)((parts).len));
                            while (i < count) {
                                __auto_type _mv_156 = ({ __auto_type _lst = parts; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_156.has_value) {
                                    __auto_type part = _mv_156.value;
                                    {
                                        __auto_type child = expr_parse_type_string(arena, part);
                                        if (child == NULL) {
                                            failed = 1;
                                        } else {
                                            ({ __auto_type _lst_p = &(items); __auto_type _item = (child); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                        }
                                    }
                                } else if (!_mv_156.has_value) {
                                    failed = 1;
                                }
                                i = (i + 1);
                            }
                            if (failed) {
                                return NULL;
                            } else {
                                {
                                    __auto_type node = ((types_SExpr*)(({ __auto_type _alloc = (types_SExpr*)slop_arena_alloc(arena, sizeof(types_SExpr)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
                                    (*node) = ((types_SExpr){ .tag = types_SExpr_lst, .data.lst = (types_SExprList){items, 0, 0, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                                    return node;
                                }
                            }
                        }
                    }
                }
            }
        } else if (expr_type_token_is_number(s)) {
            {
                __auto_type node = ((types_SExpr*)(({ __auto_type _alloc = (types_SExpr*)slop_arena_alloc(arena, sizeof(types_SExpr)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
                (*node) = ((types_SExpr){ .tag = types_SExpr_num, .data.num = (types_SExprNumber){((int64_t)(expr_type_token_to_int(s))), 0.0, 0, s, 0, 0, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                return node;
            }
        } else {
            {
                __auto_type node = ((types_SExpr*)(({ __auto_type _alloc = (types_SExpr*)slop_arena_alloc(arena, sizeof(types_SExpr)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
                (*node) = ((types_SExpr){ .tag = types_SExpr_sym, .data.sym = (types_SExprSymbol){s, 0, 0, ((slop_option_types_ResolvedType_ptr){.has_value = false})} });
                return node;
            }
        }
    }
}

uint8_t expr_type_form_is_wrapped(slop_string s) {
    {
        __auto_type len = ((int64_t)(string_len(s)));
        int64_t depth = 0;
        uint8_t closed_early = 0;
        uint8_t went_negative = 0;
        int64_t i = 0;
        while (i < len) {
            {
                __auto_type c = strlib_char_at(s, ((int64_t)(i)));
                if (c == 40) {
                    depth = (depth + 1);
                } else if (c == 41) {
                    depth = (depth - 1);
                    if (depth < 0) {
                        went_negative = 1;
                    }
                    if ((depth == 0) && (i < (len - 1))) {
                        closed_early = 1;
                    }
                } else {
                }
            }
            i = (i + 1);
        }
        return ((depth == 0) && (!(closed_early) && !(went_negative)));
    }
}

slop_list_string expr_split_top_level_types(slop_arena* arena, slop_string s) {
    {
        __auto_type len = ((int64_t)(string_len(s)));
        __auto_type out = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        int64_t token_start = 0;
        int64_t paren_depth = 0;
        int64_t i = 0;
        while (i <= len) {
            {
                __auto_type c = (((i < len)) ? strlib_char_at(s, ((int64_t)(i))) : 32);
                if (c == 40) {
                    paren_depth = (paren_depth + 1);
                } else if (c == 41) {
                    paren_depth = (paren_depth - 1);
                } else if ((c == 32) && (paren_depth == 0)) {
                    if (token_start < i) {
                        ({ __auto_type _lst_p = &(out); __auto_type _item = (strlib_substring(arena, s, ((int64_t)(token_start)), ((int64_t)((i - token_start))))); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    }
                    token_start = (i + 1);
                } else {
                }
            }
            i = (i + 1);
        }
        return out;
    }
}

uint8_t expr_type_token_is_number(slop_string s) {
    {
        __auto_type len = ((int64_t)(string_len(s)));
        int64_t digits = 0;
        int64_t other = 0;
        int64_t i = 0;
        while (i < len) {
            {
                __auto_type c = strlib_char_at(s, ((int64_t)(i)));
                if ((c >= 48) && (c <= 57)) {
                    digits = (digits + 1);
                } else if ((i == 0) && (c == 45)) {
                } else {
                    other = (other + 1);
                }
            }
            i = (i + 1);
        }
        return ((digits > 0) && (other == 0));
    }
}

int64_t expr_type_token_to_int(slop_string s) {
    SLOP_PRE(((string_len(s) > 0)), "(> (string-len s) 0)");
    {
        __auto_type len = ((int64_t)(string_len(s)));
        int64_t value = 0;
        int64_t i = 0;
        while (i < len) {
            {
                __auto_type c = strlib_char_at(s, ((int64_t)(i)));
                if ((c >= 48) && (c <= 57)) {
                    value = ((value * 10) + (c - 48));
                }
            }
            i = (i + 1);
        }
        if (strlib_char_at(s, 0) == 45) {
            return (0 - value);
        } else {
            return value;
        }
    }
}

slop_string expr_get_base_function_name(slop_arena* arena, slop_string fn_name) {
    {
        __auto_type len = ((int64_t)(string_len(fn_name)));
        int64_t dot_pos = -1;
        int64_t i = 0;
        while (i < len) {
            if (strlib_char_at(fn_name, ((int64_t)(i))) == 46) {
                dot_pos = i;
            } else {
            }
            i = (i + 1);
        }
        if (dot_pos < 0) {
            return fn_name;
        } else {
            {
                __auto_type start = (dot_pos + 1);
                __auto_type sublen = (len - start);
                return strlib_substring(arena, fn_name, ((int64_t)(start)), ((int64_t)(sublen)));
            }
        }
    }
}

slop_string expr_get_module_from_qualified_name(slop_arena* arena, slop_string fn_name) {
    {
        __auto_type len = ((int64_t)(string_len(fn_name)));
        int64_t dot_pos = -1;
        int64_t i = 0;
        while (i < len) {
            if (strlib_char_at(fn_name, ((int64_t)(i))) == 46) {
                dot_pos = i;
            } else {
            }
            i = (i + 1);
        }
        if (dot_pos < 0) {
            return SLOP_STR("");
        } else {
            return strlib_substring(arena, fn_name, 0, ((int64_t)(dot_pos)));
        }
    }
}

slop_string expr_get_runtime_function_name(slop_string fn_name) {
    if (string_eq(fn_name, SLOP_STR("string-eq"))) {
        return SLOP_STR("string_eq");
    } else if (string_eq(fn_name, SLOP_STR("string-concat"))) {
        return SLOP_STR("string_concat");
    } else if (string_eq(fn_name, SLOP_STR("string-len"))) {
        return SLOP_STR("string_len");
    } else if (string_eq(fn_name, SLOP_STR("string-new"))) {
        return SLOP_STR("string_new");
    } else if (string_eq(fn_name, SLOP_STR("int-to-string"))) {
        return SLOP_STR("int_to_string");
    } else if (string_eq(fn_name, SLOP_STR("string-push-char"))) {
        return SLOP_STR("slop_string_push_char");
    } else if (string_eq(fn_name, SLOP_STR("float-to-string-short"))) {
        return SLOP_STR("float_to_string_short");
    } else if (string_eq(fn_name, SLOP_STR("parse-int"))) {
        return SLOP_STR("strlib_parse_int");
    } else if (string_eq(fn_name, SLOP_STR("parse-float"))) {
        return SLOP_STR("strlib_parse_float");
    } else if (string_eq(fn_name, SLOP_STR("list-len"))) {
        return SLOP_STR("list_len");
    } else if (string_eq(fn_name, SLOP_STR("list-new"))) {
        return SLOP_STR("list_new");
    } else if (string_eq(fn_name, SLOP_STR("list-push"))) {
        return SLOP_STR("list_push");
    } else if (string_eq(fn_name, SLOP_STR("list-get"))) {
        return SLOP_STR("list_get");
    } else if (string_eq(fn_name, SLOP_STR("bytes-len"))) {
        return SLOP_STR("bytes_len");
    } else if (string_eq(fn_name, SLOP_STR("bytes-new"))) {
        return SLOP_STR("bytes_new");
    } else if (string_eq(fn_name, SLOP_STR("unwrap"))) {
        return SLOP_STR("unwrap");
    } else if (string_eq(fn_name, SLOP_STR("printf"))) {
        return SLOP_STR("printf");
    } else if (string_eq(fn_name, SLOP_STR("fprintf"))) {
        return SLOP_STR("fprintf");
    } else if (string_eq(fn_name, SLOP_STR("sprintf"))) {
        return SLOP_STR("sprintf");
    } else if (string_eq(fn_name, SLOP_STR("snprintf"))) {
        return SLOP_STR("snprintf");
    } else if (string_eq(fn_name, SLOP_STR("malloc"))) {
        return SLOP_STR("malloc");
    } else if (string_eq(fn_name, SLOP_STR("free"))) {
        return SLOP_STR("free");
    } else if (string_eq(fn_name, SLOP_STR("memcpy"))) {
        return SLOP_STR("memcpy");
    } else if (string_eq(fn_name, SLOP_STR("memset"))) {
        return SLOP_STR("memset");
    } else if (string_eq(fn_name, SLOP_STR("strlen"))) {
        return SLOP_STR("strlen");
    } else if (string_eq(fn_name, SLOP_STR("strcmp"))) {
        return SLOP_STR("strcmp");
    } else if (string_eq(fn_name, SLOP_STR("exit"))) {
        return SLOP_STR("exit");
    } else if (string_eq(fn_name, SLOP_STR("abort"))) {
        return SLOP_STR("abort");
    } else if (string_eq(fn_name, SLOP_STR("now-ms"))) {
        return SLOP_STR("slop_now_ms");
    } else if (string_eq(fn_name, SLOP_STR("sleep-ms"))) {
        return SLOP_STR("slop_sleep_ms");
    } else if (string_eq(fn_name, SLOP_STR("arena-new"))) {
        return SLOP_STR("slop_arena_new");
    } else if (string_eq(fn_name, SLOP_STR("arena-free"))) {
        return SLOP_STR("slop_arena_free");
    } else {
        return SLOP_STR("");
    }
}

slop_string expr_transpile_enum_variant(context_TranspileContext* ctx, slop_string variant_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_157 = context_ctx_lookup_enum_variant(ctx, variant_name);
        if (_mv_157.has_value) {
            __auto_type enum_name = _mv_157.value;
            {
                __auto_type enum_c = ctype_to_c_name(arena, enum_name);
                __auto_type variant_c = ctype_to_c_name(arena, variant_name);
                return context_ctx_str3(ctx, enum_c, SLOP_STR("_"), variant_c);
            }
        } else if (!_mv_157.has_value) {
            return ctype_to_c_name(arena, variant_name);
        }
        SLOP_UNREACHABLE();
    }
}

slop_string expr_transpile_ok(context_TranspileContext* ctx, slop_string value_c) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    __auto_type _mv_158 = context_ctx_get_current_result_type(ctx);
    if (_mv_158.has_value) {
        __auto_type result_type = _mv_158.value;
        return context_ctx_str5(ctx, SLOP_STR("(("), result_type, SLOP_STR("){ .is_ok = true, .data.ok = "), value_c, SLOP_STR(" })"));
    } else if (!_mv_158.has_value) {
        return context_ctx_str3(ctx, SLOP_STR("(slop_result){ .is_ok = true, .data.ok = "), value_c, SLOP_STR(" }"));
    }
    SLOP_UNREACHABLE();
}

slop_string expr_transpile_error(context_TranspileContext* ctx, slop_string value_c) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    __auto_type _mv_159 = context_ctx_get_current_result_type(ctx);
    if (_mv_159.has_value) {
        __auto_type result_type = _mv_159.value;
        return context_ctx_str5(ctx, SLOP_STR("(("), result_type, SLOP_STR("){ .is_ok = false, .data.err = "), value_c, SLOP_STR(" })"));
    } else if (!_mv_159.has_value) {
        return context_ctx_str3(ctx, SLOP_STR("(slop_result){ .is_ok = false, .data.err = "), value_c, SLOP_STR(" }"));
    }
    SLOP_UNREACHABLE();
}

slop_string expr_infer_option_type(context_TranspileContext* ctx, types_SExpr* val_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((val_expr != NULL)), "(!= val-expr nil)");
    __auto_type _mv_160 = (*val_expr);
    switch (_mv_160.tag) {
        case types_SExpr_num:
        {
            __auto_type num = _mv_160.data.num;
            if (num.is_float) {
                return SLOP_STR("slop_option_float");
            } else {
                return SLOP_STR("slop_option_int");
            }
        }
        case types_SExpr_str:
        {
            __auto_type _ = _mv_160.data.str;
            return SLOP_STR("slop_option_string");
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_160.data.sym;
            __auto_type _mv_161 = ctype_get_node_resolved_type(val_expr);
            if (_mv_161.has_value) {
                __auto_type rt = _mv_161.value;
                {
                    __auto_type c_type = ctype_resolved_type_to_c((*ctx).arena, rt);
                    return expr_c_type_to_option_type_name(ctx, c_type);
                }
            } else if (!_mv_161.has_value) {
                {
                    __auto_type name = sym.name;
                    __auto_type _mv_162 = context_ctx_lookup_var(ctx, name);
                    if (_mv_162.has_value) {
                        __auto_type var_entry = _mv_162.value;
                        {
                            __auto_type c_type = var_entry.c_type;
                            __auto_type slop_type = var_entry.slop_type;
                            __auto_type arena = (*ctx).arena;
                            if (string_eq(c_type, SLOP_STR("auto"))) {
                                if (string_len(slop_type) > 0) {
                                    {
                                        __auto_type derived_c_type = expr_slop_value_type_to_c_type(ctx, slop_type);
                                        return expr_c_type_to_option_type_name(ctx, derived_c_type);
                                    }
                                } else {
                                    context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("Cannot infer Option type for variable '"), name, SLOP_STR("' - type is 'auto' with no SLOP type")), context_ctx_sexpr_line(val_expr), context_ctx_sexpr_col(val_expr));
                                    return SLOP_STR("__type_error__");
                                }
                            } else if (string_eq(c_type, SLOP_STR("int64_t"))) {
                                return SLOP_STR("slop_option_int");
                            } else if (string_eq(c_type, SLOP_STR("double"))) {
                                return SLOP_STR("slop_option_float");
                            } else if (string_eq(c_type, SLOP_STR("slop_string"))) {
                                return SLOP_STR("slop_option_string");
                            } else if (string_eq(c_type, SLOP_STR("char"))) {
                                return SLOP_STR("slop_option_char");
                            } else if (string_eq(c_type, SLOP_STR("uint8_t"))) {
                                return SLOP_STR("slop_option_u8");
                            } else if (strlib_ends_with(c_type, SLOP_STR("*"))) {
                                {
                                    __auto_type base_type = expr_strip_pointer_suffix(arena, c_type);
                                    return context_ctx_str3(ctx, SLOP_STR("slop_option_"), base_type, SLOP_STR("_ptr"));
                                }
                            } else {
                                return context_ctx_str3(ctx, SLOP_STR("slop_option_"), c_type, SLOP_STR(""));
                            }
                        }
                    } else if (!_mv_162.has_value) {
                        context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("Unknown variable '"), name, SLOP_STR("' for Option type inference")), context_ctx_sexpr_line(val_expr), context_ctx_sexpr_col(val_expr));
                        return SLOP_STR("__type_error__");
                    }
                    SLOP_UNREACHABLE();
                }
            }
            SLOP_UNREACHABLE();
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_160.data.lst;
            return expr_infer_list_expr_option_type(ctx, lst.items);
        }
    }
    SLOP_UNREACHABLE();
}

slop_string expr_c_type_to_option_type_name(context_TranspileContext* ctx, slop_string c_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (strlib_ends_with(c_type, SLOP_STR("*"))) {
            {
                __auto_type base_type = expr_strip_pointer_suffix(arena, c_type);
                return context_ctx_str3(ctx, SLOP_STR("slop_option_"), base_type, SLOP_STR("_ptr"));
            }
        } else {
            return context_ctx_str3(ctx, SLOP_STR("slop_option_"), ctype_type_to_identifier(arena, c_type), SLOP_STR(""));
        }
    }
}

slop_string expr_infer_field_c_type_from_items(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type line = context_ctx_list_first_line(items);
        __auto_type col = context_ctx_list_first_col(items);
        if (len < 3) {
            return SLOP_STR("__auto_type");
        } else {
            __auto_type _mv_163 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_163.has_value) {
                __auto_type obj_expr = _mv_163.value;
                __auto_type _mv_164 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_164.has_value) {
                    __auto_type field_expr = _mv_164.value;
                    __auto_type _mv_165 = (*field_expr);
                    switch (_mv_165.tag) {
                        case types_SExpr_sym:
                        {
                            __auto_type field_sym = _mv_165.data.sym;
                            {
                                __auto_type field_name = field_sym.name;
                                __auto_type obj_c_type = expr_infer_expr_c_type(ctx, obj_expr);
                                __auto_type _mv_166 = context_ctx_lookup_field_type(ctx, obj_c_type, field_name);
                                if (_mv_166.has_value) {
                                    __auto_type c_type = _mv_166.value;
                                    return c_type;
                                } else if (!_mv_166.has_value) {
                                    __auto_type _mv_167 = context_ctx_lookup_var(ctx, expr_get_var_name_from_expr(obj_expr));
                                    if (_mv_167.has_value) {
                                        __auto_type var_entry = _mv_167.value;
                                        {
                                            __auto_type obj_slop_type = var_entry.slop_type;
                                            __auto_type _mv_168 = context_ctx_lookup_field_type(ctx, obj_slop_type, field_name);
                                            if (_mv_168.has_value) {
                                                __auto_type c_type2 = _mv_168.value;
                                                return c_type2;
                                            } else if (!_mv_168.has_value) {
                                                return SLOP_STR("__auto_type");
                                            }
                                            SLOP_UNREACHABLE();
                                        }
                                    } else if (!_mv_167.has_value) {
                                        return SLOP_STR("__auto_type");
                                    }
                                    SLOP_UNREACHABLE();
                                }
                                SLOP_UNREACHABLE();
                            }
                        }
                        default: {
                            return SLOP_STR("__auto_type");
                        }
                    }
                } else if (!_mv_164.has_value) {
                    return SLOP_STR("__auto_type");
                }
                SLOP_UNREACHABLE();
            } else if (!_mv_163.has_value) {
                return SLOP_STR("__auto_type");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_infer_list_expr_option_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type arena = (*ctx).arena;
        __auto_type line = context_ctx_list_first_line(items);
        __auto_type col = context_ctx_list_first_col(items);
        if (len < 1) {
            context_ctx_add_error_at(ctx, SLOP_STR("Empty list in option type inference"), line, col);
            return SLOP_STR("__type_error__");
        } else {
            __auto_type _mv_169 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_169.has_value) {
                __auto_type head_expr = _mv_169.value;
                __auto_type _mv_170 = (*head_expr);
                switch (_mv_170.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_170.data.sym;
                        {
                            __auto_type op = sym.name;
                            if (string_eq(op, SLOP_STR("."))) {
                                if (len < 3) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("Incomplete field access for option type inference"), line, col);
                                    return SLOP_STR("__type_error__");
                                } else {
                                    {
                                        __auto_type field_c_type = expr_infer_field_c_type_from_items(ctx, items);
                                        if (!(string_eq(field_c_type, SLOP_STR("__auto_type")))) {
                                            return expr_c_type_to_option_type_name(ctx, field_c_type);
                                        } else {
                                            __auto_type _mv_171 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_171.has_value) {
                                                __auto_type field_expr = _mv_171.value;
                                                __auto_type _mv_172 = (*field_expr);
                                                switch (_mv_172.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type field_sym = _mv_172.data.sym;
                                                        {
                                                            __auto_type field_name = field_sym.name;
                                                            if (string_eq(field_name, SLOP_STR("name"))) {
                                                                return SLOP_STR("slop_option_string");
                                                            } else if (string_eq(field_name, SLOP_STR("value"))) {
                                                                return SLOP_STR("slop_option_string");
                                                            } else if (string_eq(field_name, SLOP_STR("message"))) {
                                                                return SLOP_STR("slop_option_string");
                                                            } else if (string_eq(field_name, SLOP_STR("c-name"))) {
                                                                return SLOP_STR("slop_option_string");
                                                            } else if (string_eq(field_name, SLOP_STR("c-type"))) {
                                                                return SLOP_STR("slop_option_string");
                                                            } else if (string_eq(field_name, SLOP_STR("slop-name"))) {
                                                                return SLOP_STR("slop_option_string");
                                                            } else if (string_eq(field_name, SLOP_STR("slop-type"))) {
                                                                return SLOP_STR("slop_option_string");
                                                            } else if (string_eq(field_name, SLOP_STR("return-type"))) {
                                                                return SLOP_STR("slop_option_string");
                                                            } else if (string_eq(field_name, SLOP_STR("slop-return-type"))) {
                                                                return SLOP_STR("slop_option_string");
                                                            } else if (string_eq(field_name, SLOP_STR("enum-name"))) {
                                                                return SLOP_STR("slop_option_string");
                                                            } else if (string_eq(field_name, SLOP_STR("variant-name"))) {
                                                                return SLOP_STR("slop_option_string");
                                                            } else if (string_eq(field_name, SLOP_STR("const-type"))) {
                                                                return SLOP_STR("slop_option_types_ResolvedType_ptr");
                                                            } else {
                                                                context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("Unknown field '"), field_name, SLOP_STR("' for option type inference")), context_ctx_sexpr_line(field_expr), context_ctx_sexpr_col(field_expr));
                                                                return SLOP_STR("__type_error__");
                                                            }
                                                        }
                                                    }
                                                    default: {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("Non-symbol field for option type inference"), context_ctx_sexpr_line(field_expr), context_ctx_sexpr_col(field_expr));
                                                        return SLOP_STR("__type_error__");
                                                    }
                                                }
                                            } else if (!_mv_171.has_value) {
                                                context_ctx_add_error_at(ctx, SLOP_STR("Missing field for option type inference"), line, col);
                                                return SLOP_STR("__type_error__");
                                            }
                                            SLOP_UNREACHABLE();
                                        }
                                    }
                                }
                            } else if (string_eq(op, SLOP_STR("string-concat")) || (string_eq(op, SLOP_STR("string-copy")) || (string_eq(op, SLOP_STR("int-to-string")) || string_eq(op, SLOP_STR("substring"))))) {
                                return SLOP_STR("slop_option_string");
                            } else {
                                __auto_type _mv_173 = context_ctx_lookup_func(ctx, op);
                                if (_mv_173.has_value) {
                                    __auto_type func_entry = _mv_173.value;
                                    {
                                        __auto_type ret_type = func_entry.return_type;
                                        if (func_entry.returns_string) {
                                            return SLOP_STR("slop_option_string");
                                        } else if (string_len(ret_type) > 0) {
                                            if (string_eq(ret_type, SLOP_STR("slop_string"))) {
                                                return SLOP_STR("slop_option_string");
                                            } else if (string_eq(ret_type, SLOP_STR("int64_t"))) {
                                                return SLOP_STR("slop_option_int");
                                            } else if (string_eq(ret_type, SLOP_STR("double"))) {
                                                return SLOP_STR("slop_option_float");
                                            } else if (strlib_ends_with(ret_type, SLOP_STR("*"))) {
                                                {
                                                    __auto_type ctx_arena = (*ctx).arena;
                                                    __auto_type base_type = expr_strip_pointer_suffix(ctx_arena, ret_type);
                                                    return context_ctx_str3(ctx, SLOP_STR("slop_option_"), base_type, SLOP_STR("_ptr"));
                                                }
                                            } else {
                                                return context_ctx_str3(ctx, SLOP_STR("slop_option_"), ret_type, SLOP_STR(""));
                                            }
                                        } else {
                                            context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("Cannot infer Option type for function '"), op, SLOP_STR("' - no return type info")), line, col);
                                            return SLOP_STR("__type_error__");
                                        }
                                    }
                                } else if (!_mv_173.has_value) {
                                    context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("Unknown function '"), op, SLOP_STR("' for Option type inference")), line, col);
                                    return SLOP_STR("__type_error__");
                                }
                                SLOP_UNREACHABLE();
                            }
                        }
                    }
                    default: {
                        context_ctx_add_error_at(ctx, SLOP_STR("Non-symbol head in option type inference"), context_ctx_sexpr_line(head_expr), context_ctx_sexpr_col(head_expr));
                        return SLOP_STR("__type_error__");
                    }
                }
            } else if (!_mv_169.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("Missing list head in option type inference"), line, col);
                return SLOP_STR("__type_error__");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_strip_pointer_suffix(slop_arena* arena, slop_string s) {
    {
        __auto_type len = string_len(s);
        if (len < 1) {
            return SLOP_STR("");
        } else {
            return strlib_substring(arena, s, ((int64_t)(0)), ((int64_t)((len - 1))));
        }
    }
}

slop_string expr_extract_chan_elem_type(context_TranspileContext* ctx, slop_string chan_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type prefix_len = 10;
        {
            __auto_type len = string_len(chan_type);
            if (len <= prefix_len) {
                return SLOP_STR("int64_t");
            } else {
                return strlib_substring(arena, chan_type, ((int64_t)(prefix_len)), ((int64_t)(len)));
            }
        }
    }
}

slop_string expr_infer_list_element_option_type(context_TranspileContext* ctx, types_SExpr* list_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((list_expr != NULL)), "(!= list-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_174 = ctype_get_node_resolved_type(list_expr);
        if (_mv_174.has_value) {
            __auto_type rt = _mv_174.value;
            __auto_type _mv_175 = (*rt).inner_type;
            if (_mv_175.has_value) {
                __auto_type elem_type = _mv_175.value;
                {
                    __auto_type elem_c = ctype_resolved_type_to_c(arena, elem_type);
                    return string_concat(arena, SLOP_STR("slop_option_"), ctype_type_to_identifier(arena, elem_c));
                }
            } else if (!_mv_175.has_value) {
                return expr_infer_list_element_option_type_fallback(ctx, list_expr);
            }
            SLOP_UNREACHABLE();
        } else if (!_mv_174.has_value) {
            context_ctx_warn_fallback(ctx, list_expr, SLOP_STR("infer-list-element-option-type"));
            return expr_infer_list_element_option_type_fallback(ctx, list_expr);
        }
        SLOP_UNREACHABLE();
    }
}

slop_string expr_infer_list_element_option_type_fallback(context_TranspileContext* ctx, types_SExpr* list_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((list_expr != NULL)), "(!= list-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type list_c_type = expr_infer_expr_c_type(ctx, list_expr);
        if (strlib_starts_with(list_c_type, SLOP_STR("slop_list_"))) {
            {
                __auto_type elem_id = expr_substring_after_prefix(arena, list_c_type, SLOP_STR("slop_list_"));
                __auto_type prefixed_elem = expr_prefix_list_element_type(ctx, elem_id);
                return string_concat(arena, SLOP_STR("slop_option_"), prefixed_elem);
            }
        } else {
            __auto_type _mv_176 = (*list_expr);
            switch (_mv_176.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_176.data.sym;
                    {
                        __auto_type name = sym.name;
                        __auto_type _mv_177 = context_ctx_lookup_var(ctx, name);
                        if (_mv_177.has_value) {
                            __auto_type var_entry = _mv_177.value;
                            return expr_list_type_to_option_type(ctx, var_entry.c_type);
                        } else if (!_mv_177.has_value) {
                            return SLOP_STR("");
                        }
                        SLOP_UNREACHABLE();
                    }
                }
                case types_SExpr_lst:
                {
                    __auto_type lst = _mv_176.data.lst;
                    {
                        __auto_type items = lst.items;
                        if (((int64_t)((items).len)) < 3) {
                            return SLOP_STR("");
                        } else {
                            __auto_type _mv_178 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_178.has_value) {
                                __auto_type head = _mv_178.value;
                                __auto_type _mv_179 = (*head);
                                switch (_mv_179.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type head_sym = _mv_179.data.sym;
                                        if (string_eq(head_sym.name, SLOP_STR("."))) {
                                            __auto_type _mv_180 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_180.has_value) {
                                                __auto_type field_expr = _mv_180.value;
                                                return expr_infer_field_access_list_type(ctx, field_expr);
                                            } else if (!_mv_180.has_value) {
                                                return SLOP_STR("");
                                            }
                                            SLOP_UNREACHABLE();
                                        } else {
                                            return SLOP_STR("");
                                        }
                                    }
                                    default: {
                                        return SLOP_STR("");
                                    }
                                }
                            } else if (!_mv_178.has_value) {
                                return SLOP_STR("");
                            }
                            SLOP_UNREACHABLE();
                        }
                    }
                }
                default: {
                    return SLOP_STR("");
                }
            }
        }
    }
}

slop_string expr_infer_field_access_list_type(context_TranspileContext* ctx, types_SExpr* field_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((field_expr != NULL)), "(!= field-expr nil)");
    __auto_type _mv_181 = (*field_expr);
    switch (_mv_181.tag) {
        case types_SExpr_sym:
        {
            __auto_type field_sym = _mv_181.data.sym;
            {
                __auto_type field_name = field_sym.name;
                if (string_eq(field_name, SLOP_STR("items"))) {
                    return SLOP_STR("slop_option_types_SExpr_ptr");
                } else if (string_eq(field_name, SLOP_STR("variants"))) {
                    return SLOP_STR("slop_option_types_ResolvedVariant");
                } else if (string_eq(field_name, SLOP_STR("fields"))) {
                    return SLOP_STR("slop_option_types_ResolvedField");
                } else {
                    return SLOP_STR("");
                }
            }
        }
        default: {
            return SLOP_STR("");
        }
    }
}

slop_string expr_list_type_to_option_type(context_TranspileContext* ctx, slop_string c_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (string_eq(c_type, SLOP_STR("slop_list_string"))) {
            return SLOP_STR("slop_option_string");
        } else if (string_eq(c_type, SLOP_STR("slop_list_int"))) {
            return SLOP_STR("slop_option_int");
        } else if (string_eq(c_type, SLOP_STR("slop_list_float"))) {
            return SLOP_STR("slop_option_float");
        } else if (string_eq(c_type, SLOP_STR("slop_list_char"))) {
            return SLOP_STR("slop_option_char");
        } else if (string_eq(c_type, SLOP_STR("slop_list_u8"))) {
            return SLOP_STR("slop_option_u8");
        } else if (strlib_starts_with(c_type, SLOP_STR("slop_list_"))) {
            {
                __auto_type elem_type = expr_substring_after_prefix(arena, c_type, SLOP_STR("slop_list_"));
                {
                    __auto_type prefixed_elem = expr_prefix_list_element_type(ctx, elem_type);
                    return context_ctx_str3(ctx, SLOP_STR("slop_option_"), prefixed_elem, SLOP_STR(""));
                }
            }
        } else {
            return SLOP_STR("");
        }
    }
}

slop_string expr_prefix_list_element_type(context_TranspileContext* ctx, slop_string elem_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (strlib_ends_with(elem_type, SLOP_STR("_ptr"))) {
            {
                __auto_type base = strlib_substring(arena, elem_type, 0, ((0) > ((((int64_t)(string_len(elem_type))) - 4)) ? (0) : ((((int64_t)(string_len(elem_type))) - 4))));
                __auto_type _mv_182 = context_ctx_lookup_type(ctx, base);
                if (_mv_182.has_value) {
                    __auto_type entry = _mv_182.value;
                    return string_concat(arena, entry.c_name, SLOP_STR("_ptr"));
                } else if (!_mv_182.has_value) {
                    return elem_type;
                }
                SLOP_UNREACHABLE();
            }
        } else {
            __auto_type _mv_183 = context_ctx_lookup_type(ctx, elem_type);
            if (_mv_183.has_value) {
                __auto_type entry = _mv_183.value;
                return entry.c_name;
            } else if (!_mv_183.has_value) {
                return elem_type;
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_substring_after_prefix(slop_arena* arena, slop_string s, slop_string prefix) {
    {
        __auto_type prefix_len = string_len(prefix);
        __auto_type s_len = string_len(s);
        if (s_len <= prefix_len) {
            return SLOP_STR("");
        } else {
            {
                __auto_type start = ((int64_t)(prefix_len));
                __auto_type len = ((int64_t)((s_len - prefix_len)));
                return strlib_substring(arena, s, start, len);
            }
        }
    }
}

slop_string expr_extract_map_value_from_slop_type(slop_arena* arena, slop_string raw_slop_type) {
    {
        __auto_type slop_type = ctype_unwrap_ptr_container_type(arena, raw_slop_type);
        {
            __auto_type len = string_len(slop_type);
            if (len < 10) {
                return SLOP_STR("");
            } else {
                if (!(strlib_starts_with(slop_type, SLOP_STR("(Map ")))) {
                    return SLOP_STR("");
                } else {
                    {
                        int64_t i = 5;
                        int64_t nesting = 1;
                        int64_t key_space = 0;
                        uint8_t found_key = 0;
                        __auto_type end_idx = (len - 1);
                        while ((i < end_idx) && !(found_key)) {
                            {
                                __auto_type c = strlib_char_at(slop_type, ((int64_t)(i)));
                                if (c == 40) {
                                    nesting = (nesting + 1);
                                } else if (c == 41) {
                                    nesting = (nesting - 1);
                                } else if ((c == 32) && (nesting == 1)) {
                                    key_space = i;
                                    found_key = 1;
                                } else {
                                }
                            }
                            i = (i + 1);
                        }
                        if (!(found_key)) {
                            return SLOP_STR("");
                        } else {
                            {
                                __auto_type value_start = (key_space + 1);
                                __auto_type value_len = (end_idx - value_start);
                                if (value_len > 0) {
                                    return strlib_substring(arena, slop_type, ((int64_t)(value_start)), ((int64_t)(value_len)));
                                } else {
                                    return SLOP_STR("");
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

slop_string expr_slop_value_type_to_c_type(context_TranspileContext* ctx, slop_string slop_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (strlib_starts_with(slop_type, SLOP_STR("(Map "))) {
            return SLOP_STR("slop_map*");
        } else if (strlib_starts_with(slop_type, SLOP_STR("(Set "))) {
            return SLOP_STR("slop_map*");
        } else if (strlib_starts_with(slop_type, SLOP_STR("(Ptr (Map "))) {
            return SLOP_STR("slop_map**");
        } else if (strlib_starts_with(slop_type, SLOP_STR("(Ptr (Set "))) {
            return SLOP_STR("slop_map**");
        } else if (strlib_starts_with(slop_type, SLOP_STR("(Ptr "))) {
            {
                __auto_type inner_len = ((0) > ((((int64_t)(string_len(slop_type))) - 6)) ? (0) : ((((int64_t)(string_len(slop_type))) - 6)));
                __auto_type inner_type = strlib_substring(arena, slop_type, 5, ((int64_t)(inner_len)));
                __auto_type inner_c = expr_slop_value_type_to_c_type(ctx, inner_type);
                return string_concat(arena, inner_c, SLOP_STR("*"));
            }
        } else {
            __auto_type _mv_184 = context_ctx_lookup_type(ctx, slop_type);
            if (_mv_184.has_value) {
                __auto_type entry = _mv_184.value;
                return entry.c_name;
            } else if (!_mv_184.has_value) {
                return ctype_to_c_name(arena, slop_type);
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_get_var_name_from_expr(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_185 = (*expr);
    switch (_mv_185.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_185.data.sym;
            return sym.name;
        }
        default: {
            return SLOP_STR("");
        }
    }
}

slop_string expr_extract_map_key_from_slop_type(slop_arena* arena, slop_string raw_slop_type) {
    {
        __auto_type slop_type = ctype_unwrap_ptr_container_type(arena, raw_slop_type);
        {
            __auto_type len = string_len(slop_type);
            if (len < 10) {
                return SLOP_STR("");
            } else {
                if (!(strlib_starts_with(slop_type, SLOP_STR("(Map ")))) {
                    return SLOP_STR("");
                } else {
                    {
                        int64_t i = 5;
                        int64_t nesting = 1;
                        int64_t key_space = 0;
                        uint8_t found_key = 0;
                        __auto_type end_idx = (len - 1);
                        while ((i < end_idx) && !(found_key)) {
                            {
                                __auto_type c = strlib_char_at(slop_type, ((int64_t)(i)));
                                if (c == 40) {
                                    nesting = (nesting + 1);
                                } else if (c == 41) {
                                    nesting = (nesting - 1);
                                } else if ((c == 32) && (nesting == 1)) {
                                    key_space = i;
                                    found_key = 1;
                                } else {
                                }
                            }
                            i = (i + 1);
                        }
                        if (!(found_key)) {
                            return SLOP_STR("");
                        } else {
                            {
                                __auto_type key_start = 5;
                                __auto_type key_len = (key_space - key_start);
                                if (key_len > 0) {
                                    return strlib_substring(arena, slop_type, ((int64_t)(key_start)), ((int64_t)(key_len)));
                                } else {
                                    return SLOP_STR("");
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

slop_string expr_resolve_type_alias(context_TranspileContext* ctx, slop_string slop_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (strlib_starts_with(slop_type, SLOP_STR("(Map "))) {
        return slop_type;
    } else if (strlib_starts_with(slop_type, SLOP_STR("(Set "))) {
        return slop_type;
    } else if (strlib_starts_with(slop_type, SLOP_STR("("))) {
        return slop_type;
    } else {
        __auto_type _mv_186 = context_ctx_lookup_type_alias(ctx, slop_type);
        if (_mv_186.has_value) {
            __auto_type alias_def = _mv_186.value;
            return alias_def;
        } else if (!_mv_186.has_value) {
            return slop_type;
        }
        SLOP_UNREACHABLE();
    }
}

slop_string expr_infer_expr_slop_type(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_187 = (*expr);
        switch (_mv_187.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_187.data.sym;
                {
                    __auto_type name = sym.name;
                    __auto_type _mv_188 = context_ctx_lookup_var(ctx, name);
                    if (_mv_188.has_value) {
                        __auto_type entry = _mv_188.value;
                        return entry.slop_type;
                    } else if (!_mv_188.has_value) {
                        return SLOP_STR("");
                    }
                    SLOP_UNREACHABLE();
                }
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_187.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len < 1) {
                        return SLOP_STR("");
                    } else {
                        __auto_type _mv_189 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_189.has_value) {
                            __auto_type head = _mv_189.value;
                            __auto_type _mv_190 = (*head);
                            switch (_mv_190.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_190.data.sym;
                                    {
                                        __auto_type op = head_sym.name;
                                        if (string_eq(op, SLOP_STR(".")) && (len >= 3)) {
                                            __auto_type _mv_191 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_191.has_value) {
                                                __auto_type obj_expr = _mv_191.value;
                                                __auto_type _mv_192 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_192.has_value) {
                                                    __auto_type field_expr = _mv_192.value;
                                                    __auto_type _mv_193 = (*field_expr);
                                                    switch (_mv_193.tag) {
                                                        case types_SExpr_sym:
                                                        {
                                                            __auto_type field_sym = _mv_193.data.sym;
                                                            {
                                                                __auto_type field_name = field_sym.name;
                                                                {
                                                                    __auto_type obj_c_type_raw = expr_infer_expr_c_type(ctx, obj_expr);
                                                                    __auto_type obj_c_type = ((strlib_ends_with(obj_c_type_raw, SLOP_STR("*"))) ? strlib_substring(arena, obj_c_type_raw, 0, (obj_c_type_raw.len - 1)) : obj_c_type_raw);
                                                                    __auto_type _mv_194 = context_ctx_lookup_field_slop_type(ctx, obj_c_type, field_name);
                                                                    if (_mv_194.has_value) {
                                                                        __auto_type slop_type = _mv_194.value;
                                                                        return slop_type;
                                                                    } else if (!_mv_194.has_value) {
                                                                        {
                                                                            __auto_type obj_slop_type_raw = expr_infer_expr_slop_type(ctx, obj_expr);
                                                                            __auto_type obj_slop_type = ((strlib_starts_with(obj_slop_type_raw, SLOP_STR("(Ptr "))) ? strlib_substring(arena, obj_slop_type_raw, 5, (obj_slop_type_raw.len - 6)) : obj_slop_type_raw);
                                                                            __auto_type _mv_195 = context_ctx_lookup_field_slop_type(ctx, obj_slop_type, field_name);
                                                                            if (_mv_195.has_value) {
                                                                                __auto_type slop_type2 = _mv_195.value;
                                                                                return slop_type2;
                                                                            } else if (!_mv_195.has_value) {
                                                                                return SLOP_STR("");
                                                                            }
                                                                            SLOP_UNREACHABLE();
                                                                        }
                                                                    }
                                                                    SLOP_UNREACHABLE();
                                                                }
                                                            }
                                                        }
                                                        default: {
                                                            return SLOP_STR("");
                                                        }
                                                    }
                                                } else if (!_mv_192.has_value) {
                                                    return SLOP_STR("");
                                                }
                                                SLOP_UNREACHABLE();
                                            } else if (!_mv_191.has_value) {
                                                return SLOP_STR("");
                                            }
                                            SLOP_UNREACHABLE();
                                        } else if (string_eq(op, SLOP_STR("record-new"))) {
                                            if (len >= 2) {
                                                __auto_type _mv_196 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_196.has_value) {
                                                    __auto_type type_expr = _mv_196.value;
                                                    __auto_type _mv_197 = (*type_expr);
                                                    switch (_mv_197.tag) {
                                                        case types_SExpr_sym:
                                                        {
                                                            __auto_type type_sym = _mv_197.data.sym;
                                                            return type_sym.name;
                                                        }
                                                        default: {
                                                            return SLOP_STR("");
                                                        }
                                                    }
                                                } else if (!_mv_196.has_value) {
                                                    return SLOP_STR("");
                                                }
                                                SLOP_UNREACHABLE();
                                            } else {
                                                return SLOP_STR("");
                                            }
                                        } else if (string_eq(op, SLOP_STR("map-new"))) {
                                            if (len >= 4) {
                                                __auto_type _mv_198 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_198.has_value) {
                                                    __auto_type key_expr = _mv_198.value;
                                                    __auto_type _mv_199 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_199.has_value) {
                                                        __auto_type val_expr = _mv_199.value;
                                                        {
                                                            __auto_type key_str = ctype_sexpr_to_type_string(arena, key_expr);
                                                            __auto_type val_str = ctype_sexpr_to_type_string(arena, val_expr);
                                                            return context_ctx_str5(ctx, SLOP_STR("(Map "), key_str, SLOP_STR(" "), val_str, SLOP_STR(")"));
                                                        }
                                                    } else if (!_mv_199.has_value) {
                                                        return SLOP_STR("");
                                                    }
                                                    SLOP_UNREACHABLE();
                                                } else if (!_mv_198.has_value) {
                                                    return SLOP_STR("");
                                                }
                                                SLOP_UNREACHABLE();
                                            } else {
                                                return SLOP_STR("");
                                            }
                                        } else if (string_eq(op, SLOP_STR("set-new"))) {
                                            if (len >= 3) {
                                                __auto_type _mv_200 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_200.has_value) {
                                                    __auto_type elem_expr = _mv_200.value;
                                                    {
                                                        __auto_type elem_str = ctype_sexpr_to_type_string(arena, elem_expr);
                                                        return context_ctx_str3(ctx, SLOP_STR("(Set "), elem_str, SLOP_STR(")"));
                                                    }
                                                } else if (!_mv_200.has_value) {
                                                    return SLOP_STR("");
                                                }
                                                SLOP_UNREACHABLE();
                                            } else {
                                                return SLOP_STR("");
                                            }
                                        } else if (string_eq(op, SLOP_STR("set"))) {
                                            if (len >= 2) {
                                                __auto_type _mv_201 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_201.has_value) {
                                                    __auto_type elem_expr = _mv_201.value;
                                                    {
                                                        __auto_type elem_str = ctype_sexpr_to_type_string(arena, elem_expr);
                                                        return context_ctx_str3(ctx, SLOP_STR("(Set "), elem_str, SLOP_STR(")"));
                                                    }
                                                } else if (!_mv_201.has_value) {
                                                    return SLOP_STR("");
                                                }
                                                SLOP_UNREACHABLE();
                                            } else {
                                                return SLOP_STR("");
                                            }
                                        } else if (string_eq(op, SLOP_STR("list"))) {
                                            if (len >= 2) {
                                                __auto_type _mv_202 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_202.has_value) {
                                                    __auto_type elem_expr = _mv_202.value;
                                                    {
                                                        __auto_type elem_str = ctype_sexpr_to_type_string(arena, elem_expr);
                                                        return context_ctx_str3(ctx, SLOP_STR("(List "), elem_str, SLOP_STR(")"));
                                                    }
                                                } else if (!_mv_202.has_value) {
                                                    return SLOP_STR("");
                                                }
                                                SLOP_UNREACHABLE();
                                            } else {
                                                return SLOP_STR("");
                                            }
                                        } else if (string_eq(op, SLOP_STR("list-new"))) {
                                            if (len >= 3) {
                                                __auto_type _mv_203 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_203.has_value) {
                                                    __auto_type elem_expr = _mv_203.value;
                                                    {
                                                        __auto_type elem_str = ctype_sexpr_to_type_string(arena, elem_expr);
                                                        return context_ctx_str3(ctx, SLOP_STR("(List "), elem_str, SLOP_STR(")"));
                                                    }
                                                } else if (!_mv_203.has_value) {
                                                    return SLOP_STR("");
                                                }
                                                SLOP_UNREACHABLE();
                                            } else {
                                                return SLOP_STR("");
                                            }
                                        } else if (string_eq(op, SLOP_STR("chan-buffered")) || strlib_ends_with(op, SLOP_STR(":chan-buffered"))) {
                                            if (len >= 4) {
                                                __auto_type _mv_204 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_204.has_value) {
                                                    __auto_type type_expr = _mv_204.value;
                                                    {
                                                        __auto_type type_str = ctype_sexpr_to_type_string(arena, type_expr);
                                                        return context_ctx_str3(ctx, SLOP_STR("(Ptr (Chan "), type_str, SLOP_STR("))"));
                                                    }
                                                } else if (!_mv_204.has_value) {
                                                    return SLOP_STR("");
                                                }
                                                SLOP_UNREACHABLE();
                                            } else {
                                                return SLOP_STR("");
                                            }
                                        } else if (string_eq(op, SLOP_STR("chan")) || strlib_ends_with(op, SLOP_STR(":chan"))) {
                                            if (len >= 3) {
                                                __auto_type _mv_205 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_205.has_value) {
                                                    __auto_type type_expr = _mv_205.value;
                                                    {
                                                        __auto_type type_str = ctype_sexpr_to_type_string(arena, type_expr);
                                                        return context_ctx_str3(ctx, SLOP_STR("(Ptr (Chan "), type_str, SLOP_STR("))"));
                                                    }
                                                } else if (!_mv_205.has_value) {
                                                    return SLOP_STR("");
                                                }
                                                SLOP_UNREACHABLE();
                                            } else {
                                                return SLOP_STR("");
                                            }
                                        } else if (string_eq(op, SLOP_STR("?")) && (len >= 2)) {
                                            __auto_type _mv_206 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_206.has_value) {
                                                __auto_type inner_expr = _mv_206.value;
                                                return expr_infer_result_ok_slop_type(ctx, inner_expr);
                                            } else if (!_mv_206.has_value) {
                                                return SLOP_STR("");
                                            }
                                            SLOP_UNREACHABLE();
                                        } else {
                                            __auto_type _mv_207 = context_ctx_lookup_func(ctx, op);
                                            if (_mv_207.has_value) {
                                                __auto_type func_entry = _mv_207.value;
                                                return func_entry.slop_return_type;
                                            } else if (!_mv_207.has_value) {
                                                return SLOP_STR("");
                                            }
                                            SLOP_UNREACHABLE();
                                        }
                                    }
                                }
                                default: {
                                    return SLOP_STR("");
                                }
                            }
                        } else if (!_mv_189.has_value) {
                            return SLOP_STR("");
                        }
                        SLOP_UNREACHABLE();
                    }
                }
            }
            default: {
                return SLOP_STR("");
            }
        }
    }
}

slop_string expr_infer_map_key_c_type_from_slop_type(context_TranspileContext* ctx, slop_string slop_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (string_len(slop_type) == 0) {
            return SLOP_STR("");
        } else {
            {
                __auto_type resolved_type = expr_resolve_type_alias(ctx, slop_type);
                __auto_type key_slop_type = expr_extract_map_key_from_slop_type(arena, resolved_type);
                if (string_len(key_slop_type) > 0) {
                    return expr_slop_value_type_to_c_type(ctx, key_slop_type);
                } else {
                    {
                        __auto_type elem_slop_type = expr_extract_set_elem_from_slop_type(arena, resolved_type);
                        if (string_len(elem_slop_type) > 0) {
                            return expr_slop_value_type_to_c_type(ctx, elem_slop_type);
                        } else {
                            return SLOP_STR("");
                        }
                    }
                }
            }
        }
    }
}

slop_string expr_infer_set_elem_c_type_from_slop_type(context_TranspileContext* ctx, slop_string slop_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (string_len(slop_type) == 0) {
            return SLOP_STR("");
        } else {
            {
                __auto_type resolved_type = expr_resolve_type_alias(ctx, slop_type);
                __auto_type elem_slop_type = expr_extract_set_elem_from_slop_type(arena, resolved_type);
                if (string_len(elem_slop_type) > 0) {
                    return expr_slop_value_type_to_c_type(ctx, elem_slop_type);
                } else {
                    return SLOP_STR("");
                }
            }
        }
    }
}

slop_string expr_extract_map_value_from_inferred(context_TranspileContext* ctx, types_SExpr* map_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((map_expr != NULL)), "(!= map-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type inferred_slop_type = expr_infer_expr_slop_type(ctx, map_expr);
        if (string_len(inferred_slop_type) == 0) {
            return SLOP_STR("");
        } else {
            {
                __auto_type resolved_type = expr_resolve_type_alias(ctx, inferred_slop_type);
                return expr_extract_map_value_from_slop_type(arena, resolved_type);
            }
        }
    }
}

slop_string expr_extract_list_elem_from_inferred(context_TranspileContext* ctx, types_SExpr* list_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((list_expr != NULL)), "(!= list-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type inferred_slop_type = expr_infer_expr_slop_type(ctx, list_expr);
        if (string_len(inferred_slop_type) == 0) {
            return SLOP_STR("");
        } else {
            if (strlib_starts_with(inferred_slop_type, SLOP_STR("(List "))) {
                {
                    __auto_type elem_len = ((string_len(inferred_slop_type) - 6) - 1);
                    if (elem_len > 0) {
                        return strlib_substring(arena, inferred_slop_type, 6, ((int64_t)(elem_len)));
                    } else {
                        return SLOP_STR("");
                    }
                }
            } else {
                return SLOP_STR("");
            }
        }
    }
}

slop_string expr_infer_map_key_c_type(context_TranspileContext* ctx, types_SExpr* map_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((map_expr != NULL)), "(!= map-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_208 = (*map_expr);
        switch (_mv_208.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_208.data.sym;
                {
                    __auto_type name = sym.name;
                    __auto_type _mv_209 = context_ctx_lookup_var(ctx, name);
                    if (_mv_209.has_value) {
                        __auto_type var_entry = _mv_209.value;
                        {
                            __auto_type slop_type = var_entry.slop_type;
                            if (string_len(slop_type) > 0) {
                                {
                                    __auto_type resolved_type = expr_resolve_type_alias(ctx, slop_type);
                                    __auto_type key_slop_type = expr_extract_map_key_from_slop_type(arena, resolved_type);
                                    if (string_len(key_slop_type) > 0) {
                                        return expr_slop_value_type_to_c_type(ctx, key_slop_type);
                                    } else {
                                        {
                                            __auto_type elem_slop_type = expr_extract_set_elem_from_slop_type(arena, resolved_type);
                                            if (string_len(elem_slop_type) > 0) {
                                                return expr_slop_value_type_to_c_type(ctx, elem_slop_type);
                                            } else {
                                                return SLOP_STR("");
                                            }
                                        }
                                    }
                                }
                            } else {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_209.has_value) {
                        return SLOP_STR("");
                    }
                    SLOP_UNREACHABLE();
                }
            }
            default: {
                return expr_infer_map_key_c_type_from_slop_type(ctx, expr_infer_expr_slop_type(ctx, map_expr));
            }
        }
    }
}

uint8_t expr_is_set_type(slop_string slop_type) {
    return (strlib_starts_with(slop_type, SLOP_STR("(Set ")) || strlib_starts_with(slop_type, SLOP_STR("(Ptr (Set ")));
}

uint8_t expr_is_map_type(slop_string slop_type) {
    return (strlib_starts_with(slop_type, SLOP_STR("(Map ")) || strlib_starts_with(slop_type, SLOP_STR("(Ptr (Map ")));
}

slop_string expr_extract_set_elem_from_slop_type(slop_arena* arena, slop_string raw_slop_type) {
    {
        __auto_type slop_type = ctype_unwrap_ptr_container_type(arena, raw_slop_type);
        {
            __auto_type len = string_len(slop_type);
            if (len < 7) {
                return SLOP_STR("");
            } else {
                if (!(strlib_starts_with(slop_type, SLOP_STR("(Set ")))) {
                    return SLOP_STR("");
                } else {
                    {
                        __auto_type elem_start = 5;
                        __auto_type elem_len = ((len - 1) - elem_start);
                        if (elem_len > 0) {
                            return strlib_substring(arena, slop_type, ((int64_t)(elem_start)), ((int64_t)(elem_len)));
                        } else {
                            return SLOP_STR("");
                        }
                    }
                }
            }
        }
    }
}

slop_string expr_infer_set_elem_c_type(context_TranspileContext* ctx, types_SExpr* set_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((set_expr != NULL)), "(!= set-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_210 = (*set_expr);
        switch (_mv_210.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_210.data.sym;
                {
                    __auto_type name = sym.name;
                    __auto_type _mv_211 = context_ctx_lookup_var(ctx, name);
                    if (_mv_211.has_value) {
                        __auto_type var_entry = _mv_211.value;
                        {
                            __auto_type slop_type = var_entry.slop_type;
                            if (string_len(slop_type) > 0) {
                                {
                                    __auto_type resolved_type = expr_resolve_type_alias(ctx, slop_type);
                                    __auto_type elem_slop_type = expr_extract_set_elem_from_slop_type(arena, resolved_type);
                                    if (string_len(elem_slop_type) > 0) {
                                        return expr_slop_value_type_to_c_type(ctx, elem_slop_type);
                                    } else {
                                        return SLOP_STR("");
                                    }
                                }
                            } else {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_211.has_value) {
                        return SLOP_STR("");
                    }
                    SLOP_UNREACHABLE();
                }
            }
            default: {
                return expr_infer_set_elem_c_type_from_slop_type(ctx, expr_infer_expr_slop_type(ctx, set_expr));
            }
        }
    }
}

slop_string expr_compound_slop_type_to_id(slop_arena* arena, slop_string slop_type) {
    if (strlib_starts_with(slop_type, SLOP_STR("(Set "))) {
        {
            __auto_type inner = expr_extract_set_elem_from_slop_type(arena, slop_type);
            if (string_len(inner) > 0) {
                return string_concat(arena, SLOP_STR("set_"), expr_slop_value_type_to_option_id(arena, inner));
            } else {
                return ctype_to_c_name(arena, slop_type);
            }
        }
    } else if (strlib_starts_with(slop_type, SLOP_STR("(Map "))) {
        {
            __auto_type key_type = expr_extract_map_key_from_slop_type(arena, slop_type);
            __auto_type val_type = expr_extract_map_value_from_slop_type(arena, slop_type);
            if ((string_len(key_type) > 0) && (string_len(val_type) > 0)) {
                return string_concat(arena, SLOP_STR("map_"), string_concat(arena, expr_slop_value_type_to_option_id(arena, key_type), string_concat(arena, SLOP_STR("_"), expr_slop_value_type_to_option_id(arena, val_type))));
            } else {
                return ctype_to_c_name(arena, slop_type);
            }
        }
    } else if (strlib_starts_with(slop_type, SLOP_STR("(List "))) {
        {
            __auto_type len = string_len(slop_type);
            if (len < 8) {
                return ctype_to_c_name(arena, slop_type);
            } else {
                {
                    __auto_type inner_start = 6;
                    __auto_type inner_len = ((len - 1) - inner_start);
                    if (inner_len > 0) {
                        {
                            __auto_type inner = strlib_substring(arena, slop_type, ((int64_t)(inner_start)), ((int64_t)(inner_len)));
                            return string_concat(arena, SLOP_STR("list_"), expr_slop_value_type_to_option_id(arena, inner));
                        }
                    } else {
                        return ctype_to_c_name(arena, slop_type);
                    }
                }
            }
        }
    } else if (strlib_starts_with(slop_type, SLOP_STR("(Option "))) {
        {
            __auto_type len = string_len(slop_type);
            if (len < 10) {
                return ctype_to_c_name(arena, slop_type);
            } else {
                {
                    __auto_type inner_start = 8;
                    __auto_type inner_len = ((len - 1) - inner_start);
                    if (inner_len > 0) {
                        {
                            __auto_type inner = strlib_substring(arena, slop_type, ((int64_t)(inner_start)), ((int64_t)(inner_len)));
                            return string_concat(arena, SLOP_STR("option_"), expr_slop_value_type_to_option_id(arena, inner));
                        }
                    } else {
                        return ctype_to_c_name(arena, slop_type);
                    }
                }
            }
        }
    } else if (strlib_starts_with(slop_type, SLOP_STR("(Ptr "))) {
        {
            __auto_type len = string_len(slop_type);
            if (len < 7) {
                return ctype_to_c_name(arena, slop_type);
            } else {
                {
                    __auto_type inner_start = 5;
                    __auto_type inner_len = ((len - 1) - inner_start);
                    if (inner_len > 0) {
                        {
                            __auto_type inner = strlib_substring(arena, slop_type, ((int64_t)(inner_start)), ((int64_t)(inner_len)));
                            return string_concat(arena, expr_slop_value_type_to_option_id(arena, inner), SLOP_STR("_ptr"));
                        }
                    } else {
                        return ctype_to_c_name(arena, slop_type);
                    }
                }
            }
        }
    } else {
        return ctype_to_c_name(arena, slop_type);
    }
}

slop_string expr_slop_value_type_to_option_id(slop_arena* arena, slop_string slop_type) {
    if (string_eq(slop_type, SLOP_STR("Int"))) {
        return SLOP_STR("int");
    } else if (string_eq(slop_type, SLOP_STR("I8"))) {
        return SLOP_STR("int8_t");
    } else if (string_eq(slop_type, SLOP_STR("I16"))) {
        return SLOP_STR("int16_t");
    } else if (string_eq(slop_type, SLOP_STR("I32"))) {
        return SLOP_STR("int32_t");
    } else if (string_eq(slop_type, SLOP_STR("I64"))) {
        return SLOP_STR("int64_t");
    } else if (string_eq(slop_type, SLOP_STR("U8"))) {
        return SLOP_STR("uint8_t");
    } else if (string_eq(slop_type, SLOP_STR("U16"))) {
        return SLOP_STR("uint16_t");
    } else if (string_eq(slop_type, SLOP_STR("U32"))) {
        return SLOP_STR("uint32_t");
    } else if (string_eq(slop_type, SLOP_STR("U64"))) {
        return SLOP_STR("uint64_t");
    } else if (string_eq(slop_type, SLOP_STR("Char"))) {
        return SLOP_STR("char");
    } else if (string_eq(slop_type, SLOP_STR("Float"))) {
        return SLOP_STR("float");
    } else if (string_eq(slop_type, SLOP_STR("F32"))) {
        return SLOP_STR("float");
    } else if (string_eq(slop_type, SLOP_STR("F64"))) {
        return SLOP_STR("double");
    } else if (string_eq(slop_type, SLOP_STR("Bool"))) {
        return SLOP_STR("uint8_t");
    } else if (string_eq(slop_type, SLOP_STR("String"))) {
        return SLOP_STR("string");
    } else if (string_eq(slop_type, SLOP_STR("Bytes"))) {
        return SLOP_STR("bytes");
    } else if (strlib_starts_with(slop_type, SLOP_STR("("))) {
        return expr_compound_slop_type_to_id(arena, slop_type);
    } else {
        return ctype_to_c_name(arena, slop_type);
    }
}

slop_string expr_infer_map_value_option_type(context_TranspileContext* ctx, types_SExpr* map_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((map_expr != NULL)), "(!= map-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_212 = (*map_expr);
        switch (_mv_212.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_212.data.sym;
                {
                    __auto_type name = sym.name;
                    __auto_type _mv_213 = context_ctx_lookup_var(ctx, name);
                    if (_mv_213.has_value) {
                        __auto_type var_entry = _mv_213.value;
                        {
                            __auto_type slop_type = var_entry.slop_type;
                            if (string_len(slop_type) > 0) {
                                {
                                    __auto_type resolved_type = expr_resolve_type_alias(ctx, slop_type);
                                    __auto_type value_slop_type = expr_extract_map_value_from_slop_type(arena, resolved_type);
                                    if (string_len(value_slop_type) > 0) {
                                        {
                                            __auto_type resolved_value = expr_resolve_type_alias(ctx, value_slop_type);
                                            if (strlib_starts_with(resolved_value, SLOP_STR("(Map ")) || (strlib_starts_with(resolved_value, SLOP_STR("(Set ")) || strlib_starts_with(resolved_value, SLOP_STR("(List ")))) {
                                                return SLOP_STR("slop_option_ptr");
                                            } else {
                                                {
                                                    __auto_type value_c = expr_slop_type_to_c_type(ctx, value_slop_type);
                                                    __auto_type value_id = ctype_type_to_identifier(arena, value_c);
                                                    return context_ctx_str(ctx, SLOP_STR("slop_option_"), value_id);
                                                }
                                            }
                                        }
                                    } else {
                                        return SLOP_STR("");
                                    }
                                }
                            } else {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_213.has_value) {
                        return SLOP_STR("");
                    }
                    SLOP_UNREACHABLE();
                }
            }
            default: {
                {
                    __auto_type slop_type = expr_infer_expr_slop_type(ctx, map_expr);
                    if (string_len(slop_type) > 0) {
                        {
                            __auto_type resolved_type = expr_resolve_type_alias(ctx, slop_type);
                            __auto_type value_slop_type = expr_extract_map_value_from_slop_type(arena, resolved_type);
                            if (string_len(value_slop_type) > 0) {
                                {
                                    __auto_type resolved_value = expr_resolve_type_alias(ctx, value_slop_type);
                                    if (strlib_starts_with(resolved_value, SLOP_STR("(Map ")) || (strlib_starts_with(resolved_value, SLOP_STR("(Set ")) || strlib_starts_with(resolved_value, SLOP_STR("(List ")))) {
                                        return SLOP_STR("slop_option_ptr");
                                    } else {
                                        {
                                            __auto_type value_c = expr_slop_type_to_c_type(ctx, value_slop_type);
                                            __auto_type value_id = ctype_type_to_identifier(arena, value_c);
                                            return context_ctx_str(ctx, SLOP_STR("slop_option_"), value_id);
                                        }
                                    }
                                }
                            } else {
                                return SLOP_STR("");
                            }
                        }
                    } else {
                        return SLOP_STR("");
                    }
                }
            }
        }
    }
}

slop_string expr_option_type_to_value_c_type(slop_arena* arena, slop_string option_type) {
    if (string_eq(option_type, SLOP_STR("slop_option_int"))) {
        return SLOP_STR("int64_t");
    } else if (string_eq(option_type, SLOP_STR("slop_option_string"))) {
        return SLOP_STR("slop_string");
    } else if (string_eq(option_type, SLOP_STR("slop_option_bool"))) {
        return SLOP_STR("uint8_t");
    } else if (string_eq(option_type, SLOP_STR("slop_option_float"))) {
        return SLOP_STR("double");
    } else if (string_eq(option_type, SLOP_STR("slop_option_f32"))) {
        return SLOP_STR("float");
    } else if (string_eq(option_type, SLOP_STR("slop_option_char"))) {
        return SLOP_STR("char");
    } else if (string_eq(option_type, SLOP_STR("slop_option_u8"))) {
        return SLOP_STR("uint8_t");
    } else if (string_eq(option_type, SLOP_STR("slop_option_ptr"))) {
        return SLOP_STR("void*");
    } else if (strlib_starts_with(option_type, SLOP_STR("slop_option_"))) {
        {
            __auto_type extracted = expr_substring_after_prefix(arena, option_type, SLOP_STR("slop_option_"));
            if (strlib_starts_with(extracted, SLOP_STR("set_"))) {
                return SLOP_STR("slop_map*");
            } else if (strlib_ends_with(extracted, SLOP_STR("_ptr"))) {
                {
                    __auto_type base_len = (((int64_t)(string_len(extracted))) - 4);
                    return string_concat(arena, strlib_substring(arena, extracted, 0, ((int64_t)(base_len))), SLOP_STR("*"));
                }
            } else {
                return extracted;
            }
        }
    } else {
        return SLOP_STR("void");
    }
}

slop_string expr_infer_option_inner_slop_type(context_TranspileContext* ctx, types_SExpr* scrutinee) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((scrutinee != NULL)), "(!= scrutinee nil)");
    {
        __auto_type arena = (*ctx).arena;
        {
            __auto_type expr_type = expr_infer_expr_slop_type(ctx, scrutinee);
            {
                __auto_type resolved = (((string_len(expr_type) > 0)) ? expr_resolve_type_alias(ctx, expr_type) : SLOP_STR(""));
                if (strlib_starts_with(resolved, SLOP_STR("(Option "))) {
                    {
                        __auto_type len = string_len(resolved);
                        if (len > 9) {
                            {
                                __auto_type inner_len = ((((int64_t)(len)) - 8) - 1);
                                if (inner_len > 0) {
                                    return strlib_substring(arena, resolved, 8, ((int64_t)(inner_len)));
                                } else {
                                    return SLOP_STR("");
                                }
                            }
                        } else {
                            return SLOP_STR("");
                        }
                    }
                } else {
                    __auto_type _mv_214 = (*scrutinee);
                    switch (_mv_214.tag) {
                        case types_SExpr_lst:
                        {
                            __auto_type lst = _mv_214.data.lst;
                            {
                                __auto_type items = lst.items;
                                __auto_type len = ((int64_t)((items).len));
                                if (len < 2) {
                                    return SLOP_STR("");
                                } else {
                                    __auto_type _mv_215 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_215.has_value) {
                                        __auto_type head_expr = _mv_215.value;
                                        __auto_type _mv_216 = (*head_expr);
                                        switch (_mv_216.tag) {
                                            case types_SExpr_sym:
                                            {
                                                __auto_type sym = _mv_216.data.sym;
                                                {
                                                    __auto_type op = sym.name;
                                                    if (string_eq(op, SLOP_STR("map-get"))) {
                                                        if (len < 2) {
                                                            return SLOP_STR("");
                                                        } else {
                                                            __auto_type _mv_217 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_217.has_value) {
                                                                __auto_type map_expr = _mv_217.value;
                                                                __auto_type _mv_218 = (*map_expr);
                                                                switch (_mv_218.tag) {
                                                                    case types_SExpr_sym:
                                                                    {
                                                                        __auto_type map_sym = _mv_218.data.sym;
                                                                        {
                                                                            __auto_type map_name = map_sym.name;
                                                                            __auto_type _mv_219 = context_ctx_lookup_var(ctx, map_name);
                                                                            if (_mv_219.has_value) {
                                                                                __auto_type var_entry = _mv_219.value;
                                                                                {
                                                                                    __auto_type slop_type = var_entry.slop_type;
                                                                                    if (string_len(slop_type) > 0) {
                                                                                        {
                                                                                            __auto_type resolved_type = expr_resolve_type_alias(ctx, slop_type);
                                                                                            {
                                                                                                __auto_type value_type = expr_extract_map_value_from_slop_type(arena, resolved_type);
                                                                                                return expr_resolve_type_alias(ctx, value_type);
                                                                                            }
                                                                                        }
                                                                                    } else {
                                                                                        return SLOP_STR("");
                                                                                    }
                                                                                }
                                                                            } else if (!_mv_219.has_value) {
                                                                                return SLOP_STR("");
                                                                            }
                                                                            SLOP_UNREACHABLE();
                                                                        }
                                                                    }
                                                                    default: {
                                                                        return expr_extract_map_value_from_inferred(ctx, map_expr);
                                                                    }
                                                                }
                                                            } else if (!_mv_217.has_value) {
                                                                return SLOP_STR("");
                                                            }
                                                            SLOP_UNREACHABLE();
                                                        }
                                                    } else if (string_eq(op, SLOP_STR("list-get"))) {
                                                        if (len < 2) {
                                                            return SLOP_STR("");
                                                        } else {
                                                            __auto_type _mv_220 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_220.has_value) {
                                                                __auto_type list_expr = _mv_220.value;
                                                                __auto_type _mv_221 = (*list_expr);
                                                                switch (_mv_221.tag) {
                                                                    case types_SExpr_sym:
                                                                    {
                                                                        __auto_type list_sym = _mv_221.data.sym;
                                                                        {
                                                                            __auto_type list_name = list_sym.name;
                                                                            __auto_type _mv_222 = context_ctx_lookup_var(ctx, list_name);
                                                                            if (_mv_222.has_value) {
                                                                                __auto_type var_entry = _mv_222.value;
                                                                                {
                                                                                    __auto_type slop_type = var_entry.slop_type;
                                                                                    if (strlib_starts_with(slop_type, SLOP_STR("(List "))) {
                                                                                        {
                                                                                            __auto_type elem_len = ((string_len(slop_type) - 6) - 1);
                                                                                            if (elem_len > 0) {
                                                                                                return strlib_substring(arena, slop_type, 6, ((int64_t)(elem_len)));
                                                                                            } else {
                                                                                                return SLOP_STR("");
                                                                                            }
                                                                                        }
                                                                                    } else {
                                                                                        return SLOP_STR("");
                                                                                    }
                                                                                }
                                                                            } else if (!_mv_222.has_value) {
                                                                                return SLOP_STR("");
                                                                            }
                                                                            SLOP_UNREACHABLE();
                                                                        }
                                                                    }
                                                                    default: {
                                                                        return expr_extract_list_elem_from_inferred(ctx, list_expr);
                                                                    }
                                                                }
                                                            } else if (!_mv_220.has_value) {
                                                                return SLOP_STR("");
                                                            }
                                                            SLOP_UNREACHABLE();
                                                        }
                                                    } else {
                                                        return SLOP_STR("");
                                                    }
                                                }
                                            }
                                            default: {
                                                return SLOP_STR("");
                                            }
                                        }
                                    } else if (!_mv_215.has_value) {
                                        return SLOP_STR("");
                                    }
                                    SLOP_UNREACHABLE();
                                }
                            }
                        }
                        default: {
                            return SLOP_STR("");
                        }
                    }
                }
            }
        }
    }
}

slop_string expr_fix_ternary_none(context_TranspileContext* ctx, types_SExpr* other_expr, slop_string other_branch, slop_string this_branch) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (string_eq(this_branch, SLOP_STR("none")) && strlib_starts_with(other_branch, SLOP_STR("(slop_option_"))) {
        {
            __auto_type arena = (*ctx).arena;
            __auto_type _mv_223 = expr_extract_option_type(arena, other_branch);
            if (_mv_223.has_value) {
                __auto_type opt_type = _mv_223.value;
                return context_ctx_str3(ctx, SLOP_STR("("), opt_type, SLOP_STR("){.has_value = false}"));
            } else if (!_mv_223.has_value) {
                return this_branch;
            }
            SLOP_UNREACHABLE();
        }
    } else {
        if (string_eq(this_branch, SLOP_STR("none"))) {
            {
                __auto_type inferred = expr_infer_expr_c_type(ctx, other_expr);
                if (strlib_starts_with(inferred, SLOP_STR("slop_option_"))) {
                    return context_ctx_str3(ctx, SLOP_STR("("), inferred, SLOP_STR("){.has_value = false}"));
                } else {
                    return this_branch;
                }
            }
        } else {
            return this_branch;
        }
    }
}

slop_option_string expr_extract_option_type(slop_arena* arena, slop_string s) {
    if (string_len(s) < 15) {
        return (slop_option_string){.has_value = false};
    } else {
        {
            int64_t i = 1;
            __auto_type len = string_len(s);
            uint8_t found_brace = 0;
            int64_t end_idx = 0;
            while ((i < len) && !(found_brace)) {
                if (strlib_char_at(s, ((int64_t)(i))) == 123) {
                    found_brace = 1;
                    end_idx = (i - 2);
                } else {
                    i = (i + 1);
                }
            }
            if (found_brace) {
                return (slop_option_string){.has_value = 1, .value = strlib_substring(arena, s, 1, ((int64_t)(end_idx)))};
            } else {
                return (slop_option_string){.has_value = false};
            }
        }
    }
}

slop_string expr_transpile_array_index(context_TranspileContext* ctx, types_SExpr* arr_expr, slop_string arr_c, slop_string idx_c) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((arr_expr != NULL)), "(!= arr-expr nil)");
    __auto_type _mv_224 = (*arr_expr);
    switch (_mv_224.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_224.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_225 = context_ctx_lookup_var(ctx, name);
                if (_mv_225.has_value) {
                    __auto_type var_entry = _mv_225.value;
                    {
                        __auto_type c_type = var_entry.c_type;
                        if ((string_eq(c_type, SLOP_STR("slop_string"))) || (string_eq(c_type, SLOP_STR("string"))) || (strlib_starts_with(c_type, SLOP_STR("slop_list_")))) {
                            return context_ctx_str5(ctx, SLOP_STR("("), arr_c, SLOP_STR(").data["), idx_c, SLOP_STR("]"));
                        } else {
                            return context_ctx_str4(ctx, arr_c, SLOP_STR("["), idx_c, SLOP_STR("]"));
                        }
                    }
                } else if (!_mv_225.has_value) {
                    return context_ctx_str4(ctx, arr_c, SLOP_STR("["), idx_c, SLOP_STR("]"));
                }
                SLOP_UNREACHABLE();
            }
        }
        default: {
            return context_ctx_str4(ctx, arr_c, SLOP_STR("["), idx_c, SLOP_STR("]"));
        }
    }
}

uint8_t expr_is_pointer_expr(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_226 = (*expr);
    switch (_mv_226.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_226.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_227 = context_ctx_lookup_var(ctx, name);
                if (_mv_227.has_value) {
                    __auto_type var_entry = _mv_227.value;
                    return (var_entry.is_pointer || ({ __auto_type c_type = var_entry.c_type; strlib_ends_with(c_type, SLOP_STR("*")); }));
                } else if (!_mv_227.has_value) {
                    return 0;
                }
                SLOP_UNREACHABLE();
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_226.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) >= 1) {
                    __auto_type _mv_228 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_228.has_value) {
                        __auto_type head_ptr = _mv_228.value;
                        __auto_type _mv_229 = (*head_ptr);
                        switch (_mv_229.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type head_sym = _mv_229.data.sym;
                                {
                                    __auto_type op = head_sym.name;
                                    if (string_eq(op, SLOP_STR("deref"))) {
                                        return 0;
                                    } else if (string_eq(op, SLOP_STR("addr"))) {
                                        return 1;
                                    } else if (string_eq(op, SLOP_STR("arena-alloc"))) {
                                        return 1;
                                    } else if (string_eq(op, SLOP_STR("cast")) && (((int64_t)((items).len)) >= 2)) {
                                        __auto_type _mv_230 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_230.has_value) {
                                            __auto_type type_expr = _mv_230.value;
                                            return expr_is_pointer_type_expr(type_expr);
                                        } else if (!_mv_230.has_value) {
                                            return 0;
                                        }
                                        SLOP_UNREACHABLE();
                                    } else {
                                        return 0;
                                    }
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_228.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
                } else {
                    return 0;
                }
            }
        }
        default: {
            return 0;
        }
    }
}

slop_string expr_extract_sizeof_type(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_231 = (*expr);
        switch (_mv_231.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_231.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len >= 2) {
                        __auto_type _mv_232 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_232.has_value) {
                            __auto_type head_ptr = _mv_232.value;
                            __auto_type _mv_233 = (*head_ptr);
                            switch (_mv_233.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_233.data.sym;
                                    {
                                        __auto_type op = head_sym.name;
                                        if (string_eq(op, SLOP_STR("sizeof"))) {
                                            __auto_type _mv_234 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_234.has_value) {
                                                __auto_type type_expr = _mv_234.value;
                                                return context_to_c_type_prefixed(ctx, type_expr);
                                            } else if (!_mv_234.has_value) {
                                                return SLOP_STR("uint8_t");
                                            }
                                            SLOP_UNREACHABLE();
                                        } else if (string_eq(op, SLOP_STR("*")) || (string_eq(op, SLOP_STR("+")) || (string_eq(op, SLOP_STR("-")) || string_eq(op, SLOP_STR("/"))))) {
                                            {
                                                __auto_type i = 1;
                                                __auto_type found = SLOP_STR("uint8_t");
                                                while (i < len) {
                                                    __auto_type _mv_235 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_235.has_value) {
                                                        __auto_type arg_expr = _mv_235.value;
                                                        {
                                                            __auto_type result = expr_extract_sizeof_type(ctx, arg_expr);
                                                            if (!(string_eq(result, SLOP_STR("uint8_t")))) {
                                                                found = result;
                                                            }
                                                        }
                                                    } else if (!_mv_235.has_value) {
                                                    }
                                                    i = (i + 1);
                                                }
                                                return found;
                                            }
                                        } else {
                                            return SLOP_STR("uint8_t");
                                        }
                                    }
                                }
                                default: {
                                    return SLOP_STR("uint8_t");
                                }
                            }
                        } else if (!_mv_232.has_value) {
                            return SLOP_STR("uint8_t");
                        }
                        SLOP_UNREACHABLE();
                    } else {
                        return SLOP_STR("uint8_t");
                    }
                }
            }
            default: {
                return SLOP_STR("uint8_t");
            }
        }
    }
}

slop_string expr_transpile_expr(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_236 = (*expr);
    switch (_mv_236.tag) {
        case types_SExpr_num:
        {
            __auto_type _ = _mv_236.data.num;
            return expr_transpile_literal(ctx, expr);
        }
        case types_SExpr_str:
        {
            __auto_type _ = _mv_236.data.str;
            return expr_transpile_literal(ctx, expr);
        }
        case types_SExpr_sym:
        {
            __auto_type _ = _mv_236.data.sym;
            return expr_transpile_literal(ctx, expr);
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_236.data.lst;
            return expr_transpile_list_expr(ctx, lst.items);
        }
    }
    SLOP_UNREACHABLE();
}

slop_string expr_transpile_list_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type arena = (*ctx).arena;
        if (len < 1) {
            context_ctx_add_error_at(ctx, SLOP_STR("empty list"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("0");
        } else {
            __auto_type _mv_237 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_237.has_value) {
                __auto_type head_expr = _mv_237.value;
                __auto_type _mv_238 = (*head_expr);
                switch (_mv_238.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type head_sym = _mv_238.data.sym;
                        {
                            __auto_type op = head_sym.name;
                            if (expr_is_binop(op) && (len < 3)) {
                                context_ctx_add_error_at(ctx, SLOP_STR("binary operator needs at least 2 operands"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                return SLOP_STR("0");
                            } else if (expr_is_binop(op) && (len >= 3)) {
                                if (len > 3) {
                                    return expr_transpile_variadic_binop(ctx, op, items, 1);
                                } else {
                                    __auto_type _mv_239 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_239.has_value) {
                                        __auto_type left = _mv_239.value;
                                        __auto_type _mv_240 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_240.has_value) {
                                            __auto_type right = _mv_240.value;
                                            {
                                                __auto_type left_c = expr_transpile_expr(ctx, left);
                                                __auto_type right_c = expr_transpile_expr(ctx, right);
                                                return expr_transpile_binop(ctx, op, left_c, right_c);
                                            }
                                        } else if (!_mv_240.has_value) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("missing right operand"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                            return SLOP_STR("0");
                                        }
                                        SLOP_UNREACHABLE();
                                    } else if (!_mv_239.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing left operand"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                    SLOP_UNREACHABLE();
                                }
                            } else if (expr_is_comparison_op(op) && (len < 3)) {
                                context_ctx_add_error_at(ctx, SLOP_STR("comparison operator needs 2 operands"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                return SLOP_STR("0");
                            } else if (expr_is_comparison_op(op) && (len >= 3)) {
                                __auto_type _mv_241 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_241.has_value) {
                                    __auto_type left = _mv_241.value;
                                    __auto_type _mv_242 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_242.has_value) {
                                        __auto_type right = _mv_242.value;
                                        {
                                            __auto_type left_c = expr_transpile_expr(ctx, left);
                                            __auto_type right_c = expr_transpile_expr(ctx, right);
                                            __auto_type left_type = expr_infer_expr_c_type(ctx, left);
                                            __auto_type is_eq_op = expr_is_equality_op(op);
                                            if (is_eq_op && string_eq(left_type, SLOP_STR("slop_string"))) {
                                                if (string_eq(op, SLOP_STR("!="))) {
                                                    return context_ctx_str5(ctx, SLOP_STR("(!slop_string_eq("), left_c, SLOP_STR(", "), right_c, SLOP_STR("))"));
                                                } else {
                                                    return context_ctx_str5(ctx, SLOP_STR("slop_string_eq("), left_c, SLOP_STR(", "), right_c, SLOP_STR(")"));
                                                }
                                            } else if (is_eq_op && expr_is_aggregate_c_type(ctx, left_type)) {
                                                return expr_transpile_aggregate_eq(ctx, op, left_c, right_c, left_type, left);
                                            } else if (is_eq_op && ctype_is_container_c_type(left_type)) {
                                                context_ctx_add_error_at(ctx, context_ctx_str5(ctx, SLOP_STR("'"), op, SLOP_STR("' is not defined on '"), left_type, SLOP_STR("' - match on the variants or compare fields")), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                                return SLOP_STR("0");
                                            } else {
                                                return expr_transpile_binop(ctx, op, left_c, right_c);
                                            }
                                        }
                                    } else if (!_mv_242.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing right operand"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                    SLOP_UNREACHABLE();
                                } else if (!_mv_241.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing left operand"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("not")) && (len < 2)) {
                                context_ctx_add_error_at(ctx, SLOP_STR("not needs an argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                return SLOP_STR("0");
                            } else if (string_eq(op, SLOP_STR("not")) && (len >= 2)) {
                                __auto_type _mv_243 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_243.has_value) {
                                    __auto_type arg = _mv_243.value;
                                    return context_ctx_str3(ctx, SLOP_STR("!("), expr_transpile_expr(ctx, arg), SLOP_STR(")"));
                                } else if (!_mv_243.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("if")) && (len < 4)) {
                                context_ctx_add_error_at(ctx, SLOP_STR("if expression needs condition, then, and else branches"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                return SLOP_STR("0");
                            } else if (string_eq(op, SLOP_STR("if")) && (len >= 4)) {
                                __auto_type _mv_244 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_244.has_value) {
                                    __auto_type cond_expr = _mv_244.value;
                                    __auto_type _mv_245 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_245.has_value) {
                                        __auto_type then_expr = _mv_245.value;
                                        __auto_type _mv_246 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_246.has_value) {
                                            __auto_type else_expr = _mv_246.value;
                                            {
                                                __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                                                __auto_type then_c = expr_transpile_expr(ctx, then_expr);
                                                __auto_type else_c = expr_transpile_expr(ctx, else_expr);
                                                {
                                                    __auto_type final_else = expr_fix_ternary_none(ctx, then_expr, then_c, else_c);
                                                    __auto_type final_then = expr_fix_ternary_none(ctx, else_expr, else_c, then_c);
                                                    return context_ctx_str5(ctx, SLOP_STR("(("), cond_c, SLOP_STR(") ? "), context_ctx_str3(ctx, final_then, SLOP_STR(" : "), final_else), SLOP_STR(")"));
                                                }
                                            }
                                        } else if (!_mv_246.has_value) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("missing else"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                            return SLOP_STR("0");
                                        }
                                        SLOP_UNREACHABLE();
                                    } else if (!_mv_245.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing then"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                    SLOP_UNREACHABLE();
                                } else if (!_mv_244.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing condition"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if ((string_eq(op, SLOP_STR("let")) || string_eq(op, SLOP_STR("let*"))) && (len >= 3)) {
                                return expr_transpile_let_expr(ctx, items);
                            } else if (string_eq(op, SLOP_STR("while")) && (len >= 3)) {
                                return expr_transpile_while_expr(ctx, items);
                            } else if (string_eq(op, SLOP_STR("break")) || string_eq(op, SLOP_STR("continue"))) {
                                return op;
                            } else if (strlib_starts_with(op, SLOP_STR("@")) && !(string_eq(op, SLOP_STR("@")))) {
                                return SLOP_STR("0");
                            } else if (string_eq(op, SLOP_STR("do")) && (len >= 1)) {
                                return expr_transpile_do_expr(ctx, items);
                            } else if (string_eq(op, SLOP_STR("when")) && (len >= 2)) {
                                return expr_transpile_when_expr(ctx, items);
                            } else if (string_eq(op, SLOP_STR("set!")) && (len >= 3)) {
                                return expr_transpile_set_expr(ctx, items);
                            } else if (string_eq(op, SLOP_STR("match")) && (len >= 3)) {
                                return expr_transpile_match_expr(ctx, items);
                            } else if (string_eq(op, SLOP_STR("deref")) && (len >= 2)) {
                                __auto_type _mv_247 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_247.has_value) {
                                    __auto_type arg = _mv_247.value;
                                    return context_ctx_str3(ctx, SLOP_STR("(*"), expr_transpile_expr(ctx, arg), SLOP_STR(")"));
                                } else if (!_mv_247.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR(".")) && (len >= 3)) {
                                __auto_type _mv_248 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_248.has_value) {
                                    __auto_type obj = _mv_248.value;
                                    __auto_type _mv_249 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_249.has_value) {
                                        __auto_type field_expr = _mv_249.value;
                                        __auto_type _mv_250 = (*field_expr);
                                        switch (_mv_250.tag) {
                                            case types_SExpr_sym:
                                            {
                                                __auto_type field_sym = _mv_250.data.sym;
                                                {
                                                    __auto_type obj_c = expr_transpile_expr(ctx, obj);
                                                    __auto_type field_c = ctype_to_c_name(arena, field_sym.name);
                                                    __auto_type is_ptr = expr_is_pointer_expr(ctx, obj);
                                                    if (is_ptr) {
                                                        return context_ctx_str3(ctx, obj_c, SLOP_STR("->"), field_c);
                                                    } else {
                                                        return context_ctx_str3(ctx, obj_c, SLOP_STR("."), field_c);
                                                    }
                                                }
                                            }
                                            default: {
                                                context_ctx_add_error_at(ctx, SLOP_STR("invalid field"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                                return SLOP_STR("0");
                                            }
                                        }
                                    } else if (!_mv_249.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing field"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                    SLOP_UNREACHABLE();
                                } else if (!_mv_248.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing object"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("cast")) && (len >= 3)) {
                                __auto_type _mv_251 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_251.has_value) {
                                    __auto_type type_expr = _mv_251.value;
                                    __auto_type _mv_252 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_252.has_value) {
                                        __auto_type val_expr = _mv_252.value;
                                        {
                                            __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                            if (expr_is_fn_type_expr(type_expr)) {
                                                {
                                                    __auto_type fn_ptr_type = expr_fn_type_to_c_fn_ptr(ctx, type_expr);
                                                    return context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, fn_ptr_type, context_ctx_str(ctx, SLOP_STR(")("), context_ctx_str(ctx, val_c, SLOP_STR("))")))));
                                                }
                                            } else if (expr_is_ptr_void_type(type_expr) && expr_is_closure_typed_expr(ctx, val_expr)) {
                                                return context_ctx_str(ctx, SLOP_STR("((void*)("), context_ctx_str(ctx, val_c, SLOP_STR(".fn))")));
                                            } else {
                                                {
                                                    __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                    __auto_type is_ptr_cast = expr_is_pointer_type_expr(type_expr);
                                                    __auto_type is_str_literal = expr_is_string_literal(val_expr);
                                                    if (is_ptr_cast && is_str_literal) {
                                                        return context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, c_type, context_ctx_str(ctx, SLOP_STR(")("), context_ctx_str(ctx, val_c, SLOP_STR(".data))")))));
                                                    } else {
                                                        return context_ctx_str5(ctx, SLOP_STR("(("), c_type, SLOP_STR(")("), val_c, SLOP_STR("))"));
                                                    }
                                                }
                                            }
                                        }
                                    } else if (!_mv_252.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing cast value"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                    SLOP_UNREACHABLE();
                                } else if (!_mv_251.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing cast type"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("c-inline")) && (len >= 2)) {
                                __auto_type _mv_253 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_253.has_value) {
                                    __auto_type str_expr = _mv_253.value;
                                    __auto_type _mv_254 = (*str_expr);
                                    switch (_mv_254.tag) {
                                        case types_SExpr_str:
                                        {
                                            __auto_type str = _mv_254.data.str;
                                            return str.value;
                                        }
                                        default: {
                                            context_ctx_add_error_at(ctx, SLOP_STR("c-inline requires string"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                            return SLOP_STR("");
                                        }
                                    }
                                } else if (!_mv_253.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing c-inline string"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("some")) && (len >= 2)) {
                                __auto_type _mv_255 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_255.has_value) {
                                    __auto_type val_expr = _mv_255.value;
                                    {
                                        __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                        __auto_type val_type = expr_infer_expr_c_type(ctx, val_expr);
                                        __auto_type option_type = (string_eq(val_type, SLOP_STR("__type_error__")) ? ({ context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("Cannot infer Option type for value '"), val_c, SLOP_STR("'")), context_ctx_sexpr_line(val_expr), context_ctx_sexpr_col(val_expr)); SLOP_STR("__type_error__"); }) : (string_eq(val_type, SLOP_STR("slop_string")) ? SLOP_STR("slop_option_string") : (string_eq(val_type, SLOP_STR("int64_t")) ? SLOP_STR("slop_option_int") : (string_eq(val_type, SLOP_STR("double")) ? SLOP_STR("slop_option_float") : (string_eq(val_type, SLOP_STR("auto")) ? ({ context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("Cannot infer Option type for value '"), val_c, SLOP_STR("' - type is 'auto'")), context_ctx_sexpr_line(val_expr), context_ctx_sexpr_col(val_expr)); SLOP_STR("__type_error__"); }) : expr_infer_option_type(ctx, val_expr))))));
                                        if (string_eq(option_type, SLOP_STR("__type_error__")) || strlib_starts_with(option_type, SLOP_STR("/*"))) {
                                            if (strlib_starts_with(option_type, SLOP_STR("/*"))) {
                                                context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("Cannot infer Option type for value '"), val_c, SLOP_STR("'")), context_ctx_sexpr_line(val_expr), context_ctx_sexpr_col(val_expr));
                                            }
                                            return SLOP_STR("(slop_option_int){.has_value = 0}");
                                        } else {
                                            context_ctx_register_option_type(ctx, expr_option_type_to_value_c_type(arena, option_type), option_type);
                                            return context_ctx_str5(ctx, SLOP_STR("("), option_type, SLOP_STR("){.has_value = 1, .value = "), val_c, SLOP_STR("}"));
                                        }
                                    }
                                } else if (!_mv_255.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing some value"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("sizeof")) && (len >= 2)) {
                                __auto_type _mv_256 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_256.has_value) {
                                    __auto_type type_expr = _mv_256.value;
                                    {
                                        __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                        return context_ctx_str3(ctx, SLOP_STR("sizeof("), c_type, SLOP_STR(")"));
                                    }
                                } else if (!_mv_256.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing sizeof type"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("addr")) && (len >= 2)) {
                                __auto_type _mv_257 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_257.has_value) {
                                    __auto_type arg = _mv_257.value;
                                    return context_ctx_str3(ctx, SLOP_STR("(&"), expr_transpile_expr(ctx, arg), SLOP_STR(")"));
                                } else if (!_mv_257.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing addr argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("@")) && (len >= 3)) {
                                __auto_type _mv_258 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_258.has_value) {
                                    __auto_type arr_expr = _mv_258.value;
                                    __auto_type _mv_259 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_259.has_value) {
                                        __auto_type idx_expr = _mv_259.value;
                                        {
                                            __auto_type arr_c = expr_transpile_expr(ctx, arr_expr);
                                            __auto_type idx_c = expr_transpile_expr(ctx, idx_expr);
                                            return expr_transpile_array_index(ctx, arr_expr, arr_c, idx_c);
                                        }
                                    } else if (!_mv_259.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing index"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                    SLOP_UNREACHABLE();
                                } else if (!_mv_258.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing array"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("arena-alloc")) && (len >= 3)) {
                                __auto_type _mv_260 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_260.has_value) {
                                    __auto_type arena_expr = _mv_260.value;
                                    __auto_type _mv_261 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_261.has_value) {
                                        __auto_type size_expr = _mv_261.value;
                                        {
                                            __auto_type arena_c = expr_transpile_expr(ctx, arena_expr);
                                            __auto_type _mv_262 = (*size_expr);
                                            switch (_mv_262.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type sym = _mv_262.data.sym;
                                                    {
                                                        __auto_type type_name = sym.name;
                                                        __auto_type _mv_263 = context_ctx_lookup_type(ctx, type_name);
                                                        if (_mv_263.has_value) {
                                                            __auto_type entry = _mv_263.value;
                                                            {
                                                                __auto_type c_type = entry.c_name;
                                                                return expr_wrap_arena_alloc_checked(ctx, context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, c_type, context_ctx_str(ctx, SLOP_STR("*)slop_arena_alloc("), context_ctx_str(ctx, arena_c, context_ctx_str(ctx, SLOP_STR(", sizeof("), context_ctx_str(ctx, c_type, SLOP_STR(")))"))))))));
                                                            }
                                                        } else if (!_mv_263.has_value) {
                                                            {
                                                                __auto_type size_c = expr_transpile_expr(ctx, size_expr);
                                                                __auto_type cast_type = expr_extract_sizeof_type(ctx, size_expr);
                                                                return expr_wrap_arena_alloc_checked(ctx, context_ctx_str5(ctx, SLOP_STR("("), cast_type, SLOP_STR("*)slop_arena_alloc("), context_ctx_str3(ctx, arena_c, SLOP_STR(", "), size_c), SLOP_STR(")")));
                                                            }
                                                        }
                                                        SLOP_UNREACHABLE();
                                                    }
                                                }
                                                default: {
                                                    {
                                                        __auto_type size_c = expr_transpile_expr(ctx, size_expr);
                                                        __auto_type cast_type = expr_extract_sizeof_type(ctx, size_expr);
                                                        return expr_wrap_arena_alloc_checked(ctx, context_ctx_str5(ctx, SLOP_STR("("), cast_type, SLOP_STR("*)slop_arena_alloc("), context_ctx_str3(ctx, arena_c, SLOP_STR(", "), size_c), SLOP_STR(")")));
                                                    }
                                                }
                                            }
                                        }
                                    } else if (!_mv_261.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing arena-alloc size"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                        return SLOP_STR("NULL");
                                    }
                                    SLOP_UNREACHABLE();
                                } else if (!_mv_260.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing arena argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("NULL");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("arena-new")) && (len >= 2)) {
                                __auto_type _mv_264 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_264.has_value) {
                                    __auto_type size_expr = _mv_264.value;
                                    {
                                        __auto_type size_c = expr_transpile_expr(ctx, size_expr);
                                        return context_ctx_str3(ctx, SLOP_STR("({ slop_arena* _new_arena = malloc(sizeof(slop_arena)); if (!_new_arena) { fprintf(stderr, \"SLOP: arena-new malloc failed\\n\"); abort(); } *_new_arena = slop_arena_new("), size_c, SLOP_STR("); _new_arena; })"));
                                    }
                                } else if (!_mv_264.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("arena-new requires size argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("NULL");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("arena-free")) && (len >= 2)) {
                                __auto_type _mv_265 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_265.has_value) {
                                    __auto_type arena_expr = _mv_265.value;
                                    {
                                        __auto_type arena_c = expr_transpile_expr(ctx, arena_expr);
                                        return context_ctx_str5(ctx, SLOP_STR("({ slop_arena_free("), arena_c, SLOP_STR("); free("), arena_c, SLOP_STR("); })"));
                                    }
                                } else if (!_mv_265.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("arena-free requires arena argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("(void)0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("quote")) && (len >= 2)) {
                                __auto_type _mv_266 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_266.has_value) {
                                    __auto_type variant_expr = _mv_266.value;
                                    __auto_type _mv_267 = (*variant_expr);
                                    switch (_mv_267.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_267.data.sym;
                                            {
                                                __auto_type variant_name = sym.name;
                                                return expr_transpile_enum_variant(ctx, variant_name);
                                            }
                                        }
                                        default: {
                                            context_ctx_add_error_at(ctx, SLOP_STR("quote requires symbol"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                            return SLOP_STR("0");
                                        }
                                    }
                                } else if (!_mv_266.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing quote argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("record-new")) && (len >= 2)) {
                                return expr_transpile_record_new(ctx, items);
                            } else if (string_eq(op, SLOP_STR("list")) && (len >= 2)) {
                                return expr_transpile_list_literal(ctx, items);
                            } else if (string_eq(op, SLOP_STR("map-new")) && (len >= 2)) {
                                return expr_transpile_map_new(ctx, items);
                            } else if (string_eq(op, SLOP_STR("map-put")) && (len >= 4)) {
                                return expr_transpile_map_put(ctx, items);
                            } else if (string_eq(op, SLOP_STR("map-get")) && (len >= 3)) {
                                return expr_transpile_map_get(ctx, items);
                            } else if (string_eq(op, SLOP_STR("map-has")) && (len >= 3)) {
                                return expr_transpile_map_has(ctx, items);
                            } else if (string_eq(op, SLOP_STR("map-keys")) && (len >= 2)) {
                                return expr_transpile_map_keys(ctx, items);
                            } else if (string_eq(op, SLOP_STR("map-remove")) && (len >= 3)) {
                                return expr_transpile_map_remove(ctx, items);
                            } else if (string_eq(op, SLOP_STR("set")) && (len >= 2)) {
                                return expr_transpile_set_literal(ctx, items);
                            } else if (string_eq(op, SLOP_STR("set-new")) && (len >= 3)) {
                                return expr_transpile_set_new(ctx, items);
                            } else if (string_eq(op, SLOP_STR("set-put")) && (len >= 3)) {
                                return expr_transpile_set_put(ctx, items);
                            } else if (string_eq(op, SLOP_STR("set-has")) && (len >= 3)) {
                                return expr_transpile_set_has(ctx, items);
                            } else if (string_eq(op, SLOP_STR("set-remove")) && (len >= 3)) {
                                return expr_transpile_set_remove(ctx, items);
                            } else if (string_eq(op, SLOP_STR("set-elements")) && (len >= 2)) {
                                return expr_transpile_set_elements(ctx, items);
                            } else if (string_eq(op, SLOP_STR("union-new")) && (len >= 3)) {
                                __auto_type _mv_268 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_268.has_value) {
                                    __auto_type type_expr = _mv_268.value;
                                    __auto_type _mv_269 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_269.has_value) {
                                        __auto_type tag_expr = _mv_269.value;
                                        __auto_type _mv_270 = (*type_expr);
                                        switch (_mv_270.tag) {
                                            case types_SExpr_sym:
                                            {
                                                __auto_type type_sym = _mv_270.data.sym;
                                                __auto_type _mv_271 = expr_extract_symbol_name(tag_expr);
                                                if (_mv_271.has_value) {
                                                    __auto_type tag_str = _mv_271.value;
                                                    {
                                                        __auto_type raw_type_name = type_sym.name;
                                                        __auto_type type_name = ({ __auto_type _mv = context_ctx_lookup_type(ctx, raw_type_name); _mv.has_value ? ({ __auto_type entry = _mv.value; entry.c_name; }) : (ctype_to_c_name(arena, raw_type_name)); });
                                                        __auto_type tag_name = ctype_to_c_name(arena, tag_str);
                                                        __auto_type tag_const = context_ctx_str(ctx, type_name, context_ctx_str(ctx, SLOP_STR("_"), tag_name));
                                                        if (len >= 5) {
                                                            {
                                                                slop_string field_init = SLOP_STR("");
                                                                for (int64_t vi = 3; vi < len; vi++) {
                                                                    __auto_type _mv_272 = ({ __auto_type _lst = items; size_t _idx = (size_t)vi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                    if (_mv_272.has_value) {
                                                                        __auto_type val_expr = _mv_272.value;
                                                                        {
                                                                            __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                                            __auto_type field_name = context_ctx_str(ctx, SLOP_STR(".f"), int_to_string(arena, (vi - 3)));
                                                                            __auto_type assignment = context_ctx_str3(ctx, field_name, SLOP_STR(" = "), val_c);
                                                                            field_init = ((string_eq(field_init, SLOP_STR(""))) ? assignment : context_ctx_str3(ctx, field_init, SLOP_STR(", "), assignment));
                                                                        }
                                                                    } else if (!_mv_272.has_value) {
                                                                    }
                                                                }
                                                                return context_ctx_str3(ctx, SLOP_STR("(("), type_name, context_ctx_str3(ctx, SLOP_STR("){ .tag = "), tag_const, context_ctx_str5(ctx, SLOP_STR(", .data."), tag_name, SLOP_STR(" = { "), field_init, SLOP_STR(" } })"))));
                                                            }
                                                        } else if (len >= 4) {
                                                            __auto_type _mv_273 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_273.has_value) {
                                                                __auto_type val_expr = _mv_273.value;
                                                                {
                                                                    __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                                    return context_ctx_str3(ctx, SLOP_STR("(("), type_name, context_ctx_str3(ctx, SLOP_STR("){ .tag = "), tag_const, context_ctx_str5(ctx, SLOP_STR(", .data."), tag_name, SLOP_STR(" = "), val_c, SLOP_STR(" })"))));
                                                                }
                                                            } else if (!_mv_273.has_value) {
                                                                context_ctx_add_error_at(ctx, SLOP_STR("missing union value"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                                                return SLOP_STR("0");
                                                            }
                                                            SLOP_UNREACHABLE();
                                                        } else {
                                                            return context_ctx_str3(ctx, SLOP_STR("(("), type_name, context_ctx_str3(ctx, SLOP_STR("){ .tag = "), tag_const, SLOP_STR(" })")));
                                                        }
                                                    }
                                                } else if (!_mv_271.has_value) {
                                                    context_ctx_add_error_at(ctx, SLOP_STR("union-new tag must be symbol"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                                    return SLOP_STR("0");
                                                }
                                                SLOP_UNREACHABLE();
                                            }
                                            default: {
                                                context_ctx_add_error_at(ctx, SLOP_STR("union-new type must be symbol"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                                return SLOP_STR("0");
                                            }
                                        }
                                    } else if (!_mv_269.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing union tag"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                    SLOP_UNREACHABLE();
                                } else if (!_mv_268.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing union type"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("ok")) && (len >= 2)) {
                                __auto_type _mv_274 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_274.has_value) {
                                    __auto_type val_expr = _mv_274.value;
                                    {
                                        __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                        return expr_transpile_ok(ctx, val_c);
                                    }
                                } else if (!_mv_274.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing ok value"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("error")) && (len >= 2)) {
                                __auto_type _mv_275 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_275.has_value) {
                                    __auto_type val_expr = _mv_275.value;
                                    {
                                        __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                        return expr_transpile_error(ctx, val_c);
                                    }
                                } else if (!_mv_275.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing error value"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("?")) && (len >= 2)) {
                                __auto_type _mv_276 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_276.has_value) {
                                    __auto_type result_expr = _mv_276.value;
                                    {
                                        __auto_type result_c = expr_transpile_expr(ctx, result_expr);
                                        __auto_type _mv_277 = context_ctx_get_current_result_type(ctx);
                                        if (_mv_277.has_value) {
                                            __auto_type enclosing_type = _mv_277.value;
                                            return context_ctx_str5(ctx, SLOP_STR("({ __auto_type _tmp = "), result_c, SLOP_STR("; if (!_tmp.is_ok) return (("), enclosing_type, SLOP_STR("){ .is_ok = false, .data.err = _tmp.data.err }); _tmp.data.ok; })"));
                                        } else if (!_mv_277.has_value) {
                                            return context_ctx_str3(ctx, SLOP_STR("({ __auto_type _tmp = "), result_c, SLOP_STR("; if (!_tmp.is_ok) return _tmp; _tmp.data.ok; })"));
                                        }
                                        SLOP_UNREACHABLE();
                                    }
                                } else if (!_mv_276.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing ? argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (((string_eq(op, SLOP_STR("is-none")) || string_eq(op, SLOP_STR("is-some")))) && ((len >= 2)) && (!(expr_local_callable_shadows(ctx, op)))) {
                                __auto_type _mv_278 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_278.has_value) {
                                    __auto_type opt_expr = _mv_278.value;
                                    {
                                        __auto_type opt_c = expr_transpile_expr(ctx, opt_expr);
                                        __auto_type bang = ((string_eq(op, SLOP_STR("is-none"))) ? SLOP_STR("!") : SLOP_STR(""));
                                        return context_ctx_str5(ctx, SLOP_STR("("), bang, SLOP_STR("(("), opt_c, SLOP_STR(").has_value))"));
                                    }
                                } else if (!_mv_278.has_value) {
                                    context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("missing "), op, SLOP_STR(" argument")), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("list-len")) && (len >= 2)) {
                                __auto_type _mv_279 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_279.has_value) {
                                    __auto_type list_expr = _mv_279.value;
                                    {
                                        __auto_type list_c = expr_transpile_expr(ctx, list_expr);
                                        return context_ctx_str3(ctx, SLOP_STR("((int64_t)(("), list_c, SLOP_STR(").len))"));
                                    }
                                } else if (!_mv_279.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing list-len argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("list-get")) && (len >= 3)) {
                                __auto_type _mv_280 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_280.has_value) {
                                    __auto_type list_expr = _mv_280.value;
                                    __auto_type _mv_281 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_281.has_value) {
                                        __auto_type idx_expr = _mv_281.value;
                                        {
                                            __auto_type list_c = expr_transpile_expr(ctx, list_expr);
                                            __auto_type idx_c = expr_transpile_expr(ctx, idx_expr);
                                            __auto_type option_type = expr_infer_list_element_option_type(ctx, list_expr);
                                            if (string_len(option_type) > 0) {
                                                return context_ctx_str(ctx, SLOP_STR("({ __auto_type _lst = "), context_ctx_str(ctx, list_c, context_ctx_str(ctx, SLOP_STR("; size_t _idx = (size_t)"), context_ctx_str(ctx, idx_c, context_ctx_str(ctx, SLOP_STR("; "), context_ctx_str(ctx, option_type, SLOP_STR(" _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; })")))))));
                                            } else {
                                                return context_ctx_str(ctx, SLOP_STR("({ __auto_type _lst = "), context_ctx_str(ctx, list_c, context_ctx_str(ctx, SLOP_STR("; size_t _idx = (size_t)"), context_ctx_str(ctx, idx_c, SLOP_STR("; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; })")))));
                                            }
                                        }
                                    } else if (!_mv_281.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing list-get index"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                    SLOP_UNREACHABLE();
                                } else if (!_mv_280.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing list-get list argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("list-pop")) && (len >= 2)) {
                                __auto_type _mv_282 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_282.has_value) {
                                    __auto_type list_expr = _mv_282.value;
                                    {
                                        __auto_type list_c = expr_transpile_expr(ctx, list_expr);
                                        __auto_type option_type = expr_infer_list_element_option_type(ctx, list_expr);
                                        if (string_len(option_type) > 0) {
                                            return context_ctx_str(ctx, SLOP_STR("({ __auto_type _lst_p = &("), context_ctx_str(ctx, list_c, context_ctx_str(ctx, SLOP_STR("); "), context_ctx_str(ctx, option_type, SLOP_STR(" _r = {0}; if (_lst_p->len > 0) { _lst_p->len--; _r.has_value = true; _r.value = _lst_p->data[_lst_p->len]; } _r; })")))));
                                        } else {
                                            return context_ctx_str(ctx, SLOP_STR("({ __auto_type _lst_p = &("), context_ctx_str(ctx, list_c, SLOP_STR("); struct { bool has_value; __typeof__(_lst_p->data[0]) value; } _r = {0}; if (_lst_p->len > 0) { _lst_p->len--; _r.has_value = true; _r.value = _lst_p->data[_lst_p->len]; } _r; })")));
                                        }
                                    }
                                } else if (!_mv_282.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing list-pop list argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("list-new")) && (len >= 3)) {
                                __auto_type _mv_283 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_283.has_value) {
                                    __auto_type arena_expr = _mv_283.value;
                                    __auto_type _mv_284 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_284.has_value) {
                                        __auto_type type_expr = _mv_284.value;
                                        {
                                            __auto_type arena_c = expr_transpile_expr(ctx, arena_expr);
                                            __auto_type elem_c_type = context_to_c_type_prefixed(ctx, type_expr);
                                            __auto_type elem_id = ctype_type_to_identifier(arena, elem_c_type);
                                            __auto_type list_type = context_ctx_str(ctx, SLOP_STR("slop_list_"), elem_id);
                                            context_ctx_register_list_type(ctx, elem_c_type, list_type);
                                            context_ctx_register_option_type(ctx, elem_c_type, context_ctx_str(ctx, SLOP_STR("slop_option_"), elem_id));
                                            return context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, list_type, context_ctx_str(ctx, SLOP_STR("){ .data = ("), context_ctx_str(ctx, elem_c_type, context_ctx_str(ctx, SLOP_STR("*)slop_arena_alloc("), context_ctx_str(ctx, arena_c, context_ctx_str(ctx, SLOP_STR(", 16 * sizeof("), context_ctx_str(ctx, elem_c_type, SLOP_STR(")), .len = 0, .cap = 16 })")))))))));
                                        }
                                    } else if (!_mv_284.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing list-new type argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                    SLOP_UNREACHABLE();
                                } else if (!_mv_283.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing list-new arena argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("list-push")) && (len >= 3)) {
                                __auto_type _mv_285 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_285.has_value) {
                                    __auto_type list_expr = _mv_285.value;
                                    __auto_type _mv_286 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_286.has_value) {
                                        __auto_type item_expr = _mv_286.value;
                                        {
                                            __auto_type list_c = expr_transpile_expr(ctx, list_expr);
                                            __auto_type item_c = expr_transpile_expr(ctx, item_expr);
                                            __auto_type arena_c = expr_get_arena_for_list_push_expr(ctx, list_expr, list_c);
                                            {
                                                __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _lst_p = &("), list_c);
                                                __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("); __auto_type _item = ("));
                                                __auto_type s3 = context_ctx_str(ctx, s2, item_c);
                                                __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR("); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc("));
                                                __auto_type s5 = context_ctx_str(ctx, s4, arena_c);
                                                __auto_type s6 = context_ctx_str(ctx, s5, SLOP_STR(", _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; })"));
                                                return s6;
                                            }
                                        }
                                    } else if (!_mv_286.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing list-push item"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                    SLOP_UNREACHABLE();
                                } else if (!_mv_285.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing list-push list"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if ((string_eq(op, SLOP_STR("list-set"))) && ((len >= 4)) && (!(expr_local_callable_shadows(ctx, op)))) {
                                __auto_type _mv_287 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_287.has_value) {
                                    __auto_type list_expr = _mv_287.value;
                                    __auto_type _mv_288 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_288.has_value) {
                                        __auto_type idx_expr = _mv_288.value;
                                        __auto_type _mv_289 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_289.has_value) {
                                            __auto_type val_expr = _mv_289.value;
                                            {
                                                __auto_type list_c = expr_transpile_expr(ctx, list_expr);
                                                __auto_type idx_c = expr_transpile_expr(ctx, idx_expr);
                                                __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                {
                                                    __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _set_lst = &("), list_c);
                                                    __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("); size_t _set_idx = (size_t)("));
                                                    __auto_type s3 = context_ctx_str(ctx, s2, idx_c);
                                                    __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR("); __auto_type _set_val = ("));
                                                    __auto_type s5 = context_ctx_str(ctx, s4, val_c);
                                                    __auto_type s6 = context_ctx_str(ctx, s5, SLOP_STR("); bool _set_ok = _set_idx < _set_lst->len; if (_set_ok) { _set_lst->data[_set_idx] = _set_val; } _set_ok; })"));
                                                    return s6;
                                                }
                                            }
                                        } else if (!_mv_289.has_value) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("missing list-set value"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                            return SLOP_STR("0");
                                        }
                                        SLOP_UNREACHABLE();
                                    } else if (!_mv_288.has_value) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("missing list-set index"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                        return SLOP_STR("0");
                                    }
                                    SLOP_UNREACHABLE();
                                } else if (!_mv_287.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("missing list-set list"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("none")) && (len == 1)) {
                                __auto_type _mv_290 = context_ctx_get_current_return_type(ctx);
                                if (_mv_290.has_value) {
                                    __auto_type ret_type = _mv_290.value;
                                    if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                                        return context_ctx_str3(ctx, SLOP_STR("(("), ret_type, SLOP_STR("){.has_value = false})"));
                                    } else {
                                        return SLOP_STR("none");
                                    }
                                } else if (!_mv_290.has_value) {
                                    return SLOP_STR("none");
                                }
                                SLOP_UNREACHABLE();
                            } else if (string_eq(op, SLOP_STR("cond"))) {
                                return expr_transpile_cond_expr(ctx, items);
                            } else if (string_eq(op, SLOP_STR("for"))) {
                                return expr_transpile_for_as_expr(ctx, items);
                            } else if (string_eq(op, SLOP_STR("for-each"))) {
                                return expr_transpile_for_each_as_expr(ctx, items);
                            } else if (string_eq(op, SLOP_STR("fn"))) {
                                return expr_transpile_lambda_expr(ctx, items);
                            } else if (string_eq(op, SLOP_STR("with-arena"))) {
                                return expr_transpile_with_arena_expr(ctx, items);
                            } else {
                                return expr_transpile_fn_call(ctx, op, items);
                            }
                        }
                    }
                    default: {
                        {
                            __auto_type head_c = expr_transpile_expr(ctx, head_expr);
                            __auto_type args = SLOP_STR("");
                            __auto_type i = 1;
                            while (i < len) {
                                __auto_type _mv_291 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_291.has_value) {
                                    __auto_type arg = _mv_291.value;
                                    {
                                        __auto_type arg_c = expr_transpile_expr(ctx, arg);
                                        if (string_eq(args, SLOP_STR(""))) {
                                            args = arg_c;
                                        } else {
                                            args = context_ctx_str3(ctx, args, SLOP_STR(", "), arg_c);
                                        }
                                    }
                                } else if (!_mv_291.has_value) {
                                }
                                i = (i + 1);
                            }
                            return context_ctx_str5(ctx, head_c, SLOP_STR("("), args, SLOP_STR(")"), SLOP_STR(""));
                        }
                    }
                }
            } else if (!_mv_237.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("empty list"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("0");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_fn_call(context_TranspileContext* ctx, slop_string fn_name, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (string_eq(fn_name, SLOP_STR("println"))) {
            if (len < 2) {
                return SLOP_STR("printf(\"\\n\")");
            } else {
                __auto_type _mv_292 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_292.has_value) {
                    __auto_type arg = _mv_292.value;
                    return expr_transpile_print(ctx, arg, 1);
                } else if (!_mv_292.has_value) {
                    return SLOP_STR("printf(\"\\n\")");
                }
                SLOP_UNREACHABLE();
            }
        } else if (string_eq(fn_name, SLOP_STR("print"))) {
            if (len < 2) {
                context_ctx_add_error_at(ctx, SLOP_STR("print: missing argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("0");
            } else {
                __auto_type _mv_293 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_293.has_value) {
                    __auto_type arg = _mv_293.value;
                    return expr_transpile_print(ctx, arg, 0);
                } else if (!_mv_293.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("print: missing argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("0");
                }
                SLOP_UNREACHABLE();
            }
        } else if (string_eq(fn_name, SLOP_STR("printf"))) {
            return expr_transpile_printf_call(ctx, items);
        } else if (string_eq(fn_name, SLOP_STR("string-new"))) {
            return expr_transpile_raw_string_fn_call(ctx, fn_name, items);
        } else if (string_eq(fn_name, SLOP_STR("min"))) {
            if (len < 3) {
                context_ctx_add_error_at(ctx, SLOP_STR("min: need 2 arguments"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("0");
            } else {
                __auto_type _mv_294 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_294.has_value) {
                    __auto_type a_expr = _mv_294.value;
                    __auto_type _mv_295 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_295.has_value) {
                        __auto_type b_expr = _mv_295.value;
                        {
                            __auto_type a_c = expr_transpile_expr(ctx, a_expr);
                            __auto_type b_c = expr_transpile_expr(ctx, b_expr);
                            __auto_type s1 = string_concat(arena, SLOP_STR("(("), a_c);
                            __auto_type s2 = string_concat(arena, s1, SLOP_STR(") < ("));
                            __auto_type s3 = string_concat(arena, s2, b_c);
                            __auto_type s4 = string_concat(arena, s3, SLOP_STR(") ? ("));
                            __auto_type s5 = string_concat(arena, s4, a_c);
                            __auto_type s6 = string_concat(arena, s5, SLOP_STR(") : ("));
                            __auto_type s7 = string_concat(arena, s6, b_c);
                            __auto_type s8 = string_concat(arena, s7, SLOP_STR("))"));
                            return s8;
                        }
                    } else if (!_mv_295.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("min: missing second argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                        return SLOP_STR("0");
                    }
                    SLOP_UNREACHABLE();
                } else if (!_mv_294.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("min: missing first argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("0");
                }
                SLOP_UNREACHABLE();
            }
        } else if (string_eq(fn_name, SLOP_STR("max"))) {
            if (len < 3) {
                context_ctx_add_error_at(ctx, SLOP_STR("max: need 2 arguments"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("0");
            } else {
                __auto_type _mv_296 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_296.has_value) {
                    __auto_type a_expr = _mv_296.value;
                    __auto_type _mv_297 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_297.has_value) {
                        __auto_type b_expr = _mv_297.value;
                        {
                            __auto_type a_c = expr_transpile_expr(ctx, a_expr);
                            __auto_type b_c = expr_transpile_expr(ctx, b_expr);
                            __auto_type s1 = string_concat(arena, SLOP_STR("(("), a_c);
                            __auto_type s2 = string_concat(arena, s1, SLOP_STR(") > ("));
                            __auto_type s3 = string_concat(arena, s2, b_c);
                            __auto_type s4 = string_concat(arena, s3, SLOP_STR(") ? ("));
                            __auto_type s5 = string_concat(arena, s4, a_c);
                            __auto_type s6 = string_concat(arena, s5, SLOP_STR(") : ("));
                            __auto_type s7 = string_concat(arena, s6, b_c);
                            __auto_type s8 = string_concat(arena, s7, SLOP_STR("))"));
                            return s8;
                        }
                    } else if (!_mv_297.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("max: missing second argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                        return SLOP_STR("0");
                    }
                    SLOP_UNREACHABLE();
                } else if (!_mv_296.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("max: missing first argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("0");
                }
                SLOP_UNREACHABLE();
            }
        } else if (string_eq(fn_name, SLOP_STR("spawn"))) {
            if (len < 3) {
                context_ctx_add_error_at(ctx, SLOP_STR("spawn: need arena and function arguments"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("NULL");
            } else {
                __auto_type _mv_298 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_298.has_value) {
                    __auto_type fn_expr = _mv_298.value;
                    if (expr_is_capturing_lambda(fn_expr)) {
                        return expr_transpile_spawn_closure(ctx, items, fn_expr);
                    } else {
                        return expr_transpile_regular_fn_call(ctx, fn_name, items);
                    }
                } else if (!_mv_298.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("spawn: missing function argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("NULL");
                }
                SLOP_UNREACHABLE();
            }
        } else if (string_eq(fn_name, SLOP_STR("chan-buffered")) || strlib_ends_with(fn_name, SLOP_STR(":chan-buffered"))) {
            if (len < 4) {
                context_ctx_add_error_at(ctx, SLOP_STR("chan-buffered: need Type, arena, and capacity arguments"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("NULL");
            } else {
                __auto_type _mv_299 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_299.has_value) {
                    __auto_type type_expr = _mv_299.value;
                    __auto_type _mv_300 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_300.has_value) {
                        __auto_type arena_expr = _mv_300.value;
                        __auto_type _mv_301 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_301.has_value) {
                            __auto_type cap_expr = _mv_301.value;
                            {
                                __auto_type elem_c = context_to_c_type_prefixed(ctx, type_expr);
                                __auto_type elem_id = ctype_type_to_identifier(arena, elem_c);
                                __auto_type chan_type = context_ctx_str(ctx, SLOP_STR("slop_chan_"), elem_id);
                                __auto_type arena_c = expr_transpile_expr(ctx, arena_expr);
                                __auto_type cap_c = expr_transpile_expr(ctx, cap_expr);
                                context_ctx_register_chan_type(ctx, elem_c, chan_type);
                                {
                                    __auto_type call = context_ctx_str5(ctx, SLOP_STR("thread_chan_buffered("), arena_c, SLOP_STR(", "), cap_c, SLOP_STR(")"));
                                    return context_ctx_str5(ctx, SLOP_STR("("), chan_type, SLOP_STR("*)"), call, SLOP_STR(""));
                                }
                            }
                        } else if (!_mv_301.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("chan-buffered: missing capacity argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                            return SLOP_STR("NULL");
                        }
                        SLOP_UNREACHABLE();
                    } else if (!_mv_300.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("chan-buffered: missing arena argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                        return SLOP_STR("NULL");
                    }
                    SLOP_UNREACHABLE();
                } else if (!_mv_299.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("chan-buffered: missing type argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("NULL");
                }
                SLOP_UNREACHABLE();
            }
        } else if (string_eq(fn_name, SLOP_STR("chan")) || strlib_ends_with(fn_name, SLOP_STR(":chan"))) {
            if (len < 3) {
                context_ctx_add_error_at(ctx, SLOP_STR("chan: need Type and arena arguments"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("NULL");
            } else {
                __auto_type _mv_302 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_302.has_value) {
                    __auto_type type_expr = _mv_302.value;
                    __auto_type _mv_303 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_303.has_value) {
                        __auto_type arena_expr = _mv_303.value;
                        {
                            __auto_type elem_c = context_to_c_type_prefixed(ctx, type_expr);
                            __auto_type elem_id = ctype_type_to_identifier(arena, elem_c);
                            __auto_type chan_type = context_ctx_str(ctx, SLOP_STR("slop_chan_"), elem_id);
                            __auto_type arena_c = expr_transpile_expr(ctx, arena_expr);
                            context_ctx_register_chan_type(ctx, elem_c, chan_type);
                            {
                                __auto_type call = context_ctx_str3(ctx, SLOP_STR("thread_chan("), arena_c, SLOP_STR(")"));
                                return context_ctx_str5(ctx, SLOP_STR("("), chan_type, SLOP_STR("*)"), call, SLOP_STR(""));
                            }
                        }
                    } else if (!_mv_303.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("chan: missing arena argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                        return SLOP_STR("NULL");
                    }
                    SLOP_UNREACHABLE();
                } else if (!_mv_302.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("chan: missing type argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("NULL");
                }
                SLOP_UNREACHABLE();
            }
        } else if (string_eq(fn_name, SLOP_STR("send"))) {
            if (len < 3) {
                context_ctx_add_error_at(ctx, SLOP_STR("send: need channel and value arguments"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("0");
            } else {
                __auto_type _mv_304 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_304.has_value) {
                    __auto_type chan_expr = _mv_304.value;
                    __auto_type _mv_305 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_305.has_value) {
                        __auto_type value_expr = _mv_305.value;
                        {
                            __auto_type chan_c = expr_transpile_expr(ctx, chan_expr);
                            __auto_type value_c = expr_transpile_expr(ctx, value_expr);
                            __auto_type chan_c_type = expr_infer_expr_c_type(ctx, chan_expr);
                            {
                                __auto_type chan_type = expr_strip_pointer_suffix(arena, chan_c_type);
                                if (strlib_starts_with(chan_type, SLOP_STR("slop_chan_")) && !(string_eq(chan_type, SLOP_STR("slop_chan_int")))) {
                                    {
                                        __auto_type s1 = context_ctx_str3(ctx, SLOP_STR("thread_send_"), chan_type, SLOP_STR("("));
                                        __auto_type s2 = context_ctx_str(ctx, s1, chan_c);
                                        __auto_type s3 = context_ctx_str(ctx, s2, SLOP_STR(", "));
                                        return context_ctx_str(ctx, s3, context_ctx_str(ctx, value_c, SLOP_STR(")")));
                                    }
                                } else {
                                    return context_ctx_str5(ctx, SLOP_STR("thread_send("), chan_c, SLOP_STR(", "), value_c, SLOP_STR(")"));
                                }
                            }
                        }
                    } else if (!_mv_305.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("send: missing value argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                        return SLOP_STR("0");
                    }
                    SLOP_UNREACHABLE();
                } else if (!_mv_304.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("send: missing channel argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("0");
                }
                SLOP_UNREACHABLE();
            }
        } else if (string_eq(fn_name, SLOP_STR("recv"))) {
            if (len < 2) {
                context_ctx_add_error_at(ctx, SLOP_STR("recv: need channel argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("0");
            } else {
                __auto_type _mv_306 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_306.has_value) {
                    __auto_type chan_expr = _mv_306.value;
                    {
                        __auto_type chan_c = expr_transpile_expr(ctx, chan_expr);
                        __auto_type chan_c_type = expr_infer_expr_c_type(ctx, chan_expr);
                        {
                            __auto_type chan_type = expr_strip_pointer_suffix(arena, chan_c_type);
                            if (strlib_starts_with(chan_type, SLOP_STR("slop_chan_")) && !(string_eq(chan_type, SLOP_STR("slop_chan_int")))) {
                                {
                                    __auto_type s1 = context_ctx_str(ctx, SLOP_STR("thread_recv_"), chan_type);
                                    __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("("));
                                    __auto_type s3 = context_ctx_str(ctx, s2, chan_c);
                                    return context_ctx_str(ctx, s3, SLOP_STR(")"));
                                }
                            } else {
                                return context_ctx_str3(ctx, SLOP_STR("thread_recv("), chan_c, SLOP_STR(")"));
                            }
                        }
                    }
                } else if (!_mv_306.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("recv: missing channel argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("0");
                }
                SLOP_UNREACHABLE();
            }
        } else {
            {
                __auto_type builtin_c_name = expr_get_builtin_type_c_name(fn_name);
                if (string_len(builtin_c_name) > 0) {
                    return expr_transpile_builtin_constructor(ctx, fn_name, items);
                } else {
                    __auto_type _mv_307 = context_ctx_lookup_type(ctx, fn_name);
                    if (_mv_307.has_value) {
                        __auto_type type_entry = _mv_307.value;
                        if (type_entry.is_union) {
                            return expr_transpile_union_constructor(ctx, fn_name, type_entry.c_name, items);
                        } else {
                            {
                                __auto_type c_name = type_entry.c_name;
                                __auto_type type_name = fn_name;
                                __auto_type args = SLOP_STR("");
                                __auto_type i = 1;
                                __auto_type field_idx = 0;
                                while (i < len) {
                                    __auto_type _mv_308 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_308.has_value) {
                                        __auto_type arg = _mv_308.value;
                                        {
                                            __auto_type arg_c = expr_transpile_expr(ctx, arg);
                                            __auto_type field_type_opt = context_ctx_lookup_field_type_by_index(ctx, type_name, field_idx);
                                            __auto_type final_arg = ({ __auto_type _mv = field_type_opt; _mv.has_value ? ({ __auto_type field_type = _mv.value; expr_typed_none_arg(ctx, field_type, arg_c); }) : (arg_c); });
                                            if (string_eq(args, SLOP_STR(""))) {
                                                args = final_arg;
                                            } else {
                                                args = context_ctx_str3(ctx, args, SLOP_STR(", "), final_arg);
                                            }
                                            field_idx = (field_idx + 1);
                                        }
                                    } else if (!_mv_308.has_value) {
                                    }
                                    i = (i + 1);
                                }
                                return context_ctx_str5(ctx, SLOP_STR("("), c_name, SLOP_STR("){"), args, SLOP_STR("}"));
                            }
                        }
                    } else if (!_mv_307.has_value) {
                        __auto_type _mv_309 = context_ctx_lookup_enum_variant(ctx, fn_name);
                        if (_mv_309.has_value) {
                            __auto_type type_name = _mv_309.value;
                            {
                                __auto_type c_variant = ctype_to_c_name(arena, fn_name);
                                __auto_type c_tag_enum = context_ctx_str3(ctx, type_name, SLOP_STR("_"), c_variant);
                                if (len > 2) {
                                    {
                                        __auto_type vals = SLOP_STR("");
                                        __auto_type vi = 1;
                                        while (vi < len) {
                                            __auto_type _mv_310 = ({ __auto_type _lst = items; size_t _idx = (size_t)vi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_310.has_value) {
                                                __auto_type v = _mv_310.value;
                                                {
                                                    __auto_type v_c = expr_transpile_expr(ctx, v);
                                                    if (string_eq(vals, SLOP_STR(""))) {
                                                        vals = v_c;
                                                    } else {
                                                        vals = context_ctx_str3(ctx, vals, SLOP_STR(", "), v_c);
                                                    }
                                                }
                                            } else if (!_mv_310.has_value) {
                                            }
                                            vi = (vi + 1);
                                        }
                                        return context_ctx_str3(ctx, SLOP_STR("(("), type_name, context_ctx_str3(ctx, SLOP_STR("){ .tag = "), c_tag_enum, context_ctx_str5(ctx, SLOP_STR(", .data."), c_variant, SLOP_STR(" = { "), vals, SLOP_STR(" } })"))));
                                    }
                                } else if (len == 2) {
                                    __auto_type _mv_311 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_311.has_value) {
                                        __auto_type value_expr = _mv_311.value;
                                        {
                                            __auto_type value_c = expr_transpile_expr(ctx, value_expr);
                                            return context_ctx_str3(ctx, SLOP_STR("(("), type_name, context_ctx_str3(ctx, SLOP_STR("){ .tag = "), c_tag_enum, context_ctx_str5(ctx, SLOP_STR(", .data."), c_variant, SLOP_STR(" = "), value_c, SLOP_STR(" })"))));
                                        }
                                    } else if (!_mv_311.has_value) {
                                        return context_ctx_str3(ctx, SLOP_STR("(("), type_name, context_ctx_str3(ctx, SLOP_STR("){ .tag = "), c_tag_enum, SLOP_STR(" })")));
                                    }
                                    SLOP_UNREACHABLE();
                                } else {
                                    return context_ctx_str3(ctx, SLOP_STR("(("), type_name, context_ctx_str3(ctx, SLOP_STR("){ .tag = "), c_tag_enum, SLOP_STR(" })")));
                                }
                            }
                        } else if (!_mv_309.has_value) {
                            {
                                __auto_type func_opt = context_ctx_lookup_func(ctx, fn_name);
                                __auto_type args = SLOP_STR("");
                                __auto_type i = 1;
                                __auto_type param_idx = 0;
                                __auto_type _mv_312 = func_opt;
                                if (!_mv_312.has_value) {
                                    {
                                        __auto_type runtime_name = expr_get_runtime_function_name(fn_name);
                                        __auto_type var_opt = context_ctx_lookup_var(ctx, fn_name);
                                        if ((string_len(runtime_name) == 0) && ({ __auto_type _mv = var_opt; _mv.has_value ? ({ __auto_type _ = _mv.value; 0; }) : (1); })) {
                                            context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("undefined function '"), fn_name, SLOP_STR("' - check imports")), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                            return SLOP_STR("0");
                                        } else {
                                            while (i < len) {
                                                __auto_type _mv_313 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_313.has_value) {
                                                    __auto_type arg = _mv_313.value;
                                                    {
                                                        __auto_type arg_c = expr_transpile_expr(ctx, arg);
                                                        if (string_eq(args, SLOP_STR(""))) {
                                                            args = arg_c;
                                                        } else {
                                                            args = context_ctx_str3(ctx, args, SLOP_STR(", "), arg_c);
                                                        }
                                                    }
                                                } else if (!_mv_313.has_value) {
                                                }
                                                i = (i + 1);
                                            }
                                            return expr_transpile_call(ctx, fn_name, args);
                                        }
                                    }
                                } else if (_mv_312.has_value) {
                                    __auto_type func_entry = _mv_312.value;
                                    while (i < len) {
                                        __auto_type _mv_314 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_314.has_value) {
                                            __auto_type arg = _mv_314.value;
                                            {
                                                __auto_type arg_c = expr_transpile_expr(ctx, arg);
                                                __auto_type expected_type = ({ __auto_type _mv = ({ __auto_type _lst = func_entry.param_types; size_t _idx = (size_t)param_idx; slop_option_context_FuncParamType_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type p = _mv.value; (*p).c_type; }) : (SLOP_STR("")); });
                                                __auto_type arg_c2 = expr_typed_none_arg(ctx, expected_type, arg_c);
                                                __auto_type final_arg = expr_wrap_fn_ref_as_closure(ctx, expected_type, arg_c2, arg);
                                                if (string_eq(args, SLOP_STR(""))) {
                                                    args = final_arg;
                                                } else {
                                                    args = context_ctx_str3(ctx, args, SLOP_STR(", "), final_arg);
                                                }
                                                param_idx = (param_idx + 1);
                                            }
                                        } else if (!_mv_314.has_value) {
                                        }
                                        i = (i + 1);
                                    }
                                    return expr_transpile_call(ctx, fn_name, args);
                                }
                                SLOP_UNREACHABLE();
                            }
                        }
                        SLOP_UNREACHABLE();
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
    }
}

slop_string expr_transpile_print(context_TranspileContext* ctx, types_SExpr* arg, uint8_t newline) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((arg != NULL)), "(!= arg nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type nl = ((newline) ? SLOP_STR("\\n") : SLOP_STR(""));
        __auto_type _mv_315 = (*arg);
        switch (_mv_315.tag) {
            case types_SExpr_str:
            {
                __auto_type s = _mv_315.data.str;
                return context_ctx_str5(ctx, SLOP_STR("printf(\"%s"), nl, SLOP_STR("\", \""), expr_escape_c_string(ctx, s.value), SLOP_STR("\")"));
            }
            case types_SExpr_num:
            {
                __auto_type n = _mv_315.data.num;
                if (expr_string_contains(n.raw, SLOP_STR("."))) {
                    return context_ctx_str5(ctx, SLOP_STR("printf(\"%f"), nl, SLOP_STR("\", "), n.raw, SLOP_STR(")"));
                } else {
                    return context_ctx_str5(ctx, SLOP_STR("printf(\"%lld"), nl, SLOP_STR("\", (long long)("), n.raw, SLOP_STR("))"));
                }
            }
            default: {
                {
                    __auto_type arg_c = expr_transpile_expr(ctx, arg);
                    __auto_type _mv_316 = expr_get_expr_type_hint(ctx, arg);
                    if (_mv_316.has_value) {
                        __auto_type type_hint = _mv_316.value;
                        if (string_eq(type_hint, SLOP_STR("String")) || string_eq(type_hint, SLOP_STR("slop_string"))) {
                            return expr_transpile_print_string(ctx, arg_c, nl);
                        } else if (string_eq(type_hint, SLOP_STR("Bool")) || string_eq(type_hint, SLOP_STR("uint8_t"))) {
                            return context_ctx_str5(ctx, SLOP_STR("printf(\"%s"), nl, SLOP_STR("\", ("), arg_c, SLOP_STR(") ? \"true\" : \"false\")"));
                        } else if (string_eq(type_hint, SLOP_STR("Float")) || string_eq(type_hint, SLOP_STR("double"))) {
                            return context_ctx_str5(ctx, SLOP_STR("printf(\"%f"), nl, SLOP_STR("\", "), arg_c, SLOP_STR(")"));
                        } else {
                            return context_ctx_str5(ctx, SLOP_STR("printf(\"%lld"), nl, SLOP_STR("\", (long long)("), arg_c, SLOP_STR("))"));
                        }
                    } else if (!_mv_316.has_value) {
                        return context_ctx_str5(ctx, SLOP_STR("printf(\"%lld"), nl, SLOP_STR("\", (long long)("), arg_c, SLOP_STR("))"));
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
    }
}

slop_string expr_transpile_print_string(context_TranspileContext* ctx, slop_string arg_c, slop_string nl) {
    {
        __auto_type arena = (*ctx).arena;
        return string_concat(arena, string_concat(arena, string_concat(arena, SLOP_STR("printf(\"%.*s"), nl), string_concat(arena, SLOP_STR("\", (int)("), arg_c)), string_concat(arena, SLOP_STR(").len, ("), string_concat(arena, arg_c, SLOP_STR(").data)"))));
    }
}

slop_string expr_transpile_printf_call(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type args = SLOP_STR("");
        int64_t i = 1;
        while (i < len) {
            __auto_type _mv_317 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_317.has_value) {
                __auto_type arg = _mv_317.value;
                {
                    __auto_type arg_c = ({ __auto_type _mv = (*arg); slop_string _mr = {0}; switch (_mv.tag) { case types_SExpr_str: { __auto_type s = _mv.data.str; _mr = context_ctx_str3(ctx, SLOP_STR("\""), expr_escape_c_string(ctx, s.value), SLOP_STR("\"")); break; } default: { _mr = expr_transpile_expr(ctx, arg); break; }  } _mr; });
                    if (string_eq(args, SLOP_STR(""))) {
                        args = arg_c;
                    } else {
                        args = context_ctx_str3(ctx, args, SLOP_STR(", "), arg_c);
                    }
                }
            } else if (!_mv_317.has_value) {
            }
            i = (i + 1);
        }
        return context_ctx_str3(ctx, SLOP_STR("printf("), args, SLOP_STR(")"));
    }
}

slop_string expr_transpile_raw_string_fn_call(context_TranspileContext* ctx, slop_string fn_name, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type args = SLOP_STR("");
        int64_t i = 1;
        while (i < len) {
            __auto_type _mv_318 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_318.has_value) {
                __auto_type arg = _mv_318.value;
                {
                    __auto_type arg_c = ({ __auto_type _mv = (*arg); slop_string _mr = {0}; switch (_mv.tag) { case types_SExpr_str: { __auto_type s = _mv.data.str; _mr = context_ctx_str3(ctx, SLOP_STR("\""), expr_escape_c_string(ctx, s.value), SLOP_STR("\"")); break; } default: { _mr = expr_transpile_expr(ctx, arg); break; }  } _mr; });
                    if (string_eq(args, SLOP_STR(""))) {
                        args = arg_c;
                    } else {
                        args = context_ctx_str3(ctx, args, SLOP_STR(", "), arg_c);
                    }
                }
            } else if (!_mv_318.has_value) {
            }
            i = (i + 1);
        }
        return expr_transpile_call(ctx, fn_name, args);
    }
}

uint8_t expr_string_contains(slop_string s, slop_string substr) {
    return (strlib_count_occurrences(s, substr) > 0);
}

slop_option_string expr_get_expr_type_hint(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type slop_type = expr_infer_expr_slop_type(ctx, expr);
        if (string_eq(slop_type, SLOP_STR("String"))) {
            return (slop_option_string){.has_value = 1, .value = SLOP_STR("slop_string")};
        } else if (string_eq(slop_type, SLOP_STR("Bool"))) {
            return (slop_option_string){.has_value = 1, .value = SLOP_STR("uint8_t")};
        } else if (string_eq(slop_type, SLOP_STR("Int"))) {
            return (slop_option_string){.has_value = 1, .value = SLOP_STR("int64_t")};
        } else if (string_eq(slop_type, SLOP_STR("Float"))) {
            return (slop_option_string){.has_value = 1, .value = SLOP_STR("double")};
        } else {
            __auto_type _mv_319 = (*expr);
            switch (_mv_319.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_319.data.sym;
                    __auto_type _mv_320 = context_ctx_lookup_var(ctx, sym.name);
                    if (_mv_320.has_value) {
                        __auto_type entry = _mv_320.value;
                        {
                            __auto_type ct = entry.c_type;
                            if (string_eq(ct, SLOP_STR("auto"))) {
                                return (slop_option_string){.has_value = false};
                            } else {
                                return (slop_option_string){.has_value = 1, .value = ct};
                            }
                        }
                    } else if (!_mv_320.has_value) {
                        return (slop_option_string){.has_value = false};
                    }
                    SLOP_UNREACHABLE();
                }
                case types_SExpr_lst:
                {
                    __auto_type lst = _mv_319.data.lst;
                    {
                        __auto_type items = lst.items;
                        if (((int64_t)((items).len)) >= 1) {
                            __auto_type _mv_321 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_321.has_value) {
                                __auto_type head = _mv_321.value;
                                __auto_type _mv_322 = (*head);
                                switch (_mv_322.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type head_sym = _mv_322.data.sym;
                                        {
                                            __auto_type op = head_sym.name;
                                            if (string_eq(op, SLOP_STR(".")) && (((int64_t)((items).len)) >= 3)) {
                                                {
                                                    __auto_type c_type = expr_infer_expr_c_type(ctx, expr);
                                                    if (string_eq(c_type, SLOP_STR("slop_string"))) {
                                                        return (slop_option_string){.has_value = 1, .value = SLOP_STR("slop_string")};
                                                    } else if (string_eq(c_type, SLOP_STR("uint8_t"))) {
                                                        return (slop_option_string){.has_value = 1, .value = SLOP_STR("uint8_t")};
                                                    } else if (string_eq(c_type, SLOP_STR("double"))) {
                                                        return (slop_option_string){.has_value = 1, .value = SLOP_STR("double")};
                                                    } else if (string_eq(c_type, SLOP_STR("int64_t"))) {
                                                        return (slop_option_string){.has_value = 1, .value = SLOP_STR("int64_t")};
                                                    } else {
                                                        __auto_type _mv_323 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                        if (_mv_323.has_value) {
                                                            __auto_type obj_expr = _mv_323.value;
                                                            __auto_type _mv_324 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_324.has_value) {
                                                                __auto_type field_expr = _mv_324.value;
                                                                __auto_type _mv_325 = (*field_expr);
                                                                switch (_mv_325.tag) {
                                                                    case types_SExpr_sym:
                                                                    {
                                                                        __auto_type field_sym = _mv_325.data.sym;
                                                                        {
                                                                            __auto_type field_name = field_sym.name;
                                                                            __auto_type obj_slop_type = expr_infer_expr_slop_type(ctx, obj_expr);
                                                                            if (string_len(obj_slop_type) > 0) {
                                                                                __auto_type _mv_326 = context_ctx_lookup_field_slop_type(ctx, obj_slop_type, field_name);
                                                                                if (_mv_326.has_value) {
                                                                                    __auto_type fst = _mv_326.value;
                                                                                    if (string_eq(fst, SLOP_STR("String"))) {
                                                                                        return (slop_option_string){.has_value = 1, .value = SLOP_STR("slop_string")};
                                                                                    } else if (string_eq(fst, SLOP_STR("Bool"))) {
                                                                                        return (slop_option_string){.has_value = 1, .value = SLOP_STR("uint8_t")};
                                                                                    } else if (string_eq(fst, SLOP_STR("Int"))) {
                                                                                        return (slop_option_string){.has_value = 1, .value = SLOP_STR("int64_t")};
                                                                                    } else if (string_eq(fst, SLOP_STR("Float"))) {
                                                                                        return (slop_option_string){.has_value = 1, .value = SLOP_STR("double")};
                                                                                    } else {
                                                                                        return (slop_option_string){.has_value = false};
                                                                                    }
                                                                                } else if (!_mv_326.has_value) {
                                                                                    return (slop_option_string){.has_value = false};
                                                                                }
                                                                                SLOP_UNREACHABLE();
                                                                            } else {
                                                                                return (slop_option_string){.has_value = false};
                                                                            }
                                                                        }
                                                                    }
                                                                    default: {
                                                                        return (slop_option_string){.has_value = false};
                                                                    }
                                                                }
                                                            } else if (!_mv_324.has_value) {
                                                                return (slop_option_string){.has_value = false};
                                                            }
                                                            SLOP_UNREACHABLE();
                                                        } else if (!_mv_323.has_value) {
                                                            return (slop_option_string){.has_value = false};
                                                        }
                                                        SLOP_UNREACHABLE();
                                                    }
                                                }
                                            } else if (string_eq(op, SLOP_STR("int-to-string")) || (string_eq(op, SLOP_STR("string-copy")) || (string_eq(op, SLOP_STR("string-concat")) || string_eq(op, SLOP_STR("pretty-print"))))) {
                                                return (slop_option_string){.has_value = 1, .value = SLOP_STR("slop_string")};
                                            } else {
                                                __auto_type _mv_327 = context_ctx_lookup_func(ctx, op);
                                                if (_mv_327.has_value) {
                                                    __auto_type func_entry = _mv_327.value;
                                                    if (func_entry.returns_string) {
                                                        return (slop_option_string){.has_value = 1, .value = SLOP_STR("slop_string")};
                                                    } else {
                                                        return (slop_option_string){.has_value = false};
                                                    }
                                                } else if (!_mv_327.has_value) {
                                                    return (slop_option_string){.has_value = false};
                                                }
                                                SLOP_UNREACHABLE();
                                            }
                                        }
                                    }
                                    default: {
                                        return (slop_option_string){.has_value = false};
                                    }
                                }
                            } else if (!_mv_321.has_value) {
                                return (slop_option_string){.has_value = false};
                            }
                            SLOP_UNREACHABLE();
                        } else {
                            return (slop_option_string){.has_value = false};
                        }
                    }
                }
                default: {
                    return (slop_option_string){.has_value = false};
                }
            }
        }
    }
}

slop_string expr_transpile_union_constructor(context_TranspileContext* ctx, slop_string type_name, slop_string c_type_name, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 2) {
            return context_ctx_str3(ctx, SLOP_STR("(("), c_type_name, SLOP_STR("){})"));
        } else {
            __auto_type _mv_328 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_328.has_value) {
                __auto_type tag_expr = _mv_328.value;
                __auto_type _mv_329 = (*tag_expr);
                switch (_mv_329.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type tag_list = _mv_329.data.lst;
                        {
                            __auto_type tag_items = tag_list.items;
                            if (((int64_t)((tag_items).len)) < 1) {
                                return context_ctx_str3(ctx, SLOP_STR("(("), c_type_name, SLOP_STR("){})"));
                            } else {
                                __auto_type _mv_330 = ({ __auto_type _lst = tag_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_330.has_value) {
                                    __auto_type tag_name_expr = _mv_330.value;
                                    __auto_type _mv_331 = (*tag_name_expr);
                                    switch (_mv_331.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type tag_sym = _mv_331.data.sym;
                                            {
                                                __auto_type tag_name = tag_sym.name;
                                                __auto_type c_tag_name = ctype_to_c_name(arena, tag_name);
                                                __auto_type c_tag_enum = context_ctx_str(ctx, c_type_name, context_ctx_str(ctx, SLOP_STR("_"), c_tag_name));
                                                __auto_type num_tag_items = ((int64_t)((tag_items).len));
                                                if (num_tag_items >= 3) {
                                                    {
                                                        slop_string field_init = SLOP_STR("");
                                                        for (int64_t fi = 1; fi < num_tag_items; fi++) {
                                                            __auto_type _mv_332 = ({ __auto_type _lst = tag_items; size_t _idx = (size_t)fi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_332.has_value) {
                                                                __auto_type value_expr = _mv_332.value;
                                                                {
                                                                    __auto_type value_c = expr_transpile_expr(ctx, value_expr);
                                                                    __auto_type field_name = context_ctx_str(ctx, SLOP_STR(".f"), int_to_string(arena, (fi - 1)));
                                                                    __auto_type assignment = context_ctx_str3(ctx, field_name, SLOP_STR(" = "), value_c);
                                                                    field_init = ((string_eq(field_init, SLOP_STR(""))) ? assignment : context_ctx_str3(ctx, field_init, SLOP_STR(", "), assignment));
                                                                }
                                                            } else if (!_mv_332.has_value) {
                                                            }
                                                        }
                                                        return context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, c_type_name, context_ctx_str(ctx, SLOP_STR("){ .tag = "), context_ctx_str(ctx, c_tag_enum, context_ctx_str(ctx, SLOP_STR(", .data."), context_ctx_str(ctx, c_tag_name, context_ctx_str(ctx, SLOP_STR(" = { "), context_ctx_str(ctx, field_init, SLOP_STR(" } })")))))))));
                                                    }
                                                } else if (num_tag_items == 2) {
                                                    __auto_type _mv_333 = ({ __auto_type _lst = tag_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_333.has_value) {
                                                        __auto_type value_expr = _mv_333.value;
                                                        {
                                                            __auto_type value_c = expr_transpile_expr(ctx, value_expr);
                                                            return context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, c_type_name, context_ctx_str(ctx, SLOP_STR("){ .tag = "), context_ctx_str(ctx, c_tag_enum, context_ctx_str(ctx, SLOP_STR(", .data."), context_ctx_str(ctx, c_tag_name, context_ctx_str(ctx, SLOP_STR(" = "), context_ctx_str(ctx, value_c, SLOP_STR(" })")))))))));
                                                        }
                                                    } else if (!_mv_333.has_value) {
                                                        return context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, c_type_name, context_ctx_str(ctx, SLOP_STR("){ .tag = "), context_ctx_str(ctx, c_tag_enum, SLOP_STR(" })")))));
                                                    }
                                                    SLOP_UNREACHABLE();
                                                } else {
                                                    return context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, c_type_name, context_ctx_str(ctx, SLOP_STR("){ .tag = "), context_ctx_str(ctx, c_tag_enum, SLOP_STR(" })")))));
                                                }
                                            }
                                        }
                                        default: {
                                            return context_ctx_str3(ctx, SLOP_STR("(("), c_type_name, SLOP_STR("){})/* tag not symbol */"));
                                        }
                                    }
                                } else if (!_mv_330.has_value) {
                                    return context_ctx_str3(ctx, SLOP_STR("(("), c_type_name, SLOP_STR("){})/* no tag */"));
                                }
                                SLOP_UNREACHABLE();
                            }
                        }
                    }
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_329.data.sym;
                        {
                            __auto_type tag_name = sym.name;
                            __auto_type c_tag_name = ctype_to_c_name(arena, tag_name);
                            __auto_type c_tag_enum = context_ctx_str(ctx, c_type_name, context_ctx_str(ctx, SLOP_STR("_"), c_tag_name));
                            return context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, c_type_name, context_ctx_str(ctx, SLOP_STR("){ .tag = "), context_ctx_str(ctx, c_tag_enum, SLOP_STR(" })")))));
                        }
                    }
                    default: {
                        return context_ctx_str3(ctx, SLOP_STR("(("), c_type_name, SLOP_STR("){})/* unknown tag form */"));
                    }
                }
            } else if (!_mv_328.has_value) {
                return context_ctx_str3(ctx, SLOP_STR("(("), c_type_name, SLOP_STR("){})/* no args */"));
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_cond_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result_type = expr_infer_cond_result_c_type(ctx, items);
        __auto_type result = SLOP_STR("");
        int64_t i = 1;
        while (i < len) {
            __auto_type _mv_334 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_334.has_value) {
                __auto_type clause_expr = _mv_334.value;
                __auto_type _mv_335 = (*clause_expr);
                switch (_mv_335.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type clause_lst = _mv_335.data.lst;
                        {
                            __auto_type clause_items = clause_lst.items;
                            __auto_type clause_len = ((int64_t)((clause_items).len));
                            if (clause_len >= 2) {
                                __auto_type _mv_336 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_336.has_value) {
                                    __auto_type test_expr = _mv_336.value;
                                    __auto_type _mv_337 = (*test_expr);
                                    switch (_mv_337.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_337.data.sym;
                                            if (string_eq(sym.name, SLOP_STR("else"))) {
                                                __auto_type _mv_338 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)(clause_len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_338.has_value) {
                                                    __auto_type body_expr = _mv_338.value;
                                                    {
                                                        __auto_type body_c = expr_transpile_expr(ctx, body_expr);
                                                        result = context_ctx_str(ctx, result, expr_typed_none(ctx, result_type, body_c));
                                                    }
                                                } else if (!_mv_338.has_value) {
                                                    result = context_ctx_str(ctx, result, SLOP_STR("0"));
                                                }
                                            } else {
                                                {
                                                    __auto_type test_c = expr_transpile_expr(ctx, test_expr);
                                                    __auto_type _mv_339 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)(clause_len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_339.has_value) {
                                                        __auto_type body_expr = _mv_339.value;
                                                        {
                                                            __auto_type body_c = expr_typed_none(ctx, result_type, expr_transpile_expr(ctx, body_expr));
                                                            result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR("("), context_ctx_str(ctx, test_c, context_ctx_str(ctx, SLOP_STR(" ? "), context_ctx_str(ctx, body_c, SLOP_STR(" : "))))));
                                                        }
                                                    } else if (!_mv_339.has_value) {
                                                        result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR("("), context_ctx_str(ctx, test_c, SLOP_STR(" ? 0 : "))));
                                                    }
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            {
                                                __auto_type test_c = expr_transpile_expr(ctx, test_expr);
                                                __auto_type _mv_340 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)(clause_len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_340.has_value) {
                                                    __auto_type body_expr = _mv_340.value;
                                                    {
                                                        __auto_type body_c = expr_typed_none(ctx, result_type, expr_transpile_expr(ctx, body_expr));
                                                        result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR("("), context_ctx_str(ctx, test_c, context_ctx_str(ctx, SLOP_STR(" ? "), context_ctx_str(ctx, body_c, SLOP_STR(" : "))))));
                                                    }
                                                } else if (!_mv_340.has_value) {
                                                    result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR("("), context_ctx_str(ctx, test_c, SLOP_STR(" ? 0 : "))));
                                                }
                                            }
                                            break;
                                        }
                                    }
                                } else if (!_mv_336.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_334.has_value) {
            }
            i = (i + 1);
        }
        if (string_eq(result, SLOP_STR(""))) {
            return SLOP_STR("0");
        } else {
            {
                int64_t open_count = 0;
                int64_t j = 0;
                __auto_type rlen = string_len(result);
                while (j < ((int64_t)(rlen))) {
                    {
                        __auto_type c = strlib_char_at(result, ((int64_t)(j)));
                        if (c == 40) {
                            open_count = (open_count + 1);
                        } else if (c == 41) {
                            open_count = (open_count - 1);
                        } else {
                        }
                    }
                    j = (j + 1);
                }
                while (open_count > 0) {
                    result = context_ctx_str(ctx, result, SLOP_STR(")"));
                    open_count = (open_count - 1);
                }
                return result;
            }
        }
    }
}

slop_string expr_transpile_match_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 3) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid match expr"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("0");
        } else {
            __auto_type _mv_341 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_341.has_value) {
                __auto_type scrutinee = _mv_341.value;
                {
                    __auto_type scrutinee_c = expr_transpile_expr(ctx, scrutinee);
                    __auto_type patterns = expr_collect_match_patterns(ctx, items);
                    if (expr_is_option_patterns(patterns)) {
                        {
                            __auto_type scrut_type = expr_resolve_type_alias(ctx, expr_infer_expr_slop_type(ctx, scrutinee));
                            if (strlib_starts_with(scrut_type, SLOP_STR("(Result "))) {
                                context_ctx_add_error_at(ctx, SLOP_STR("match uses Option patterns (some/none) but scrutinee has Result type - use (ok)/(error) patterns"), context_ctx_sexpr_line(scrutinee), context_ctx_sexpr_col(scrutinee));
                            }
                        }
                        return expr_build_option_match_expr(ctx, scrutinee, scrutinee_c, items);
                    } else if (expr_is_result_patterns(patterns)) {
                        return expr_build_result_match_expr(ctx, scrutinee, scrutinee_c, items);
                    } else if (expr_is_enum_expr_patterns(ctx, patterns)) {
                        return expr_build_enum_match_expr(ctx, scrutinee_c, items);
                    } else if (expr_is_union_expr_patterns(ctx, patterns)) {
                        return expr_build_union_match_expr(ctx, scrutinee, scrutinee_c, items);
                    } else {
                        return expr_build_ternary_match_expr(ctx, scrutinee_c, items);
                    }
                }
            } else if (!_mv_341.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing match scrutinee"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("0");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_list_types_SExpr_ptr expr_collect_match_patterns(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
        int64_t i = 2;
        while (i < len) {
            __auto_type _mv_342 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_342.has_value) {
                __auto_type branch = _mv_342.value;
                __auto_type _mv_343 = (*branch);
                switch (_mv_343.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_343.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if (((int64_t)((branch_items).len)) >= 1) {
                                __auto_type _mv_344 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_344.has_value) {
                                    __auto_type pattern = _mv_344.value;
                                    ({ __auto_type _lst_p = &(result); __auto_type _item = (pattern); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                } else if (!_mv_344.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_342.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_string expr_get_expr_pattern_tag(types_SExpr* pat_expr) {
    SLOP_PRE(((pat_expr != NULL)), "(!= pat-expr nil)");
    __auto_type _mv_345 = (*pat_expr);
    switch (_mv_345.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_345.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_346 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_346.has_value) {
                        __auto_type head = _mv_346.value;
                        __auto_type _mv_347 = (*head);
                        switch (_mv_347.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_347.data.sym;
                                return sym.name;
                            }
                            default: {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_346.has_value) {
                        return SLOP_STR("");
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_345.data.sym;
            return sym.name;
        }
        default: {
            return SLOP_STR("");
        }
    }
}

uint8_t expr_is_option_patterns(slop_list_types_SExpr_ptr patterns) {
    {
        __auto_type len = ((int64_t)((patterns).len));
        uint8_t found = 0;
        int64_t i = 0;
        while ((i < len) && !(found)) {
            __auto_type _mv_348 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_348.has_value) {
                __auto_type pat = _mv_348.value;
                {
                    __auto_type tag = expr_get_expr_pattern_tag(pat);
                    if (string_eq(tag, SLOP_STR("some")) || string_eq(tag, SLOP_STR("none"))) {
                        found = 1;
                    }
                }
            } else if (!_mv_348.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

uint8_t expr_is_result_patterns(slop_list_types_SExpr_ptr patterns) {
    {
        __auto_type len = ((int64_t)((patterns).len));
        uint8_t found = 0;
        int64_t i = 0;
        while ((i < len) && !(found)) {
            __auto_type _mv_349 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_349.has_value) {
                __auto_type pat = _mv_349.value;
                {
                    __auto_type tag = expr_get_expr_pattern_tag(pat);
                    if (string_eq(tag, SLOP_STR("ok")) || string_eq(tag, SLOP_STR("error"))) {
                        found = 1;
                    }
                }
            } else if (!_mv_349.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

uint8_t expr_is_enum_expr_patterns(context_TranspileContext* ctx, slop_list_types_SExpr_ptr patterns) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((patterns).len));
        uint8_t all_symbols = 1;
        uint8_t has_enum_variant = 0;
        int64_t i = 0;
        while ((i < len) && all_symbols) {
            __auto_type _mv_350 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_350.has_value) {
                __auto_type pat_expr = _mv_350.value;
                __auto_type _mv_351 = (*pat_expr);
                switch (_mv_351.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type s = _mv_351.data.sym;
                        {
                            __auto_type name = s.name;
                            if (!(string_eq(name, SLOP_STR("else"))) && !(string_eq(name, SLOP_STR("_")))) {
                                __auto_type _mv_352 = context_ctx_lookup_enum_variant(ctx, name);
                                if (_mv_352.has_value) {
                                    __auto_type _ = _mv_352.value;
                                    has_enum_variant = 1;
                                } else if (!_mv_352.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        all_symbols = 0;
                        break;
                    }
                }
            } else if (!_mv_350.has_value) {
            }
            i = (i + 1);
        }
        return (all_symbols && has_enum_variant);
    }
}

uint8_t expr_is_union_expr_patterns(context_TranspileContext* ctx, slop_list_types_SExpr_ptr patterns) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((patterns).len));
        uint8_t has_union_variant = 0;
        int64_t i = 0;
        while ((i < len) && !(has_union_variant)) {
            __auto_type _mv_353 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_353.has_value) {
                __auto_type pat_expr = _mv_353.value;
                {
                    __auto_type tag = expr_get_expr_pattern_tag(pat_expr);
                    if ((!(string_eq(tag, SLOP_STR("")))) && (!(string_eq(tag, SLOP_STR("some")))) && (!(string_eq(tag, SLOP_STR("none")))) && (!(string_eq(tag, SLOP_STR("ok")))) && (!(string_eq(tag, SLOP_STR("error")))) && (!(string_eq(tag, SLOP_STR("else")))) && (!(string_eq(tag, SLOP_STR("_"))))) {
                        __auto_type _mv_354 = context_ctx_lookup_enum_variant(ctx, tag);
                        if (_mv_354.has_value) {
                            __auto_type _ = _mv_354.value;
                            has_union_variant = 1;
                        } else if (!_mv_354.has_value) {
                        }
                    }
                }
            } else if (!_mv_353.has_value) {
            }
            i = (i + 1);
        }
        return has_union_variant;
    }
}

slop_option_string expr_get_expr_binding_name(types_SExpr* pat_expr) {
    SLOP_PRE(((pat_expr != NULL)), "(!= pat-expr nil)");
    __auto_type _mv_355 = (*pat_expr);
    switch (_mv_355.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_355.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 2) {
                    return (slop_option_string){.has_value = false};
                } else {
                    __auto_type _mv_356 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_356.has_value) {
                        __auto_type binding = _mv_356.value;
                        __auto_type _mv_357 = (*binding);
                        switch (_mv_357.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_357.data.sym;
                                return (slop_option_string){.has_value = 1, .value = sym.name};
                            }
                            default: {
                                return (slop_option_string){.has_value = false};
                            }
                        }
                    } else if (!_mv_356.has_value) {
                        return (slop_option_string){.has_value = false};
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        default: {
            return (slop_option_string){.has_value = false};
        }
    }
}

slop_string expr_get_match_branch_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr branch_items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((branch_items).len));
        if (len < 2) {
            return SLOP_STR("0");
        } else {
            __auto_type _mv_358 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)(len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_358.has_value) {
                __auto_type body_expr = _mv_358.value;
                return expr_transpile_expr(ctx, body_expr);
            } else if (!_mv_358.has_value) {
                return SLOP_STR("0");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_branch_body_with_binding(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_list_types_SExpr_ptr branch_items, slop_string binding_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((scrutinee != NULL)), "(!= scrutinee nil)");
    context_ctx_push_scope(ctx);
    if (!(string_eq(binding_name, SLOP_STR("")))) {
        {
            __auto_type arena = (*ctx).arena;
            __auto_type c_name = ctype_to_c_name(arena, binding_name);
            __auto_type inner_slop_type = expr_infer_option_inner_slop_type(ctx, scrutinee);
            context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_name, SLOP_STR("auto"), inner_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
        }
    }
    {
        __auto_type result = expr_get_match_branch_body(ctx, branch_items);
        context_ctx_pop_scope(ctx);
        return result;
    }
}

slop_string expr_build_option_match_expr(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_string scrutinee_c, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((scrutinee != NULL)), "(!= scrutinee nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type some_body = SLOP_STR("0");
        __auto_type none_body = SLOP_STR("0");
        __auto_type some_binding = SLOP_STR("");
        int64_t i = 2;
        while (i < len) {
            __auto_type _mv_359 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_359.has_value) {
                __auto_type branch = _mv_359.value;
                __auto_type _mv_360 = (*branch);
                switch (_mv_360.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_360.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if (((int64_t)((branch_items).len)) >= 2) {
                                __auto_type _mv_361 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_361.has_value) {
                                    __auto_type pattern = _mv_361.value;
                                    {
                                        __auto_type tag = expr_get_expr_pattern_tag(pattern);
                                        if (string_eq(tag, SLOP_STR("some"))) {
                                            __auto_type _mv_362 = expr_get_expr_binding_name(pattern);
                                            if (_mv_362.has_value) {
                                                __auto_type name = _mv_362.value;
                                                some_binding = name;
                                                some_body = expr_transpile_branch_body_with_binding(ctx, scrutinee, branch_items, name);
                                            } else if (!_mv_362.has_value) {
                                                some_body = expr_get_match_branch_body(ctx, branch_items);
                                            }
                                        } else if (string_eq(tag, SLOP_STR("none"))) {
                                            none_body = expr_get_match_branch_body(ctx, branch_items);
                                        } else {
                                        }
                                    }
                                } else if (!_mv_361.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_359.has_value) {
            }
            i = (i + 1);
        }
        {
            __auto_type result_type = expr_infer_match_result_c_type(ctx, items);
            if (string_eq(some_binding, SLOP_STR(""))) {
                return expr_build_option_match_no_binding(ctx, scrutinee_c, some_body, none_body, result_type);
            } else {
                return expr_build_option_match_with_binding(ctx, arena, scrutinee_c, some_binding, some_body, none_body, result_type);
            }
        }
    }
}

slop_string expr_build_option_match_no_binding(context_TranspileContext* ctx, slop_string scrutinee_c, slop_string some_body, slop_string none_body, slop_string result_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (string_eq(result_type, SLOP_STR("void"))) {
        {
            __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrutinee_c);
            __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("; if (_mv.has_value) { "));
            __auto_type s3 = context_ctx_str(ctx, s2, some_body);
            __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR("; } else { "));
            __auto_type s5 = context_ctx_str(ctx, s4, none_body);
            __auto_type s6 = context_ctx_str(ctx, s5, SLOP_STR("; } (void)0; })"));
            return s6;
        }
    } else {
        {
            __auto_type typed_none_body = expr_typed_none(ctx, result_type, none_body);
            __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrutinee_c);
            __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("; _mv.has_value ? ("));
            __auto_type s3 = context_ctx_str(ctx, s2, some_body);
            __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR(") : ("));
            __auto_type s5 = context_ctx_str(ctx, s4, typed_none_body);
            __auto_type s6 = context_ctx_str(ctx, s5, SLOP_STR("); })"));
            return s6;
        }
    }
}

slop_string expr_build_option_match_with_binding(context_TranspileContext* ctx, slop_arena* arena, slop_string scrutinee_c, slop_string binding, slop_string some_body, slop_string none_body, slop_string result_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type var_c = ctype_to_c_name(arena, binding);
        if (string_eq(result_type, SLOP_STR("void"))) {
            {
                __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrutinee_c);
                __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("; if (_mv.has_value) { __auto_type "));
                __auto_type s3 = context_ctx_str(ctx, s2, var_c);
                __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR(" = _mv.value; "));
                __auto_type s5 = context_ctx_str(ctx, s4, some_body);
                __auto_type s6 = context_ctx_str(ctx, s5, SLOP_STR("; } else { "));
                __auto_type s7 = context_ctx_str(ctx, s6, none_body);
                __auto_type s8 = context_ctx_str(ctx, s7, SLOP_STR("; } (void)0; })"));
                return s8;
            }
        } else {
            {
                __auto_type typed_none_body = expr_typed_none(ctx, result_type, none_body);
                __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrutinee_c);
                __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("; _mv.has_value ? ({ __auto_type "));
                __auto_type s3 = context_ctx_str(ctx, s2, var_c);
                __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR(" = _mv.value; "));
                __auto_type s5 = context_ctx_str(ctx, s4, some_body);
                __auto_type s6 = context_ctx_str(ctx, s5, SLOP_STR("; }) : ("));
                __auto_type s7 = context_ctx_str(ctx, s6, typed_none_body);
                __auto_type s8 = context_ctx_str(ctx, s7, SLOP_STR("); })"));
                return s8;
            }
        }
    }
}

slop_string expr_infer_cond_result_c_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if (len < 2) {
            return SLOP_STR("int64_t");
        } else {
            __auto_type _mv_363 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_363.has_value) {
                __auto_type first_clause = _mv_363.value;
                __auto_type _mv_364 = (*first_clause);
                switch (_mv_364.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type clause_lst = _mv_364.data.lst;
                        {
                            __auto_type clause_items = clause_lst.items;
                            __auto_type clause_len = ((int64_t)((clause_items).len));
                            if (clause_len < 2) {
                                return SLOP_STR("int64_t");
                            } else {
                                __auto_type _mv_365 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)(clause_len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_365.has_value) {
                                    __auto_type body_expr = _mv_365.value;
                                    return expr_infer_expr_c_type(ctx, body_expr);
                                } else if (!_mv_365.has_value) {
                                    return SLOP_STR("int64_t");
                                }
                                SLOP_UNREACHABLE();
                            }
                        }
                    }
                    default: {
                        return SLOP_STR("int64_t");
                    }
                }
            } else if (!_mv_363.has_value) {
                return SLOP_STR("int64_t");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_infer_match_branch_body_type(context_TranspileContext* ctx, types_SExpr* branch) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((branch != NULL)), "(!= branch nil)");
    __auto_type _mv_366 = (*branch);
    switch (_mv_366.tag) {
        case types_SExpr_lst:
        {
            __auto_type branch_lst = _mv_366.data.lst;
            {
                __auto_type branch_items = branch_lst.items;
                __auto_type branch_len = ((int64_t)((branch_items).len));
                if (branch_len < 2) {
                    return SLOP_STR("__type_error__");
                } else {
                    __auto_type _mv_367 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)(branch_len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_367.has_value) {
                        __auto_type body_expr = _mv_367.value;
                        return expr_infer_expr_c_type(ctx, body_expr);
                    } else if (!_mv_367.has_value) {
                        return SLOP_STR("__type_error__");
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        default: {
            return SLOP_STR("__type_error__");
        }
    }
}

slop_string expr_infer_match_result_c_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 2;
        __auto_type result = SLOP_STR("__type_error__");
        if (len < 3) {
            return SLOP_STR("int64_t");
        } else {
            while ((i < len) && string_eq(result, SLOP_STR("__type_error__"))) {
                __auto_type _mv_368 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_368.has_value) {
                    __auto_type branch = _mv_368.value;
                    result = expr_infer_match_branch_body_type(ctx, branch);
                } else if (!_mv_368.has_value) {
                }
                i = (i + 1);
            }
            if (string_eq(result, SLOP_STR("__type_error__"))) {
                return SLOP_STR("int64_t");
            } else {
                return result;
            }
        }
    }
}

slop_string expr_slop_type_to_c_type(context_TranspileContext* ctx, slop_string slop_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_369 = context_ctx_lookup_type(ctx, slop_type);
        if (_mv_369.has_value) {
            __auto_type entry = _mv_369.value;
            return entry.c_name;
        } else if (!_mv_369.has_value) {
            if (strlib_starts_with(slop_type, SLOP_STR("(Ptr "))) {
                {
                    __auto_type inner = strlib_substring(arena, slop_type, 5, ((0) > ((((int64_t)(string_len(slop_type))) - 6)) ? (0) : ((((int64_t)(string_len(slop_type))) - 6))));
                    return context_ctx_str(ctx, expr_slop_type_to_c_type(ctx, inner), SLOP_STR("*"));
                }
            } else if (strlib_starts_with(slop_type, SLOP_STR("(Map ")) || strlib_starts_with(slop_type, SLOP_STR("(Set "))) {
                return SLOP_STR("slop_map*");
            } else if (strlib_starts_with(slop_type, SLOP_STR("(List "))) {
                {
                    __auto_type inner = strlib_substring(arena, slop_type, 6, ((0) > ((((int64_t)(string_len(slop_type))) - 7)) ? (0) : ((((int64_t)(string_len(slop_type))) - 7))));
                    return context_ctx_str(ctx, SLOP_STR("slop_list_"), ctype_type_to_identifier(arena, expr_slop_type_to_c_type(ctx, inner)));
                }
            } else if (strlib_starts_with(slop_type, SLOP_STR("(Option "))) {
                {
                    __auto_type inner = strlib_substring(arena, slop_type, 8, ((0) > ((((int64_t)(string_len(slop_type))) - 9)) ? (0) : ((((int64_t)(string_len(slop_type))) - 9))));
                    return context_ctx_str(ctx, SLOP_STR("slop_option_"), ctype_type_to_identifier(arena, expr_slop_type_to_c_type(ctx, inner)));
                }
            } else if (strlib_starts_with(slop_type, SLOP_STR("(Chan "))) {
                {
                    __auto_type inner = strlib_substring(arena, slop_type, 6, ((0) > ((((int64_t)(string_len(slop_type))) - 7)) ? (0) : ((((int64_t)(string_len(slop_type))) - 7))));
                    return context_ctx_str(ctx, SLOP_STR("slop_chan_"), ctype_type_to_identifier(arena, expr_slop_type_to_c_type(ctx, inner)));
                }
            } else if (strlib_starts_with(slop_type, SLOP_STR("(Thread "))) {
                {
                    __auto_type inner = strlib_substring(arena, slop_type, 8, ((0) > ((((int64_t)(string_len(slop_type))) - 9)) ? (0) : ((((int64_t)(string_len(slop_type))) - 9))));
                    return context_ctx_str(ctx, SLOP_STR("slop_thread_"), ctype_type_to_identifier(arena, expr_slop_type_to_c_type(ctx, inner)));
                }
            } else {
                return slop_type;
            }
        }
        SLOP_UNREACHABLE();
    }
}

slop_string expr_infer_expr_c_type(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type checker_type = ({ __auto_type _mv = ctype_get_node_resolved_type(expr); _mv.has_value ? ({ __auto_type rt = _mv.value; ({ __auto_type c_type = ctype_resolved_type_to_c((*ctx).arena, rt); ((strlib_contains(c_type, SLOP_STR("__typevar_error__"))) ? SLOP_STR("") : c_type); }); }) : (SLOP_STR("")); });
        if (string_len(checker_type) > 0) {
            return checker_type;
        } else {
            context_ctx_warn_fallback(ctx, expr, SLOP_STR("infer-expr-c-type"));
            __auto_type _mv_370 = (*expr);
            switch (_mv_370.tag) {
                case types_SExpr_str:
                {
                    __auto_type _ = _mv_370.data.str;
                    return SLOP_STR("slop_string");
                }
                case types_SExpr_num:
                {
                    __auto_type num = _mv_370.data.num;
                    if (num.is_float) {
                        return SLOP_STR("double");
                    } else {
                        return SLOP_STR("int64_t");
                    }
                }
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_370.data.sym;
                    {
                        __auto_type name = sym.name;
                        __auto_type _mv_371 = context_ctx_lookup_var(ctx, name);
                        if (_mv_371.has_value) {
                            __auto_type entry = _mv_371.value;
                            {
                                __auto_type c_type = entry.c_type;
                                __auto_type slop_type = entry.slop_type;
                                if (string_eq(c_type, SLOP_STR("auto")) || (string_len(c_type) == 0)) {
                                    if (string_len(slop_type) > 0) {
                                        return expr_slop_type_to_c_type(ctx, slop_type);
                                    } else {
                                        return SLOP_STR("int64_t");
                                    }
                                } else {
                                    return c_type;
                                }
                            }
                        } else if (!_mv_371.has_value) {
                            return SLOP_STR("int64_t");
                        }
                        SLOP_UNREACHABLE();
                    }
                }
                case types_SExpr_lst:
                {
                    __auto_type lst = _mv_370.data.lst;
                    {
                        __auto_type items = lst.items;
                        if (((int64_t)((items).len)) < 1) {
                            return SLOP_STR("int64_t");
                        } else {
                            __auto_type _mv_372 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_372.has_value) {
                                __auto_type head = _mv_372.value;
                                __auto_type _mv_373 = (*head);
                                switch (_mv_373.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type sym = _mv_373.data.sym;
                                        {
                                            __auto_type op = sym.name;
                                            if (({ __auto_type _mv = context_ctx_lookup_func(ctx, op); _mv.has_value ? ({ __auto_type func_entry = _mv.value; func_entry.returns_string; }) : (0); })) {
                                                return SLOP_STR("slop_string");
                                            } else if (string_eq(op, SLOP_STR("."))) {
                                                return expr_infer_field_c_type_from_items(ctx, items);
                                            } else if (string_eq(op, SLOP_STR("let")) || string_eq(op, SLOP_STR("let*"))) {
                                                if (((int64_t)((items).len)) < 3) {
                                                    return SLOP_STR("int64_t");
                                                } else {
                                                    __auto_type _mv_374 = ({ __auto_type _lst = items; size_t _idx = (size_t)(((int64_t)((items).len)) - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_374.has_value) {
                                                        __auto_type body = _mv_374.value;
                                                        return expr_infer_expr_c_type(ctx, body);
                                                    } else if (!_mv_374.has_value) {
                                                        return SLOP_STR("int64_t");
                                                    }
                                                    SLOP_UNREACHABLE();
                                                }
                                            } else if (string_eq(op, SLOP_STR("do"))) {
                                                if (((int64_t)((items).len)) < 2) {
                                                    return SLOP_STR("void");
                                                } else {
                                                    __auto_type _mv_375 = ({ __auto_type _lst = items; size_t _idx = (size_t)(((int64_t)((items).len)) - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_375.has_value) {
                                                        __auto_type last_expr = _mv_375.value;
                                                        return expr_infer_expr_c_type(ctx, last_expr);
                                                    } else if (!_mv_375.has_value) {
                                                        return SLOP_STR("void");
                                                    }
                                                    SLOP_UNREACHABLE();
                                                }
                                            } else if (string_eq(op, SLOP_STR("cond"))) {
                                                return expr_infer_cond_result_c_type(ctx, items);
                                            } else if (string_eq(op, SLOP_STR("with-arena"))) {
                                                if (((int64_t)((items).len)) < 3) {
                                                    return SLOP_STR("int64_t");
                                                } else {
                                                    __auto_type _mv_376 = ({ __auto_type _lst = items; size_t _idx = (size_t)(((int64_t)((items).len)) - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_376.has_value) {
                                                        __auto_type body = _mv_376.value;
                                                        return expr_infer_expr_c_type(ctx, body);
                                                    } else if (!_mv_376.has_value) {
                                                        return SLOP_STR("int64_t");
                                                    }
                                                    SLOP_UNREACHABLE();
                                                }
                                            } else if (string_eq(op, SLOP_STR("match"))) {
                                                return expr_infer_match_result_c_type(ctx, items);
                                            } else if (string_eq(op, SLOP_STR("if"))) {
                                                if (((int64_t)((items).len)) < 3) {
                                                    return SLOP_STR("int64_t");
                                                } else {
                                                    __auto_type _mv_377 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_377.has_value) {
                                                        __auto_type then_expr = _mv_377.value;
                                                        return expr_infer_expr_c_type(ctx, then_expr);
                                                    } else if (!_mv_377.has_value) {
                                                        return SLOP_STR("int64_t");
                                                    }
                                                    SLOP_UNREACHABLE();
                                                }
                                            } else if (string_eq(op, SLOP_STR("some"))) {
                                                if (((int64_t)((items).len)) < 2) {
                                                    context_ctx_add_error_at(ctx, SLOP_STR("some constructor requires a value"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                                                    return SLOP_STR("__type_error__");
                                                } else {
                                                    __auto_type _mv_378 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_378.has_value) {
                                                        __auto_type val_expr = _mv_378.value;
                                                        {
                                                            __auto_type val_type = expr_infer_expr_c_type(ctx, val_expr);
                                                            if (string_eq(val_type, SLOP_STR("slop_string"))) {
                                                                return SLOP_STR("slop_option_string");
                                                            } else if (string_eq(val_type, SLOP_STR("int64_t"))) {
                                                                return SLOP_STR("slop_option_int");
                                                            } else if (string_eq(val_type, SLOP_STR("double"))) {
                                                                return SLOP_STR("slop_option_float");
                                                            } else if (strlib_ends_with(val_type, SLOP_STR("*"))) {
                                                                {
                                                                    __auto_type ctx_arena = (*ctx).arena;
                                                                    __auto_type base_type = expr_strip_pointer_suffix(ctx_arena, val_type);
                                                                    return context_ctx_str3(ctx, SLOP_STR("slop_option_"), base_type, SLOP_STR("_ptr"));
                                                                }
                                                            } else {
                                                                return context_ctx_str3(ctx, SLOP_STR("slop_option_"), val_type, SLOP_STR(""));
                                                            }
                                                        }
                                                    } else if (!_mv_378.has_value) {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("some constructor: missing value expression"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                                                        return SLOP_STR("__type_error__");
                                                    }
                                                    SLOP_UNREACHABLE();
                                                }
                                            } else if (string_eq(op, SLOP_STR("none"))) {
                                                __auto_type _mv_379 = context_ctx_get_current_return_type(ctx);
                                                if (_mv_379.has_value) {
                                                    __auto_type ret_type = _mv_379.value;
                                                    if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                                                        return ret_type;
                                                    } else {
                                                        return SLOP_STR("slop_option_int");
                                                    }
                                                } else if (!_mv_379.has_value) {
                                                    return SLOP_STR("slop_option_int");
                                                }
                                                SLOP_UNREACHABLE();
                                            } else if (string_eq(op, SLOP_STR("list-push"))) {
                                                return SLOP_STR("void");
                                            } else if (string_eq(op, SLOP_STR("list-set"))) {
                                                return SLOP_STR("bool");
                                            } else if (string_eq(op, SLOP_STR("set!"))) {
                                                return SLOP_STR("void");
                                            } else if (string_eq(op, SLOP_STR("cast"))) {
                                                if (((int64_t)((items).len)) < 2) {
                                                    return SLOP_STR("void*");
                                                } else {
                                                    __auto_type _mv_380 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_380.has_value) {
                                                        __auto_type type_expr = _mv_380.value;
                                                        return context_to_c_type_prefixed(ctx, type_expr);
                                                    } else if (!_mv_380.has_value) {
                                                        return SLOP_STR("void*");
                                                    }
                                                    SLOP_UNREACHABLE();
                                                }
                                            } else if (string_eq(op, SLOP_STR("deref"))) {
                                                if (((int64_t)((items).len)) < 2) {
                                                    return SLOP_STR("int64_t");
                                                } else {
                                                    __auto_type _mv_381 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_381.has_value) {
                                                        __auto_type inner = _mv_381.value;
                                                        {
                                                            __auto_type inner_type = expr_infer_expr_c_type(ctx, inner);
                                                            if (strlib_ends_with(inner_type, SLOP_STR("*"))) {
                                                                return expr_strip_pointer_suffix((*ctx).arena, inner_type);
                                                            } else {
                                                                return inner_type;
                                                            }
                                                        }
                                                    } else if (!_mv_381.has_value) {
                                                        return SLOP_STR("int64_t");
                                                    }
                                                    SLOP_UNREACHABLE();
                                                }
                                            } else if (string_eq(op, SLOP_STR("string-concat"))) {
                                                return SLOP_STR("slop_string");
                                            } else if (string_eq(op, SLOP_STR("list-len"))) {
                                                return SLOP_STR("int64_t");
                                            } else if (string_eq(op, SLOP_STR("is-none")) || string_eq(op, SLOP_STR("is-some"))) {
                                                return SLOP_STR("bool");
                                            } else if (string_eq(op, SLOP_STR("string-len"))) {
                                                return SLOP_STR("int64_t");
                                            } else if (string_eq(op, SLOP_STR("string-eq"))) {
                                                return SLOP_STR("uint8_t");
                                            } else if (string_eq(op, SLOP_STR("addr"))) {
                                                if (((int64_t)((items).len)) < 2) {
                                                    return SLOP_STR("void*");
                                                } else {
                                                    __auto_type _mv_382 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_382.has_value) {
                                                        __auto_type inner = _mv_382.value;
                                                        return context_ctx_str3(ctx, expr_infer_expr_c_type(ctx, inner), SLOP_STR("*"), SLOP_STR(""));
                                                    } else if (!_mv_382.has_value) {
                                                        return SLOP_STR("void*");
                                                    }
                                                    SLOP_UNREACHABLE();
                                                }
                                            } else if (string_eq(op, SLOP_STR("send")) || strlib_ends_with(op, SLOP_STR(":send"))) {
                                                return SLOP_STR("slop_result_void_thread_ChanError");
                                            } else if (string_eq(op, SLOP_STR("recv")) || strlib_ends_with(op, SLOP_STR(":recv"))) {
                                                if (((int64_t)((items).len)) < 2) {
                                                    return SLOP_STR("slop_result_int64_t_thread_ChanError");
                                                } else {
                                                    __auto_type _mv_383 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_383.has_value) {
                                                        __auto_type chan_arg = _mv_383.value;
                                                        {
                                                            __auto_type chan_c_type = expr_infer_expr_c_type(ctx, chan_arg);
                                                            __auto_type chan_type = expr_strip_pointer_suffix((*ctx).arena, chan_c_type);
                                                            if (strlib_starts_with(chan_type, SLOP_STR("slop_chan_"))) {
                                                                {
                                                                    __auto_type inner_id = expr_substring_after_prefix((*ctx).arena, chan_type, SLOP_STR("slop_chan_"));
                                                                    return context_ctx_str3(ctx, SLOP_STR("slop_result_"), inner_id, SLOP_STR("_thread_ChanError"));
                                                                }
                                                            } else {
                                                                return SLOP_STR("slop_result_int64_t_thread_ChanError");
                                                            }
                                                        }
                                                    } else if (!_mv_383.has_value) {
                                                        return SLOP_STR("slop_result_int64_t_thread_ChanError");
                                                    }
                                                    SLOP_UNREACHABLE();
                                                }
                                            } else if (string_eq(op, SLOP_STR("join")) || strlib_ends_with(op, SLOP_STR(":join"))) {
                                                return SLOP_STR("int64_t");
                                            } else if (string_eq(op, SLOP_STR("spawn")) || strlib_ends_with(op, SLOP_STR(":spawn"))) {
                                                return SLOP_STR("slop_thread*");
                                            } else if (string_eq(op, SLOP_STR("chan-buffered")) || strlib_ends_with(op, SLOP_STR(":chan-buffered"))) {
                                                if (((int64_t)((items).len)) < 4) {
                                                    return SLOP_STR("slop_chan_int*");
                                                } else {
                                                    __auto_type _mv_384 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_384.has_value) {
                                                        __auto_type type_expr = _mv_384.value;
                                                        {
                                                            __auto_type elem_c = context_to_c_type_prefixed(ctx, type_expr);
                                                            __auto_type elem_id = ctype_type_to_identifier((*ctx).arena, elem_c);
                                                            return context_ctx_str3(ctx, SLOP_STR("slop_chan_"), elem_id, SLOP_STR("*"));
                                                        }
                                                    } else if (!_mv_384.has_value) {
                                                        return SLOP_STR("slop_chan_int*");
                                                    }
                                                    SLOP_UNREACHABLE();
                                                }
                                            } else if (string_eq(op, SLOP_STR("chan")) || strlib_ends_with(op, SLOP_STR(":chan"))) {
                                                if (((int64_t)((items).len)) < 3) {
                                                    return SLOP_STR("slop_chan_int*");
                                                } else {
                                                    __auto_type _mv_385 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_385.has_value) {
                                                        __auto_type type_expr = _mv_385.value;
                                                        {
                                                            __auto_type elem_c = context_to_c_type_prefixed(ctx, type_expr);
                                                            __auto_type elem_id = ctype_type_to_identifier((*ctx).arena, elem_c);
                                                            return context_ctx_str3(ctx, SLOP_STR("slop_chan_"), elem_id, SLOP_STR("*"));
                                                        }
                                                    } else if (!_mv_385.has_value) {
                                                        return SLOP_STR("slop_chan_int*");
                                                    }
                                                    SLOP_UNREACHABLE();
                                                }
                                            } else if (string_eq(op, SLOP_STR("arena-alloc"))) {
                                                return SLOP_STR("void*");
                                            } else if (string_eq(op, SLOP_STR("arena-new"))) {
                                                return SLOP_STR("slop_arena*");
                                            } else if (string_eq(op, SLOP_STR("arena-free"))) {
                                                return SLOP_STR("void");
                                            } else if (string_eq(op, SLOP_STR("list-new"))) {
                                                if (((int64_t)((items).len)) < 3) {
                                                    context_ctx_add_error_at(ctx, SLOP_STR("Cannot infer list-new type: missing element type argument"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                                                    return SLOP_STR("__type_error__");
                                                } else {
                                                    __auto_type _mv_386 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_386.has_value) {
                                                        __auto_type type_expr = _mv_386.value;
                                                        {
                                                            __auto_type elem_c = ctype_to_c_type((*ctx).arena, type_expr);
                                                            return context_ctx_str3(ctx, SLOP_STR("slop_list_"), ctype_type_to_identifier((*ctx).arena, elem_c), SLOP_STR(""));
                                                        }
                                                    } else if (!_mv_386.has_value) {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("Cannot infer list-new element type"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                                                        return SLOP_STR("__type_error__");
                                                    }
                                                    SLOP_UNREACHABLE();
                                                }
                                            } else if (string_eq(op, SLOP_STR("list-get"))) {
                                                if (((int64_t)((items).len)) < 2) {
                                                    context_ctx_add_error_at(ctx, SLOP_STR("Cannot infer list-get type: missing list argument"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                                                    return SLOP_STR("__type_error__");
                                                } else {
                                                    __auto_type _mv_387 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_387.has_value) {
                                                        __auto_type list_arg = _mv_387.value;
                                                        {
                                                            __auto_type list_c_type = expr_infer_expr_c_type(ctx, list_arg);
                                                            if (strlib_starts_with(list_c_type, SLOP_STR("slop_list_"))) {
                                                                {
                                                                    __auto_type elem_id = expr_substring_after_prefix((*ctx).arena, list_c_type, SLOP_STR("slop_list_"));
                                                                    return context_ctx_str3(ctx, SLOP_STR("slop_option_"), elem_id, SLOP_STR(""));
                                                                }
                                                            } else {
                                                                context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("Cannot infer list-get element type from '"), list_c_type, SLOP_STR("'")), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                                                                return SLOP_STR("__type_error__");
                                                            }
                                                        }
                                                    } else if (!_mv_387.has_value) {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("Cannot infer list-get type: missing argument"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                                                        return SLOP_STR("__type_error__");
                                                    }
                                                    SLOP_UNREACHABLE();
                                                }
                                            } else if (string_eq(op, SLOP_STR("int-to-string"))) {
                                                return SLOP_STR("slop_string");
                                            } else if (string_eq(op, SLOP_STR("when"))) {
                                                return SLOP_STR("void");
                                            } else if (string_eq(op, SLOP_STR("for")) || string_eq(op, SLOP_STR("for-each"))) {
                                                return SLOP_STR("int64_t");
                                            } else if (string_eq(op, SLOP_STR("+")) || (string_eq(op, SLOP_STR("-")) || (string_eq(op, SLOP_STR("*")) || (string_eq(op, SLOP_STR("/")) || string_eq(op, SLOP_STR("%")))))) {
                                                return SLOP_STR("int64_t");
                                            } else if (string_eq(op, SLOP_STR("=")) || (string_eq(op, SLOP_STR(">")) || (string_eq(op, SLOP_STR("<")) || (string_eq(op, SLOP_STR(">=")) || (string_eq(op, SLOP_STR("<=")) || (string_eq(op, SLOP_STR("==")) || string_eq(op, SLOP_STR("!=")))))))) {
                                                return SLOP_STR("uint8_t");
                                            } else if (string_eq(op, SLOP_STR("and")) || (string_eq(op, SLOP_STR("or")) || string_eq(op, SLOP_STR("not")))) {
                                                return SLOP_STR("uint8_t");
                                            } else if (string_eq(op, SLOP_STR("@"))) {
                                                return SLOP_STR("uint8_t");
                                            } else {
                                                __auto_type _mv_388 = context_ctx_lookup_type(ctx, op);
                                                if (_mv_388.has_value) {
                                                    __auto_type type_entry = _mv_388.value;
                                                    return type_entry.c_name;
                                                } else if (!_mv_388.has_value) {
                                                    __auto_type _mv_389 = context_ctx_lookup_func(ctx, op);
                                                    if (_mv_389.has_value) {
                                                        __auto_type func_entry = _mv_389.value;
                                                        {
                                                            __auto_type ret_type = func_entry.return_type;
                                                            if (func_entry.returns_string) {
                                                                return SLOP_STR("slop_string");
                                                            } else if (string_eq(ret_type, SLOP_STR("void"))) {
                                                                return SLOP_STR("void");
                                                            } else if (string_len(ret_type) > 0) {
                                                                return ret_type;
                                                            } else {
                                                                context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("function '"), op, SLOP_STR("' has no return type information")), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                                                                return SLOP_STR("__type_error__");
                                                            }
                                                        }
                                                    } else if (!_mv_389.has_value) {
                                                        context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("unknown function or type '"), op, SLOP_STR("'")), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                                                        return SLOP_STR("__type_error__");
                                                    }
                                                    SLOP_UNREACHABLE();
                                                }
                                                SLOP_UNREACHABLE();
                                            }
                                        }
                                    }
                                    default: {
                                        context_ctx_add_error_at(ctx, SLOP_STR("cannot infer type: list head is not a symbol"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                                        return SLOP_STR("__type_error__");
                                    }
                                }
                            } else if (!_mv_372.has_value) {
                                context_ctx_add_error_at(ctx, SLOP_STR("cannot infer type of empty list"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                                return SLOP_STR("__type_error__");
                            }
                            SLOP_UNREACHABLE();
                        }
                    }
                }
                default: {
                    context_ctx_add_error_at(ctx, SLOP_STR("cannot infer type of expression"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    return SLOP_STR("__type_error__");
                }
            }
        }
    }
}

slop_string expr_build_result_match_expr(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_string scrutinee_c, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result_type = expr_infer_match_result_c_type(ctx, items);
        __auto_type ok_body = SLOP_STR("0");
        __auto_type err_body = SLOP_STR("0");
        __auto_type ok_binding = SLOP_STR("");
        __auto_type err_binding = SLOP_STR("");
        int64_t i = 2;
        while (i < len) {
            __auto_type _mv_390 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_390.has_value) {
                __auto_type branch = _mv_390.value;
                __auto_type _mv_391 = (*branch);
                switch (_mv_391.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_391.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if (((int64_t)((branch_items).len)) >= 2) {
                                __auto_type _mv_392 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_392.has_value) {
                                    __auto_type pattern = _mv_392.value;
                                    {
                                        __auto_type tag = expr_get_expr_pattern_tag(pattern);
                                        if (string_eq(tag, SLOP_STR("ok"))) {
                                            __auto_type _mv_393 = expr_get_expr_binding_name(pattern);
                                            if (_mv_393.has_value) {
                                                __auto_type name = _mv_393.value;
                                                ok_binding = name;
                                                ok_body = expr_transpile_branch_body_with_binding(ctx, scrutinee, branch_items, name);
                                            } else if (!_mv_393.has_value) {
                                                ok_body = expr_get_match_branch_body(ctx, branch_items);
                                            }
                                        } else if (string_eq(tag, SLOP_STR("error"))) {
                                            __auto_type _mv_394 = expr_get_expr_binding_name(pattern);
                                            if (_mv_394.has_value) {
                                                __auto_type name = _mv_394.value;
                                                err_binding = name;
                                                err_body = expr_transpile_branch_body_with_binding(ctx, scrutinee, branch_items, name);
                                            } else if (!_mv_394.has_value) {
                                                err_body = expr_get_match_branch_body(ctx, branch_items);
                                            }
                                        } else {
                                        }
                                    }
                                } else if (!_mv_392.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_390.has_value) {
            }
            i = (i + 1);
        }
        {
            __auto_type ok_bind = ((string_eq(ok_binding, SLOP_STR(""))) ? SLOP_STR("") : context_ctx_str3(ctx, SLOP_STR("__auto_type "), ctype_to_c_name(arena, ok_binding), SLOP_STR(" = _mv.data.ok; ")));
            __auto_type err_bind = ((string_eq(err_binding, SLOP_STR(""))) ? SLOP_STR("") : context_ctx_str3(ctx, SLOP_STR("__auto_type "), ctype_to_c_name(arena, err_binding), SLOP_STR(" = _mv.data.err; ")));
            if (string_eq(result_type, SLOP_STR("void"))) {
                context_ctx_str(ctx, context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrutinee_c), context_ctx_str(ctx, SLOP_STR("; if (_mv.is_ok) { "), context_ctx_str(ctx, ok_bind, context_ctx_str(ctx, ok_body, context_ctx_str(ctx, SLOP_STR("; } else { "), context_ctx_str(ctx, err_bind, context_ctx_str(ctx, err_body, SLOP_STR("; } (void)0; })"))))))));
            }
            return context_ctx_str(ctx, context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrutinee_c), context_ctx_str(ctx, context_ctx_str3(ctx, SLOP_STR("; "), result_type, SLOP_STR(" _mr; if (_mv.is_ok) { ")), context_ctx_str(ctx, ok_bind, context_ctx_str(ctx, SLOP_STR("_mr = "), context_ctx_str(ctx, ok_body, context_ctx_str(ctx, SLOP_STR("; } else { "), context_ctx_str(ctx, err_bind, context_ctx_str(ctx, SLOP_STR("_mr = "), context_ctx_str(ctx, err_body, SLOP_STR("; } _mr; })"))))))))));
        }
    }
}

slop_string expr_build_enum_match_expr(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result_type = expr_infer_match_result_c_type(ctx, items);
        __auto_type cases = SLOP_STR("");
        int64_t i = 2;
        while (i < len) {
            __auto_type _mv_395 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_395.has_value) {
                __auto_type branch = _mv_395.value;
                __auto_type _mv_396 = (*branch);
                switch (_mv_396.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_396.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if (((int64_t)((branch_items).len)) >= 2) {
                                __auto_type _mv_397 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_397.has_value) {
                                    __auto_type pattern = _mv_397.value;
                                    cases = expr_build_enum_case_expr(ctx, arena, cases, pattern, branch_items, result_type);
                                } else if (!_mv_397.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_395.has_value) {
            }
            i = (i + 1);
        }
        if (string_eq(result_type, SLOP_STR("void"))) {
            {
                __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrutinee_c);
                __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("; switch (_mv) { "));
                __auto_type s3 = context_ctx_str(ctx, s2, cases);
                __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR(" } (void)0; })"));
                return s4;
            }
        } else {
            {
                __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrutinee_c);
                __auto_type s2 = context_ctx_str(ctx, s1, context_ctx_str(ctx, SLOP_STR("; "), context_ctx_str(ctx, result_type, SLOP_STR(" _mr = {0}; switch (_mv) { "))));
                __auto_type s3 = context_ctx_str(ctx, s2, cases);
                __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR(" } _mr; })"));
                return s4;
            }
        }
    }
}

slop_string expr_build_enum_case_expr(context_TranspileContext* ctx, slop_arena* arena, slop_string cases, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, slop_string result_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type tag = expr_get_expr_pattern_tag(pattern);
        __auto_type is_void = string_eq(result_type, SLOP_STR("void"));
        if (string_eq(tag, SLOP_STR("else")) || string_eq(tag, SLOP_STR("_"))) {
            {
                __auto_type body = expr_typed_none(ctx, result_type, expr_get_match_branch_body(ctx, branch_items));
                if (is_void) {
                    return context_ctx_str(ctx, cases, context_ctx_str3(ctx, SLOP_STR("default: { "), body, SLOP_STR("; break; } ")));
                } else {
                    return context_ctx_str(ctx, cases, context_ctx_str3(ctx, SLOP_STR("default: { _mr = "), body, SLOP_STR("; break; } ")));
                }
            }
        } else {
            __auto_type _mv_398 = context_ctx_lookup_enum_variant(ctx, tag);
            if (_mv_398.has_value) {
                __auto_type type_name = _mv_398.value;
                {
                    __auto_type c_tag = ctype_to_c_name(arena, tag);
                    __auto_type case_label = context_ctx_str4(ctx, type_name, SLOP_STR("_"), c_tag, SLOP_STR(""));
                    __auto_type body = expr_typed_none(ctx, result_type, expr_get_match_branch_body(ctx, branch_items));
                    if (is_void) {
                        return context_ctx_str(ctx, cases, context_ctx_str(ctx, SLOP_STR("case "), context_ctx_str(ctx, case_label, context_ctx_str3(ctx, SLOP_STR(": { "), body, SLOP_STR("; break; } ")))));
                    } else {
                        return context_ctx_str(ctx, cases, context_ctx_str(ctx, SLOP_STR("case "), context_ctx_str(ctx, case_label, context_ctx_str3(ctx, SLOP_STR(": { _mr = "), body, SLOP_STR("; break; } ")))));
                    }
                }
            } else if (!_mv_398.has_value) {
                context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("unknown enum variant '"), tag, SLOP_STR("' in match expression")), context_ctx_sexpr_line(pattern), context_ctx_sexpr_col(pattern));
                return cases;
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_build_union_match_expr(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_string scrutinee_c, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result_type = expr_infer_match_result_c_type(ctx, items);
        __auto_type cases = SLOP_STR("");
        int64_t i = 2;
        while (i < len) {
            __auto_type _mv_399 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_399.has_value) {
                __auto_type branch = _mv_399.value;
                __auto_type _mv_400 = (*branch);
                switch (_mv_400.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_400.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if (((int64_t)((branch_items).len)) >= 2) {
                                __auto_type _mv_401 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_401.has_value) {
                                    __auto_type pattern = _mv_401.value;
                                    cases = expr_build_union_case_expr(ctx, arena, cases, scrutinee, pattern, branch_items, result_type);
                                } else if (!_mv_401.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_399.has_value) {
            }
            i = (i + 1);
        }
        {
            __auto_type scrut_c_type = expr_infer_expr_c_type(ctx, scrutinee);
            __auto_type scrut_val = (((context_ends_with_star(scrut_c_type) || expr_is_pointer_expr(ctx, scrutinee))) ? context_ctx_str3(ctx, SLOP_STR("*("), scrutinee_c, SLOP_STR(")")) : scrutinee_c);
            if (string_eq(result_type, SLOP_STR("void"))) {
                {
                    __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrut_val);
                    __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("; switch (_mv.tag) { "));
                    __auto_type s3 = context_ctx_str(ctx, s2, cases);
                    __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR(" } (void)0; })"));
                    return s4;
                }
            } else {
                {
                    __auto_type s1 = context_ctx_str(ctx, SLOP_STR("({ __auto_type _mv = "), scrut_val);
                    __auto_type s2 = context_ctx_str(ctx, s1, context_ctx_str(ctx, SLOP_STR("; "), context_ctx_str(ctx, result_type, SLOP_STR(" _mr = {0}; switch (_mv.tag) { "))));
                    __auto_type s3 = context_ctx_str(ctx, s2, cases);
                    __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR(" } _mr; })"));
                    return s4;
                }
            }
        }
    }
}

slop_string expr_typed_none(context_TranspileContext* ctx, slop_string result_type, slop_string body) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (string_eq(body, SLOP_STR("none")) && context_ctx_is_option_c_type(ctx, result_type)) {
        return context_ctx_str3(ctx, SLOP_STR("("), result_type, SLOP_STR("){.has_value = false}"));
    } else {
        return body;
    }
}

slop_string expr_typed_none_arg(context_TranspileContext* ctx, slop_string expected_type, slop_string arg_c) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (string_eq(arg_c, SLOP_STR("none")) && context_ctx_is_option_c_type(ctx, expected_type)) {
        return context_ctx_str3(ctx, SLOP_STR("(("), expected_type, SLOP_STR("){.has_value = false})"));
    } else {
        return arg_c;
    }
}

slop_string expr_wrap_fn_ref_as_closure(context_TranspileContext* ctx, slop_string expected_type, slop_string arg_c, types_SExpr* arg_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (string_eq(expected_type, SLOP_STR("slop_closure_t"))) {
        __auto_type _mv_402 = (*arg_expr);
        switch (_mv_402.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_402.data.sym;
                {
                    __auto_type slop_name = sym.name;
                    __auto_type _mv_403 = context_ctx_lookup_func(ctx, slop_name);
                    if (_mv_403.has_value) {
                        __auto_type func_entry = _mv_403.value;
                        {
                            __auto_type trampoline_name = expr_generate_fn_trampoline(ctx, arg_c, func_entry);
                            return context_ctx_str5(ctx, SLOP_STR("(slop_closure_t){(void*)"), trampoline_name, SLOP_STR(", NULL}"), SLOP_STR(""), SLOP_STR(""));
                        }
                    } else if (!_mv_403.has_value) {
                        return arg_c;
                    }
                    SLOP_UNREACHABLE();
                }
            }
            default: {
                return arg_c;
            }
        }
    } else {
        return arg_c;
    }
}

slop_string expr_generate_fn_trampoline(context_TranspileContext* ctx, slop_string fn_c_name, context_FuncEntry func_entry) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type trampoline_name = context_ctx_str(ctx, SLOP_STR("_wrap_"), fn_c_name);
        if (context_ctx_skip_trampoline_generation(ctx)) {
            return trampoline_name;
        } else {
            if (context_ctx_has_trampoline(ctx, fn_c_name)) {
                return trampoline_name;
            } else {
                {
                    __auto_type ret_type = func_entry.return_type;
                    __auto_type param_types = func_entry.param_types;
                    __auto_type count = ((int64_t)((param_types).len));
                    __auto_type param_str = SLOP_STR("");
                    __auto_type arg_str = SLOP_STR("");
                    int64_t i = 0;
                    while (i < count) {
                        __auto_type _mv_404 = ({ __auto_type _lst = param_types; size_t _idx = (size_t)i; slop_option_context_FuncParamType_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_404.has_value) {
                            __auto_type param_type_ptr = _mv_404.value;
                            {
                                __auto_type c_type = (*param_type_ptr).c_type;
                                __auto_type arg_name = context_ctx_str3(ctx, SLOP_STR("_p"), int_to_string(arena, i), SLOP_STR(""));
                                param_str = context_ctx_str(ctx, param_str, context_ctx_str3(ctx, SLOP_STR(", "), c_type, context_ctx_str(ctx, SLOP_STR(" "), arg_name)));
                                if (i == 0) {
                                    arg_str = arg_name;
                                } else {
                                    arg_str = context_ctx_str3(ctx, arg_str, SLOP_STR(", "), arg_name);
                                }
                            }
                        } else if (!_mv_404.has_value) {
                        }
                        i = (i + 1);
                    }
                    {
                        __auto_type fn_def = context_ctx_str(ctx, SLOP_STR("static "), context_ctx_str(ctx, ret_type, context_ctx_str(ctx, SLOP_STR(" "), context_ctx_str(ctx, trampoline_name, context_ctx_str(ctx, SLOP_STR("(void* _env"), context_ctx_str(ctx, param_str, context_ctx_str(ctx, SLOP_STR(") { return "), context_ctx_str(ctx, fn_c_name, context_ctx_str(ctx, SLOP_STR("("), context_ctx_str(ctx, arg_str, SLOP_STR("); }")))))))))));
                        context_ctx_add_deferred_lambda(ctx, fn_def);
                        context_ctx_add_trampoline(ctx, fn_c_name);
                        return trampoline_name;
                    }
                }
            }
        }
    }
}

slop_string expr_build_union_case_expr(context_TranspileContext* ctx, slop_arena* arena, slop_string cases, types_SExpr* scrutinee, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, slop_string result_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type tag = expr_get_expr_pattern_tag(pattern);
        __auto_type is_void = string_eq(result_type, SLOP_STR("void"));
        if (string_eq(tag, SLOP_STR("else")) || string_eq(tag, SLOP_STR("_"))) {
            {
                __auto_type body = expr_typed_none(ctx, result_type, expr_get_match_branch_body(ctx, branch_items));
                if (is_void) {
                    return context_ctx_str(ctx, cases, context_ctx_str3(ctx, SLOP_STR("default: { "), body, SLOP_STR("; break; } ")));
                } else {
                    return context_ctx_str(ctx, cases, context_ctx_str3(ctx, SLOP_STR("default: { _mr = "), body, SLOP_STR("; break; } ")));
                }
            }
        } else {
            __auto_type _mv_405 = context_ctx_lookup_enum_variant(ctx, tag);
            if (_mv_405.has_value) {
                __auto_type type_name = _mv_405.value;
                {
                    __auto_type c_tag = ctype_to_c_name(arena, tag);
                    __auto_type case_label = context_ctx_str4(ctx, type_name, SLOP_STR("_"), c_tag, SLOP_STR(""));
                    __auto_type binding_opt = expr_get_expr_binding_name(pattern);
                    __auto_type _mv_406 = binding_opt;
                    if (_mv_406.has_value) {
                        __auto_type binding_name = _mv_406.value;
                        {
                            __auto_type c_binding = ctype_to_c_name(arena, binding_name);
                            __auto_type body = expr_typed_none(ctx, result_type, expr_transpile_branch_body_with_binding(ctx, scrutinee, branch_items, binding_name));
                            __auto_type s1 = context_ctx_str(ctx, cases, SLOP_STR("case "));
                            __auto_type s2 = context_ctx_str(ctx, s1, case_label);
                            __auto_type s3 = context_ctx_str(ctx, s2, SLOP_STR(": { __auto_type "));
                            __auto_type s4 = context_ctx_str(ctx, s3, c_binding);
                            __auto_type s5 = context_ctx_str(ctx, s4, SLOP_STR(" = _mv.data."));
                            __auto_type s6 = context_ctx_str(ctx, s5, c_tag);
                            __auto_type s7 = ((is_void) ? context_ctx_str(ctx, s6, SLOP_STR("; ")) : context_ctx_str(ctx, s6, SLOP_STR("; _mr = ")));
                            __auto_type s8 = context_ctx_str(ctx, s7, body);
                            __auto_type s9 = context_ctx_str(ctx, s8, SLOP_STR("; break; } "));
                            return s9;
                        }
                    } else if (!_mv_406.has_value) {
                        {
                            __auto_type body = expr_typed_none(ctx, result_type, expr_get_match_branch_body(ctx, branch_items));
                            __auto_type s1 = context_ctx_str(ctx, cases, SLOP_STR("case "));
                            __auto_type s2 = context_ctx_str(ctx, s1, case_label);
                            __auto_type s3 = ((is_void) ? context_ctx_str(ctx, s2, SLOP_STR(": { ")) : context_ctx_str(ctx, s2, SLOP_STR(": { _mr = ")));
                            __auto_type s4 = context_ctx_str(ctx, s3, body);
                            __auto_type s5 = context_ctx_str(ctx, s4, SLOP_STR("; break; } "));
                            return s5;
                        }
                    }
                    SLOP_UNREACHABLE();
                }
            } else if (!_mv_405.has_value) {
                return cases;
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_build_ternary_match_expr(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result = SLOP_STR("");
        uint8_t first_branch = 1;
        int64_t i = (len - 1);
        while (i >= 2) {
            __auto_type _mv_407 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_407.has_value) {
                __auto_type branch = _mv_407.value;
                __auto_type _mv_408 = (*branch);
                switch (_mv_408.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_408.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if (((int64_t)((branch_items).len)) >= 2) {
                                __auto_type _mv_409 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_409.has_value) {
                                    __auto_type pattern = _mv_409.value;
                                    {
                                        __auto_type tag = expr_get_expr_pattern_tag(pattern);
                                        __auto_type body = expr_get_match_branch_body(ctx, branch_items);
                                        if (string_eq(tag, SLOP_STR("else")) || string_eq(tag, SLOP_STR("_"))) {
                                            result = body;
                                            first_branch = 0;
                                        } else if (first_branch) {
                                            result = body;
                                            first_branch = 0;
                                        } else {
                                            {
                                                __auto_type pattern_c = expr_transpile_expr(ctx, pattern);
                                                result = context_ctx_str(ctx, context_ctx_str(ctx, SLOP_STR("(("), scrutinee_c), context_ctx_str(ctx, SLOP_STR(" == "), context_ctx_str(ctx, pattern_c, context_ctx_str(ctx, SLOP_STR(") ? "), context_ctx_str(ctx, body, context_ctx_str(ctx, SLOP_STR(" : "), context_ctx_str(ctx, result, SLOP_STR(")"))))))));
                                            }
                                        }
                                    }
                                } else if (!_mv_409.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_407.has_value) {
            }
            i = (i - 1);
        }
        if (string_eq(result, SLOP_STR(""))) {
            return SLOP_STR("0");
        } else {
            return result;
        }
    }
}

uint8_t expr_discard_needs_void(types_SExpr* e) {
    __auto_type _mv_410 = (*e);
    switch (_mv_410.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_410.data.lst;
            __auto_type _mv_411 = ({ __auto_type _lst = lst.items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_411.has_value) {
                __auto_type head = _mv_411.value;
                __auto_type _mv_412 = (*head);
                switch (_mv_412.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_412.data.sym;
                        {
                            __auto_type name = sym.name;
                            return (string_eq(name, SLOP_STR("if")) || (string_eq(name, SLOP_STR("when")) || string_eq(name, SLOP_STR("cond"))));
                        }
                    }
                    default: {
                        return 0;
                    }
                }
            } else if (!_mv_411.has_value) {
                return 0;
            }
            SLOP_UNREACHABLE();
        }
        default: {
            return 0;
        }
    }
}

slop_string expr_transpile_discarded_expr(context_TranspileContext* ctx, types_SExpr* e) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type c = expr_transpile_expr(ctx, e);
        if (expr_discard_needs_void(e)) {
            return context_ctx_str3(ctx, SLOP_STR("(void)("), c, SLOP_STR(")"));
        } else {
            return c;
        }
    }
}

slop_string expr_transpile_let_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 3) {
            return SLOP_STR("({ (void)0; })");
        } else {
            __auto_type _mv_413 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_413.has_value) {
                __auto_type bindings_expr = _mv_413.value;
                __auto_type _mv_414 = (*bindings_expr);
                switch (_mv_414.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type bindings_lst = _mv_414.data.lst;
                        context_ctx_push_scope(ctx);
                        {
                            __auto_type result = SLOP_STR("({ ");
                            __auto_type bindings_items = bindings_lst.items;
                            __auto_type bindings_len = ((int64_t)((bindings_items).len));
                            __auto_type bi = 0;
                            while (bi < bindings_len) {
                                __auto_type _mv_415 = ({ __auto_type _lst = bindings_items; size_t _idx = (size_t)bi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_415.has_value) {
                                    __auto_type binding = _mv_415.value;
                                    expr_register_let_binding_in_context(ctx, binding);
                                } else if (!_mv_415.has_value) {
                                }
                                bi = (bi + 1);
                            }
                            bi = 0;
                            while (bi < bindings_len) {
                                __auto_type _mv_416 = ({ __auto_type _lst = bindings_items; size_t _idx = (size_t)bi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_416.has_value) {
                                    __auto_type binding = _mv_416.value;
                                    {
                                        __auto_type binding_c = expr_transpile_binding_expr(ctx, binding);
                                        result = context_ctx_str3(ctx, result, binding_c, SLOP_STR(" "));
                                    }
                                } else if (!_mv_416.has_value) {
                                }
                                bi = (bi + 1);
                            }
                            {
                                __auto_type i = 2;
                                while (i < (len - 1)) {
                                    __auto_type _mv_417 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_417.has_value) {
                                        __auto_type body_expr = _mv_417.value;
                                        {
                                            __auto_type body_c = expr_transpile_discarded_expr(ctx, body_expr);
                                            result = context_ctx_str3(ctx, result, body_c, SLOP_STR("; "));
                                        }
                                    } else if (!_mv_417.has_value) {
                                    }
                                    i = (i + 1);
                                }
                                {
                                    __auto_type final_result = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)(len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type last_expr = _mv.value; ({ __auto_type last_c = expr_transpile_expr(ctx, last_expr); context_ctx_str3(ctx, result, last_c, SLOP_STR("; })")); }); }) : (context_ctx_str(ctx, result, SLOP_STR("0; })"))); });
                                    context_ctx_pop_scope(ctx);
                                    return final_result;
                                }
                            }
                        }
                    }
                    default: {
                        return SLOP_STR("({ (void)0; })");
                    }
                }
            } else if (!_mv_413.has_value) {
                return SLOP_STR("({ (void)0; })");
            }
            SLOP_UNREACHABLE();
        }
    }
}

void expr_register_let_binding_in_context(context_TranspileContext* ctx, types_SExpr* binding) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((binding != NULL)), "(!= binding nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_418 = (*binding);
        switch (_mv_418.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_418.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len >= 2) {
                        {
                            __auto_type has_mut = expr_binding_has_mut(items);
                            __auto_type name_idx = ((has_mut) ? 1 : 0);
                            __auto_type has_type = ((has_mut) ? (len >= 4) : (len >= 3));
                            __auto_type type_idx = (name_idx + 1);
                            __auto_type init_idx = ((has_mut) ? ((has_type) ? 3 : 2) : ((has_type) ? 2 : 1));
                            __auto_type _mv_419 = ({ __auto_type _lst = items; size_t _idx = (size_t)name_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_419.has_value) {
                                __auto_type name_expr = _mv_419.value;
                                __auto_type _mv_420 = (*name_expr);
                                switch (_mv_420.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type name_sym = _mv_420.data.sym;
                                        {
                                            __auto_type var_name = name_sym.name;
                                            __auto_type c_name = ctype_to_c_name(arena, var_name);
                                            __auto_type c_type = ((has_type) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type type_expr = _mv.value; context_to_c_type_prefixed(ctx, type_expr); }) : (SLOP_STR("int64_t")); }) : ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)init_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type init_expr = _mv.value; ({ __auto_type _mv = ctype_get_node_resolved_type(init_expr); _mv.has_value ? ({ __auto_type rt = _mv.value; ctype_resolved_type_to_c(arena, rt); }) : (SLOP_STR("int64_t")); }); }) : (SLOP_STR("int64_t")); }));
                                            context_ctx_bind_var(ctx, (context_VarEntry){var_name, c_name, c_type, SLOP_STR(""), 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                        }
                                        break;
                                    }
                                    default: {
                                        break;
                                    }
                                }
                            } else if (!_mv_419.has_value) {
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
    }
}

slop_string expr_transpile_binding_expr(context_TranspileContext* ctx, types_SExpr* binding) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((binding != NULL)), "(!= binding nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_421 = (*binding);
        switch (_mv_421.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_421.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len < 2) {
                        return SLOP_STR("");
                    } else {
                        {
                            __auto_type has_mut = expr_binding_has_mut(items);
                            __auto_type name_idx = ((has_mut) ? 1 : 0);
                            __auto_type _mv_422 = ({ __auto_type _lst = items; size_t _idx = (size_t)name_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_422.has_value) {
                                __auto_type name_expr = _mv_422.value;
                                __auto_type _mv_423 = (*name_expr);
                                switch (_mv_423.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type name_sym = _mv_423.data.sym;
                                        {
                                            __auto_type var_name = ctype_to_c_name(arena, name_sym.name);
                                            __auto_type has_type = ((has_mut) ? (len >= 4) : (len >= 3));
                                            __auto_type type_idx = (name_idx + 1);
                                            __auto_type init_idx = ((has_mut) ? ((has_type) ? 3 : 2) : ((has_type) ? 2 : 1));
                                            if (has_type) {
                                                __auto_type _mv_424 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_424.has_value) {
                                                    __auto_type type_expr = _mv_424.value;
                                                    {
                                                        __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                        __auto_type _mv_425 = ({ __auto_type _lst = items; size_t _idx = (size_t)init_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                        if (_mv_425.has_value) {
                                                            __auto_type init_expr = _mv_425.value;
                                                            {
                                                                __auto_type init_c = expr_transpile_typed_init(ctx, init_expr, c_type);
                                                                return context_ctx_str5(ctx, c_type, SLOP_STR(" "), context_ctx_str3(ctx, var_name, SLOP_STR(" = "), init_c), SLOP_STR(";"), SLOP_STR(""));
                                                            }
                                                        } else if (!_mv_425.has_value) {
                                                            return context_ctx_str5(ctx, c_type, SLOP_STR(" "), var_name, SLOP_STR(" = {0};"), SLOP_STR(""));
                                                        }
                                                        SLOP_UNREACHABLE();
                                                    }
                                                } else if (!_mv_424.has_value) {
                                                    __auto_type _mv_426 = ({ __auto_type _lst = items; size_t _idx = (size_t)init_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_426.has_value) {
                                                        __auto_type init_expr = _mv_426.value;
                                                        {
                                                            __auto_type init_c = expr_transpile_expr(ctx, init_expr);
                                                            return context_ctx_str5(ctx, SLOP_STR("__auto_type "), var_name, SLOP_STR(" = "), init_c, SLOP_STR(";"));
                                                        }
                                                    } else if (!_mv_426.has_value) {
                                                        return context_ctx_str3(ctx, SLOP_STR("__auto_type "), var_name, SLOP_STR(" = 0;"));
                                                    }
                                                    SLOP_UNREACHABLE();
                                                }
                                                SLOP_UNREACHABLE();
                                            } else {
                                                __auto_type _mv_427 = ({ __auto_type _lst = items; size_t _idx = (size_t)init_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_427.has_value) {
                                                    __auto_type init_expr = _mv_427.value;
                                                    {
                                                        __auto_type init_c = expr_transpile_expr(ctx, init_expr);
                                                        return context_ctx_str5(ctx, SLOP_STR("__auto_type "), var_name, SLOP_STR(" = "), init_c, SLOP_STR(";"));
                                                    }
                                                } else if (!_mv_427.has_value) {
                                                    return context_ctx_str3(ctx, SLOP_STR("__auto_type "), var_name, SLOP_STR(" = 0;"));
                                                }
                                                SLOP_UNREACHABLE();
                                            }
                                        }
                                    }
                                    default: {
                                        return SLOP_STR("");
                                    }
                                }
                            } else if (!_mv_422.has_value) {
                                return SLOP_STR("");
                            }
                            SLOP_UNREACHABLE();
                        }
                    }
                }
            }
            default: {
                return SLOP_STR("");
            }
        }
    }
}

uint8_t expr_binding_has_mut(slop_list_types_SExpr_ptr items) {
    if (((int64_t)((items).len)) < 1) {
        return 0;
    } else {
        __auto_type _mv_428 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_428.has_value) {
            __auto_type first = _mv_428.value;
            __auto_type _mv_429 = (*first);
            switch (_mv_429.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_429.data.sym;
                    return string_eq(sym.name, SLOP_STR("mut"));
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_428.has_value) {
            return 0;
        }
        SLOP_UNREACHABLE();
    }
}

slop_string expr_transpile_typed_init(context_TranspileContext* ctx, types_SExpr* init_expr, slop_string target_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((init_expr != NULL)), "(!= init-expr nil)");
    __auto_type _mv_430 = (*init_expr);
    switch (_mv_430.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_430.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return expr_transpile_expr(ctx, init_expr);
                } else {
                    __auto_type _mv_431 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_431.has_value) {
                        __auto_type head = _mv_431.value;
                        __auto_type _mv_432 = (*head);
                        switch (_mv_432.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_432.data.sym;
                                {
                                    __auto_type op = sym.name;
                                    if (string_eq(op, SLOP_STR("some"))) {
                                        if (((int64_t)((items).len)) < 2) {
                                            return expr_transpile_expr(ctx, init_expr);
                                        } else {
                                            __auto_type _mv_433 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_433.has_value) {
                                                __auto_type val_expr = _mv_433.value;
                                                {
                                                    __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                    return context_ctx_str5(ctx, SLOP_STR("("), target_type, SLOP_STR("){.has_value = 1, .value = "), val_c, SLOP_STR("}"));
                                                }
                                            } else if (!_mv_433.has_value) {
                                                return expr_transpile_expr(ctx, init_expr);
                                            }
                                            SLOP_UNREACHABLE();
                                        }
                                    } else if (string_eq(op, SLOP_STR("none"))) {
                                        return context_ctx_str3(ctx, SLOP_STR("("), target_type, SLOP_STR("){.has_value = false}"));
                                    } else {
                                        return expr_transpile_expr(ctx, init_expr);
                                    }
                                }
                            }
                            default: {
                                return expr_transpile_expr(ctx, init_expr);
                            }
                        }
                    } else if (!_mv_431.has_value) {
                        return expr_transpile_expr(ctx, init_expr);
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        default: {
            return expr_transpile_expr(ctx, init_expr);
        }
    }
}

slop_string expr_transpile_while_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if (len < 3) {
            return SLOP_STR("({ (void)0; })");
        } else {
            __auto_type _mv_434 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_434.has_value) {
                __auto_type cond_expr = _mv_434.value;
                {
                    __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                    __auto_type body_str = SLOP_STR("");
                    {
                        __auto_type i = 2;
                        while (i < len) {
                            __auto_type _mv_435 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_435.has_value) {
                                __auto_type body_expr = _mv_435.value;
                                {
                                    __auto_type body_c = expr_transpile_discarded_expr(ctx, body_expr);
                                    body_str = context_ctx_str3(ctx, body_str, body_c, SLOP_STR("; "));
                                }
                            } else if (!_mv_435.has_value) {
                            }
                            i = (i + 1);
                        }
                    }
                    {
                        __auto_type part1 = context_ctx_str3(ctx, SLOP_STR("({ while ("), cond_c, SLOP_STR(") { "));
                        __auto_type part2 = context_ctx_str(ctx, body_str, SLOP_STR("} (void)0; })"));
                        return context_ctx_str(ctx, part1, part2);
                    }
                }
            } else if (!_mv_434.has_value) {
                return SLOP_STR("({ (void)0; })");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_do_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if (len <= 1) {
            return SLOP_STR("({ (void)0; })");
        } else {
            {
                __auto_type result = SLOP_STR("({ ");
                int64_t i = 1;
                while (i < len) {
                    __auto_type _mv_436 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_436.has_value) {
                        __auto_type expr = _mv_436.value;
                        {
                            __auto_type is_last = (i == (len - 1));
                            __auto_type expr_c = (((i == (len - 1))) ? expr_transpile_expr(ctx, expr) : expr_transpile_discarded_expr(ctx, expr));
                            result = context_ctx_str3(ctx, result, expr_c, SLOP_STR("; "));
                        }
                    } else if (!_mv_436.has_value) {
                    }
                    i = (i + 1);
                }
                return context_ctx_str(ctx, result, SLOP_STR("})"));
            }
        }
    }
}

slop_string expr_transpile_when_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if (len < 2) {
            return SLOP_STR("({ (void)0; })");
        } else {
            __auto_type _mv_437 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_437.has_value) {
                __auto_type cond_expr = _mv_437.value;
                {
                    __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                    __auto_type body_c = SLOP_STR("({ ");
                    {
                        __auto_type i = 2;
                        while (i < len) {
                            __auto_type _mv_438 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_438.has_value) {
                                __auto_type body_expr = _mv_438.value;
                                body_c = context_ctx_str3(ctx, body_c, expr_transpile_discarded_expr(ctx, body_expr), SLOP_STR("; "));
                            } else if (!_mv_438.has_value) {
                            }
                            i = (i + 1);
                        }
                    }
                    body_c = context_ctx_str(ctx, body_c, SLOP_STR("0; })"));
                    return context_ctx_str5(ctx, SLOP_STR("(("), cond_c, SLOP_STR(") ? "), body_c, SLOP_STR(" : ({ (void)0; }))"));
                }
            } else if (!_mv_437.has_value) {
                return SLOP_STR("({ (void)0; })");
            }
            SLOP_UNREACHABLE();
        }
    }
}

uint8_t expr_set_is_self_assign(slop_list_types_SExpr_ptr items) {
    if (((int64_t)((items).len)) == 3) {
        __auto_type _mv_439 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_439.has_value) {
            __auto_type target_expr = _mv_439.value;
            __auto_type _mv_440 = (*target_expr);
            switch (_mv_440.tag) {
                case types_SExpr_sym:
                {
                    __auto_type tsym = _mv_440.data.sym;
                    __auto_type _mv_441 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_441.has_value) {
                        __auto_type value_expr = _mv_441.value;
                        __auto_type _mv_442 = (*value_expr);
                        switch (_mv_442.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type vsym = _mv_442.data.sym;
                                return string_eq(tsym.name, vsym.name);
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_441.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_439.has_value) {
            return 0;
        }
        SLOP_UNREACHABLE();
    } else {
        return 0;
    }
}

slop_string expr_transpile_set_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (expr_set_is_self_assign(items)) {
            return SLOP_STR("({ (void)0; })");
        } else {
            if (len < 3) {
                return SLOP_STR("({ (void)0; })");
            } else {
                __auto_type _mv_443 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_443.has_value) {
                    __auto_type target_expr = _mv_443.value;
                    __auto_type _mv_444 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_444.has_value) {
                        __auto_type val_expr = _mv_444.value;
                        {
                            __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                            __auto_type _mv_445 = (*target_expr);
                            switch (_mv_445.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type target_lst = _mv_445.data.lst;
                                    {
                                        __auto_type target_items = target_lst.items;
                                        if (((int64_t)((target_items).len)) < 1) {
                                            return context_ctx_str5(ctx, SLOP_STR("({ "), expr_transpile_expr(ctx, target_expr), SLOP_STR(" = "), val_c, SLOP_STR("; (void)0; })"));
                                        } else {
                                            __auto_type _mv_446 = ({ __auto_type _lst = target_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_446.has_value) {
                                                __auto_type head = _mv_446.value;
                                                __auto_type _mv_447 = (*head);
                                                switch (_mv_447.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type sym = _mv_447.data.sym;
                                                        {
                                                            __auto_type op = sym.name;
                                                            if (string_eq(op, SLOP_STR("@"))) {
                                                                if (((int64_t)((target_items).len)) < 3) {
                                                                    return SLOP_STR("({ (void)0; })");
                                                                } else {
                                                                    __auto_type _mv_448 = ({ __auto_type _lst = target_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                    if (_mv_448.has_value) {
                                                                        __auto_type arr_expr = _mv_448.value;
                                                                        __auto_type _mv_449 = ({ __auto_type _lst = target_items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                        if (_mv_449.has_value) {
                                                                            __auto_type idx_expr = _mv_449.value;
                                                                            {
                                                                                __auto_type arr_c = expr_transpile_expr(ctx, arr_expr);
                                                                                __auto_type idx_c = expr_transpile_expr(ctx, idx_expr);
                                                                                return context_ctx_str(ctx, SLOP_STR("({ "), context_ctx_str(ctx, arr_c, context_ctx_str(ctx, SLOP_STR("["), context_ctx_str(ctx, idx_c, context_ctx_str(ctx, SLOP_STR("] = "), context_ctx_str(ctx, val_c, SLOP_STR("; (void)0; })")))))));
                                                                            }
                                                                        } else if (!_mv_449.has_value) {
                                                                            return SLOP_STR("({ (void)0; })");
                                                                        }
                                                                        SLOP_UNREACHABLE();
                                                                    } else if (!_mv_448.has_value) {
                                                                        return SLOP_STR("({ (void)0; })");
                                                                    }
                                                                    SLOP_UNREACHABLE();
                                                                }
                                                            } else if (string_eq(op, SLOP_STR("."))) {
                                                                {
                                                                    __auto_type target_c = expr_transpile_expr(ctx, target_expr);
                                                                    return context_ctx_str5(ctx, SLOP_STR("({ "), target_c, SLOP_STR(" = "), val_c, SLOP_STR("; (void)0; })"));
                                                                }
                                                            } else {
                                                                {
                                                                    __auto_type target_c = expr_transpile_expr(ctx, target_expr);
                                                                    return context_ctx_str5(ctx, SLOP_STR("({ "), target_c, SLOP_STR(" = "), val_c, SLOP_STR("; (void)0; })"));
                                                                }
                                                            }
                                                        }
                                                    }
                                                    default: {
                                                        {
                                                            __auto_type target_c = expr_transpile_expr(ctx, target_expr);
                                                            return context_ctx_str5(ctx, SLOP_STR("({ "), target_c, SLOP_STR(" = "), val_c, SLOP_STR("; (void)0; })"));
                                                        }
                                                    }
                                                }
                                            } else if (!_mv_446.has_value) {
                                                return SLOP_STR("({ (void)0; })");
                                            }
                                            SLOP_UNREACHABLE();
                                        }
                                    }
                                }
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_445.data.sym;
                                    {
                                        __auto_type var_name = sym.name;
                                        __auto_type target_c = ({ __auto_type _mv = context_ctx_lookup_var(ctx, var_name); _mv.has_value ? ({ __auto_type entry = _mv.value; entry.c_name; }) : (ctype_to_c_name(arena, var_name)); });
                                        return context_ctx_str5(ctx, SLOP_STR("({ "), target_c, SLOP_STR(" = "), val_c, SLOP_STR("; (void)0; })"));
                                    }
                                }
                                default: {
                                    {
                                        __auto_type target_c = expr_transpile_expr(ctx, target_expr);
                                        return context_ctx_str5(ctx, SLOP_STR("({ "), target_c, SLOP_STR(" = "), val_c, SLOP_STR("; (void)0; })"));
                                    }
                                }
                            }
                        }
                    } else if (!_mv_444.has_value) {
                        return SLOP_STR("({ (void)0; })");
                    }
                    SLOP_UNREACHABLE();
                } else if (!_mv_443.has_value) {
                    return SLOP_STR("({ (void)0; })");
                }
                SLOP_UNREACHABLE();
            }
        }
    }
}

slop_string expr_resolve_arena_c_name(context_TranspileContext* ctx, slop_string op, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    __auto_type _mv_450 = context_ctx_lookup_var(ctx, SLOP_STR("arena"));
    if (_mv_450.has_value) {
        __auto_type entry = _mv_450.value;
        return entry.c_name;
    } else if (!_mv_450.has_value) {
        __auto_type _mv_451 = context_ctx_find_arena_var(ctx);
        if (_mv_451.has_value) {
            __auto_type entry = _mv_451.value;
            return entry.c_name;
        } else if (!_mv_451.has_value) {
            context_ctx_add_error_at(ctx, context_ctx_str(ctx, op, SLOP_STR(": no arena in scope")), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("arena");
        }
        SLOP_UNREACHABLE();
    }
    SLOP_UNREACHABLE();
}

uint8_t expr_local_callable_shadows(context_TranspileContext* ctx, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    __auto_type _mv_452 = context_ctx_lookup_var(ctx, name);
    if (_mv_452.has_value) {
        __auto_type entry = _mv_452.value;
        return (entry.is_closure || strlib_starts_with(entry.slop_type, SLOP_STR("(Fn")));
    } else if (!_mv_452.has_value) {
        return 0;
    }
    SLOP_UNREACHABLE();
}

slop_string expr_get_arena_for_list_push_expr(context_TranspileContext* ctx, types_SExpr* list_expr, slop_string list_c) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((list_expr != NULL)), "(!= list-expr nil)");
    __auto_type _mv_453 = context_ctx_lookup_var(ctx, SLOP_STR("arena"));
    if (_mv_453.has_value) {
        __auto_type arena_var = _mv_453.value;
        return arena_var.c_name;
    } else if (!_mv_453.has_value) {
        __auto_type _mv_454 = context_ctx_lookup_var(ctx, SLOP_STR("ctx"));
        if (_mv_454.has_value) {
            __auto_type ctx_var = _mv_454.value;
            return context_ctx_str(ctx, ctx_var.c_name, SLOP_STR("->arena"));
        } else if (!_mv_454.has_value) {
            {
                __auto_type arena_from_field = expr_get_arena_from_field_access(ctx, list_expr);
                if (string_len(arena_from_field) > 0) {
                    return arena_from_field;
                } else {
                    __auto_type _mv_455 = context_ctx_find_arena_var(ctx);
                    if (_mv_455.has_value) {
                        __auto_type arena_entry = _mv_455.value;
                        return arena_entry.c_name;
                    } else if (!_mv_455.has_value) {
                        return SLOP_STR("arena");
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        SLOP_UNREACHABLE();
    }
    SLOP_UNREACHABLE();
}

slop_string expr_get_arena_from_field_access(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_456 = (*expr);
    switch (_mv_456.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_456.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if (len < 3) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_457 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_457.has_value) {
                        __auto_type head_expr = _mv_457.value;
                        __auto_type _mv_458 = (*head_expr);
                        switch (_mv_458.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_458.data.sym;
                                if (string_eq(sym.name, SLOP_STR("."))) {
                                    __auto_type _mv_459 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_459.has_value) {
                                        __auto_type base_expr = _mv_459.value;
                                        return expr_get_arena_from_base(ctx, base_expr);
                                    } else if (!_mv_459.has_value) {
                                        return SLOP_STR("");
                                    }
                                    SLOP_UNREACHABLE();
                                } else {
                                    return SLOP_STR("");
                                }
                            }
                            default: {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_457.has_value) {
                        return SLOP_STR("");
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        default: {
            return SLOP_STR("");
        }
    }
}

slop_string expr_get_arena_from_base(context_TranspileContext* ctx, types_SExpr* base_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((base_expr != NULL)), "(!= base-expr nil)");
    __auto_type _mv_460 = (*base_expr);
    switch (_mv_460.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_460.data.sym;
            {
                __auto_type var_name = sym.name;
                __auto_type _mv_461 = context_ctx_lookup_var(ctx, var_name);
                if (_mv_461.has_value) {
                    __auto_type entry = _mv_461.value;
                    if (entry.is_pointer) {
                        return context_ctx_str(ctx, entry.c_name, SLOP_STR("->arena"));
                    } else {
                        return context_ctx_str(ctx, entry.c_name, SLOP_STR(".arena"));
                    }
                } else if (!_mv_461.has_value) {
                    {
                        __auto_type arena = (*ctx).arena;
                        __auto_type c_name = ctype_to_c_name(arena, var_name);
                        return context_ctx_str(ctx, c_name, SLOP_STR("->arena"));
                    }
                }
                SLOP_UNREACHABLE();
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_460.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 2) {
                    return SLOP_STR("arena");
                } else {
                    __auto_type _mv_462 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_462.has_value) {
                        __auto_type head_expr = _mv_462.value;
                        __auto_type _mv_463 = (*head_expr);
                        switch (_mv_463.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_463.data.sym;
                                if (string_eq(sym.name, SLOP_STR("deref"))) {
                                    __auto_type _mv_464 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_464.has_value) {
                                        __auto_type ptr_expr = _mv_464.value;
                                        {
                                            __auto_type ptr_c = expr_transpile_expr(ctx, ptr_expr);
                                            return context_ctx_str(ctx, ptr_c, SLOP_STR("->arena"));
                                        }
                                    } else if (!_mv_464.has_value) {
                                        return SLOP_STR("arena");
                                    }
                                    SLOP_UNREACHABLE();
                                } else {
                                    return SLOP_STR("arena");
                                }
                            }
                            default: {
                                return SLOP_STR("arena");
                            }
                        }
                    } else if (!_mv_462.has_value) {
                        return SLOP_STR("arena");
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        default: {
            return SLOP_STR("arena");
        }
    }
}

slop_string expr_get_arena_for_list_push(context_TranspileContext* ctx, slop_string list_c) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return SLOP_STR("arena");
}

uint8_t expr_is_ptr_to_ptr_map(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_465 = (*expr);
    switch (_mv_465.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_465.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_466 = context_ctx_lookup_var(ctx, name);
                if (_mv_466.has_value) {
                    __auto_type entry = _mv_466.value;
                    {
                        __auto_type c_type = entry.c_type;
                        return strlib_ends_with(c_type, SLOP_STR("**"));
                    }
                } else if (!_mv_466.has_value) {
                    return 0;
                }
                SLOP_UNREACHABLE();
            }
        }
        default: {
            {
                __auto_type slop_type = expr_resolve_type_alias(ctx, expr_infer_expr_slop_type(ctx, expr));
                return (strlib_starts_with(slop_type, SLOP_STR("(Ptr (Map ")) || strlib_starts_with(slop_type, SLOP_STR("(Ptr (Set ")));
            }
        }
    }
}

slop_string expr_deref_container_c(context_TranspileContext* ctx, slop_string container_c, slop_string slop_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (strlib_starts_with(slop_type, SLOP_STR("(Ptr (Map ")) || strlib_starts_with(slop_type, SLOP_STR("(Ptr (Set "))) {
        return context_ctx_str3(ctx, SLOP_STR("(*"), container_c, SLOP_STR(")"));
    } else {
        return container_c;
    }
}

slop_string expr_resolve_container_c(context_TranspileContext* ctx, types_SExpr* container_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((container_expr != NULL)), "(!= container-expr nil)");
    {
        __auto_type c = expr_transpile_expr(ctx, container_expr);
        if (expr_is_ptr_to_ptr_map(ctx, container_expr)) {
            return context_ctx_str3(ctx, SLOP_STR("(*"), c, SLOP_STR(")"));
        } else {
            return c;
        }
    }
}

slop_string expr_transpile_record_new(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 2) {
            context_ctx_add_error_at(ctx, SLOP_STR("record-new: missing type"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("0");
        } else {
            __auto_type _mv_467 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_467.has_value) {
                __auto_type type_expr = _mv_467.value;
                __auto_type _mv_468 = (*type_expr);
                switch (_mv_468.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type type_sym = _mv_468.data.sym;
                        {
                            __auto_type raw_type_name = type_sym.name;
                            __auto_type type_name = ({ __auto_type _mv = context_ctx_lookup_type(ctx, raw_type_name); _mv.has_value ? ({ __auto_type entry = _mv.value; entry.c_name; }) : (context_ctx_prefix_type(ctx, ctype_to_c_name(arena, raw_type_name))); });
                            return expr_transpile_record_fields(ctx, type_name, items, 2);
                        }
                    }
                    case types_SExpr_lst:
                    {
                        __auto_type type_lst = _mv_468.data.lst;
                        {
                            __auto_type type_items = type_lst.items;
                            if (((int64_t)((type_items).len)) < 1) {
                                context_ctx_add_error_at(ctx, SLOP_STR("record-new: invalid inline type"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                return SLOP_STR("0");
                            } else {
                                __auto_type _mv_469 = ({ __auto_type _lst = type_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_469.has_value) {
                                    __auto_type head = _mv_469.value;
                                    __auto_type _mv_470 = (*head);
                                    switch (_mv_470.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type head_sym = _mv_470.data.sym;
                                            if (string_eq(head_sym.name, SLOP_STR("record"))) {
                                                {
                                                    __auto_type type_name = context_to_c_type_prefixed(ctx, type_expr);
                                                    return expr_transpile_record_fields(ctx, type_name, items, 2);
                                                }
                                            } else {
                                                context_ctx_add_error_at(ctx, SLOP_STR("record-new: expected record keyword"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                                return SLOP_STR("0");
                                            }
                                        }
                                        default: {
                                            context_ctx_add_error_at(ctx, SLOP_STR("record-new: invalid type head"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                            return SLOP_STR("0");
                                        }
                                    }
                                } else if (!_mv_469.has_value) {
                                    context_ctx_add_error_at(ctx, SLOP_STR("record-new: empty type"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                                    return SLOP_STR("0");
                                }
                                SLOP_UNREACHABLE();
                            }
                        }
                    }
                    default: {
                        context_ctx_add_error_at(ctx, SLOP_STR("record-new: invalid type"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                        return SLOP_STR("0");
                    }
                }
            } else if (!_mv_467.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("record-new: missing type"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("0");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_record_fields(context_TranspileContext* ctx, slop_string type_name, slop_list_types_SExpr_ptr items, int64_t start_idx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result = context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, type_name, SLOP_STR("){")));
        int64_t i = start_idx;
        uint8_t first = 1;
        while (i < len) {
            __auto_type _mv_471 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_471.has_value) {
                __auto_type field_expr = _mv_471.value;
                __auto_type _mv_472 = (*field_expr);
                switch (_mv_472.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type field_lst = _mv_472.data.lst;
                        {
                            __auto_type field_items = field_lst.items;
                            if (((int64_t)((field_items).len)) >= 2) {
                                __auto_type _mv_473 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_473.has_value) {
                                    __auto_type name_expr = _mv_473.value;
                                    __auto_type _mv_474 = (*name_expr);
                                    switch (_mv_474.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type name_sym = _mv_474.data.sym;
                                            __auto_type _mv_475 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_475.has_value) {
                                                __auto_type val_expr = _mv_475.value;
                                                {
                                                    __auto_type raw_field_name = name_sym.name;
                                                    __auto_type field_name = ctype_to_c_name(arena, raw_field_name);
                                                    __auto_type field_type_opt = context_ctx_lookup_field_type(ctx, type_name, raw_field_name);
                                                    __auto_type field_val = ({ __auto_type _mv = field_type_opt; _mv.has_value ? ({ __auto_type field_type = _mv.value; expr_transpile_typed_init(ctx, val_expr, field_type); }) : (expr_transpile_expr(ctx, val_expr)); });
                                                    if (first) {
                                                        result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR("."), context_ctx_str(ctx, field_name, context_ctx_str(ctx, SLOP_STR(" = "), field_val))));
                                                    } else {
                                                        result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR(", ."), context_ctx_str(ctx, field_name, context_ctx_str(ctx, SLOP_STR(" = "), field_val))));
                                                    }
                                                    first = 0;
                                                }
                                            } else if (!_mv_475.has_value) {
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_473.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_471.has_value) {
            }
            i = (i + 1);
        }
        return context_ctx_str(ctx, result, SLOP_STR("})"));
    }
}

slop_string expr_build_inline_struct_type(context_TranspileContext* ctx, slop_list_types_SExpr_ptr type_items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((type_items).len));
        __auto_type result = SLOP_STR("struct { ");
        int64_t i = 1;
        while (i < len) {
            __auto_type _mv_476 = ({ __auto_type _lst = type_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_476.has_value) {
                __auto_type field_expr = _mv_476.value;
                __auto_type _mv_477 = (*field_expr);
                switch (_mv_477.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type field_lst = _mv_477.data.lst;
                        {
                            __auto_type field_items = field_lst.items;
                            if (((int64_t)((field_items).len)) >= 2) {
                                __auto_type _mv_478 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_478.has_value) {
                                    __auto_type name_expr = _mv_478.value;
                                    __auto_type _mv_479 = (*name_expr);
                                    switch (_mv_479.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type name_sym = _mv_479.data.sym;
                                            __auto_type _mv_480 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_480.has_value) {
                                                __auto_type type_expr = _mv_480.value;
                                                {
                                                    __auto_type field_name = ctype_to_c_name(arena, name_sym.name);
                                                    __auto_type field_type = context_to_c_type_prefixed(ctx, type_expr);
                                                    result = context_ctx_str(ctx, result, context_ctx_str(ctx, field_type, context_ctx_str(ctx, SLOP_STR(" "), context_ctx_str(ctx, field_name, SLOP_STR("; ")))));
                                                }
                                            } else if (!_mv_480.has_value) {
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_478.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_476.has_value) {
            }
            i = (i + 1);
        }
        return context_ctx_str(ctx, result, SLOP_STR("}"));
    }
}

slop_string expr_transpile_inline_record_fields(context_TranspileContext* ctx, slop_string struct_def, slop_list_types_SExpr_ptr items, int64_t start_idx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result = context_ctx_str(ctx, SLOP_STR("(("), context_ctx_str(ctx, struct_def, SLOP_STR("){")));
        int64_t i = start_idx;
        uint8_t first = 1;
        while (i < len) {
            __auto_type _mv_481 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_481.has_value) {
                __auto_type field_expr = _mv_481.value;
                __auto_type _mv_482 = (*field_expr);
                switch (_mv_482.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type field_lst = _mv_482.data.lst;
                        {
                            __auto_type field_items = field_lst.items;
                            if (((int64_t)((field_items).len)) >= 2) {
                                __auto_type _mv_483 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_483.has_value) {
                                    __auto_type name_expr = _mv_483.value;
                                    __auto_type _mv_484 = (*name_expr);
                                    switch (_mv_484.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type name_sym = _mv_484.data.sym;
                                            __auto_type _mv_485 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_485.has_value) {
                                                __auto_type val_expr = _mv_485.value;
                                                {
                                                    __auto_type field_name = ctype_to_c_name(arena, name_sym.name);
                                                    __auto_type field_val = expr_transpile_expr(ctx, val_expr);
                                                    if (first) {
                                                        result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR("."), context_ctx_str(ctx, field_name, context_ctx_str(ctx, SLOP_STR(" = "), field_val))));
                                                    } else {
                                                        result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR(", ."), context_ctx_str(ctx, field_name, context_ctx_str(ctx, SLOP_STR(" = "), field_val))));
                                                    }
                                                    first = 0;
                                                }
                                            } else if (!_mv_485.has_value) {
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_483.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_481.has_value) {
            }
            i = (i + 1);
        }
        return context_ctx_str(ctx, result, SLOP_STR("})"));
    }
}

slop_string expr_transpile_list_literal(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 2) {
            context_ctx_add_error_at(ctx, SLOP_STR("list: missing type"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("0");
        } else {
            __auto_type _mv_486 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_486.has_value) {
                __auto_type type_expr = _mv_486.value;
                {
                    __auto_type elem_type = context_to_c_type_prefixed(ctx, type_expr);
                    __auto_type elem_count = (len - 2);
                    {
                        __auto_type type_id = ctype_type_to_identifier(arena, elem_type);
                        __auto_type count_str = int_to_string(arena, elem_count);
                        __auto_type elem_codes = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                        __auto_type i = 2;
                        context_ctx_register_list_type(ctx, elem_type, context_ctx_str(ctx, SLOP_STR("slop_list_"), type_id));
                        context_ctx_register_option_type(ctx, elem_type, context_ctx_str(ctx, SLOP_STR("slop_option_"), type_id));
                        while (i < len) {
                            __auto_type _mv_487 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_487.has_value) {
                                __auto_type elem_expr = _mv_487.value;
                                ({ __auto_type _lst_p = &(elem_codes); __auto_type _item = (expr_transpile_expr(ctx, elem_expr)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            } else if (!_mv_487.has_value) {
                            }
                            i = (i + 1);
                        }
                        {
                            __auto_type arena_var = ({ __auto_type _mv = context_ctx_lookup_var(ctx, SLOP_STR("arena")); _mv.has_value ? ({ __auto_type v = _mv.value; (slop_option_context_VarEntry){.has_value = 1, .value = v}; }) : (context_ctx_find_arena_var(ctx)); });
                            __auto_type _mv_488 = arena_var;
                            if (_mv_488.has_value) {
                                __auto_type arena_var = _mv_488.value;
                                {
                                    __auto_type arena_c = arena_var.c_name;
                                    __auto_type list_type = context_ctx_str(ctx, SLOP_STR("slop_list_"), type_id);
                                    __auto_type result = context_ctx_str(ctx, SLOP_STR("({ "), context_ctx_str(ctx, list_type, context_ctx_str(ctx, SLOP_STR(" _ll = ("), context_ctx_str(ctx, list_type, SLOP_STR("){ .data = (")))));
                                    result = context_ctx_str(ctx, result, context_ctx_str(ctx, elem_type, context_ctx_str(ctx, SLOP_STR("*)slop_arena_alloc("), context_ctx_str(ctx, arena_c, context_ctx_str(ctx, SLOP_STR(", "), context_ctx_str(ctx, count_str, context_ctx_str(ctx, SLOP_STR(" * sizeof("), context_ctx_str(ctx, elem_type, SLOP_STR("))")))))))));
                                    result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR(", .len = "), context_ctx_str(ctx, count_str, context_ctx_str(ctx, SLOP_STR(", .cap = "), context_ctx_str(ctx, count_str, SLOP_STR(" };"))))));
                                    i = 0;
                                    while (i < ((int64_t)((elem_codes).len))) {
                                        __auto_type _mv_489 = ({ __auto_type _lst = elem_codes; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_489.has_value) {
                                            __auto_type ec = _mv_489.value;
                                            {
                                                __auto_type idx_str = int_to_string(arena, i);
                                                result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR(" _ll.data["), context_ctx_str(ctx, idx_str, context_ctx_str(ctx, SLOP_STR("] = "), context_ctx_str(ctx, ec, SLOP_STR(";"))))));
                                            }
                                        } else if (!_mv_489.has_value) {
                                        }
                                        i = (i + 1);
                                    }
                                    return context_ctx_str(ctx, result, SLOP_STR(" _ll; })"));
                                }
                            } else if (!_mv_488.has_value) {
                                context_ctx_add_warning(ctx, SLOP_STR("list literal uses stack-allocated compound literal (no arena in scope)"));
                                {
                                    __auto_type result = context_ctx_str(ctx, SLOP_STR("((slop_list_"), context_ctx_str(ctx, type_id, SLOP_STR("){")));
                                    __auto_type data_part = context_ctx_str(ctx, SLOP_STR(".len = "), context_ctx_str(ctx, count_str, context_ctx_str(ctx, SLOP_STR(", .cap = "), context_ctx_str(ctx, count_str, context_ctx_str(ctx, SLOP_STR(", .data = ("), context_ctx_str(ctx, elem_type, SLOP_STR("[]){")))))));
                                    __auto_type first = 1;
                                    i = 0;
                                    while (i < ((int64_t)((elem_codes).len))) {
                                        __auto_type _mv_490 = ({ __auto_type _lst = elem_codes; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_490.has_value) {
                                            __auto_type ec = _mv_490.value;
                                            if (first) {
                                                data_part = context_ctx_str(ctx, data_part, ec);
                                            } else {
                                                data_part = context_ctx_str(ctx, data_part, context_ctx_str(ctx, SLOP_STR(", "), ec));
                                            }
                                            first = 0;
                                        } else if (!_mv_490.has_value) {
                                        }
                                        i = (i + 1);
                                    }
                                    return context_ctx_str(ctx, result, context_ctx_str(ctx, data_part, SLOP_STR("}})")));
                                }
                            }
                            SLOP_UNREACHABLE();
                        }
                    }
                }
            } else if (!_mv_486.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("list: missing type"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("0");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_build_struct_key_info(context_TranspileContext* ctx, slop_string c_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return context_ctx_str(ctx, SLOP_STR("sizeof("), context_ctx_str(ctx, c_name, context_ctx_str(ctx, SLOP_STR("), slop_hash_"), context_ctx_str(ctx, c_name, context_ctx_str(ctx, SLOP_STR(", slop_eq_"), c_name)))));
}

slop_string expr_get_map_key_c_info(context_TranspileContext* ctx, types_SExpr* key_type_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((key_type_expr != NULL)), "(!= key-type-expr nil)");
    __auto_type _mv_491 = (*key_type_expr);
    switch (_mv_491.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_491.data.sym;
            {
                __auto_type name = sym.name;
                if (string_eq(name, SLOP_STR("String"))) {
                    return SLOP_STR("sizeof(slop_string), slop_hash_string, slop_eq_string");
                } else if (string_eq(name, SLOP_STR("Int")) || string_eq(name, SLOP_STR("I64"))) {
                    return SLOP_STR("sizeof(int64_t), slop_hash_int, slop_eq_int");
                } else if (string_eq(name, SLOP_STR("I32"))) {
                    return SLOP_STR("sizeof(int32_t), slop_hash_int, slop_eq_int");
                } else if (string_eq(name, SLOP_STR("Uint")) || string_eq(name, SLOP_STR("U64"))) {
                    return SLOP_STR("sizeof(uint64_t), slop_hash_uint, slop_eq_uint");
                } else if (string_eq(name, SLOP_STR("U32"))) {
                    return SLOP_STR("sizeof(uint32_t), slop_hash_uint, slop_eq_uint");
                } else if (string_eq(name, SLOP_STR("Symbol"))) {
                    return SLOP_STR("sizeof(int64_t), slop_hash_symbol, slop_eq_symbol");
                } else {
                    {
                        __auto_type arena = (*ctx).arena;
                        __auto_type result = expr_get_struct_key_info_by_name(ctx, name);
                        if (string_len(result) > 0) {
                            return result;
                        } else {
                            {
                                __auto_type c_name = ctype_to_c_name(arena, name);
                                context_ctx_register_struct_key_type(ctx, c_name);
                                return expr_build_struct_key_info(ctx, c_name);
                            }
                        }
                    }
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_491.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return SLOP_STR("sizeof(void*), slop_hash_ptr, slop_eq_ptr");
                } else {
                    __auto_type _mv_492 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_492.has_value) {
                        __auto_type head = _mv_492.value;
                        __auto_type _mv_493 = (*head);
                        switch (_mv_493.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_493.data.sym;
                                {
                                    __auto_type head_name = sym.name;
                                    if (string_eq(head_name, SLOP_STR("Ptr"))) {
                                        return SLOP_STR("sizeof(void*), slop_hash_ptr, slop_eq_ptr");
                                    } else {
                                        return SLOP_STR("sizeof(slop_string), slop_hash_string, slop_eq_string");
                                    }
                                }
                            }
                            default: {
                                return SLOP_STR("sizeof(slop_string), slop_hash_string, slop_eq_string");
                            }
                        }
                    } else if (!_mv_492.has_value) {
                        return SLOP_STR("sizeof(void*), slop_hash_ptr, slop_eq_ptr");
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        default: {
            return SLOP_STR("sizeof(slop_string), slop_hash_string, slop_eq_string");
        }
    }
}

slop_string expr_get_struct_key_info_by_name(context_TranspileContext* ctx, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    __auto_type _mv_494 = context_ctx_lookup_type(ctx, name);
    if (_mv_494.has_value) {
        __auto_type type_entry = _mv_494.value;
        {
            __auto_type c_name = type_entry.c_name;
            context_ctx_register_struct_key_type(ctx, c_name);
            return expr_build_struct_key_info(ctx, c_name);
        }
    } else if (!_mv_494.has_value) {
        __auto_type _mv_495 = context_ctx_get_module(ctx);
        if (_mv_495.has_value) {
            __auto_type mod = _mv_495.value;
            {
                __auto_type prefixed = context_ctx_str3(ctx, mod, SLOP_STR("_"), name);
                __auto_type _mv_496 = context_ctx_lookup_type(ctx, prefixed);
                if (_mv_496.has_value) {
                    __auto_type type_entry = _mv_496.value;
                    {
                        __auto_type c_name = type_entry.c_name;
                        context_ctx_register_struct_key_type(ctx, c_name);
                        return expr_build_struct_key_info(ctx, c_name);
                    }
                } else if (!_mv_496.has_value) {
                    return SLOP_STR("");
                }
                SLOP_UNREACHABLE();
            }
        } else if (!_mv_495.has_value) {
            return SLOP_STR("");
        }
        SLOP_UNREACHABLE();
    }
    SLOP_UNREACHABLE();
}

slop_string expr_transpile_map_new(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if (len < 3) {
            if (len < 2) {
                context_ctx_add_error_at(ctx, SLOP_STR("map-new: missing arena"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("NULL");
            } else {
                __auto_type _mv_497 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_497.has_value) {
                    __auto_type arena_expr = _mv_497.value;
                    {
                        __auto_type arena_c = expr_transpile_expr(ctx, arena_expr);
                        return context_ctx_str(ctx, SLOP_STR("slop_map_new_ptr("), context_ctx_str(ctx, arena_c, SLOP_STR(", 16, sizeof(slop_string), slop_hash_string, slop_eq_string)")));
                    }
                } else if (!_mv_497.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("map-new: missing arena"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("NULL");
                }
                SLOP_UNREACHABLE();
            }
        } else {
            __auto_type _mv_498 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_498.has_value) {
                __auto_type arena_expr = _mv_498.value;
                __auto_type _mv_499 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_499.has_value) {
                    __auto_type key_type_expr = _mv_499.value;
                    {
                        __auto_type arena_c = expr_transpile_expr(ctx, arena_expr);
                        __auto_type key_info = expr_get_map_key_c_info(ctx, key_type_expr);
                        return context_ctx_str(ctx, SLOP_STR("slop_map_new_ptr("), context_ctx_str(ctx, arena_c, context_ctx_str(ctx, SLOP_STR(", 16, "), context_ctx_str(ctx, key_info, SLOP_STR(")")))));
                    }
                } else if (!_mv_499.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("map-new: missing KeyType"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("NULL");
                }
                SLOP_UNREACHABLE();
            } else if (!_mv_498.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("map-new: missing arena"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("NULL");
            }
            SLOP_UNREACHABLE();
        }
    }
}

uint8_t expr_is_c_primitive_type(slop_string t) {
    if (string_eq(t, SLOP_STR("int64_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("int32_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("int16_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("int8_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("uint64_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("uint32_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("uint16_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("uint8_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("double"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("float"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("bool"))) {
        return 1;
    } else {
        return 0;
    }
}

slop_string expr_map_key_c_type(context_TranspileContext* ctx, types_SExpr* key_expr, types_SExpr* container_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((key_expr != NULL)), "(!= key-expr nil)");
    {
        __auto_type container_key_type = (((container_expr != NULL)) ? ({ __auto_type map_type = expr_infer_map_key_c_type(ctx, container_expr); (((string_len(map_type) > 0)) ? map_type : expr_infer_set_elem_c_type(ctx, container_expr)); }) : SLOP_STR(""));
        if (string_len(container_key_type) > 0) {
            return container_key_type;
        } else {
            return expr_infer_expr_c_type(ctx, key_expr);
        }
    }
}

slop_string expr_wrap_map_key_as_ptr(context_TranspileContext* ctx, slop_string key_c, types_SExpr* key_expr, types_SExpr* container_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((key_expr != NULL)), "(!= key-expr nil)");
    {
        __auto_type key_type = expr_map_key_c_type(ctx, key_expr, container_expr);
        if (string_eq(key_type, SLOP_STR("slop_string"))) {
            return context_ctx_str(ctx, SLOP_STR("&("), context_ctx_str(ctx, key_c, SLOP_STR(")")));
        } else if (context_ends_with_star(key_type)) {
            return context_ctx_str(ctx, SLOP_STR("&(void*){"), context_ctx_str(ctx, key_c, SLOP_STR("}")));
        } else if (expr_is_c_primitive_type(key_type)) {
            return context_ctx_str(ctx, SLOP_STR("&("), context_ctx_str(ctx, key_type, context_ctx_str(ctx, SLOP_STR("){"), context_ctx_str(ctx, key_c, SLOP_STR("}")))));
        } else {
            return context_ctx_str(ctx, SLOP_STR("&("), context_ctx_str(ctx, key_c, SLOP_STR(")")));
        }
    }
}

uint8_t expr_key_expr_is_addressable(types_SExpr* key_expr) {
    SLOP_PRE(((key_expr != NULL)), "(!= key-expr nil)");
    __auto_type _mv_500 = (*key_expr);
    switch (_mv_500.tag) {
        case types_SExpr_sym:
        {
            __auto_type _ = _mv_500.data.sym;
            return 1;
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_500.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_501 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_501.has_value) {
                        __auto_type head = _mv_501.value;
                        __auto_type _mv_502 = (*head);
                        switch (_mv_502.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type head_sym = _mv_502.data.sym;
                                {
                                    __auto_type op = head_sym.name;
                                    return (string_eq(op, SLOP_STR(".")) || (string_eq(op, SLOP_STR("deref")) || string_eq(op, SLOP_STR("@"))));
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_501.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        default: {
            return 0;
        }
    }
}

slop_string expr_with_map_key(context_TranspileContext* ctx, slop_string key_c, types_SExpr* key_expr, types_SExpr* container_expr, slop_string prefix, slop_string suffix) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((key_expr != NULL)), "(!= key-expr nil)");
    {
        __auto_type temp = context_ctx_gensym(ctx, SLOP_STR("_key"));
        {
            __auto_type decl = expr_map_key_temp_decl(ctx, key_c, key_expr, container_expr, temp);
            __auto_type key_ptr = expr_map_key_ptr(ctx, key_c, key_expr, container_expr, temp);
            if (string_eq(decl, SLOP_STR(""))) {
                return context_ctx_str3(ctx, prefix, key_ptr, suffix);
            } else {
                return context_ctx_str(ctx, context_ctx_str3(ctx, SLOP_STR("({ "), decl, prefix), context_ctx_str3(ctx, key_ptr, suffix, SLOP_STR("; })")));
            }
        }
    }
}

uint8_t expr_map_key_needs_temp(context_TranspileContext* ctx, types_SExpr* key_expr, types_SExpr* container_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((key_expr != NULL)), "(!= key-expr nil)");
    {
        __auto_type key_type = expr_map_key_c_type(ctx, key_expr, container_expr);
        return (!(string_eq(key_type, SLOP_STR("slop_string"))) && (!(context_ends_with_star(key_type)) && (!(expr_is_c_primitive_type(key_type)) && !(expr_key_expr_is_addressable(key_expr)))));
    }
}

slop_string expr_map_key_temp_decl(context_TranspileContext* ctx, slop_string key_c, types_SExpr* key_expr, types_SExpr* container_expr, slop_string temp) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((key_expr != NULL)), "(!= key-expr nil)");
    if (expr_map_key_needs_temp(ctx, key_expr, container_expr)) {
        return context_ctx_str5(ctx, expr_map_key_c_type(ctx, key_expr, container_expr), SLOP_STR(" "), temp, SLOP_STR(" = ("), context_ctx_str(ctx, key_c, SLOP_STR("); ")));
    } else {
        return SLOP_STR("");
    }
}

slop_string expr_map_key_ptr(context_TranspileContext* ctx, slop_string key_c, types_SExpr* key_expr, types_SExpr* container_expr, slop_string temp) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((key_expr != NULL)), "(!= key-expr nil)");
    if (expr_map_key_needs_temp(ctx, key_expr, container_expr)) {
        return context_ctx_str(ctx, SLOP_STR("&"), temp);
    } else {
        return expr_wrap_map_key_as_ptr(ctx, key_c, key_expr, container_expr);
    }
}

slop_string expr_map_put_value_decl_type(context_TranspileContext* ctx, types_SExpr* map_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((map_expr != NULL)), "(!= map-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type option_type = expr_infer_map_value_option_type(ctx, map_expr);
        __auto_type value_slop_type = expr_extract_map_value_from_inferred(ctx, map_expr);
        if ((string_len(option_type) == 0) || (string_len(value_slop_type) == 0)) {
            return SLOP_STR("__auto_type");
        } else {
            {
                __auto_type read_c_type = expr_option_type_to_value_c_type(arena, option_type);
                __auto_type foreach_c_type = expr_slop_value_type_to_c_type(ctx, value_slop_type);
                if (expr_is_c_primitive_type(read_c_type) && string_eq(read_c_type, foreach_c_type)) {
                    return read_c_type;
                } else {
                    return SLOP_STR("__auto_type");
                }
            }
        }
    }
}

slop_string expr_transpile_map_put(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if (len < 4) {
            context_ctx_add_error_at(ctx, SLOP_STR("map-put: needs map, key, val"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("0");
        } else {
            __auto_type _mv_503 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_503.has_value) {
                __auto_type map_expr = _mv_503.value;
                __auto_type _mv_504 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_504.has_value) {
                    __auto_type key_expr = _mv_504.value;
                    __auto_type _mv_505 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_505.has_value) {
                        __auto_type val_expr = _mv_505.value;
                        {
                            __auto_type map_c = expr_resolve_container_c(ctx, map_expr);
                            __auto_type key_c = expr_transpile_expr(ctx, key_expr);
                            __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                            __auto_type key_temp = context_ctx_gensym(ctx, SLOP_STR("_key"));
                            __auto_type key_decl = expr_map_key_temp_decl(ctx, key_c, key_expr, map_expr, key_temp);
                            __auto_type key_ptr = expr_map_key_ptr(ctx, key_c, key_expr, map_expr, key_temp);
                            __auto_type val_decl_type = expr_map_put_value_decl_type(ctx, map_expr);
                            __auto_type arena_c = expr_resolve_arena_c_name(ctx, SLOP_STR("map-put"), items);
                            {
                                __auto_type s1 = context_ctx_str4(ctx, context_ctx_str(ctx, SLOP_STR("({ "), key_decl), val_decl_type, SLOP_STR(" _val = "), val_c);
                                __auto_type s2 = context_ctx_str(ctx, s1, context_ctx_str5(ctx, SLOP_STR("; void* _vptr = slop_arena_alloc("), arena_c, SLOP_STR(", sizeof(_val)); memcpy(_vptr, &_val, sizeof(_val)); slop_map_put("), arena_c, SLOP_STR(", ")));
                                __auto_type s3 = context_ctx_str(ctx, s2, map_c);
                                __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR(", "));
                                __auto_type s5 = context_ctx_str(ctx, s4, key_ptr);
                                __auto_type s6 = context_ctx_str(ctx, s5, SLOP_STR(", _vptr); })"));
                                return s6;
                            }
                        }
                    } else if (!_mv_505.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("map-put: missing val"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                        return SLOP_STR("0");
                    }
                    SLOP_UNREACHABLE();
                } else if (!_mv_504.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("map-put: missing key"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("0");
                }
                SLOP_UNREACHABLE();
            } else if (!_mv_503.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("map-put: missing map"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("0");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_map_get(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type arena = (*ctx).arena;
        if (len < 3) {
            context_ctx_add_error_at(ctx, SLOP_STR("map-get: needs map, key"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("NULL");
        } else {
            __auto_type _mv_506 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_506.has_value) {
                __auto_type map_expr = _mv_506.value;
                __auto_type _mv_507 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_507.has_value) {
                    __auto_type key_expr = _mv_507.value;
                    {
                        __auto_type map_c = expr_resolve_container_c(ctx, map_expr);
                        __auto_type key_c = expr_transpile_expr(ctx, key_expr);
                        __auto_type key_temp = context_ctx_gensym(ctx, SLOP_STR("_key"));
                        __auto_type key_decl = expr_map_key_temp_decl(ctx, key_c, key_expr, map_expr, key_temp);
                        __auto_type key_ptr = expr_map_key_ptr(ctx, key_c, key_expr, map_expr, key_temp);
                        __auto_type option_type = expr_infer_map_value_option_type(ctx, map_expr);
                        if (string_len(option_type) > 0) {
                            {
                                __auto_type inner_type_name = expr_substring_after_prefix(arena, option_type, SLOP_STR("slop_option_"));
                                __auto_type value_c_type = expr_option_type_to_value_c_type(arena, option_type);
                                context_ctx_register_option_type(ctx, value_c_type, option_type);
                                return context_ctx_str(ctx, context_ctx_str3(ctx, SLOP_STR("({ "), key_decl, SLOP_STR("void* _ptr = slop_map_get(")), context_ctx_str(ctx, map_c, context_ctx_str(ctx, SLOP_STR(", "), context_ctx_str(ctx, key_ptr, context_ctx_str(ctx, SLOP_STR("); _ptr ? ("), context_ctx_str(ctx, option_type, context_ctx_str(ctx, SLOP_STR("){ .has_value = true, .value = *("), context_ctx_str(ctx, value_c_type, context_ctx_str(ctx, SLOP_STR("*)_ptr } : ("), context_ctx_str(ctx, option_type, SLOP_STR("){ .has_value = false }; })")))))))))));
                            }
                        } else {
                            return context_ctx_str(ctx, context_ctx_str3(ctx, SLOP_STR("({ "), key_decl, SLOP_STR("void* _ptr = slop_map_get(")), context_ctx_str(ctx, map_c, context_ctx_str(ctx, SLOP_STR(", "), context_ctx_str(ctx, key_ptr, SLOP_STR("); struct { bool has_value; void* value; } _r; if (_ptr) { _r.has_value = true; _r.value = _ptr; } else { _r.has_value = false; } _r; })")))));
                        }
                    }
                } else if (!_mv_507.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("map-get: missing key"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("NULL");
                }
                SLOP_UNREACHABLE();
            } else if (!_mv_506.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("map-get: missing map"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("NULL");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_map_has(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if (len < 3) {
            context_ctx_add_error_at(ctx, SLOP_STR("map-has: needs map, key"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("false");
        } else {
            __auto_type _mv_508 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_508.has_value) {
                __auto_type map_expr = _mv_508.value;
                __auto_type _mv_509 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_509.has_value) {
                    __auto_type key_expr = _mv_509.value;
                    {
                        __auto_type map_c = expr_resolve_container_c(ctx, map_expr);
                        __auto_type key_c = expr_transpile_expr(ctx, key_expr);
                        __auto_type prefix = context_ctx_str3(ctx, SLOP_STR("(slop_map_get("), map_c, SLOP_STR(", "));
                        return expr_with_map_key(ctx, key_c, key_expr, map_expr, prefix, SLOP_STR(") != NULL)"));
                    }
                } else if (!_mv_509.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("map-has: missing key"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("false");
                }
                SLOP_UNREACHABLE();
            } else if (!_mv_508.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("map-has: missing map"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("false");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_map_remove(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if (len < 3) {
            context_ctx_add_error_at(ctx, SLOP_STR("map-remove: needs map, key"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("0");
        } else {
            __auto_type _mv_510 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_510.has_value) {
                __auto_type map_expr = _mv_510.value;
                __auto_type _mv_511 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_511.has_value) {
                    __auto_type key_expr = _mv_511.value;
                    {
                        __auto_type map_c = expr_resolve_container_c(ctx, map_expr);
                        __auto_type key_c = expr_transpile_expr(ctx, key_expr);
                        __auto_type prefix = context_ctx_str3(ctx, SLOP_STR("slop_map_remove("), map_c, SLOP_STR(", "));
                        return expr_with_map_key(ctx, key_c, key_expr, map_expr, prefix, SLOP_STR(")"));
                    }
                } else if (!_mv_511.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("map-remove: missing key"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("0");
                }
                SLOP_UNREACHABLE();
            } else if (!_mv_510.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("map-remove: missing map"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("0");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_map_keys(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type arena = (*ctx).arena;
        if (len < 2) {
            context_ctx_add_error_at(ctx, SLOP_STR("map-keys: needs map"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("NULL");
        } else {
            __auto_type _mv_512 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_512.has_value) {
                __auto_type map_expr = _mv_512.value;
                {
                    __auto_type map_c = expr_resolve_container_c(ctx, map_expr);
                    __auto_type key_c_type = expr_infer_map_key_c_type(ctx, map_expr);
                    __auto_type arena_c = expr_resolve_arena_c_name(ctx, SLOP_STR("map-keys"), items);
                    if (string_eq(key_c_type, SLOP_STR("slop_string"))) {
                        return context_ctx_str(ctx, context_ctx_str3(ctx, SLOP_STR("slop_map_keys("), arena_c, SLOP_STR(", ")), context_ctx_str(ctx, map_c, SLOP_STR(")")));
                    } else if (string_len(key_c_type) == 0) {
                        context_ctx_add_error_at(ctx, SLOP_STR("map-keys: cannot infer key type"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                        return SLOP_STR("NULL");
                    } else {
                        {
                            __auto_type key_id = ctype_type_to_identifier(arena, key_c_type);
                            __auto_type list_type = context_ctx_str(ctx, SLOP_STR("slop_list_"), ctype_type_to_identifier(arena, key_c_type));
                            context_ctx_register_list_type(ctx, key_c_type, list_type);
                            context_ctx_register_option_type(ctx, key_c_type, context_ctx_str(ctx, SLOP_STR("slop_option_"), key_id));
                            return context_ctx_str(ctx, context_ctx_str3(ctx, SLOP_STR("({ slop_set_elements_result _r = slop_set_elements_raw("), arena_c, SLOP_STR(", ")), context_ctx_str(ctx, map_c, context_ctx_str(ctx, SLOP_STR("); ("), context_ctx_str(ctx, list_type, context_ctx_str(ctx, SLOP_STR("){.data = ("), context_ctx_str(ctx, key_c_type, context_ctx_str(ctx, SLOP_STR("*)_r.data, .len = _r.len, .cap = _r.cap}; })"), SLOP_STR(""))))))));
                        }
                    }
                }
            } else if (!_mv_512.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("map-keys: missing map"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("NULL");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_set_new(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if (len < 3) {
            context_ctx_add_error_at(ctx, SLOP_STR("set-new: needs arena and ElementType"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("NULL");
        } else {
            __auto_type _mv_513 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_513.has_value) {
                __auto_type arena_expr = _mv_513.value;
                __auto_type _mv_514 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_514.has_value) {
                    __auto_type elem_type_expr = _mv_514.value;
                    {
                        __auto_type arena_c = expr_transpile_expr(ctx, arena_expr);
                        __auto_type elem_info = expr_get_map_key_c_info(ctx, elem_type_expr);
                        return context_ctx_str(ctx, SLOP_STR("slop_map_new_ptr("), context_ctx_str(ctx, arena_c, context_ctx_str(ctx, SLOP_STR(", 16, "), context_ctx_str(ctx, elem_info, SLOP_STR(")")))));
                    }
                } else if (!_mv_514.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("set-new: missing ElementType"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("NULL");
                }
                SLOP_UNREACHABLE();
            } else if (!_mv_513.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("set-new: missing arena"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("NULL");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_set_put(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if (len < 3) {
            context_ctx_add_error_at(ctx, SLOP_STR("set-put: needs set, element"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("0");
        } else {
            __auto_type _mv_515 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_515.has_value) {
                __auto_type set_expr = _mv_515.value;
                __auto_type _mv_516 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_516.has_value) {
                    __auto_type elem_expr = _mv_516.value;
                    {
                        __auto_type set_c = expr_resolve_container_c(ctx, set_expr);
                        __auto_type elem_c = expr_transpile_expr(ctx, elem_expr);
                        __auto_type elem_temp = context_ctx_gensym(ctx, SLOP_STR("_key"));
                        __auto_type elem_decl = expr_map_key_temp_decl(ctx, elem_c, elem_expr, set_expr, elem_temp);
                        __auto_type elem_ptr = expr_map_key_ptr(ctx, elem_c, elem_expr, set_expr, elem_temp);
                        __auto_type arena_c = expr_resolve_arena_c_name(ctx, SLOP_STR("set-put"), items);
                        return context_ctx_str(ctx, context_ctx_str3(ctx, context_ctx_str3(ctx, SLOP_STR("({ "), elem_decl, SLOP_STR("uint8_t _dummy = 1; slop_map_put(")), arena_c, SLOP_STR(", ")), context_ctx_str(ctx, set_c, context_ctx_str(ctx, SLOP_STR(", "), context_ctx_str(ctx, elem_ptr, SLOP_STR(", &_dummy); })")))));
                    }
                } else if (!_mv_516.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("set-put: missing element"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("0");
                }
                SLOP_UNREACHABLE();
            } else if (!_mv_515.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("set-put: missing set"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("0");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_set_has(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if (len < 3) {
            context_ctx_add_error_at(ctx, SLOP_STR("set-has: needs set, element"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("false");
        } else {
            __auto_type _mv_517 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_517.has_value) {
                __auto_type set_expr = _mv_517.value;
                __auto_type _mv_518 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_518.has_value) {
                    __auto_type elem_expr = _mv_518.value;
                    {
                        __auto_type set_c = expr_resolve_container_c(ctx, set_expr);
                        __auto_type elem_c = expr_transpile_expr(ctx, elem_expr);
                        __auto_type prefix = context_ctx_str3(ctx, SLOP_STR("(slop_map_get("), set_c, SLOP_STR(", "));
                        return expr_with_map_key(ctx, elem_c, elem_expr, set_expr, prefix, SLOP_STR(") != NULL)"));
                    }
                } else if (!_mv_518.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("set-has: missing element"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("false");
                }
                SLOP_UNREACHABLE();
            } else if (!_mv_517.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("set-has: missing set"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("false");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_set_remove(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if (len < 3) {
            context_ctx_add_error_at(ctx, SLOP_STR("set-remove: needs set, element"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("0");
        } else {
            __auto_type _mv_519 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_519.has_value) {
                __auto_type set_expr = _mv_519.value;
                __auto_type _mv_520 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_520.has_value) {
                    __auto_type elem_expr = _mv_520.value;
                    {
                        __auto_type set_c = expr_resolve_container_c(ctx, set_expr);
                        __auto_type elem_c = expr_transpile_expr(ctx, elem_expr);
                        __auto_type prefix = context_ctx_str3(ctx, SLOP_STR("slop_map_remove("), set_c, SLOP_STR(", "));
                        return expr_with_map_key(ctx, elem_c, elem_expr, set_expr, prefix, SLOP_STR(")"));
                    }
                } else if (!_mv_520.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("set-remove: missing element"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("0");
                }
                SLOP_UNREACHABLE();
            } else if (!_mv_519.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("set-remove: missing set"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("0");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_set_elements(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type arena = (*ctx).arena;
        if (len < 2) {
            context_ctx_add_error_at(ctx, SLOP_STR("set-elements: needs set"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("NULL");
        } else {
            __auto_type _mv_521 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_521.has_value) {
                __auto_type set_expr = _mv_521.value;
                {
                    __auto_type set_c = expr_resolve_container_c(ctx, set_expr);
                    __auto_type elem_c_type = expr_infer_set_elem_c_type(ctx, set_expr);
                    __auto_type arena_c = expr_resolve_arena_c_name(ctx, SLOP_STR("set-elements"), items);
                    if (string_eq(elem_c_type, SLOP_STR("slop_string"))) {
                        return context_ctx_str(ctx, context_ctx_str3(ctx, SLOP_STR("slop_map_keys("), arena_c, SLOP_STR(", ")), context_ctx_str(ctx, set_c, SLOP_STR(")")));
                    } else if (string_len(elem_c_type) == 0) {
                        context_ctx_add_error_at(ctx, SLOP_STR("set-elements: cannot infer element type"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                        return SLOP_STR("NULL");
                    } else {
                        {
                            __auto_type elem_id = ctype_type_to_identifier(arena, elem_c_type);
                            __auto_type list_type = context_ctx_str(ctx, SLOP_STR("slop_list_"), ctype_type_to_identifier(arena, elem_c_type));
                            context_ctx_register_list_type(ctx, elem_c_type, list_type);
                            context_ctx_register_option_type(ctx, elem_c_type, context_ctx_str(ctx, SLOP_STR("slop_option_"), elem_id));
                            return context_ctx_str(ctx, context_ctx_str3(ctx, SLOP_STR("({ slop_set_elements_result _r = slop_set_elements_raw("), arena_c, SLOP_STR(", ")), context_ctx_str(ctx, set_c, context_ctx_str(ctx, SLOP_STR("); ("), context_ctx_str(ctx, list_type, context_ctx_str(ctx, SLOP_STR("){.data = ("), context_ctx_str(ctx, elem_c_type, context_ctx_str(ctx, SLOP_STR("*)_r.data, .len = _r.len, .cap = _r.cap}; })"), SLOP_STR(""))))))));
                        }
                    }
                }
            } else if (!_mv_521.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("set-elements: missing set"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("NULL");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_set_literal(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 2) {
            context_ctx_add_error_at(ctx, SLOP_STR("set: needs at least Type"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("NULL");
        } else {
            __auto_type _mv_522 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_522.has_value) {
                __auto_type type_expr = _mv_522.value;
                {
                    __auto_type elem_info = expr_get_map_key_c_info(ctx, type_expr);
                    __auto_type arena_c = expr_resolve_arena_c_name(ctx, SLOP_STR("set"), items);
                    __auto_type num_elems = (len - 2);
                    __auto_type init_cap = (((num_elems > 16)) ? num_elems : 16);
                    __auto_type result = context_ctx_str(ctx, context_ctx_str3(ctx, SLOP_STR("({ slop_map* _s = slop_map_new_ptr("), arena_c, SLOP_STR(", ")), context_ctx_str(ctx, int_to_string(arena, init_cap), context_ctx_str(ctx, SLOP_STR(", "), context_ctx_str(ctx, elem_info, SLOP_STR("); ")))));
                    {
                        __auto_type i = 2;
                        while (i < len) {
                            __auto_type _mv_523 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_523.has_value) {
                                __auto_type elem_expr = _mv_523.value;
                                {
                                    __auto_type elem_c = expr_transpile_expr(ctx, elem_expr);
                                    __auto_type elem_temp = context_ctx_gensym(ctx, SLOP_STR("_key"));
                                    {
                                        __auto_type elem_decl = expr_map_key_temp_decl(ctx, elem_c, elem_expr, NULL, elem_temp);
                                        __auto_type elem_ptr = expr_map_key_ptr(ctx, elem_c, elem_expr, NULL, elem_temp);
                                        result = context_ctx_str(ctx, result, context_ctx_str(ctx, context_ctx_str3(ctx, elem_decl, context_ctx_str3(ctx, SLOP_STR("slop_map_put("), arena_c, SLOP_STR(", _s, ")), SLOP_STR("")), context_ctx_str(ctx, elem_ptr, SLOP_STR(", &(uint8_t){1}); "))));
                                    }
                                }
                            } else if (!_mv_523.has_value) {
                            }
                            i = (i + 1);
                        }
                    }
                    return context_ctx_str(ctx, result, SLOP_STR("_s; })"));
                }
            } else if (!_mv_522.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("set: missing type"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("NULL");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_for_as_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 2) {
            return SLOP_STR("({ /* for: need binding */ 0; })");
        } else {
            __auto_type _mv_524 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_524.has_value) {
                __auto_type binding_expr = _mv_524.value;
                __auto_type _mv_525 = (*binding_expr);
                switch (_mv_525.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type binding_lst = _mv_525.data.lst;
                        {
                            __auto_type binding_items = binding_lst.items;
                            __auto_type binding_len = ((int64_t)((binding_items).len));
                            if (binding_len < 3) {
                                return SLOP_STR("({ /* for: binding needs (var start end) */ 0; })");
                            } else {
                                __auto_type _mv_526 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_526.has_value) {
                                    __auto_type var_expr = _mv_526.value;
                                    __auto_type _mv_527 = (*var_expr);
                                    switch (_mv_527.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type var_sym = _mv_527.data.sym;
                                            {
                                                __auto_type var_name = ctype_to_c_name(arena, var_sym.name);
                                                __auto_type _mv_528 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_528.has_value) {
                                                    __auto_type start_expr = _mv_528.value;
                                                    __auto_type _mv_529 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_529.has_value) {
                                                        __auto_type end_expr = _mv_529.value;
                                                        {
                                                            __auto_type start_c = expr_transpile_expr(ctx, start_expr);
                                                            __auto_type end_c = expr_transpile_expr(ctx, end_expr);
                                                            __auto_type result = context_ctx_str5(ctx, SLOP_STR("({ for (int64_t "), var_name, SLOP_STR(" = "), start_c, context_ctx_str5(ctx, SLOP_STR("; "), var_name, SLOP_STR(" < "), end_c, context_ctx_str3(ctx, SLOP_STR("; "), var_name, SLOP_STR("++) { "))));
                                                            context_ctx_push_scope(ctx);
                                                            context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, SLOP_STR("int64_t"), SLOP_STR(""), 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                                            {
                                                                __auto_type i = 2;
                                                                while (i < len) {
                                                                    __auto_type _mv_530 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                    if (_mv_530.has_value) {
                                                                        __auto_type body_expr = _mv_530.value;
                                                                        {
                                                                            __auto_type body_c = expr_transpile_expr(ctx, body_expr);
                                                                            result = context_ctx_str3(ctx, result, body_c, SLOP_STR("; "));
                                                                        }
                                                                    } else if (!_mv_530.has_value) {
                                                                    }
                                                                    i = (i + 1);
                                                                }
                                                            }
                                                            context_ctx_pop_scope(ctx);
                                                            return context_ctx_str(ctx, result, SLOP_STR("} (void)0; })"));
                                                        }
                                                    } else if (!_mv_529.has_value) {
                                                        return SLOP_STR("({ /* for: missing end */ 0; })");
                                                    }
                                                    SLOP_UNREACHABLE();
                                                } else if (!_mv_528.has_value) {
                                                    return SLOP_STR("({ /* for: missing start */ 0; })");
                                                }
                                                SLOP_UNREACHABLE();
                                            }
                                        }
                                        default: {
                                            return SLOP_STR("({ /* for: var must be symbol */ 0; })");
                                        }
                                    }
                                } else if (!_mv_526.has_value) {
                                    return SLOP_STR("({ /* for: missing var */ 0; })");
                                }
                                SLOP_UNREACHABLE();
                            }
                        }
                    }
                    default: {
                        return SLOP_STR("({ /* for: binding must be list */ 0; })");
                    }
                }
            } else if (!_mv_524.has_value) {
                return SLOP_STR("({ /* for: missing binding */ 0; })");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_for_each_as_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 2) {
            return SLOP_STR("({ /* for-each: need binding */ 0; })");
        } else {
            __auto_type _mv_531 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_531.has_value) {
                __auto_type binding_expr = _mv_531.value;
                __auto_type _mv_532 = (*binding_expr);
                switch (_mv_532.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type binding_lst = _mv_532.data.lst;
                        {
                            __auto_type binding_items = binding_lst.items;
                            __auto_type binding_len = ((int64_t)((binding_items).len));
                            if (binding_len < 2) {
                                return SLOP_STR("({ /* for-each: binding needs (var coll) */ 0; })");
                            } else {
                                __auto_type _mv_533 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_533.has_value) {
                                    __auto_type first_elem = _mv_533.value;
                                    __auto_type _mv_534 = (*first_elem);
                                    switch (_mv_534.tag) {
                                        case types_SExpr_lst:
                                        {
                                            __auto_type _ = _mv_534.data.lst;
                                            return expr_transpile_for_each_map_kv_as_expr(ctx, binding_items, items, len);
                                        }
                                        case types_SExpr_sym:
                                        {
                                            __auto_type var_sym = _mv_534.data.sym;
                                            {
                                                __auto_type var_name = ctype_to_c_name(arena, var_sym.name);
                                                __auto_type _mv_535 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_535.has_value) {
                                                    __auto_type coll_expr = _mv_535.value;
                                                    {
                                                        __auto_type coll_slop_type = expr_infer_expr_slop_type(ctx, coll_expr);
                                                        __auto_type resolved_type = expr_resolve_type_alias(ctx, coll_slop_type);
                                                        if (expr_is_set_type(resolved_type)) {
                                                            return expr_transpile_for_each_set_as_expr(ctx, var_name, var_sym, coll_expr, resolved_type, items, len);
                                                        } else if (expr_is_map_type(resolved_type)) {
                                                            return expr_transpile_for_each_map_keys_as_expr(ctx, var_name, var_sym, coll_expr, resolved_type, items, len);
                                                        } else {
                                                            return expr_transpile_for_each_list_as_expr(ctx, var_name, var_sym, coll_expr, items, len);
                                                        }
                                                    }
                                                } else if (!_mv_535.has_value) {
                                                    return SLOP_STR("({ /* for-each: missing collection */ 0; })");
                                                }
                                                SLOP_UNREACHABLE();
                                            }
                                        }
                                        default: {
                                            return SLOP_STR("({ /* for-each: var must be symbol or list */ 0; })");
                                        }
                                    }
                                } else if (!_mv_533.has_value) {
                                    return SLOP_STR("({ /* for-each: missing var */ 0; })");
                                }
                                SLOP_UNREACHABLE();
                            }
                        }
                    }
                    default: {
                        return SLOP_STR("({ /* for-each: binding must be list */ 0; })");
                    }
                }
            } else if (!_mv_531.has_value) {
                return SLOP_STR("({ /* for-each: missing binding */ 0; })");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_for_each_list_as_expr(context_TranspileContext* ctx, slop_string var_name, types_SExprSymbol var_sym, types_SExpr* coll_expr, slop_list_types_SExpr_ptr items, int64_t len) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((coll_expr != NULL)), "(!= coll-expr nil)");
    {
        __auto_type coll_c = expr_transpile_expr(ctx, coll_expr);
        __auto_type elem_slop_type = expr_infer_collection_element_slop_type(ctx, coll_expr);
        __auto_type result = context_ctx_str3(ctx, SLOP_STR("({ __auto_type _coll = "), coll_c, context_ctx_str3(ctx, SLOP_STR("; for (size_t _i = 0; _i < _coll.len; _i++) { __auto_type "), var_name, SLOP_STR(" = _coll.data[_i]; ")));
        context_ctx_push_scope(ctx);
        {
            __auto_type is_ptr_elem = strlib_starts_with(elem_slop_type, SLOP_STR("(Ptr "));
            __auto_type elem_c_type = ((is_ptr_elem) ? expr_slop_type_to_c_type(ctx, elem_slop_type) : SLOP_STR("auto"));
            context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, elem_c_type, elem_slop_type, is_ptr_elem, 0, 0, SLOP_STR(""), SLOP_STR("")});
        }
        {
            int64_t i = 2;
            while (i < len) {
                __auto_type _mv_536 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_536.has_value) {
                    __auto_type body_expr = _mv_536.value;
                    {
                        __auto_type body_c = expr_transpile_expr(ctx, body_expr);
                        result = context_ctx_str3(ctx, result, body_c, SLOP_STR("; "));
                    }
                } else if (!_mv_536.has_value) {
                }
                i = (i + 1);
            }
        }
        context_ctx_pop_scope(ctx);
        return context_ctx_str(ctx, result, SLOP_STR("} (void)0; })"));
    }
}

slop_string expr_transpile_for_each_set_as_expr(context_TranspileContext* ctx, slop_string var_name, types_SExprSymbol var_sym, types_SExpr* coll_expr, slop_string resolved_type, slop_list_types_SExpr_ptr items, int64_t len) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((coll_expr != NULL)), "(!= coll-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type coll_c = expr_transpile_expr(ctx, coll_expr);
        __auto_type elem_slop_type = expr_extract_set_elem_from_slop_type(arena, resolved_type);
        __auto_type elem_c_type = expr_slop_value_type_to_c_type(ctx, elem_slop_type);
        {
            __auto_type result = context_ctx_str3(ctx, SLOP_STR("({ slop_map* _coll = (slop_map*)"), expr_deref_container_c(ctx, coll_c, resolved_type), SLOP_STR("; for (size_t _i = 0; _i < _coll->cap; _i++) { "));
            __auto_type if_part = SLOP_STR("if (_coll->entries[_i].occupied) { ");
            __auto_type cast_part = context_ctx_str(ctx, elem_c_type, SLOP_STR("*)_coll->entries[_i].key"));
            __auto_type assign_prefix = context_ctx_str4(ctx, elem_c_type, SLOP_STR(" "), var_name, SLOP_STR(" = *("));
            __auto_type assign_part = context_ctx_str3(ctx, assign_prefix, cast_part, SLOP_STR("; "));
            result = context_ctx_str3(ctx, result, if_part, assign_part);
            context_ctx_push_scope(ctx);
            context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, elem_c_type, elem_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
            {
                int64_t i = 2;
                while (i < len) {
                    __auto_type _mv_537 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_537.has_value) {
                        __auto_type body_expr = _mv_537.value;
                        {
                            __auto_type body_c = expr_transpile_expr(ctx, body_expr);
                            result = context_ctx_str3(ctx, result, body_c, SLOP_STR("; "));
                        }
                    } else if (!_mv_537.has_value) {
                    }
                    i = (i + 1);
                }
            }
            context_ctx_pop_scope(ctx);
            return context_ctx_str(ctx, result, SLOP_STR("} } (void)0; })"));
        }
    }
}

slop_string expr_transpile_for_each_map_keys_as_expr(context_TranspileContext* ctx, slop_string var_name, types_SExprSymbol var_sym, types_SExpr* coll_expr, slop_string resolved_type, slop_list_types_SExpr_ptr items, int64_t len) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((coll_expr != NULL)), "(!= coll-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type coll_c = expr_transpile_expr(ctx, coll_expr);
        __auto_type key_slop_type = expr_extract_map_key_from_slop_type(arena, resolved_type);
        __auto_type key_c_type = expr_slop_value_type_to_c_type(ctx, key_slop_type);
        {
            __auto_type result = context_ctx_str3(ctx, SLOP_STR("({ slop_map* _coll = (slop_map*)"), expr_deref_container_c(ctx, coll_c, resolved_type), SLOP_STR("; for (size_t _i = 0; _i < _coll->cap; _i++) { "));
            __auto_type if_part = SLOP_STR("if (_coll->entries[_i].occupied) { ");
            __auto_type cast_part = context_ctx_str(ctx, key_c_type, SLOP_STR("*)_coll->entries[_i].key"));
            __auto_type assign_prefix = context_ctx_str4(ctx, key_c_type, SLOP_STR(" "), var_name, SLOP_STR(" = *("));
            __auto_type assign_part = context_ctx_str3(ctx, assign_prefix, cast_part, SLOP_STR("; "));
            result = context_ctx_str3(ctx, result, if_part, assign_part);
            context_ctx_push_scope(ctx);
            context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, key_c_type, key_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
            {
                int64_t i = 2;
                while (i < len) {
                    __auto_type _mv_538 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_538.has_value) {
                        __auto_type body_expr = _mv_538.value;
                        {
                            __auto_type body_c = expr_transpile_expr(ctx, body_expr);
                            result = context_ctx_str3(ctx, result, body_c, SLOP_STR("; "));
                        }
                    } else if (!_mv_538.has_value) {
                    }
                    i = (i + 1);
                }
            }
            context_ctx_pop_scope(ctx);
            return context_ctx_str(ctx, result, SLOP_STR("} } (void)0; })"));
        }
    }
}

slop_string expr_transpile_for_each_map_kv_as_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr binding_items, slop_list_types_SExpr_ptr items, int64_t len) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_539 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_539.has_value) {
            __auto_type kv_list_expr = _mv_539.value;
            __auto_type _mv_540 = (*kv_list_expr);
            switch (_mv_540.tag) {
                case types_SExpr_lst:
                {
                    __auto_type kv_lst = _mv_540.data.lst;
                    {
                        __auto_type kv_items = kv_lst.items;
                        if (((int64_t)((kv_items).len)) < 2) {
                            return SLOP_STR("({ /* for-each: map binding needs ((k v) map) */ 0; })");
                        } else {
                            __auto_type _mv_541 = ({ __auto_type _lst = kv_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_541.has_value) {
                                __auto_type k_expr = _mv_541.value;
                                __auto_type _mv_542 = ({ __auto_type _lst = kv_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_542.has_value) {
                                    __auto_type v_expr = _mv_542.value;
                                    __auto_type _mv_543 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_543.has_value) {
                                        __auto_type map_expr = _mv_543.value;
                                        __auto_type _mv_544 = (*k_expr);
                                        switch (_mv_544.tag) {
                                            case types_SExpr_sym:
                                            {
                                                __auto_type k_sym = _mv_544.data.sym;
                                                __auto_type _mv_545 = (*v_expr);
                                                switch (_mv_545.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type v_sym = _mv_545.data.sym;
                                                        {
                                                            __auto_type k_name = ctype_to_c_name(arena, k_sym.name);
                                                            __auto_type v_name = ctype_to_c_name(arena, v_sym.name);
                                                            __auto_type map_c = expr_transpile_expr(ctx, map_expr);
                                                            __auto_type map_slop_type = expr_infer_expr_slop_type(ctx, map_expr);
                                                            __auto_type resolved_type = expr_resolve_type_alias(ctx, map_slop_type);
                                                            __auto_type key_slop_type = expr_extract_map_key_from_slop_type(arena, resolved_type);
                                                            __auto_type val_slop_type = expr_extract_map_value_from_slop_type(arena, resolved_type);
                                                            __auto_type key_c_type = expr_slop_value_type_to_c_type(ctx, key_slop_type);
                                                            __auto_type val_c_type = expr_slop_value_type_to_c_type(ctx, val_slop_type);
                                                            {
                                                                __auto_type result = context_ctx_str3(ctx, SLOP_STR("({ slop_map* _coll = (slop_map*)"), expr_deref_container_c(ctx, map_c, resolved_type), SLOP_STR("; for (size_t _i = 0; _i < _coll->cap; _i++) { "));
                                                                __auto_type if_part = SLOP_STR("if (_coll->entries[_i].occupied) { ");
                                                                __auto_type k_cast = context_ctx_str(ctx, key_c_type, SLOP_STR("*)_coll->entries[_i].key"));
                                                                __auto_type k_prefix = context_ctx_str4(ctx, key_c_type, SLOP_STR(" "), k_name, SLOP_STR(" = *("));
                                                                __auto_type k_assign = context_ctx_str3(ctx, k_prefix, k_cast, SLOP_STR("; "));
                                                                __auto_type v_cast = context_ctx_str(ctx, val_c_type, SLOP_STR("*)_coll->entries[_i].value"));
                                                                __auto_type v_prefix = context_ctx_str4(ctx, val_c_type, SLOP_STR(" "), v_name, SLOP_STR(" = *("));
                                                                __auto_type v_assign = context_ctx_str3(ctx, v_prefix, v_cast, SLOP_STR("; "));
                                                                result = context_ctx_str4(ctx, result, if_part, k_assign, v_assign);
                                                                context_ctx_push_scope(ctx);
                                                                context_ctx_bind_var(ctx, (context_VarEntry){k_sym.name, k_name, key_c_type, key_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                                                context_ctx_bind_var(ctx, (context_VarEntry){v_sym.name, v_name, val_c_type, val_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                                                {
                                                                    __auto_type i = 2;
                                                                    while (i < len) {
                                                                        __auto_type _mv_546 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                        if (_mv_546.has_value) {
                                                                            __auto_type body_expr = _mv_546.value;
                                                                            {
                                                                                __auto_type body_c = expr_transpile_expr(ctx, body_expr);
                                                                                result = context_ctx_str3(ctx, result, body_c, SLOP_STR("; "));
                                                                            }
                                                                        } else if (!_mv_546.has_value) {
                                                                        }
                                                                        i = (i + 1);
                                                                    }
                                                                }
                                                                context_ctx_pop_scope(ctx);
                                                                return context_ctx_str(ctx, result, SLOP_STR("} } (void)0; })"));
                                                            }
                                                        }
                                                    }
                                                    default: {
                                                        return SLOP_STR("({ /* for-each: map value must be symbol */ 0; })");
                                                    }
                                                }
                                            }
                                            default: {
                                                return SLOP_STR("({ /* for-each: map key must be symbol */ 0; })");
                                            }
                                        }
                                    } else if (!_mv_543.has_value) {
                                        return SLOP_STR("({ /* for-each: missing map expression */ 0; })");
                                    }
                                    SLOP_UNREACHABLE();
                                } else if (!_mv_542.has_value) {
                                    return SLOP_STR("({ /* for-each: missing value binding */ 0; })");
                                }
                                SLOP_UNREACHABLE();
                            } else if (!_mv_541.has_value) {
                                return SLOP_STR("({ /* for-each: missing key binding */ 0; })");
                            }
                            SLOP_UNREACHABLE();
                        }
                    }
                }
                default: {
                    return SLOP_STR("({ /* for-each: invalid map binding */ 0; })");
                }
            }
        } else if (!_mv_539.has_value) {
            return SLOP_STR("({ /* for-each: missing binding */ 0; })");
        }
        SLOP_UNREACHABLE();
    }
}

slop_string expr_transpile_with_arena_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 3) {
            return SLOP_STR("({ (void)0; })");
        } else {
            {
                __auto_type is_named = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type item1 = _mv.value; ({ __auto_type _mv = (*item1); uint8_t _mr = {0}; switch (_mv.tag) { case types_SExpr_sym: { __auto_type s1 = _mv.data.sym; _mr = string_eq(s1.name, SLOP_STR(":as")); break; } default: { _mr = 0; break; }  } _mr; }); }) : (0); });
                __auto_type arena_name = ((is_named) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type name_expr = _mv.value; ({ __auto_type _mv = (*name_expr); slop_string _mr = {0}; switch (_mv.tag) { case types_SExpr_sym: { __auto_type s2 = _mv.data.sym; _mr = s2.name; break; } default: { _mr = SLOP_STR("arena"); break; }  } _mr; }); }) : (SLOP_STR("arena")); }) : SLOP_STR("arena"));
                __auto_type size_idx = ((is_named) ? 3 : 1);
                __auto_type body_start = ((is_named) ? 4 : 2);
                __auto_type c_arena_name = ctype_to_c_name(arena, arena_name);
                __auto_type c_local = ((is_named) ? string_concat(arena, SLOP_STR("_arena_"), c_arena_name) : SLOP_STR("_arena"));
                if (is_named && (len < 5)) {
                    context_ctx_add_error_at(ctx, SLOP_STR("with-arena :as requires name, size and body"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    return SLOP_STR("({ (void)0; })");
                } else {
                    context_ctx_push_scope(ctx);
                    {
                        __auto_type result_str = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)size_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type size_expr = _mv.value; ({ __auto_type size_c = expr_transpile_expr(ctx, size_expr); __auto_type result = context_ctx_str5(ctx, SLOP_STR("({ slop_arena "), c_local, SLOP_STR(" = slop_arena_new("), size_c, SLOP_STR("); ")); ({ result = context_ctx_str5(ctx, result, SLOP_STR("slop_arena* "), c_arena_name, SLOP_STR(" = &"), context_ctx_str(ctx, c_local, SLOP_STR("; "))); (void)0; }); context_ctx_bind_var(ctx, (context_VarEntry){arena_name, c_arena_name, SLOP_STR("slop_arena*"), SLOP_STR(""), 1, 0, 0, SLOP_STR(""), SLOP_STR("")}); ({ __auto_type i = body_start; ({ while ((i < (len - 1))) { ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type body_expr = _mv.value; ({ __auto_type body_c = expr_transpile_expr(ctx, body_expr); ({ result = context_ctx_str3(ctx, result, body_c, SLOP_STR("; ")); (void)0; }); }); } else { ({ (void)0; }); } (void)0; }); ({ i = (i + 1); (void)0; }); } (void)0; }); }); ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)(len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type last_expr = _mv.value; ({ __auto_type last_c = expr_transpile_expr(ctx, last_expr); __auto_type free_part = context_ctx_str3(ctx, SLOP_STR("slop_arena_free("), c_arena_name, SLOP_STR("); ")); ({ result = context_ctx_str5(ctx, result, SLOP_STR("__auto_type _wa_result = "), last_c, SLOP_STR("; "), free_part); (void)0; }); ({ result = context_ctx_str(ctx, result, SLOP_STR("_wa_result; })")); (void)0; }); }); } else { ({ __auto_type free_part = context_ctx_str3(ctx, SLOP_STR("slop_arena_free("), c_arena_name, SLOP_STR("); ")); ({ result = context_ctx_str3(ctx, result, free_part, SLOP_STR("0; })")); (void)0; }); }); } (void)0; }); result; }); }) : (({ context_ctx_add_error_at(ctx, SLOP_STR("with-arena: missing size"), context_ctx_list_first_line(items), context_ctx_list_first_col(items)); SLOP_STR("({ (void)0; })"); })); });
                        context_ctx_pop_scope(ctx);
                        return result_str;
                    }
                }
            }
        }
    }
}

slop_string expr_transpile_lambda_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 2) {
            context_ctx_add_error_at(ctx, SLOP_STR("lambda needs params"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("NULL");
        } else {
            __auto_type _mv_547 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_547.has_value) {
                __auto_type second = _mv_547.value;
                __auto_type _mv_548 = (*second);
                switch (_mv_548.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type params_lst = _mv_548.data.lst;
                        return expr_transpile_lambda_with_params(ctx, items, params_lst.items);
                    }
                    case types_SExpr_sym:
                    {
                        __auto_type _ = _mv_548.data.sym;
                        context_ctx_add_error_at(ctx, SLOP_STR("named function not allowed in expression context"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                        return SLOP_STR("NULL");
                    }
                    default: {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid lambda form"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                        return SLOP_STR("NULL");
                    }
                }
            } else if (!_mv_547.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("lambda missing params"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                return SLOP_STR("NULL");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_transpile_lambda_with_params(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, slop_list_types_SExpr_ptr params) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type param_names = expr_extract_param_names(arena, params);
        __auto_type empty_pending = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        __auto_type free_vars = expr_find_free_vars(ctx, param_names, items, 2, empty_pending);
        {
            __auto_type base_name = context_ctx_gensym(ctx, SLOP_STR("_lambda"));
            __auto_type lambda_name = ({ __auto_type _mv = context_ctx_get_module(ctx); _mv.has_value ? ({ __auto_type mod = _mv.value; context_ctx_str3(ctx, ctype_to_c_name(arena, mod), SLOP_STR("_"), base_name); }) : (base_name); });
            if (((int64_t)((free_vars).len)) > 0) {
                return expr_transpile_closure(ctx, items, params, param_names, free_vars, lambda_name);
            } else {
                return expr_transpile_simple_lambda(ctx, items, params, lambda_name);
            }
        }
    }
}

slop_list_string expr_extract_param_names(slop_arena* arena, slop_list_types_SExpr_ptr params) {
    {
        __auto_type names = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        __auto_type count = ((int64_t)((params).len));
        int64_t i = 0;
        while (i < count) {
            __auto_type _mv_549 = ({ __auto_type _lst = params; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_549.has_value) {
                __auto_type param_expr = _mv_549.value;
                __auto_type _mv_550 = (*param_expr);
                switch (_mv_550.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type param_lst = _mv_550.data.lst;
                        {
                            __auto_type param_items = param_lst.items;
                            if (((int64_t)((param_items).len)) >= 1) {
                                __auto_type _mv_551 = ({ __auto_type _lst = param_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_551.has_value) {
                                    __auto_type name_expr = _mv_551.value;
                                    __auto_type _mv_552 = (*name_expr);
                                    switch (_mv_552.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type name_sym = _mv_552.data.sym;
                                            ({ __auto_type _lst_p = &(names); __auto_type _item = (name_sym.name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_551.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_549.has_value) {
            }
            i = (i + 1);
        }
        return names;
    }
}

slop_string expr_infer_lambda_return_type(context_TranspileContext* ctx, types_SExpr* body) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (body == NULL) {
        return SLOP_STR("int64_t");
    } else {
        {
            __auto_type c_type = expr_infer_expr_c_type(ctx, body);
            if (string_eq(c_type, SLOP_STR(""))) {
                return SLOP_STR("int64_t");
            } else {
                return c_type;
            }
        }
    }
}

slop_string expr_transpile_simple_lambda(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, slop_list_types_SExpr_ptr params, slop_string lambda_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type body_expr = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)(((int64_t)((items).len)) - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type e = _mv.value; e; }) : (NULL); });
        __auto_type param_str = expr_build_lambda_params(ctx, params);
        __auto_type return_type = expr_infer_lambda_return_type(ctx, body_expr);
        context_ctx_push_scope(ctx);
        expr_bind_lambda_params(ctx, params);
        {
            __auto_type body_start = 2;
            __auto_type body_code = expr_transpile_lambda_body(ctx, items, body_start, return_type);
            context_ctx_pop_scope(ctx);
            {
                __auto_type fn_def = expr_build_lambda_function(ctx, lambda_name, return_type, param_str, body_code);
                context_ctx_add_deferred_lambda(ctx, fn_def);
                context_ctx_set_last_lambda_info(ctx, 1, SLOP_STR("void"), lambda_name);
                return context_ctx_str5(ctx, SLOP_STR("(slop_closure_t){(void*)"), lambda_name, SLOP_STR(", NULL}"), SLOP_STR(""), SLOP_STR(""));
            }
        }
    }
}

slop_string expr_transpile_closure(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, slop_list_types_SExpr_ptr params, slop_list_string param_names, slop_list_string free_vars, slop_string lambda_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type body_expr = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)(((int64_t)((items).len)) - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type e = _mv.value; e; }) : (NULL); });
        __auto_type env_name = context_ctx_str(ctx, lambda_name, SLOP_STR("_env"));
        __auto_type env_type = context_ctx_str(ctx, env_name, SLOP_STR("_t"));
        {
            __auto_type struct_def = expr_build_closure_struct(ctx, env_type, free_vars);
            context_ctx_add_deferred_lambda(ctx, struct_def);
            {
                __auto_type param_str = expr_build_closure_params(ctx, params);
                __auto_type return_type = expr_infer_lambda_return_type(ctx, body_expr);
                __auto_type captured_accesses = expr_capture_free_var_accesses(ctx, free_vars);
                context_ctx_push_scope(ctx);
                expr_bind_closure_captures(ctx, free_vars);
                expr_bind_lambda_params(ctx, params);
                {
                    __auto_type body_start = 2;
                    __auto_type body_code = expr_transpile_lambda_body(ctx, items, body_start, return_type);
                    context_ctx_pop_scope(ctx);
                    {
                        __auto_type fn_def = expr_build_closure_function(ctx, lambda_name, env_type, return_type, param_str, body_code, free_vars);
                        context_ctx_add_deferred_lambda(ctx, fn_def);
                        context_ctx_set_last_lambda_info(ctx, 1, env_type, lambda_name);
                        return expr_build_closure_instance(ctx, lambda_name, env_name, env_type, free_vars, captured_accesses);
                    }
                }
            }
        }
    }
}

slop_string expr_build_closure_struct(context_TranspileContext* ctx, slop_string env_type, slop_list_string free_vars) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type count = ((int64_t)((free_vars).len));
        __auto_type fields = SLOP_STR("");
        int64_t i = 0;
        while (i < count) {
            __auto_type _mv_553 = ({ __auto_type _lst = free_vars; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_553.has_value) {
                __auto_type var_name = _mv_553.value;
                {
                    __auto_type var_info = context_ctx_lookup_var(ctx, var_name);
                    __auto_type is_mut = ({ __auto_type _mv = var_info; _mv.has_value ? ({ __auto_type entry = _mv.value; entry.is_mutable; }) : (0); });
                    __auto_type var_type = ({ __auto_type _mv = var_info; _mv.has_value ? ({ __auto_type entry = _mv.value; ({ __auto_type c_type = entry.c_type; __auto_type slop_type = entry.slop_type; ((is_mut) ? ((((string_len(c_type) > 0) && !(string_eq(c_type, SLOP_STR("__auto_type"))))) ? c_type : (((string_len(slop_type) > 0)) ? expr_slop_type_to_c_type(ctx, slop_type) : SLOP_STR("int64_t"))) : (((string_len(slop_type) > 0)) ? expr_slop_type_to_c_type(ctx, slop_type) : c_type)); }); }) : (SLOP_STR("int64_t")); });
                    __auto_type c_name = ctype_to_c_name(arena, var_name);
                    __auto_type field_type = ((is_mut) ? context_ctx_str(ctx, var_type, SLOP_STR("*")) : var_type);
                    fields = context_ctx_str(ctx, fields, context_ctx_str4(ctx, field_type, SLOP_STR(" "), c_name, SLOP_STR("; ")));
                }
            } else if (!_mv_553.has_value) {
            }
            i = (i + 1);
        }
        return context_ctx_str(ctx, SLOP_STR("typedef struct { "), context_ctx_str3(ctx, fields, SLOP_STR("} "), context_ctx_str(ctx, env_type, SLOP_STR(";"))));
    }
}

slop_string expr_build_closure_params(context_TranspileContext* ctx, slop_list_types_SExpr_ptr params) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    return expr_build_lambda_params(ctx, params);
}

void expr_bind_closure_captures(context_TranspileContext* ctx, slop_list_string free_vars) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type count = ((int64_t)((free_vars).len));
        int64_t i = 0;
        while (i < count) {
            __auto_type _mv_554 = ({ __auto_type _lst = free_vars; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_554.has_value) {
                __auto_type var_name = _mv_554.value;
                {
                    __auto_type c_name = ctype_to_c_name(arena, var_name);
                    __auto_type var_info = context_ctx_lookup_var(ctx, var_name);
                    __auto_type is_mut = ({ __auto_type _mv = var_info; _mv.has_value ? ({ __auto_type entry = _mv.value; entry.is_mutable; }) : (0); });
                    __auto_type access_expr = ((is_mut) ? context_ctx_str3(ctx, SLOP_STR("(*_env->"), c_name, SLOP_STR(")")) : context_ctx_str3(ctx, SLOP_STR("_env->"), c_name, SLOP_STR("")));
                    __auto_type var_type = ({ __auto_type _mv = var_info; _mv.has_value ? ({ __auto_type entry = _mv.value; entry.c_type; }) : (SLOP_STR("int64_t")); });
                    __auto_type slop_type = ({ __auto_type _mv = var_info; _mv.has_value ? ({ __auto_type entry = _mv.value; entry.slop_type; }) : (SLOP_STR("")); });
                    context_ctx_bind_var(ctx, (context_VarEntry){var_name, access_expr, var_type, slop_type, 0, is_mut, 0, SLOP_STR(""), SLOP_STR("")});
                }
            } else if (!_mv_554.has_value) {
            }
            i = (i + 1);
        }
    }
}

slop_list_string expr_capture_free_var_accesses(context_TranspileContext* ctx, slop_list_string free_vars) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type count = ((int64_t)((free_vars).len));
        __auto_type result = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        int64_t i = 0;
        while (i < count) {
            __auto_type _mv_555 = ({ __auto_type _lst = free_vars; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_555.has_value) {
                __auto_type var_name = _mv_555.value;
                {
                    __auto_type c_name = ctype_to_c_name(arena, var_name);
                    __auto_type var_info = context_ctx_lookup_var(ctx, var_name);
                    __auto_type base_access = ({ __auto_type _mv = var_info; _mv.has_value ? ({ __auto_type entry = _mv.value; entry.c_name; }) : (c_name); });
                    __auto_type is_mut = ({ __auto_type _mv = var_info; _mv.has_value ? ({ __auto_type entry = _mv.value; entry.is_mutable; }) : (0); });
                    __auto_type access_expr = ((is_mut) ? context_ctx_str3(ctx, SLOP_STR("&("), base_access, SLOP_STR(")")) : base_access);
                    ({ __auto_type _lst_p = &(result); __auto_type _item = (access_expr); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                }
            } else if (!_mv_555.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_string expr_build_closure_function(context_TranspileContext* ctx, slop_string name, slop_string env_type, slop_string ret_type, slop_string params, slop_string body, slop_list_string free_vars) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        {
            __auto_type env_param = context_ctx_str3(ctx, env_type, SLOP_STR("* _env"), SLOP_STR(""));
            __auto_type full_params = ((string_eq(params, SLOP_STR("(void)"))) ? context_ctx_str3(ctx, SLOP_STR("("), env_param, SLOP_STR(")")) : context_ctx_str5(ctx, SLOP_STR("("), env_param, SLOP_STR(", "), expr_trim_parens(arena, params), SLOP_STR(")")));
            return context_ctx_str(ctx, SLOP_STR("static "), context_ctx_str(ctx, ret_type, context_ctx_str(ctx, SLOP_STR(" "), context_ctx_str(ctx, name, context_ctx_str(ctx, full_params, context_ctx_str(ctx, SLOP_STR(" { "), context_ctx_str(ctx, body, SLOP_STR(" }"))))))));
        }
    }
}

slop_string expr_trim_parens(slop_arena* arena, slop_string s) {
    {
        __auto_type len = ((int64_t)(string_len(s)));
        if (len < 2) {
            return s;
        } else {
            return strlib_substring(arena, s, ((int64_t)(1)), ((int64_t)((len - 2))));
        }
    }
}

slop_string expr_find_arena_ptr_expr(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    __auto_type _mv_556 = context_ctx_lookup_var(ctx, SLOP_STR("_arena"));
    if (_mv_556.has_value) {
        __auto_type entry = _mv_556.value;
        return SLOP_STR("&_arena");
    } else if (!_mv_556.has_value) {
        __auto_type _mv_557 = context_ctx_lookup_var(ctx, SLOP_STR("arena"));
        if (_mv_557.has_value) {
            __auto_type entry = _mv_557.value;
            return entry.c_name;
        } else if (!_mv_557.has_value) {
            __auto_type _mv_558 = context_ctx_find_arena_var(ctx);
            if (_mv_558.has_value) {
                __auto_type entry = _mv_558.value;
                return entry.c_name;
            } else if (!_mv_558.has_value) {
                return SLOP_STR("");
            }
            SLOP_UNREACHABLE();
        }
        SLOP_UNREACHABLE();
    }
    SLOP_UNREACHABLE();
}

slop_string expr_build_closure_instance(context_TranspileContext* ctx, slop_string lambda_name, slop_string env_name, slop_string env_type, slop_list_string free_vars, slop_list_string captured_accesses) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        {
            __auto_type initializer = expr_build_env_initializer(ctx, free_vars, captured_accesses);
            __auto_type arena_expr = expr_find_arena_ptr_expr(ctx);
            {
                __auto_type alloc_decl = ((string_eq(arena_expr, SLOP_STR(""))) ? ({ context_ctx_add_warning(ctx, context_ctx_str(ctx, SLOP_STR("closure env allocated with malloc (no arena in scope): "), env_type)); context_ctx_str(ctx, env_type, context_ctx_str(ctx, SLOP_STR("* "), context_ctx_str(ctx, env_name, context_ctx_str(ctx, SLOP_STR(" = ("), context_ctx_str(ctx, env_type, context_ctx_str(ctx, SLOP_STR("*)malloc(sizeof("), context_ctx_str(ctx, env_type, SLOP_STR("));")))))))); }) : context_ctx_str(ctx, env_type, context_ctx_str(ctx, SLOP_STR("* "), context_ctx_str(ctx, env_name, context_ctx_str(ctx, SLOP_STR(" = ("), context_ctx_str(ctx, env_type, context_ctx_str(ctx, SLOP_STR("*)slop_arena_alloc("), context_ctx_str(ctx, arena_expr, context_ctx_str(ctx, SLOP_STR(", sizeof("), context_ctx_str(ctx, env_type, SLOP_STR("));")))))))))));
                __auto_type assign_stmt = context_ctx_str(ctx, SLOP_STR("*"), context_ctx_str(ctx, env_name, context_ctx_str(ctx, SLOP_STR(" = ("), context_ctx_str(ctx, env_type, context_ctx_str(ctx, SLOP_STR(")"), context_ctx_str(ctx, initializer, SLOP_STR(";")))))));
                return context_ctx_str(ctx, SLOP_STR("({ "), context_ctx_str(ctx, alloc_decl, context_ctx_str(ctx, SLOP_STR(" "), context_ctx_str(ctx, assign_stmt, context_ctx_str(ctx, SLOP_STR(" (slop_closure_t){ (void*)"), context_ctx_str(ctx, lambda_name, context_ctx_str(ctx, SLOP_STR(", (void*)"), context_ctx_str(ctx, env_name, SLOP_STR(" }; })")))))))));
            }
        }
    }
}

slop_string expr_build_env_initializer(context_TranspileContext* ctx, slop_list_string free_vars, slop_list_string captured_accesses) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type count = ((int64_t)((free_vars).len));
        __auto_type result = SLOP_STR("{ ");
        int64_t i = 0;
        while (i < count) {
            __auto_type _mv_559 = ({ __auto_type _lst = free_vars; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_559.has_value) {
                __auto_type var_name = _mv_559.value;
                {
                    __auto_type c_name = ctype_to_c_name(arena, var_name);
                    __auto_type access_expr = ({ __auto_type _mv = ({ __auto_type _lst = captured_accesses; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type acc = _mv.value; acc; }) : (c_name); });
                    if (i > 0) {
                        result = context_ctx_str(ctx, result, context_ctx_str5(ctx, SLOP_STR(", ."), c_name, SLOP_STR(" = "), access_expr, SLOP_STR("")));
                    } else {
                        result = context_ctx_str(ctx, result, context_ctx_str5(ctx, SLOP_STR("."), c_name, SLOP_STR(" = "), access_expr, SLOP_STR("")));
                    }
                }
            } else if (!_mv_559.has_value) {
            }
            i = (i + 1);
        }
        return context_ctx_str(ctx, result, SLOP_STR(" }"));
    }
}

slop_string expr_build_lambda_params(context_TranspileContext* ctx, slop_list_types_SExpr_ptr params) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type param_count = ((int64_t)((params).len));
        if (param_count == 0) {
            return SLOP_STR("(void)");
        } else {
            {
                __auto_type result = SLOP_STR("(");
                int64_t i = 0;
                while (i < param_count) {
                    __auto_type _mv_560 = ({ __auto_type _lst = params; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_560.has_value) {
                        __auto_type param_expr = _mv_560.value;
                        __auto_type _mv_561 = (*param_expr);
                        switch (_mv_561.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type param_lst = _mv_561.data.lst;
                                {
                                    __auto_type param_items = param_lst.items;
                                    if (((int64_t)((param_items).len)) >= 2) {
                                        __auto_type _mv_562 = ({ __auto_type _lst = param_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_562.has_value) {
                                            __auto_type name_expr = _mv_562.value;
                                            __auto_type _mv_563 = (*name_expr);
                                            switch (_mv_563.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type name_sym = _mv_563.data.sym;
                                                    __auto_type _mv_564 = ({ __auto_type _lst = param_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_564.has_value) {
                                                        __auto_type type_expr = _mv_564.value;
                                                        {
                                                            __auto_type param_name = ctype_to_c_name(arena, name_sym.name);
                                                            __auto_type param_type = context_to_c_type_prefixed(ctx, type_expr);
                                                            if (i > 0) {
                                                                result = context_ctx_str(ctx, result, context_ctx_str5(ctx, SLOP_STR(", "), param_type, SLOP_STR(" "), param_name, SLOP_STR("")));
                                                            } else {
                                                                result = context_ctx_str(ctx, result, context_ctx_str4(ctx, param_type, SLOP_STR(" "), param_name, SLOP_STR("")));
                                                            }
                                                        }
                                                    } else if (!_mv_564.has_value) {
                                                    }
                                                    break;
                                                }
                                                default: {
                                                    break;
                                                }
                                            }
                                        } else if (!_mv_562.has_value) {
                                        }
                                    }
                                }
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_560.has_value) {
                    }
                    i = (i + 1);
                }
                return context_ctx_str(ctx, result, SLOP_STR(")"));
            }
        }
    }
}

void expr_bind_lambda_params(context_TranspileContext* ctx, slop_list_types_SExpr_ptr params) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type param_count = ((int64_t)((params).len));
        int64_t i = 0;
        while (i < param_count) {
            __auto_type _mv_565 = ({ __auto_type _lst = params; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_565.has_value) {
                __auto_type param_expr = _mv_565.value;
                __auto_type _mv_566 = (*param_expr);
                switch (_mv_566.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type param_lst = _mv_566.data.lst;
                        {
                            __auto_type param_items = param_lst.items;
                            if (((int64_t)((param_items).len)) >= 2) {
                                __auto_type _mv_567 = ({ __auto_type _lst = param_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_567.has_value) {
                                    __auto_type name_expr = _mv_567.value;
                                    __auto_type _mv_568 = (*name_expr);
                                    switch (_mv_568.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type name_sym = _mv_568.data.sym;
                                            __auto_type _mv_569 = ({ __auto_type _lst = param_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_569.has_value) {
                                                __auto_type type_expr = _mv_569.value;
                                                {
                                                    __auto_type param_name = name_sym.name;
                                                    __auto_type c_name = ctype_to_c_name(arena, param_name);
                                                    __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                    __auto_type is_ptr = expr_is_pointer_type_sexpr(type_expr);
                                                    context_ctx_bind_var(ctx, (context_VarEntry){param_name, c_name, c_type, SLOP_STR(""), is_ptr, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                                }
                                            } else if (!_mv_569.has_value) {
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_567.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_565.has_value) {
            }
            i = (i + 1);
        }
    }
}

uint8_t expr_is_pointer_type_sexpr(types_SExpr* type_expr) {
    __auto_type _mv_570 = (*type_expr);
    switch (_mv_570.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_570.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_571 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_571.has_value) {
                        __auto_type head = _mv_571.value;
                        __auto_type _mv_572 = (*head);
                        switch (_mv_572.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_572.data.sym;
                                return (string_eq(sym.name, SLOP_STR("Ptr")) || string_eq(sym.name, SLOP_STR("ScopedPtr")));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_571.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        default: {
            return 0;
        }
    }
}

slop_string expr_transpile_lambda_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start, slop_string return_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type is_void = string_eq(return_type, SLOP_STR("void"));
        __auto_type result = SLOP_STR("");
        int64_t i = start;
        if (len <= start) {
            if (is_void) {
                return SLOP_STR("(void)0;");
            } else {
                return SLOP_STR("return 0;");
            }
        } else {
            while (i < len) {
                __auto_type _mv_573 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_573.has_value) {
                    __auto_type expr = _mv_573.value;
                    {
                        __auto_type expr_c = expr_transpile_expr(ctx, expr);
                        __auto_type is_last = (i == (len - 1));
                        if (is_last) {
                            if (is_void) {
                                result = context_ctx_str(ctx, result, context_ctx_str(ctx, expr_c, SLOP_STR(";")));
                            } else {
                                result = context_ctx_str(ctx, result, context_ctx_str(ctx, SLOP_STR("return "), context_ctx_str(ctx, expr_c, SLOP_STR(";"))));
                            }
                        } else {
                            result = context_ctx_str(ctx, result, context_ctx_str3(ctx, expr_c, SLOP_STR("; "), SLOP_STR("")));
                        }
                    }
                } else if (!_mv_573.has_value) {
                }
                i = (i + 1);
            }
            return result;
        }
    }
}

slop_string expr_build_lambda_function(context_TranspileContext* ctx, slop_string name, slop_string ret_type, slop_string params, slop_string body) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        {
            __auto_type full_params = ((string_eq(params, SLOP_STR("(void)"))) ? SLOP_STR("(void* _env)") : context_ctx_str5(ctx, SLOP_STR("(void* _env, "), expr_trim_parens(arena, params), SLOP_STR(")"), SLOP_STR(""), SLOP_STR("")));
            return context_ctx_str(ctx, SLOP_STR("static "), context_ctx_str(ctx, ret_type, context_ctx_str(ctx, SLOP_STR(" "), context_ctx_str(ctx, name, context_ctx_str(ctx, full_params, context_ctx_str(ctx, SLOP_STR(" { "), context_ctx_str(ctx, body, SLOP_STR(" }"))))))));
        }
    }
}

uint8_t expr_is_capturing_lambda(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_574 = (*expr);
    switch (_mv_574.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_574.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 2) {
                    return 0;
                } else {
                    __auto_type _mv_575 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_575.has_value) {
                        __auto_type head = _mv_575.value;
                        __auto_type _mv_576 = (*head);
                        switch (_mv_576.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_576.data.sym;
                                if (!(string_eq(sym.name, SLOP_STR("fn")))) {
                                    return 0;
                                } else {
                                    __auto_type _mv_577 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_577.has_value) {
                                        __auto_type second = _mv_577.value;
                                        __auto_type _mv_578 = (*second);
                                        switch (_mv_578.tag) {
                                            case types_SExpr_lst:
                                            {
                                                __auto_type _ = _mv_578.data.lst;
                                                return 1;
                                            }
                                            default: {
                                                return 0;
                                            }
                                        }
                                    } else if (!_mv_577.has_value) {
                                        return 0;
                                    }
                                    SLOP_UNREACHABLE();
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_575.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        default: {
            return 0;
        }
    }
}

slop_string expr_transpile_spawn_closure(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, types_SExpr* fn_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((fn_expr != NULL)), "(!= fn-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_579 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_579.has_value) {
            __auto_type arena_expr = _mv_579.value;
            {
                __auto_type arena_c = expr_transpile_expr(ctx, arena_expr);
                __auto_type has_captures = expr_lambda_has_captures(ctx, fn_expr);
                if (has_captures) {
                    {
                        __auto_type closure_c = expr_transpile_expr(ctx, fn_expr);
                        return context_ctx_str(ctx, SLOP_STR("({ slop_closure_t _spawn_cl = "), context_ctx_str(ctx, closure_c, context_ctx_str(ctx, SLOP_STR("; slop_thread_int* _spawn_th = slop_arena_alloc("), context_ctx_str(ctx, arena_c, context_ctx_str(ctx, SLOP_STR(", sizeof(slop_thread_int));"), context_ctx_str(ctx, SLOP_STR(" _spawn_th->func = _spawn_cl.fn;"), context_ctx_str(ctx, SLOP_STR(" _spawn_th->env = _spawn_cl.env;"), context_ctx_str(ctx, SLOP_STR(" _spawn_th->done = false;"), context_ctx_str(ctx, SLOP_STR(" pthread_create(&_spawn_th->id, NULL, (void*)slop_thread_int_entry, (void*)_spawn_th);"), SLOP_STR(" _spawn_th; })"))))))))));
                    }
                } else {
                    return expr_transpile_regular_fn_call(ctx, SLOP_STR("spawn"), items);
                }
            }
        } else if (!_mv_579.has_value) {
            context_ctx_add_error_at(ctx, SLOP_STR("spawn: missing arena argument"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            return SLOP_STR("NULL");
        }
        SLOP_UNREACHABLE();
    }
}

uint8_t expr_lambda_has_captures(context_TranspileContext* ctx, types_SExpr* fn_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((fn_expr != NULL)), "(!= fn-expr nil)");
    __auto_type _mv_580 = (*fn_expr);
    switch (_mv_580.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_580.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type arena = (*ctx).arena;
                if (((int64_t)((items).len)) < 2) {
                    return 0;
                } else {
                    __auto_type _mv_581 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_581.has_value) {
                        __auto_type params_expr = _mv_581.value;
                        __auto_type _mv_582 = (*params_expr);
                        switch (_mv_582.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type params_lst = _mv_582.data.lst;
                                {
                                    __auto_type params = params_lst.items;
                                    __auto_type param_names = expr_extract_param_names(arena, params);
                                    __auto_type empty_pending = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                                    __auto_type free_vars = expr_find_free_vars(ctx, param_names, items, 2, empty_pending);
                                    return (((int64_t)((free_vars).len)) > 0);
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_581.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        default: {
            return 0;
        }
    }
}

slop_string expr_transpile_regular_fn_call(context_TranspileContext* ctx, slop_string fn_name, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type func_opt = context_ctx_lookup_func(ctx, fn_name);
        __auto_type args = SLOP_STR("");
        int64_t i = 1;
        int64_t param_idx = 0;
        while (i < len) {
            __auto_type _mv_583 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_583.has_value) {
                __auto_type arg = _mv_583.value;
                {
                    __auto_type arg_c = expr_transpile_expr(ctx, arg);
                    __auto_type expected_type = ({ __auto_type _mv = func_opt; _mv.has_value ? ({ __auto_type func_entry = _mv.value; ({ __auto_type _mv = ({ __auto_type _lst = func_entry.param_types; size_t _idx = (size_t)param_idx; slop_option_context_FuncParamType_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type p = _mv.value; (*p).c_type; }) : (SLOP_STR("")); }); }) : (SLOP_STR("")); });
                    __auto_type final_arg = expr_typed_none_arg(ctx, expected_type, arg_c);
                    if (string_eq(args, SLOP_STR(""))) {
                        args = final_arg;
                    } else {
                        args = context_ctx_str3(ctx, args, SLOP_STR(", "), final_arg);
                    }
                    param_idx = (param_idx + 1);
                }
            } else if (!_mv_583.has_value) {
            }
            i = (i + 1);
        }
        return expr_transpile_call(ctx, fn_name, args);
    }
}

slop_string expr_infer_generic_type_binding(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (((int64_t)((items).len)) < 2) {
            return SLOP_STR("");
        } else {
            __auto_type _mv_584 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_584.has_value) {
                __auto_type first_arg = _mv_584.value;
                {
                    __auto_type slop_type = expr_infer_expr_slop_type(ctx, first_arg);
                    if (string_eq(slop_type, SLOP_STR(""))) {
                        {
                            __auto_type c_type = expr_infer_expr_c_type(ctx, first_arg);
                            return expr_extract_type_binding_from_c_type(arena, c_type);
                        }
                    } else {
                        return expr_extract_type_binding_from_slop_type(arena, slop_type);
                    }
                }
            } else if (!_mv_584.has_value) {
                return SLOP_STR("");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string expr_extract_type_binding_from_slop_type(slop_arena* arena, slop_string slop_type) {
    if (strlib_starts_with(slop_type, SLOP_STR("(Ptr (Chan "))) {
        {
            __auto_type inner_start = 11;
            __auto_type inner_end = expr_find_matching_paren(slop_type, inner_start);
            if (inner_end > inner_start) {
                {
                    __auto_type inner_type = strlib_substring(arena, slop_type, ((int64_t)(inner_start)), ((int64_t)((inner_end - inner_start))));
                    return expr_slop_type_to_c_identifier(arena, inner_type);
                }
            } else {
                return SLOP_STR("int");
            }
        }
    } else if (strlib_starts_with(slop_type, SLOP_STR("(Ptr (Thread "))) {
        {
            __auto_type inner_start = 13;
            __auto_type inner_end = expr_find_matching_paren(slop_type, inner_start);
            if (inner_end > inner_start) {
                {
                    __auto_type inner_type = strlib_substring(arena, slop_type, ((int64_t)(inner_start)), ((int64_t)((inner_end - inner_start))));
                    return expr_slop_type_to_c_identifier(arena, inner_type);
                }
            } else {
                return SLOP_STR("int");
            }
        }
    } else {
        return expr_slop_type_to_c_identifier(arena, slop_type);
    }
}

slop_string expr_extract_type_binding_from_c_type(slop_arena* arena, slop_string c_type) {
    if (strlib_starts_with(c_type, SLOP_STR("slop_chan_"))) {
        {
            __auto_type start = 10;
            __auto_type end_offset = ((strlib_ends_with(c_type, SLOP_STR("*"))) ? 1 : 0);
            __auto_type len = string_len(c_type);
            if (len > start) {
                return strlib_substring(arena, c_type, ((int64_t)(start)), ((int64_t)(((((int64_t)(len)) - start) - end_offset))));
            } else {
                return SLOP_STR("int");
            }
        }
    } else if (strlib_starts_with(c_type, SLOP_STR("slop_thread_"))) {
        {
            __auto_type start = 12;
            __auto_type end_offset = ((strlib_ends_with(c_type, SLOP_STR("*"))) ? 1 : 0);
            __auto_type len = string_len(c_type);
            if (len > start) {
                return strlib_substring(arena, c_type, ((int64_t)(start)), ((int64_t)(((((int64_t)(len)) - start) - end_offset))));
            } else {
                return SLOP_STR("int");
            }
        }
    } else {
        return SLOP_STR("int");
    }
}

slop_string expr_slop_type_to_c_identifier(slop_arena* arena, slop_string slop_type) {
    if (string_eq(slop_type, SLOP_STR("Int"))) {
        return SLOP_STR("int");
    } else if (string_eq(slop_type, SLOP_STR("I64"))) {
        return SLOP_STR("int");
    } else if (string_eq(slop_type, SLOP_STR("I32"))) {
        return SLOP_STR("i32");
    } else if (string_eq(slop_type, SLOP_STR("I16"))) {
        return SLOP_STR("i16");
    } else if (string_eq(slop_type, SLOP_STR("I8"))) {
        return SLOP_STR("i8");
    } else if (string_eq(slop_type, SLOP_STR("U64"))) {
        return SLOP_STR("u64");
    } else if (string_eq(slop_type, SLOP_STR("U32"))) {
        return SLOP_STR("u32");
    } else if (string_eq(slop_type, SLOP_STR("U16"))) {
        return SLOP_STR("u16");
    } else if (string_eq(slop_type, SLOP_STR("U8"))) {
        return SLOP_STR("u8");
    } else if (string_eq(slop_type, SLOP_STR("String"))) {
        return SLOP_STR("string");
    } else if (string_eq(slop_type, SLOP_STR("Bool"))) {
        return SLOP_STR("bool");
    } else if (string_eq(slop_type, SLOP_STR("Float"))) {
        return SLOP_STR("double");
    } else if (string_eq(slop_type, SLOP_STR("Unit"))) {
        return SLOP_STR("unit");
    } else {
        return ctype_to_c_name(arena, slop_type);
    }
}

int64_t expr_find_matching_paren(slop_string s, int64_t start) {
    {
        __auto_type len = ((int64_t)(string_len(s)));
        int64_t depth = 0;
        int64_t i = start;
        int64_t found = -1;
        while ((i < len) && (found < 0)) {
            {
                __auto_type c = strlib_char_at(s, ((int64_t)(i)));
                if (c == 40) {
                    depth = (depth + 1);
                } else if (c == 41) {
                    if (depth == 0) {
                        found = i;
                    } else {
                        depth = (depth - 1);
                    }
                } else {
                }
            }
            i = (i + 1);
        }
        if (found < 0) {
            return len;
        } else {
            return found;
        }
    }
}

slop_list_string expr_find_free_vars(context_TranspileContext* ctx, slop_list_string param_names, slop_list_types_SExpr_ptr body_items, int64_t start, slop_list_string pending) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type all_symbols = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        __auto_type free_vars = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        __auto_type len = ((int64_t)((body_items).len));
        int64_t i = start;
        while (i < len) {
            __auto_type _mv_585 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_585.has_value) {
                __auto_type expr = _mv_585.value;
                expr_collect_symbols_in_expr(ctx, (&all_symbols), pending, expr);
            } else if (!_mv_585.has_value) {
            }
            i = (i + 1);
        }
        {
            __auto_type sym_count = ((int64_t)((all_symbols).len));
            int64_t j = 0;
            while (j < sym_count) {
                __auto_type _mv_586 = ({ __auto_type _lst = all_symbols; size_t _idx = (size_t)j; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_586.has_value) {
                    __auto_type sym_name = _mv_586.value;
                    if (expr_is_free_var(ctx, param_names, pending, sym_name)) {
                        if (!(expr_list_contains_string(free_vars, sym_name))) {
                            ({ __auto_type _lst_p = &(free_vars); __auto_type _item = (sym_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        }
                    }
                } else if (!_mv_586.has_value) {
                }
                j = (j + 1);
            }
        }
        return free_vars;
    }
}

void expr_collect_symbols_in_expr(context_TranspileContext* ctx, slop_list_string* symbols, slop_list_string pending, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_587 = (*expr);
    switch (_mv_587.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_587.data.sym;
            {
                __auto_type name = sym.name;
                if (!(expr_is_special_keyword(name)) && !(expr_list_contains_string(pending, name))) {
                    ({ __auto_type _lst_p = &((*symbols)); __auto_type _item = (name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(ctx->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                }
            }
            break;
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_587.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if (len > 0) {
                    __auto_type _mv_588 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_588.has_value) {
                        __auto_type head = _mv_588.value;
                        __auto_type _mv_589 = (*head);
                        switch (_mv_589.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type head_sym = _mv_589.data.sym;
                                {
                                    __auto_type op = head_sym.name;
                                    if (string_eq(op, SLOP_STR("let"))) {
                                        expr_collect_symbols_in_let(ctx, symbols, pending, items);
                                    } else if (string_eq(op, SLOP_STR("fn"))) {
                                        expr_collect_nested_lambda_free_vars(ctx, symbols, pending, items);
                                    } else if (string_eq(op, SLOP_STR("match"))) {
                                        expr_collect_symbols_in_match(ctx, symbols, pending, items);
                                    } else if (string_eq(op, SLOP_STR("for")) || string_eq(op, SLOP_STR("for-each"))) {
                                        expr_collect_symbols_in_for(ctx, symbols, pending, items);
                                    } else if (string_eq(op, SLOP_STR("with-arena"))) {
                                        expr_collect_symbols_in_with_arena(ctx, symbols, pending, items);
                                    } else {
                                        expr_collect_symbols_in_list(ctx, symbols, pending, items, 0);
                                    }
                                }
                                break;
                            }
                            default: {
                                expr_collect_symbols_in_list(ctx, symbols, pending, items, 0);
                                break;
                            }
                        }
                    } else if (!_mv_588.has_value) {
                    }
                }
            }
            break;
        }
        default: {
            break;
        }
    }
}

void expr_collect_symbols_in_list(context_TranspileContext* ctx, slop_list_string* symbols, slop_list_string pending, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = start;
        while (i < len) {
            __auto_type _mv_590 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_590.has_value) {
                __auto_type item = _mv_590.value;
                expr_collect_symbols_in_expr(ctx, symbols, pending, item);
            } else if (!_mv_590.has_value) {
            }
            i = (i + 1);
        }
    }
}

void expr_collect_symbols_in_let(context_TranspileContext* ctx, slop_list_string* symbols, slop_list_string pending, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len >= 2) {
            __auto_type _mv_591 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_591.has_value) {
                __auto_type bindings_expr = _mv_591.value;
                {
                    __auto_type new_names = expr_extract_let_binding_names(arena, bindings_expr);
                    __auto_type updated_pending = expr_list_concat(arena, pending, new_names);
                    __auto_type _mv_592 = (*bindings_expr);
                    switch (_mv_592.tag) {
                        case types_SExpr_lst:
                        {
                            __auto_type bindings_lst = _mv_592.data.lst;
                            {
                                __auto_type bindings = bindings_lst.items;
                                __auto_type binding_count = ((int64_t)((bindings).len));
                                __auto_type i = 0;
                                while (i < binding_count) {
                                    __auto_type _mv_593 = ({ __auto_type _lst = bindings; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_593.has_value) {
                                        __auto_type binding = _mv_593.value;
                                        __auto_type _mv_594 = (*binding);
                                        switch (_mv_594.tag) {
                                            case types_SExpr_lst:
                                            {
                                                __auto_type bind_lst = _mv_594.data.lst;
                                                {
                                                    __auto_type bind_items = bind_lst.items;
                                                    if (((int64_t)((bind_items).len)) >= 2) {
                                                        {
                                                            __auto_type val_idx = ((expr_is_mut_binding(bind_items)) ? 2 : 1);
                                                            __auto_type _mv_595 = ({ __auto_type _lst = bind_items; size_t _idx = (size_t)val_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_595.has_value) {
                                                                __auto_type val_expr = _mv_595.value;
                                                                expr_collect_symbols_in_expr(ctx, symbols, pending, val_expr);
                                                            } else if (!_mv_595.has_value) {
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
                                    } else if (!_mv_593.has_value) {
                                    }
                                    i = (i + 1);
                                }
                            }
                            break;
                        }
                        default: {
                            break;
                        }
                    }
                    expr_collect_symbols_in_list(ctx, symbols, updated_pending, items, 2);
                }
            } else if (!_mv_591.has_value) {
            }
        }
    }
}

uint8_t expr_is_mut_binding(slop_list_types_SExpr_ptr items) {
    if (((int64_t)((items).len)) < 1) {
        return 0;
    } else {
        __auto_type _mv_596 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_596.has_value) {
            __auto_type first = _mv_596.value;
            __auto_type _mv_597 = (*first);
            switch (_mv_597.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_597.data.sym;
                    return string_eq(sym.name, SLOP_STR("mut"));
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_596.has_value) {
            return 0;
        }
        SLOP_UNREACHABLE();
    }
}

slop_list_string expr_extract_let_binding_names(slop_arena* arena, types_SExpr* bindings_expr) {
    SLOP_PRE(((bindings_expr != NULL)), "(!= bindings-expr nil)");
    {
        __auto_type names = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        __auto_type _mv_598 = (*bindings_expr);
        switch (_mv_598.tag) {
            case types_SExpr_lst:
            {
                __auto_type bindings_lst = _mv_598.data.lst;
                {
                    __auto_type bindings = bindings_lst.items;
                    __auto_type binding_count = ((int64_t)((bindings).len));
                    __auto_type i = 0;
                    while (i < binding_count) {
                        __auto_type _mv_599 = ({ __auto_type _lst = bindings; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_599.has_value) {
                            __auto_type binding = _mv_599.value;
                            __auto_type _mv_600 = (*binding);
                            switch (_mv_600.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type bind_lst = _mv_600.data.lst;
                                    {
                                        __auto_type bind_items = bind_lst.items;
                                        if (((int64_t)((bind_items).len)) >= 1) {
                                            {
                                                __auto_type name_idx = ((expr_is_mut_binding(bind_items)) ? 1 : 0);
                                                __auto_type _mv_601 = ({ __auto_type _lst = bind_items; size_t _idx = (size_t)name_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_601.has_value) {
                                                    __auto_type name_expr = _mv_601.value;
                                                    __auto_type _mv_602 = (*name_expr);
                                                    switch (_mv_602.tag) {
                                                        case types_SExpr_sym:
                                                        {
                                                            __auto_type sym = _mv_602.data.sym;
                                                            ({ __auto_type _lst_p = &(names); __auto_type _item = (sym.name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                            break;
                                                        }
                                                        default: {
                                                            break;
                                                        }
                                                    }
                                                } else if (!_mv_601.has_value) {
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
                        } else if (!_mv_599.has_value) {
                        }
                        i = (i + 1);
                    }
                }
                break;
            }
            default: {
                break;
            }
        }
        return names;
    }
}

void expr_collect_symbols_in_match(context_TranspileContext* ctx, slop_list_string* symbols, slop_list_string pending, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if (len >= 2) {
            __auto_type _mv_603 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_603.has_value) {
                __auto_type scrutinee = _mv_603.value;
                expr_collect_symbols_in_expr(ctx, symbols, pending, scrutinee);
            } else if (!_mv_603.has_value) {
            }
            {
                int64_t i = 2;
                while (i < len) {
                    __auto_type _mv_604 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_604.has_value) {
                        __auto_type clause = _mv_604.value;
                        __auto_type _mv_605 = (*clause);
                        switch (_mv_605.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type clause_lst = _mv_605.data.lst;
                                {
                                    __auto_type clause_items = clause_lst.items;
                                    expr_collect_symbols_in_list(ctx, symbols, pending, clause_items, 1);
                                }
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_604.has_value) {
                    }
                    i = (i + 1);
                }
            }
        }
    }
}

void expr_collect_symbols_in_for(context_TranspileContext* ctx, slop_list_string* symbols, slop_list_string pending, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len >= 2) {
            __auto_type _mv_606 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_606.has_value) {
                __auto_type binding = _mv_606.value;
                __auto_type _mv_607 = (*binding);
                switch (_mv_607.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type bind_lst = _mv_607.data.lst;
                        {
                            __auto_type bind_items = bind_lst.items;
                            expr_collect_symbols_in_list(ctx, symbols, pending, bind_items, 1);
                            {
                                __auto_type loop_var_pending = expr_extract_for_loop_var_pending(arena, pending, bind_items);
                                expr_collect_symbols_in_list(ctx, symbols, loop_var_pending, items, 2);
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_606.has_value) {
            }
        }
    }
}

slop_list_string expr_extract_for_loop_var_pending(slop_arena* arena, slop_list_string pending, slop_list_types_SExpr_ptr bind_items) {
    if (((int64_t)((bind_items).len)) < 1) {
        return pending;
    } else {
        __auto_type _mv_608 = ({ __auto_type _lst = bind_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_608.has_value) {
            __auto_type var_expr = _mv_608.value;
            __auto_type _mv_609 = (*var_expr);
            switch (_mv_609.tag) {
                case types_SExpr_sym:
                {
                    __auto_type var_sym = _mv_609.data.sym;
                    {
                        __auto_type result = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                        __auto_type var_name = var_sym.name;
                        __auto_type plen = ((int64_t)((pending).len));
                        __auto_type i = 0;
                        while (i < plen) {
                            __auto_type _mv_610 = ({ __auto_type _lst = pending; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_610.has_value) {
                                __auto_type s = _mv_610.value;
                                ({ __auto_type _lst_p = &(result); __auto_type _item = (s); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            } else if (!_mv_610.has_value) {
                            }
                            i = (i + 1);
                        }
                        ({ __auto_type _lst_p = &(result); __auto_type _item = (var_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        return result;
                    }
                }
                default: {
                    return pending;
                }
            }
        } else if (!_mv_608.has_value) {
            return pending;
        }
        SLOP_UNREACHABLE();
    }
}

void expr_collect_symbols_in_with_arena(context_TranspileContext* ctx, slop_list_string* symbols, slop_list_string pending, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len >= 3) {
            {
                __auto_type is_named = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type item1 = _mv.value; ({ __auto_type _mv = (*item1); uint8_t _mr = {0}; switch (_mv.tag) { case types_SExpr_sym: { __auto_type s1 = _mv.data.sym; _mr = string_eq(s1.name, SLOP_STR(":as")); break; } default: { _mr = 0; break; }  } _mr; }); }) : (0); });
                __auto_type arena_name = ((is_named) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type name_expr = _mv.value; ({ __auto_type _mv = (*name_expr); slop_string _mr = {0}; switch (_mv.tag) { case types_SExpr_sym: { __auto_type s2 = _mv.data.sym; _mr = s2.name; break; } default: { _mr = SLOP_STR("arena"); break; }  } _mr; }); }) : (SLOP_STR("arena")); }) : SLOP_STR("arena"));
                __auto_type size_idx = ((is_named) ? 3 : 1);
                __auto_type body_start = ((is_named) ? 4 : 2);
                __auto_type _mv_611 = ({ __auto_type _lst = items; size_t _idx = (size_t)size_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_611.has_value) {
                    __auto_type size_expr = _mv_611.value;
                    expr_collect_symbols_in_expr(ctx, symbols, pending, size_expr);
                } else if (!_mv_611.has_value) {
                }
                {
                    __auto_type updated_pending = expr_list_concat(arena, pending, ({ __auto_type tmp = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }); ({ __auto_type _lst_p = &(tmp); __auto_type _item = (arena_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); tmp; }));
                    expr_collect_symbols_in_list(ctx, symbols, updated_pending, items, body_start);
                }
            }
        }
    }
}

void expr_collect_nested_lambda_free_vars(context_TranspileContext* ctx, slop_list_string* symbols, slop_list_string pending, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len >= 2) {
            __auto_type _mv_612 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_612.has_value) {
                __auto_type params_expr = _mv_612.value;
                __auto_type _mv_613 = (*params_expr);
                switch (_mv_613.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type params_lst = _mv_613.data.lst;
                        {
                            __auto_type params = params_lst.items;
                            __auto_type param_names = expr_extract_param_names(arena, params);
                            __auto_type nested_pending = expr_list_concat(arena, pending, param_names);
                            expr_collect_symbols_in_list(ctx, symbols, nested_pending, items, 2);
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_612.has_value) {
            }
        }
    }
}

uint8_t expr_is_special_keyword(slop_string name) {
    return ((string_eq(name, SLOP_STR("let"))) || (string_eq(name, SLOP_STR("if"))) || (string_eq(name, SLOP_STR("cond"))) || (string_eq(name, SLOP_STR("match"))) || (string_eq(name, SLOP_STR("when"))) || (string_eq(name, SLOP_STR("while"))) || (string_eq(name, SLOP_STR("for"))) || (string_eq(name, SLOP_STR("for-each"))) || (string_eq(name, SLOP_STR("do"))) || (string_eq(name, SLOP_STR("set!"))) || (string_eq(name, SLOP_STR("deref"))) || (string_eq(name, SLOP_STR("cast"))) || (string_eq(name, SLOP_STR("fn"))) || (string_eq(name, SLOP_STR("true"))) || (string_eq(name, SLOP_STR("false"))) || (string_eq(name, SLOP_STR("nil"))) || (string_eq(name, SLOP_STR("none"))) || (string_eq(name, SLOP_STR("some"))) || (string_eq(name, SLOP_STR("ok"))) || (string_eq(name, SLOP_STR("error"))) || (string_eq(name, SLOP_STR("mut"))) || (string_eq(name, SLOP_STR("else"))) || (string_eq(name, SLOP_STR("and"))) || (string_eq(name, SLOP_STR("or"))) || (string_eq(name, SLOP_STR("not"))) || (string_eq(name, SLOP_STR("with-arena"))) || (string_eq(name, SLOP_STR(":as"))));
}

uint8_t expr_is_free_var(context_TranspileContext* ctx, slop_list_string param_names, slop_list_string pending, slop_string sym_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (expr_list_contains_string(param_names, sym_name)) {
        return 0;
    } else {
        if (expr_list_contains_string(pending, sym_name)) {
            return 1;
        } else {
            if (expr_is_builtin_op(sym_name)) {
                return 0;
            } else {
                __auto_type _mv_614 = context_ctx_lookup_func(ctx, sym_name);
                if (_mv_614.has_value) {
                    __auto_type _ = _mv_614.value;
                    return 0;
                } else if (!_mv_614.has_value) {
                    __auto_type _mv_615 = context_ctx_lookup_type(ctx, sym_name);
                    if (_mv_615.has_value) {
                        __auto_type _ = _mv_615.value;
                        return 0;
                    } else if (!_mv_615.has_value) {
                        __auto_type _mv_616 = context_ctx_lookup_var(ctx, sym_name);
                        if (_mv_616.has_value) {
                            __auto_type _ = _mv_616.value;
                            return 1;
                        } else if (!_mv_616.has_value) {
                            return 0;
                        }
                        SLOP_UNREACHABLE();
                    }
                    SLOP_UNREACHABLE();
                }
                SLOP_UNREACHABLE();
            }
        }
    }
}

uint8_t expr_is_builtin_op(slop_string name) {
    return ((string_eq(name, SLOP_STR("+"))) || (string_eq(name, SLOP_STR("-"))) || (string_eq(name, SLOP_STR("*"))) || (string_eq(name, SLOP_STR("/"))) || (string_eq(name, SLOP_STR("%"))) || (string_eq(name, SLOP_STR("=="))) || (string_eq(name, SLOP_STR("!="))) || (string_eq(name, SLOP_STR("<"))) || (string_eq(name, SLOP_STR(">"))) || (string_eq(name, SLOP_STR("<="))) || (string_eq(name, SLOP_STR(">="))) || (string_eq(name, SLOP_STR("@"))));
}

uint8_t expr_list_contains_string(slop_list_string lst, slop_string needle) {
    {
        __auto_type len = ((int64_t)((lst).len));
        int64_t i = 0;
        uint8_t found = 0;
        while ((i < len) && !(found)) {
            __auto_type _mv_617 = ({ __auto_type _lst = lst; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_617.has_value) {
                __auto_type s = _mv_617.value;
                if (string_eq(s, needle)) {
                    found = 1;
                }
            } else if (!_mv_617.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

slop_list_string expr_list_concat(slop_arena* arena, slop_list_string a, slop_list_string b) {
    {
        __auto_type result = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        __auto_type len_a = ((int64_t)((a).len));
        __auto_type len_b = ((int64_t)((b).len));
        int64_t i = 0;
        while (i < len_a) {
            __auto_type _mv_618 = ({ __auto_type _lst = a; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_618.has_value) {
                __auto_type s = _mv_618.value;
                ({ __auto_type _lst_p = &(result); __auto_type _item = (s); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            } else if (!_mv_618.has_value) {
            }
            i = (i + 1);
        }
        i = 0;
        while (i < len_b) {
            __auto_type _mv_619 = ({ __auto_type _lst = b; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_619.has_value) {
                __auto_type s = _mv_619.value;
                ({ __auto_type _lst_p = &(result); __auto_type _item = (s); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            } else if (!_mv_619.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_string expr_extract_first_type_arg(slop_arena* arena, slop_string slop_type, int64_t start) {
    {
        __auto_type len = ((int64_t)(string_len(slop_type)));
        int64_t depth = 0;
        int64_t end_pos = start;
        uint8_t found = 0;
        while ((end_pos < len) && !(found)) {
            {
                __auto_type c = strlib_char_at(slop_type, ((int64_t)(end_pos)));
                if (c == 40) {
                    depth = (depth + 1);
                    end_pos = (end_pos + 1);
                } else if (c == 41) {
                    if (depth == 0) {
                        found = 1;
                    } else {
                        depth = (depth - 1);
                        end_pos = (end_pos + 1);
                    }
                } else if ((c == 32) && (depth == 0)) {
                    found = 1;
                } else {
                    end_pos = (end_pos + 1);
                }
            }
        }
        if (end_pos > start) {
            return strlib_substring(arena, slop_type, ((int64_t)(start)), ((int64_t)((end_pos - start))));
        } else {
            return SLOP_STR("");
        }
    }
}

slop_string expr_extract_second_type_arg(slop_arena* arena, slop_string slop_type, int64_t start) {
    {
        __auto_type first_arg = expr_extract_first_type_arg(arena, slop_type, start);
        __auto_type first_len = string_len(first_arg);
        if (first_len == 0) {
            return SLOP_STR("");
        } else {
            return expr_extract_first_type_arg(arena, slop_type, (start + (((int64_t)(first_len)) + 1)));
        }
    }
}

slop_string expr_infer_result_ok_slop_type(context_TranspileContext* ctx, types_SExpr* scrutinee) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((scrutinee != NULL)), "(!= scrutinee nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type expr_type = expr_infer_expr_slop_type(ctx, scrutinee);
        {
            __auto_type resolved = (((string_len(expr_type) > 0)) ? expr_resolve_type_alias(ctx, expr_type) : SLOP_STR(""));
            if (strlib_starts_with(resolved, SLOP_STR("(Result "))) {
                return expr_extract_first_type_arg(arena, resolved, 8);
            } else {
                return SLOP_STR("");
            }
        }
    }
}

slop_string expr_infer_result_err_slop_type(context_TranspileContext* ctx, types_SExpr* scrutinee) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((scrutinee != NULL)), "(!= scrutinee nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type expr_type = expr_infer_expr_slop_type(ctx, scrutinee);
        {
            __auto_type resolved = (((string_len(expr_type) > 0)) ? expr_resolve_type_alias(ctx, expr_type) : SLOP_STR(""));
            if (strlib_starts_with(resolved, SLOP_STR("(Result "))) {
                return expr_extract_second_type_arg(arena, resolved, 8);
            } else {
                return SLOP_STR("");
            }
        }
    }
}

slop_string expr_infer_collection_element_slop_type(context_TranspileContext* ctx, types_SExpr* coll_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((coll_expr != NULL)), "(!= coll-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_620 = (*coll_expr);
        switch (_mv_620.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_620.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) < 1) {
                        return SLOP_STR("");
                    } else {
                        __auto_type _mv_621 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_621.has_value) {
                            __auto_type head = _mv_621.value;
                            __auto_type _mv_622 = (*head);
                            switch (_mv_622.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_622.data.sym;
                                    {
                                        __auto_type op = sym.name;
                                        if (string_eq(op, SLOP_STR("map-keys"))) {
                                            if (((int64_t)((items).len)) < 2) {
                                                return SLOP_STR("");
                                            } else {
                                                __auto_type _mv_623 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_623.has_value) {
                                                    __auto_type map_expr = _mv_623.value;
                                                    {
                                                        __auto_type map_slop_type = expr_infer_expr_slop_type(ctx, map_expr);
                                                        if (string_len(map_slop_type) > 0) {
                                                            {
                                                                __auto_type resolved = expr_resolve_type_alias(ctx, map_slop_type);
                                                                return expr_extract_map_key_from_slop_type(arena, resolved);
                                                            }
                                                        } else {
                                                            return SLOP_STR("");
                                                        }
                                                    }
                                                } else if (!_mv_623.has_value) {
                                                    return SLOP_STR("");
                                                }
                                                SLOP_UNREACHABLE();
                                            }
                                        } else if (string_eq(op, SLOP_STR("set-elements"))) {
                                            if (((int64_t)((items).len)) < 2) {
                                                return SLOP_STR("");
                                            } else {
                                                __auto_type _mv_624 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_624.has_value) {
                                                    __auto_type set_expr = _mv_624.value;
                                                    {
                                                        __auto_type set_slop_type = expr_infer_expr_slop_type(ctx, set_expr);
                                                        if (string_len(set_slop_type) > 0) {
                                                            {
                                                                __auto_type resolved = expr_resolve_type_alias(ctx, set_slop_type);
                                                                return expr_extract_set_elem_from_slop_type(arena, resolved);
                                                            }
                                                        } else {
                                                            return SLOP_STR("");
                                                        }
                                                    }
                                                } else if (!_mv_624.has_value) {
                                                    return SLOP_STR("");
                                                }
                                                SLOP_UNREACHABLE();
                                            }
                                        } else if (string_eq(op, SLOP_STR("map-values"))) {
                                            if (((int64_t)((items).len)) < 2) {
                                                return SLOP_STR("");
                                            } else {
                                                __auto_type _mv_625 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_625.has_value) {
                                                    __auto_type map_expr = _mv_625.value;
                                                    {
                                                        __auto_type map_slop_type = expr_infer_expr_slop_type(ctx, map_expr);
                                                        if (string_len(map_slop_type) > 0) {
                                                            {
                                                                __auto_type resolved = expr_resolve_type_alias(ctx, map_slop_type);
                                                                return expr_extract_map_value_from_slop_type(arena, resolved);
                                                            }
                                                        } else {
                                                            return SLOP_STR("");
                                                        }
                                                    }
                                                } else if (!_mv_625.has_value) {
                                                    return SLOP_STR("");
                                                }
                                                SLOP_UNREACHABLE();
                                            }
                                        } else {
                                            return expr_infer_elem_from_type(ctx, coll_expr);
                                        }
                                    }
                                }
                                default: {
                                    return expr_infer_elem_from_type(ctx, coll_expr);
                                }
                            }
                        } else if (!_mv_621.has_value) {
                            return SLOP_STR("");
                        }
                        SLOP_UNREACHABLE();
                    }
                }
            }
            default: {
                return expr_infer_elem_from_type(ctx, coll_expr);
            }
        }
    }
}

slop_string expr_infer_elem_from_type(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type slop_type = expr_infer_expr_slop_type(ctx, expr);
        if (string_len(slop_type) == 0) {
            return SLOP_STR("");
        } else {
            {
                __auto_type resolved_type = expr_resolve_type_alias(ctx, slop_type);
                if (strlib_starts_with(resolved_type, SLOP_STR("(List "))) {
                    {
                        __auto_type elem_len = ((string_len(resolved_type) - 6) - 1);
                        if (elem_len > 0) {
                            return strlib_substring(arena, resolved_type, 6, ((int64_t)(elem_len)));
                        } else {
                            return SLOP_STR("");
                        }
                    }
                } else if (expr_is_set_type(resolved_type)) {
                    return expr_extract_set_elem_from_slop_type(arena, resolved_type);
                } else if (expr_is_map_type(resolved_type)) {
                    return expr_extract_map_key_from_slop_type(arena, resolved_type);
                } else {
                    return SLOP_STR("");
                }
            }
        }
    }
}

