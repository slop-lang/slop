#ifndef SLOP_expr_H
#define SLOP_expr_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_types.h"
#include "slop_context.h"
#include "slop_ctype.h"
#include "slop_strlib.h"

#ifndef SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
SLOP_LIST_DEFINE(types_SExpr*, slop_list_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

slop_string expr_escape_c_string(context_TranspileContext* ctx, slop_string s);
slop_string expr_wrap_arena_alloc_checked(context_TranspileContext* ctx, slop_string alloc_expr);
uint8_t expr_is_binop(slop_string op);
uint8_t expr_is_comparison_op(slop_string op);
uint8_t expr_is_unop(slop_string op);
slop_option_string expr_extract_symbol_name(types_SExpr* expr);
slop_string expr_transpile_literal(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_transpile_symbol(context_TranspileContext* ctx, slop_string name);
slop_string expr_get_prefixed_enum_value(context_TranspileContext* ctx, slop_string enum_name, slop_string variant_name);
slop_string expr_binop_to_c(slop_string op);
slop_string expr_transpile_binop(context_TranspileContext* ctx, slop_string op, slop_string left, slop_string right);
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
slop_string expr_extract_fn_return_c_type(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_extract_fn_arg_c_types(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_parse_fn_args_to_c_types(context_TranspileContext* ctx, slop_string args_str);
slop_string expr_closure_type_to_c(context_TranspileContext* ctx, slop_string slop_type);
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
slop_string expr_extract_map_value_from_slop_type(slop_arena* arena, slop_string slop_type);
slop_string expr_slop_value_type_to_c_type(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_get_var_name_from_expr(types_SExpr* expr);
slop_string expr_extract_map_key_from_slop_type(slop_arena* arena, slop_string slop_type);
slop_string expr_resolve_type_alias(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_infer_expr_slop_type(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_infer_map_key_c_type_from_slop_type(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_infer_set_elem_c_type_from_slop_type(context_TranspileContext* ctx, slop_string slop_type);
slop_string expr_extract_map_value_from_inferred(context_TranspileContext* ctx, types_SExpr* map_expr);
slop_string expr_extract_list_elem_from_inferred(context_TranspileContext* ctx, types_SExpr* list_expr);
slop_string expr_infer_map_key_c_type(context_TranspileContext* ctx, types_SExpr* map_expr);
uint8_t expr_is_set_type(slop_string slop_type);
uint8_t expr_is_map_type(slop_string slop_type);
slop_string expr_extract_set_elem_from_slop_type(slop_arena* arena, slop_string slop_type);
slop_string expr_infer_set_elem_c_type(context_TranspileContext* ctx, types_SExpr* set_expr);
slop_string expr_compound_slop_type_to_id(slop_arena* arena, slop_string slop_type);
slop_string expr_slop_value_type_to_option_id(slop_arena* arena, slop_string slop_type);
slop_string expr_infer_map_value_option_type(context_TranspileContext* ctx, types_SExpr* map_expr);
slop_string expr_option_type_to_value_c_type(slop_arena* arena, slop_string option_type);
slop_string expr_infer_option_inner_slop_type(context_TranspileContext* ctx, types_SExpr* scrutinee);
slop_string expr_fix_ternary_none(context_TranspileContext* ctx, slop_string other_branch, slop_string this_branch);
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
slop_string expr_build_union_match_expr(context_TranspileContext* ctx, types_SExpr* scrutinee, slop_string scrutinee_c, slop_list_types_SExpr_ptr items);
slop_string expr_typed_none(context_TranspileContext* ctx, slop_string result_type, slop_string body);
slop_string expr_typed_none_arg(context_TranspileContext* ctx, slop_string expected_type, slop_string arg_c);
slop_string expr_wrap_fn_ref_as_closure(context_TranspileContext* ctx, slop_string expected_type, slop_string arg_c, types_SExpr* arg_expr);
slop_string expr_generate_fn_trampoline(context_TranspileContext* ctx, slop_string fn_c_name, context_FuncEntry func_entry);
slop_string expr_build_union_case_expr(context_TranspileContext* ctx, slop_arena* arena, slop_string cases, types_SExpr* scrutinee, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, slop_string result_type);
slop_string expr_build_ternary_match_expr(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_let_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void expr_register_let_binding_in_context(context_TranspileContext* ctx, types_SExpr* binding);
slop_string expr_transpile_binding_expr(context_TranspileContext* ctx, types_SExpr* binding);
uint8_t expr_binding_has_mut(slop_list_types_SExpr_ptr items);
slop_string expr_transpile_typed_init(context_TranspileContext* ctx, types_SExpr* init_expr, slop_string target_type);
slop_string expr_transpile_while_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_do_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_when_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_set_expr(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_get_arena_for_list_push_expr(context_TranspileContext* ctx, types_SExpr* list_expr, slop_string list_c);
slop_string expr_get_arena_from_field_access(context_TranspileContext* ctx, types_SExpr* expr);
slop_string expr_get_arena_from_base(context_TranspileContext* ctx, types_SExpr* base_expr);
slop_string expr_get_arena_for_list_push(context_TranspileContext* ctx, slop_string list_c);
uint8_t expr_is_ptr_to_ptr_map(context_TranspileContext* ctx, types_SExpr* expr);
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
slop_string expr_wrap_map_key_as_ptr(context_TranspileContext* ctx, slop_string key_c, types_SExpr* key_expr, types_SExpr* container_expr);
slop_string expr_transpile_map_put(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_map_get(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_string expr_transpile_map_has(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
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

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif


#endif
