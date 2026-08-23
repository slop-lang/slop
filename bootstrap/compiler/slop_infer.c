#include "../runtime/slop_runtime.h"
#include "slop_infer.h"

uint8_t infer_string_contains_char(slop_string s, int64_t c);
int64_t infer_string_index_of(slop_string s, int64_t c);
slop_string infer_string_substring(slop_arena* arena, slop_string s, int64_t start, int64_t end);
uint8_t infer_is_qualified_threading_builtin(slop_string op);
uint8_t infer_is_bare_threading_builtin(slop_string op);
uint8_t infer_is_threading_module(slop_string mod_name);
uint8_t infer_is_send_op(slop_string op);
uint8_t infer_is_recv_op(slop_string op);
uint8_t infer_is_spawn_op(slop_string op);
uint8_t infer_is_join_op(slop_string op);
uint8_t infer_is_chan_buffered_op(slop_string op);
uint8_t infer_is_chan_op(slop_string op);
types_ResolvedType* infer_infer_threading_builtin(env_TypeEnv* env, slop_string op, types_SExpr* expr, slop_list_types_SExpr_ptr items, int64_t len, int64_t line, int64_t col);
uint8_t infer_has_type_params(types_FnSignature* sig);
slop_option_types_ResolvedType_ptr infer_find_binding(slop_list_string bind_names, slop_list_types_ResolvedType_ptr bind_types, slop_string name);
void infer_unify_types(slop_arena* arena, types_ResolvedType* formal, types_ResolvedType* actual, slop_list_string bind_names, slop_list_types_ResolvedType_ptr bind_types);
types_ResolvedType* infer_substitute_type_vars(slop_arena* arena, types_ResolvedType* t, slop_list_string bind_names, slop_list_types_ResolvedType_ptr bind_types);
types_ResolvedType* infer_infer_generic_call(env_TypeEnv* env, types_FnSignature* sig, types_SExpr* expr, int64_t line, int64_t col);
uint8_t infer_is_unwrappable_container(types_ResolvedType* t);
uint8_t infer_container_inners_equal(types_ResolvedType* a, types_ResolvedType* b);
uint8_t infer_types_equal(types_ResolvedType* a, types_ResolvedType* b);
uint8_t infer_types_compatible_with_range(types_ResolvedType* a, types_ResolvedType* b);
uint8_t infer_type_is_null_pointer(types_ResolvedType* t);
types_ResolvedType* infer_unify_branch_types(env_TypeEnv* env, types_ResolvedType* a, types_ResolvedType* b, int64_t line, int64_t col);
void infer_sexpr_set_resolved_type(types_SExpr* expr, types_ResolvedType* t);
types_ResolvedType* infer_infer_expr(env_TypeEnv* env, types_SExpr* expr);
types_ResolvedType* infer_infer_expr_inner(env_TypeEnv* env, types_SExpr* expr);
types_ResolvedType* infer_infer_list_expr(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst);
types_ResolvedType* infer_infer_special_form(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst, slop_string op);
void infer_check_fn_call_args(env_TypeEnv* env, types_FnSignature* sig, types_SExpr* expr, int64_t line, int64_t col);
void infer_check_single_arg(env_TypeEnv* env, types_FnSignature* sig, types_SExpr* expr, int64_t arg_idx, int64_t line, int64_t col);
uint8_t infer_is_assignable_list_target(types_SExpr* expr);
void infer_check_list_target(env_TypeEnv* env, slop_string op, types_SExpr* expr, int64_t line, int64_t col);
void infer_check_builtin_args(env_TypeEnv* env, slop_string op, int64_t expected, int64_t actual, int64_t line, int64_t col);
types_ResolvedType* infer_resolve_alias_chain(types_ResolvedType* t);
void infer_check_option_predicate_arg(env_TypeEnv* env, slop_string op, slop_list_types_SExpr_ptr items, int64_t len, int64_t line, int64_t col);
void infer_infer_builtin_args(env_TypeEnv* env, types_SExpr* expr);
void infer_infer_body_exprs(env_TypeEnv* env, types_SExpr* expr, int64_t start_idx);
types_ResolvedType* infer_infer_field_access(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst, int64_t line, int64_t col);
types_ResolvedType* infer_check_field_exists(env_TypeEnv* env, types_ResolvedType* obj_type, slop_string field_name, int64_t line, int64_t col);
types_ResolvedType* infer_infer_cond_expr(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst);
void infer_bind_match_pattern(env_TypeEnv* env, types_ResolvedType* scrutinee_type, types_SExpr* pattern);
slop_string infer_match_pattern_head(types_SExpr* pattern);
uint8_t infer_is_wildcard_head(slop_string head);
uint8_t infer_string_list_contains(slop_list_string names, slop_string name);
slop_list_string infer_match_expected_variants(slop_arena* arena, types_ResolvedType* scrutinee_type);
void infer_check_match_exhaustive(env_TypeEnv* env, types_ResolvedType* scrutinee_type, slop_list_string covered, uint8_t has_wildcard, int64_t line, int64_t col);
types_ResolvedType* infer_infer_match_expr(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst);
void infer_check_return_type(env_TypeEnv* env, types_SExpr* fn_form, slop_string fn_name, types_ResolvedType* inferred_type, int64_t fn_line, int64_t fn_col);
void infer_check_spec_return_type(env_TypeEnv* env, types_SExpr* spec_form, slop_string fn_name, types_ResolvedType* inferred_type, int64_t fn_line, int64_t fn_col);
void infer_check_spec_body_return(env_TypeEnv* env, types_SExpr* spec_body, slop_string fn_name, types_ResolvedType* inferred_type, int64_t fn_line, int64_t fn_col);
uint8_t infer_checker_is_primitive_type(slop_string name);
uint8_t infer_is_integer_type(slop_string name);
void infer_check_return_expr(env_TypeEnv* env, types_SExpr* ret_expr, slop_string fn_name, types_ResolvedType* inferred_type, int64_t fn_line, int64_t fn_col);
void infer_bind_param_from_form(env_TypeEnv* env, types_SExpr* param_form);
types_ResolvedType* infer_get_param_type_from_form(env_TypeEnv* env, types_SExpr* param_form);
types_ResolvedType* infer_resolve_complex_type_expr(env_TypeEnv* env, types_SExpr* type_expr);
types_ResolvedType* infer_resolve_option_inner_type(env_TypeEnv* env, types_SExpr* type_expr);
types_ResolvedType* infer_resolve_ptr_inner_type(env_TypeEnv* env, types_SExpr* type_expr);
types_ResolvedType* infer_resolve_type_lenient(env_TypeEnv* env, slop_string type_name);
types_ResolvedType* infer_resolve_simple_type(env_TypeEnv* env, slop_string type_name);
void infer_bind_let_binding(env_TypeEnv* env, types_SExpr* binding_form);
types_ResolvedType* infer_infer_let_expr(env_TypeEnv* env, types_SExpr* expr);
types_ResolvedType* infer_infer_with_arena_expr(env_TypeEnv* env, types_SExpr* expr);
slop_string infer_get_fn_name(types_SExpr* fn_form);
types_ResolvedType* infer_resolve_hole_type(env_TypeEnv* env, slop_list_types_SExpr_ptr items, int64_t len);
slop_string infer_get_hole_prompt(slop_list_types_SExpr_ptr items, int64_t len);
int64_t infer_find_last_body_idx(slop_list_types_SExpr_ptr items);
uint8_t infer_is_c_name_related(slop_list_types_SExpr_ptr items, int64_t idx);
uint8_t infer_is_annotation_expr(types_SExpr* expr);
uint8_t infer_is_checkable_annotation(types_SExpr* expr);
types_ResolvedType* infer_infer_fn_body(env_TypeEnv* env, types_SExpr* fn_form);
void infer_check_match_patterns(env_TypeEnv* env, types_ResolvedType* scrutinee_type, slop_list_types_SExpr_ptr patterns);

uint8_t infer_string_contains_char(slop_string s, int64_t c) {
    {
        __auto_type len = ((int64_t)(s.len));
        __auto_type data = s.data;
        uint8_t found = 0;
        for (int64_t i = 0; i < len; i++) {
            if (!(found) && (((int64_t)(data[i])) == c)) {
                found = 1;
            }
        }
        return found;
    }
}

int64_t infer_string_index_of(slop_string s, int64_t c) {
    {
        __auto_type len = ((int64_t)(s.len));
        __auto_type data = s.data;
        int64_t result = -1;
        for (int64_t i = 0; i < len; i++) {
            if ((result == -1) && (((int64_t)(data[i])) == c)) {
                result = i;
            }
        }
        return result;
    }
}

slop_string infer_string_substring(slop_arena* arena, slop_string s, int64_t start, int64_t end) {
    {
        __auto_type s_len = ((int64_t)(s.len));
        __auto_type actual_end = (((end < s_len)) ? end : s_len);
        __auto_type actual_start = (((start < 0)) ? 0 : start);
        __auto_type new_len = (actual_end - actual_start);
        if (new_len <= 0) {
            return (slop_string){.len = 0, .data = ((uint8_t*)(SLOP_STR("").data))};
        } else {
            {
                __auto_type buf = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (new_len + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
                __auto_type src = s.data;
                for (int64_t i = 0; i < new_len; i++) {
                    buf[i] = src[(actual_start + i)];
                }
                buf[new_len] = 0;
                return (slop_string){.len = new_len, .data = buf};
            }
        }
    }
}

uint8_t infer_is_qualified_threading_builtin(slop_string op) {
    if (strlib_ends_with(op, SLOP_STR(":send"))) {
        return 1;
    } else if (strlib_ends_with(op, SLOP_STR(":recv"))) {
        return 1;
    } else if (strlib_ends_with(op, SLOP_STR(":spawn"))) {
        return 1;
    } else if (strlib_ends_with(op, SLOP_STR(":join"))) {
        return 1;
    } else if (strlib_ends_with(op, SLOP_STR(":chan-buffered"))) {
        return 1;
    } else if (strlib_ends_with(op, SLOP_STR(":chan"))) {
        return 1;
    } else {
        return 0;
    }
}

uint8_t infer_is_bare_threading_builtin(slop_string op) {
    if (string_eq(op, SLOP_STR("send"))) {
        return 1;
    } else if (string_eq(op, SLOP_STR("recv"))) {
        return 1;
    } else if (string_eq(op, SLOP_STR("spawn"))) {
        return 1;
    } else if (string_eq(op, SLOP_STR("join"))) {
        return 1;
    } else if (string_eq(op, SLOP_STR("chan-buffered"))) {
        return 1;
    } else if (string_eq(op, SLOP_STR("chan"))) {
        return 1;
    } else {
        return 0;
    }
}

uint8_t infer_is_threading_module(slop_string mod_name) {
    return string_eq(mod_name, SLOP_STR("thread"));
}

uint8_t infer_is_send_op(slop_string op) {
    return (string_eq(op, SLOP_STR("send")) || strlib_ends_with(op, SLOP_STR(":send")));
}

uint8_t infer_is_recv_op(slop_string op) {
    return (string_eq(op, SLOP_STR("recv")) || strlib_ends_with(op, SLOP_STR(":recv")));
}

uint8_t infer_is_spawn_op(slop_string op) {
    return (string_eq(op, SLOP_STR("spawn")) || strlib_ends_with(op, SLOP_STR(":spawn")));
}

uint8_t infer_is_join_op(slop_string op) {
    return (string_eq(op, SLOP_STR("join")) || strlib_ends_with(op, SLOP_STR(":join")));
}

uint8_t infer_is_chan_buffered_op(slop_string op) {
    return (string_eq(op, SLOP_STR("chan-buffered")) || strlib_ends_with(op, SLOP_STR(":chan-buffered")));
}

uint8_t infer_is_chan_op(slop_string op) {
    return (string_eq(op, SLOP_STR("chan")) || strlib_ends_with(op, SLOP_STR(":chan")));
}

types_ResolvedType* infer_infer_threading_builtin(env_TypeEnv* env, slop_string op, types_SExpr* expr, slop_list_types_SExpr_ptr items, int64_t len, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    infer_infer_builtin_args(env, expr);
    if (infer_is_send_op(op)) {
        infer_check_builtin_args(env, SLOP_STR("send"), 2, (len - 1), line, col);
        return env_env_make_result_type(env);
    } else if (infer_is_recv_op(op)) {
        infer_check_builtin_args(env, SLOP_STR("recv"), 1, (len - 1), line, col);
        return env_env_make_result_type(env);
    } else if (infer_is_spawn_op(op)) {
        infer_check_builtin_args(env, SLOP_STR("spawn"), 2, (len - 1), line, col);
        return env_env_make_ptr_type(env, env_env_get_generic_type(env));
    } else if (infer_is_join_op(op)) {
        infer_check_builtin_args(env, SLOP_STR("join"), 1, (len - 1), line, col);
        return env_env_get_generic_type(env);
    } else if (infer_is_chan_buffered_op(op)) {
        infer_check_builtin_args(env, SLOP_STR("chan-buffered"), 3, (len - 1), line, col);
        {
            __auto_type arena = env_env_arena(env);
            __auto_type elem_type = (((len >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type type_arg = _mv.value; ({ __auto_type type_name = parser_sexpr_get_symbol_name(type_arg); ({ __auto_type _mv = env_env_lookup_type(env, type_name); _mv.has_value ? ({ __auto_type t = _mv.value; t; }) : (NULL); }); }); }) : (NULL); }) : NULL);
            __auto_type chan_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_chan, SLOP_STR("Chan"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_chan_int*"));
            if (elem_type != NULL) {
                types_resolved_type_set_inner(chan_type, elem_type);
            }
            return env_env_make_ptr_type(env, chan_type);
        }
    } else if (infer_is_chan_op(op)) {
        infer_check_builtin_args(env, SLOP_STR("chan"), 2, (len - 1), line, col);
        {
            __auto_type arena = env_env_arena(env);
            __auto_type elem_type = (((len >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type type_arg = _mv.value; ({ __auto_type type_name = parser_sexpr_get_symbol_name(type_arg); ({ __auto_type _mv = env_env_lookup_type(env, type_name); _mv.has_value ? ({ __auto_type t = _mv.value; t; }) : (NULL); }); }); }) : (NULL); }) : NULL);
            __auto_type chan_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_chan, SLOP_STR("Chan"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_chan_int*"));
            if (elem_type != NULL) {
                types_resolved_type_set_inner(chan_type, elem_type);
            }
            return env_env_make_ptr_type(env, chan_type);
        }
    } else {
        infer_check_builtin_args(env, SLOP_STR("chan-buffered"), 3, (len - 1), line, col);
        return env_env_make_ptr_type(env, env_env_get_generic_type(env));
    }
}

uint8_t infer_has_type_params(types_FnSignature* sig) {
    SLOP_PRE(((sig != NULL)), "(!= sig nil)");
    return (((int64_t)(((*sig).type_params).len)) > 0);
}

slop_option_types_ResolvedType_ptr infer_find_binding(slop_list_string bind_names, slop_list_types_ResolvedType_ptr bind_types, slop_string name) {
    {
        __auto_type len = ((int64_t)((bind_names).len));
        slop_option_types_ResolvedType_ptr found = (slop_option_types_ResolvedType_ptr){.has_value = false};
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_1648 = ({ __auto_type _lst = bind_names; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1648.has_value) {
                __auto_type bn = _mv_1648.value;
                if (string_eq(bn, name)) {
                    __auto_type _mv_1649 = ({ __auto_type _lst = bind_types; size_t _idx = (size_t)i; slop_option_types_ResolvedType_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1649.has_value) {
                        __auto_type bt = _mv_1649.value;
                        found = (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = bt};
                    } else if (!_mv_1649.has_value) {
                    }
                }
            } else if (!_mv_1648.has_value) {
            }
        }
        return found;
    }
}

void infer_unify_types(slop_arena* arena, types_ResolvedType* formal, types_ResolvedType* actual, slop_list_string bind_names, slop_list_types_ResolvedType_ptr bind_types) {
    SLOP_PRE(((formal != NULL)), "(!= formal nil)");
    SLOP_PRE(((actual != NULL)), "(!= actual nil)");
    {
        __auto_type f_kind = (*formal).kind;
        if (f_kind == types_ResolvedTypeKind_rk_typevar) {
            {
                __auto_type tv_name = (*formal).name;
                __auto_type _mv_1650 = infer_find_binding(bind_names, bind_types, tv_name);
                if (_mv_1650.has_value) {
                    __auto_type existing = _mv_1650.value;
                } else if (!_mv_1650.has_value) {
                    ({ __auto_type _lst_p = &(bind_names); __auto_type _item = (tv_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(bind_types); __auto_type _item = (actual); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                }
            }
        } else if (f_kind == types_ResolvedTypeKind_rk_ptr) {
            if ((*actual).kind == types_ResolvedTypeKind_rk_ptr) {
                __auto_type _mv_1651 = (*formal).inner_type;
                if (_mv_1651.has_value) {
                    __auto_type f_inner = _mv_1651.value;
                    __auto_type _mv_1652 = (*actual).inner_type;
                    if (_mv_1652.has_value) {
                        __auto_type a_inner = _mv_1652.value;
                        infer_unify_types(arena, f_inner, a_inner, bind_names, bind_types);
                    } else if (!_mv_1652.has_value) {
                    }
                } else if (!_mv_1651.has_value) {
                }
            }
        } else if (f_kind == types_ResolvedTypeKind_rk_chan) {
            if ((*actual).kind == types_ResolvedTypeKind_rk_chan) {
                __auto_type _mv_1653 = (*formal).inner_type;
                if (_mv_1653.has_value) {
                    __auto_type f_inner = _mv_1653.value;
                    __auto_type _mv_1654 = (*actual).inner_type;
                    if (_mv_1654.has_value) {
                        __auto_type a_inner = _mv_1654.value;
                        infer_unify_types(arena, f_inner, a_inner, bind_names, bind_types);
                    } else if (!_mv_1654.has_value) {
                    }
                } else if (!_mv_1653.has_value) {
                }
            }
        } else if (f_kind == types_ResolvedTypeKind_rk_thread) {
            if ((*actual).kind == types_ResolvedTypeKind_rk_thread) {
                __auto_type _mv_1655 = (*formal).inner_type;
                if (_mv_1655.has_value) {
                    __auto_type f_inner = _mv_1655.value;
                    __auto_type _mv_1656 = (*actual).inner_type;
                    if (_mv_1656.has_value) {
                        __auto_type a_inner = _mv_1656.value;
                        infer_unify_types(arena, f_inner, a_inner, bind_names, bind_types);
                    } else if (!_mv_1656.has_value) {
                    }
                } else if (!_mv_1655.has_value) {
                }
            }
        } else if (f_kind == types_ResolvedTypeKind_rk_list) {
            if ((*actual).kind == types_ResolvedTypeKind_rk_list) {
                __auto_type _mv_1657 = (*formal).inner_type;
                if (_mv_1657.has_value) {
                    __auto_type f_inner = _mv_1657.value;
                    __auto_type _mv_1658 = (*actual).inner_type;
                    if (_mv_1658.has_value) {
                        __auto_type a_inner = _mv_1658.value;
                        infer_unify_types(arena, f_inner, a_inner, bind_names, bind_types);
                    } else if (!_mv_1658.has_value) {
                    }
                } else if (!_mv_1657.has_value) {
                }
            }
        } else if (f_kind == types_ResolvedTypeKind_rk_option) {
            if ((*actual).kind == types_ResolvedTypeKind_rk_option) {
                __auto_type _mv_1659 = (*formal).inner_type;
                if (_mv_1659.has_value) {
                    __auto_type f_inner = _mv_1659.value;
                    __auto_type _mv_1660 = (*actual).inner_type;
                    if (_mv_1660.has_value) {
                        __auto_type a_inner = _mv_1660.value;
                        infer_unify_types(arena, f_inner, a_inner, bind_names, bind_types);
                    } else if (!_mv_1660.has_value) {
                    }
                } else if (!_mv_1659.has_value) {
                }
            }
        } else if (f_kind == types_ResolvedTypeKind_rk_result) {
            if ((*actual).kind == types_ResolvedTypeKind_rk_result) {
                __auto_type _mv_1661 = (*formal).inner_type;
                if (_mv_1661.has_value) {
                    __auto_type f_inner = _mv_1661.value;
                    __auto_type _mv_1662 = (*actual).inner_type;
                    if (_mv_1662.has_value) {
                        __auto_type a_inner = _mv_1662.value;
                        infer_unify_types(arena, f_inner, a_inner, bind_names, bind_types);
                    } else if (!_mv_1662.has_value) {
                    }
                } else if (!_mv_1661.has_value) {
                }
                __auto_type _mv_1663 = (*formal).inner_type2;
                if (_mv_1663.has_value) {
                    __auto_type f_inner2 = _mv_1663.value;
                    __auto_type _mv_1664 = (*actual).inner_type2;
                    if (_mv_1664.has_value) {
                        __auto_type a_inner2 = _mv_1664.value;
                        infer_unify_types(arena, f_inner2, a_inner2, bind_names, bind_types);
                    } else if (!_mv_1664.has_value) {
                    }
                } else if (!_mv_1663.has_value) {
                }
            }
        } else {
        }
    }
}

types_ResolvedType* infer_substitute_type_vars(slop_arena* arena, types_ResolvedType* t, slop_list_string bind_names, slop_list_types_ResolvedType_ptr bind_types) {
    SLOP_PRE(((t != NULL)), "(!= t nil)");
    {
        __auto_type kind = (*t).kind;
        if (kind == types_ResolvedTypeKind_rk_typevar) {
            {
                __auto_type tv_name = (*t).name;
                __auto_type _mv_1665 = infer_find_binding(bind_names, bind_types, tv_name);
                if (_mv_1665.has_value) {
                    __auto_type bound = _mv_1665.value;
                    return bound;
                } else if (!_mv_1665.has_value) {
                    return t;
                }
                SLOP_UNREACHABLE();
            }
        } else if (kind == types_ResolvedTypeKind_rk_ptr) {
            __auto_type _mv_1666 = (*t).inner_type;
            if (_mv_1666.has_value) {
                __auto_type inner = _mv_1666.value;
                {
                    __auto_type new_inner = infer_substitute_type_vars(arena, inner, bind_names, bind_types);
                    __auto_type inner_name = (*new_inner).name;
                    __auto_type ptr_name = string_concat(arena, SLOP_STR("Ptr_"), inner_name);
                    __auto_type new_ptr = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_ptr, ptr_name, ((slop_option_string){.has_value = false}), SLOP_STR("void*"));
                    types_resolved_type_set_inner(new_ptr, new_inner);
                    return new_ptr;
                }
            } else if (!_mv_1666.has_value) {
                return t;
            }
            SLOP_UNREACHABLE();
        } else if (kind == types_ResolvedTypeKind_rk_chan) {
            __auto_type _mv_1667 = (*t).inner_type;
            if (_mv_1667.has_value) {
                __auto_type inner = _mv_1667.value;
                {
                    __auto_type new_inner = infer_substitute_type_vars(arena, inner, bind_names, bind_types);
                    __auto_type new_chan = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_chan, SLOP_STR("Chan"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_chan_int*"));
                    types_resolved_type_set_inner(new_chan, new_inner);
                    return new_chan;
                }
            } else if (!_mv_1667.has_value) {
                return t;
            }
            SLOP_UNREACHABLE();
        } else if (kind == types_ResolvedTypeKind_rk_thread) {
            __auto_type _mv_1668 = (*t).inner_type;
            if (_mv_1668.has_value) {
                __auto_type inner = _mv_1668.value;
                {
                    __auto_type new_inner = infer_substitute_type_vars(arena, inner, bind_names, bind_types);
                    __auto_type new_thread = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_thread, SLOP_STR("Thread"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_thread_int*"));
                    types_resolved_type_set_inner(new_thread, new_inner);
                    return new_thread;
                }
            } else if (!_mv_1668.has_value) {
                return t;
            }
            SLOP_UNREACHABLE();
        } else if (kind == types_ResolvedTypeKind_rk_list) {
            __auto_type _mv_1669 = (*t).inner_type;
            if (_mv_1669.has_value) {
                __auto_type inner = _mv_1669.value;
                {
                    __auto_type new_inner = infer_substitute_type_vars(arena, inner, bind_names, bind_types);
                    __auto_type new_list = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_list, SLOP_STR("List"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_list_t*"));
                    types_resolved_type_set_inner(new_list, new_inner);
                    return new_list;
                }
            } else if (!_mv_1669.has_value) {
                return t;
            }
            SLOP_UNREACHABLE();
        } else if (kind == types_ResolvedTypeKind_rk_option) {
            __auto_type _mv_1670 = (*t).inner_type;
            if (_mv_1670.has_value) {
                __auto_type inner = _mv_1670.value;
                {
                    __auto_type new_inner = infer_substitute_type_vars(arena, inner, bind_names, bind_types);
                    __auto_type inner_name = (*new_inner).name;
                    __auto_type opt_name = string_concat(arena, SLOP_STR("Option_"), inner_name);
                    __auto_type new_opt = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_option, opt_name, ((slop_option_string){.has_value = false}), SLOP_STR("slop_option"));
                    types_resolved_type_set_inner(new_opt, new_inner);
                    return new_opt;
                }
            } else if (!_mv_1670.has_value) {
                return t;
            }
            SLOP_UNREACHABLE();
        } else if (kind == types_ResolvedTypeKind_rk_result) {
            {
                __auto_type new_ok = ({ __auto_type _mv = (*t).inner_type; _mv.has_value ? ({ __auto_type ok = _mv.value; infer_substitute_type_vars(arena, ok, bind_names, bind_types); }) : (NULL); });
                __auto_type new_err = ({ __auto_type _mv = (*t).inner_type2; _mv.has_value ? ({ __auto_type err = _mv.value; infer_substitute_type_vars(arena, err, bind_names, bind_types); }) : (NULL); });
                if (new_ok == NULL) {
                    return t;
                } else {
                    {
                        __auto_type ok_name = (*new_ok).name;
                        __auto_type err_name = (((new_err != NULL)) ? (*new_err).name : SLOP_STR("Error"));
                        __auto_type result_name = string_concat(arena, SLOP_STR("Result_"), string_concat(arena, ok_name, string_concat(arena, SLOP_STR("_"), err_name)));
                        __auto_type new_result = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_result, result_name, ((slop_option_string){.has_value = false}), SLOP_STR("Result"));
                        types_resolved_type_set_inner(new_result, new_ok);
                        if (new_err != NULL) {
                            types_resolved_type_set_inner2(new_result, new_err);
                        }
                        return new_result;
                    }
                }
            }
        } else {
            return t;
        }
    }
}

types_ResolvedType* infer_infer_generic_call(env_TypeEnv* env, types_FnSignature* sig, types_SExpr* expr, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((sig != NULL)), "(!= sig nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = env_env_arena(env);
        __auto_type params = (*sig).params;
        __auto_type num_params = ((int64_t)((params).len));
        __auto_type bind_names = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        __auto_type bind_types = ((slop_list_types_ResolvedType_ptr){ .data = (types_ResolvedType**)slop_arena_alloc(arena, 16 * sizeof(types_ResolvedType*)), .len = 0, .cap = 16 });
        if (parser_sexpr_is_list(expr)) {
            {
                __auto_type num_args = (parser_sexpr_list_len(expr) - 1);
                if (((*sig).is_variadic) ? (num_args < num_params) : (num_args != num_params)) {
                    {
                        __auto_type msg = string_concat(arena, SLOP_STR("'"), string_concat(arena, (*sig).name, string_concat(arena, SLOP_STR("' expects "), string_concat(arena, int_to_string(arena, num_params), string_concat(arena, SLOP_STR(" argument(s), got "), int_to_string(arena, num_args))))));
                        env_env_add_error(env, msg, line, col);
                    }
                }
                {
                    __auto_type limit = (((num_args < num_params)) ? num_args : num_params);
                    for (int64_t i = 0; i < limit; i++) {
                        __auto_type _mv_1671 = parser_sexpr_list_get(expr, (i + 1));
                        if (_mv_1671.has_value) {
                            __auto_type arg_expr = _mv_1671.value;
                            {
                                __auto_type actual_type = infer_infer_expr(env, arg_expr);
                                __auto_type _mv_1672 = ({ __auto_type _lst = params; size_t _idx = (size_t)i; slop_option_types_ParamInfo _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1672.has_value) {
                                    __auto_type param_info = _mv_1672.value;
                                    {
                                        __auto_type formal_type = param_info.param_type;
                                        infer_unify_types(arena, formal_type, actual_type, bind_names, bind_types);
                                    }
                                } else if (!_mv_1672.has_value) {
                                }
                            }
                        } else if (!_mv_1671.has_value) {
                        }
                    }
                }
            }
        }
        {
            __auto_type ret_type = (*sig).return_type;
            return infer_substitute_type_vars(arena, ret_type, bind_names, bind_types);
        }
    }
}

uint8_t infer_is_unwrappable_container(types_ResolvedType* t) {
    SLOP_PRE(((t != NULL)), "(!= t nil)");
    {
        __auto_type kind = (*t).kind;
        return ((kind == types_ResolvedTypeKind_rk_list) || (kind == types_ResolvedTypeKind_rk_option));
    }
}

uint8_t infer_container_inners_equal(types_ResolvedType* a, types_ResolvedType* b) {
    SLOP_PRE(((a != NULL)), "(!= a nil)");
    SLOP_PRE(((b != NULL)), "(!= b nil)");
    {
        __auto_type ca = a;
        __auto_type cb = b;
        int64_t steps = 0;
        uint8_t done = 0;
        uint8_t result = 1;
        while (!(done) && (steps < 32)) {
            __auto_type _mv_1673 = (*ca).inner_type;
            if (_mv_1673.has_value) {
                __auto_type a_inner = _mv_1673.value;
                __auto_type _mv_1674 = (*cb).inner_type;
                if (_mv_1674.has_value) {
                    __auto_type b_inner = _mv_1674.value;
                    if ((infer_is_unwrappable_container(a_inner)) && (infer_is_unwrappable_container(b_inner)) && (((*a_inner).kind == (*b_inner).kind)) && ((a_inner != ca)) && ((b_inner != cb))) {
                        ca = a_inner;
                        cb = b_inner;
                        steps = (steps + 1);
                    } else {
                        result = ((((a_inner == ca) || (b_inner == cb))) ? string_eq((*ca).name, (*cb).name) : infer_types_equal(a_inner, b_inner));
                        done = 1;
                    }
                } else if (!_mv_1674.has_value) {
                    result = 1;
                    done = 1;
                }
            } else if (!_mv_1673.has_value) {
                result = 1;
                done = 1;
            }
        }
        if (done) {
            return result;
        } else {
            return string_eq((*ca).name, (*cb).name);
        }
    }
}

uint8_t infer_types_equal(types_ResolvedType* a, types_ResolvedType* b) {
    SLOP_PRE(((a != NULL)), "(!= a nil)");
    SLOP_PRE(((b != NULL)), "(!= b nil)");
    {
        __auto_type a_kind = (*a).kind;
        __auto_type b_kind = (*b).kind;
        __auto_type a_name = (*a).name;
        __auto_type b_name = (*b).name;
        if (a == b) {
            return 1;
        } else if ((a_kind == types_ResolvedTypeKind_rk_option) && (b_kind == types_ResolvedTypeKind_rk_option)) {
            return ((string_eq(a_name, SLOP_STR("Option_T"))) || (string_eq(b_name, SLOP_STR("Option_T"))) || (infer_container_inners_equal(a, b)));
        } else if ((a_kind == types_ResolvedTypeKind_rk_list) && (b_kind == types_ResolvedTypeKind_rk_list)) {
            return infer_container_inners_equal(a, b);
        } else if (string_eq(a_name, b_name)) {
            return 1;
        } else if ((a_kind == types_ResolvedTypeKind_rk_typevar) || (b_kind == types_ResolvedTypeKind_rk_typevar)) {
            return 1;
        } else if (string_eq(a_name, SLOP_STR("<nil>")) && (b_kind == types_ResolvedTypeKind_rk_ptr)) {
            return 1;
        } else if (string_eq(b_name, SLOP_STR("<nil>")) && (a_kind == types_ResolvedTypeKind_rk_ptr)) {
            return 1;
        } else if (string_eq(a_name, SLOP_STR("T")) || string_eq(b_name, SLOP_STR("T"))) {
            return 1;
        } else if ((a_kind == types_ResolvedTypeKind_rk_result) && (b_kind == types_ResolvedTypeKind_rk_result)) {
            return (string_eq(a_name, SLOP_STR("Result")) || string_eq(b_name, SLOP_STR("Result")));
        } else if ((a_kind == types_ResolvedTypeKind_rk_range) || (b_kind == types_ResolvedTypeKind_rk_range)) {
            return infer_types_compatible_with_range(a, b);
        } else if ((a_kind == types_ResolvedTypeKind_rk_function) && (b_kind == types_ResolvedTypeKind_rk_function)) {
            return 1;
        } else if (string_eq(a_name, SLOP_STR("Fn")) || string_eq(b_name, SLOP_STR("Fn"))) {
            return ((a_kind == types_ResolvedTypeKind_rk_function) || (b_kind == types_ResolvedTypeKind_rk_function));
        } else {
            return 0;
        }
    }
}

uint8_t infer_types_compatible_with_range(types_ResolvedType* a, types_ResolvedType* b) {
    SLOP_PRE(((a != NULL)), "(!= a nil)");
    SLOP_PRE(((b != NULL)), "(!= b nil)");
    {
        __auto_type a_kind = (*a).kind;
        __auto_type b_kind = (*b).kind;
        if (a_kind == types_ResolvedTypeKind_rk_range) {
            __auto_type _mv_1675 = (*a).inner_type;
            if (_mv_1675.has_value) {
                __auto_type base = _mv_1675.value;
                return string_eq((*base).name, (*b).name);
            } else if (!_mv_1675.has_value) {
                return 0;
            }
            SLOP_UNREACHABLE();
        } else if (b_kind == types_ResolvedTypeKind_rk_range) {
            __auto_type _mv_1676 = (*b).inner_type;
            if (_mv_1676.has_value) {
                __auto_type base = _mv_1676.value;
                return string_eq((*a).name, (*base).name);
            } else if (!_mv_1676.has_value) {
                return 0;
            }
            SLOP_UNREACHABLE();
        } else {
            return 0;
        }
    }
}

uint8_t infer_type_is_null_pointer(types_ResolvedType* t) {
    SLOP_PRE(((t != NULL)), "(!= t nil)");
    return string_eq((*t).name, SLOP_STR("<nil>"));
}

types_ResolvedType* infer_unify_branch_types(env_TypeEnv* env, types_ResolvedType* a, types_ResolvedType* b, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((a != NULL)), "(!= a nil)");
    SLOP_PRE(((b != NULL)), "(!= b nil)");
    if ((*a).kind == types_ResolvedTypeKind_rk_never) {
        return b;
    } else {
        if ((*b).kind == types_ResolvedTypeKind_rk_never) {
            return a;
        } else {
            if (infer_type_is_null_pointer(a) && ((*b).kind == types_ResolvedTypeKind_rk_ptr)) {
                return b;
            } else {
                if (infer_type_is_null_pointer(b) && ((*a).kind == types_ResolvedTypeKind_rk_ptr)) {
                    return a;
                } else {
                    if (infer_types_equal(a, b)) {
                        return a;
                    } else {
                        {
                            __auto_type arena = env_env_arena(env);
                            __auto_type msg = string_concat(arena, SLOP_STR("Branch types differ: "), string_concat(arena, (*a).name, string_concat(arena, SLOP_STR(" vs "), (*b).name)));
                            env_env_add_warning(env, msg, line, col);
                            return a;
                        }
                    }
                }
            }
        }
    }
}

void infer_sexpr_set_resolved_type(types_SExpr* expr, types_ResolvedType* t) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_1677 = (*expr);
    switch (_mv_1677.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1677.data.sym;
            (*expr) = ((types_SExpr){ .tag = types_SExpr_sym, .data.sym = (types_SExprSymbol){sym.name, sym.line, sym.col, (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = t}} });
            break;
        }
        case types_SExpr_str:
        {
            __auto_type str = _mv_1677.data.str;
            (*expr) = ((types_SExpr){ .tag = types_SExpr_str, .data.str = (types_SExprString){str.value, str.line, str.col, (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = t}} });
            break;
        }
        case types_SExpr_num:
        {
            __auto_type num = _mv_1677.data.num;
            (*expr) = ((types_SExpr){ .tag = types_SExpr_num, .data.num = (types_SExprNumber){num.int_value, num.float_value, num.is_float, num.raw, num.line, num.col, (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = t}} });
            break;
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1677.data.lst;
            (*expr) = ((types_SExpr){ .tag = types_SExpr_lst, .data.lst = (types_SExprList){lst.items, lst.line, lst.col, (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = t}} });
            break;
        }
    }
}

types_ResolvedType* infer_infer_expr(env_TypeEnv* env, types_SExpr* expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type result = infer_infer_expr_inner(env, expr);
        if (result != NULL) {
            infer_sexpr_set_resolved_type(expr, result);
        }
        return result;
    }
}

types_ResolvedType* infer_infer_expr_inner(env_TypeEnv* env, types_SExpr* expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type line = parser_sexpr_line(expr);
        __auto_type col = parser_sexpr_col(expr);
        __auto_type _mv_1678 = (*expr);
        switch (_mv_1678.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_1678.data.sym;
                {
                    __auto_type name = sym.name;
                    if (string_eq(name, SLOP_STR("true")) || string_eq(name, SLOP_STR("false"))) {
                        return env_env_get_bool_type(env);
                    } else if (string_eq(name, SLOP_STR("nil"))) {
                        return env_env_get_null_type(env);
                    } else if (string_eq(name, SLOP_STR("unit"))) {
                        return env_env_get_unit_type(env);
                    } else if (string_eq(name, SLOP_STR("none"))) {
                        return env_env_make_option_type(env, NULL);
                    } else {
                        __auto_type _mv_1679 = env_env_lookup_var(env, name);
                        if (_mv_1679.has_value) {
                            __auto_type t = _mv_1679.value;
                            return t;
                        } else if (!_mv_1679.has_value) {
                            __auto_type _mv_1680 = env_env_lookup_constant(env, name);
                            if (_mv_1680.has_value) {
                                __auto_type t = _mv_1680.value;
                                return t;
                            } else if (!_mv_1680.has_value) {
                                __auto_type _mv_1681 = env_env_lookup_function(env, name);
                                if (_mv_1681.has_value) {
                                    __auto_type sig = _mv_1681.value;
                                    return env_env_make_fn_type(env, sig);
                                } else if (!_mv_1681.has_value) {
                                    if (infer_string_contains_char(name, 46)) {
                                        {
                                            __auto_type dot_pos = infer_string_index_of(name, 46);
                                            __auto_type arena = env_env_arena(env);
                                            __auto_type base_name = infer_string_substring(arena, name, 0, dot_pos);
                                            __auto_type field_name = infer_string_substring(arena, name, (dot_pos + 1), ((int64_t)(name.len)));
                                            __auto_type _mv_1682 = env_env_lookup_var(env, base_name);
                                            if (_mv_1682.has_value) {
                                                __auto_type obj_type = _mv_1682.value;
                                                return infer_check_field_exists(env, obj_type, field_name, line, col);
                                            } else if (!_mv_1682.has_value) {
                                                __auto_type _mv_1683 = env_env_lookup_type(env, base_name);
                                                if (_mv_1683.has_value) {
                                                    __auto_type type_info = _mv_1683.value;
                                                    return type_info;
                                                } else if (!_mv_1683.has_value) {
                                                    {
                                                        __auto_type msg = string_concat(arena, SLOP_STR("Undefined variable: "), name);
                                                        env_env_add_error(env, msg, line, col);
                                                        return env_env_get_int_type(env);
                                                    }
                                                }
                                                SLOP_UNREACHABLE();
                                            }
                                            SLOP_UNREACHABLE();
                                        }
                                    } else {
                                        __auto_type _mv_1684 = env_env_lookup_type(env, name);
                                        if (_mv_1684.has_value) {
                                            __auto_type type_info = _mv_1684.value;
                                            return type_info;
                                        } else if (!_mv_1684.has_value) {
                                            __auto_type _mv_1685 = env_env_lookup_variant(env, name);
                                            if (_mv_1685.has_value) {
                                                __auto_type enum_name = _mv_1685.value;
                                                __auto_type _mv_1686 = env_env_lookup_type(env, enum_name);
                                                if (_mv_1686.has_value) {
                                                    __auto_type t = _mv_1686.value;
                                                    return t;
                                                } else if (!_mv_1686.has_value) {
                                                    return env_env_get_int_type(env);
                                                }
                                                SLOP_UNREACHABLE();
                                            } else if (!_mv_1685.has_value) {
                                                {
                                                    __auto_type arena = env_env_arena(env);
                                                    __auto_type msg = string_concat(arena, SLOP_STR("Undefined variable: "), name);
                                                    env_env_add_error(env, msg, line, col);
                                                    return env_env_get_int_type(env);
                                                }
                                            }
                                            SLOP_UNREACHABLE();
                                        }
                                        SLOP_UNREACHABLE();
                                    }
                                }
                                SLOP_UNREACHABLE();
                            }
                            SLOP_UNREACHABLE();
                        }
                        SLOP_UNREACHABLE();
                    }
                }
            }
            case types_SExpr_num:
            {
                __auto_type num = _mv_1678.data.num;
                if (num.is_float) {
                    return env_env_get_float_type(env);
                } else {
                    return env_env_get_int_type(env);
                }
            }
            case types_SExpr_str:
            {
                __auto_type str = _mv_1678.data.str;
                return env_env_get_string_type(env);
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1678.data.lst;
                return infer_infer_list_expr(env, expr, lst);
            }
        }
        SLOP_UNREACHABLE();
    }
}

types_ResolvedType* infer_infer_list_expr(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type items = lst.items;
        __auto_type len = ((int64_t)((items).len));
        if (len == 0) {
            return env_env_get_unit_type(env);
        } else {
            __auto_type _mv_1687 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (!_mv_1687.has_value) {
                return env_env_get_unit_type(env);
            } else if (_mv_1687.has_value) {
                __auto_type head = _mv_1687.value;
                __auto_type _mv_1688 = (*head);
                switch (_mv_1688.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_1688.data.sym;
                        {
                            __auto_type op = sym.name;
                            return infer_infer_special_form(env, expr, lst, op);
                        }
                    }
                    default: {
                        return env_env_get_unit_type(env);
                    }
                }
            }
            SLOP_UNREACHABLE();
        }
    }
}

types_ResolvedType* infer_infer_special_form(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst, slop_string op) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type items = lst.items;
        __auto_type len = ((int64_t)((items).len));
        __auto_type line = parser_sexpr_line(expr);
        __auto_type col = parser_sexpr_col(expr);
        if (string_eq(op, SLOP_STR("if"))) {
            if (len >= 4) {
                __auto_type _mv_1689 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1689.has_value) {
                    __auto_type cond_expr = _mv_1689.value;
                    {
                        __auto_type _ = infer_infer_expr(env, cond_expr);
                    }
                } else if (!_mv_1689.has_value) {
                }
                __auto_type _mv_1690 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1690.has_value) {
                    __auto_type then_expr = _mv_1690.value;
                    {
                        __auto_type then_type = infer_infer_expr(env, then_expr);
                        __auto_type _mv_1691 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1691.has_value) {
                            __auto_type else_expr = _mv_1691.value;
                            {
                                __auto_type else_type = infer_infer_expr(env, else_expr);
                                return infer_unify_branch_types(env, then_type, else_type, line, col);
                            }
                        } else if (!_mv_1691.has_value) {
                            return then_type;
                        }
                        SLOP_UNREACHABLE();
                    }
                } else if (!_mv_1690.has_value) {
                    return env_env_get_unit_type(env);
                }
                SLOP_UNREACHABLE();
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("cond"))) {
            return infer_infer_cond_expr(env, expr, lst);
        } else if (string_eq(op, SLOP_STR("match"))) {
            return infer_infer_match_expr(env, expr, lst);
        } else if (string_eq(op, SLOP_STR("do"))) {
            infer_infer_body_exprs(env, expr, 1);
            if (len > 1) {
                __auto_type _mv_1692 = ({ __auto_type _lst = items; size_t _idx = (size_t)(len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1692.has_value) {
                    __auto_type last = _mv_1692.value;
                    return infer_infer_expr(env, last);
                } else if (!_mv_1692.has_value) {
                    return env_env_get_unit_type(env);
                }
                SLOP_UNREACHABLE();
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("let"))) {
            return infer_infer_let_expr(env, expr);
        } else if (string_eq(op, SLOP_STR("when"))) {
            infer_infer_body_exprs(env, expr, 1);
            return env_env_get_unit_type(env);
        } else if (string_eq(op, SLOP_STR("for"))) {
            if (len >= 2) {
                __auto_type _mv_1693 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1693.has_value) {
                    __auto_type binding_form = _mv_1693.value;
                    if (parser_sexpr_is_list(binding_form)) {
                        {
                            __auto_type bind_len = parser_sexpr_list_len(binding_form);
                            if (bind_len >= 3) {
                                __auto_type _mv_1694 = parser_sexpr_list_get(binding_form, 0);
                                if (_mv_1694.has_value) {
                                    __auto_type var_expr = _mv_1694.value;
                                    {
                                        __auto_type var_name = parser_sexpr_get_symbol_name(var_expr);
                                        if (!(string_eq(var_name, SLOP_STR("")))) {
                                            env_env_push_scope(env);
                                            env_env_bind_var(env, var_name, env_env_get_int_type(env));
                                            __auto_type _mv_1695 = parser_sexpr_list_get(binding_form, 1);
                                            if (_mv_1695.has_value) {
                                                __auto_type start_expr = _mv_1695.value;
                                                {
                                                    __auto_type _ = infer_infer_expr(env, start_expr);
                                                }
                                            } else if (!_mv_1695.has_value) {
                                            }
                                            __auto_type _mv_1696 = parser_sexpr_list_get(binding_form, 2);
                                            if (_mv_1696.has_value) {
                                                __auto_type end_expr = _mv_1696.value;
                                                {
                                                    __auto_type _ = infer_infer_expr(env, end_expr);
                                                }
                                            } else if (!_mv_1696.has_value) {
                                            }
                                            for (int64_t body_idx = 2; body_idx < len; body_idx++) {
                                                __auto_type _mv_1697 = ({ __auto_type _lst = items; size_t _idx = (size_t)body_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1697.has_value) {
                                                    __auto_type body_expr = _mv_1697.value;
                                                    {
                                                        __auto_type _ = infer_infer_expr(env, body_expr);
                                                    }
                                                } else if (!_mv_1697.has_value) {
                                                }
                                            }
                                            env_env_pop_scope(env);
                                        }
                                    }
                                } else if (!_mv_1694.has_value) {
                                }
                            }
                        }
                    }
                } else if (!_mv_1693.has_value) {
                }
                return env_env_get_unit_type(env);
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("for-each"))) {
            if (len >= 3) {
                __auto_type _mv_1698 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1698.has_value) {
                    __auto_type binding_form = _mv_1698.value;
                    if (parser_sexpr_is_list(binding_form)) {
                        {
                            __auto_type bind_len = parser_sexpr_list_len(binding_form);
                            if (bind_len >= 2) {
                                __auto_type _mv_1699 = parser_sexpr_list_get(binding_form, 0);
                                if (_mv_1699.has_value) {
                                    __auto_type var_expr = _mv_1699.value;
                                    {
                                        __auto_type var_name = parser_sexpr_get_symbol_name(var_expr);
                                        if (string_eq(var_name, SLOP_STR(""))) {
                                            return env_env_get_unit_type(env);
                                        } else {
                                            __auto_type _mv_1700 = parser_sexpr_list_get(binding_form, 1);
                                            if (_mv_1700.has_value) {
                                                __auto_type coll_expr = _mv_1700.value;
                                                {
                                                    __auto_type coll_type = infer_infer_expr(env, coll_expr);
                                                    __auto_type coll_line = parser_sexpr_line(coll_expr);
                                                    __auto_type coll_col = parser_sexpr_col(coll_expr);
                                                    {
                                                        __auto_type elem_type = ({ __auto_type _mv = (*coll_type).inner_type; _mv.has_value ? ({ __auto_type inner = _mv.value; inner; }) : (({ __auto_type arena = env_env_arena(env); __auto_type coll_name = (*coll_type).name; __auto_type msg = string_concat(arena, SLOP_STR("for-each: cannot determine element type of '"), string_concat(arena, coll_name, SLOP_STR("' - collection has no inner type"))); env_env_add_warning(env, msg, coll_line, coll_col); env_env_get_unknown_type(env); })); });
                                                        env_env_push_scope(env);
                                                        env_env_bind_var(env, var_name, elem_type);
                                                        for (int64_t body_idx = 2; body_idx < len; body_idx++) {
                                                            __auto_type _mv_1701 = ({ __auto_type _lst = items; size_t _idx = (size_t)body_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_1701.has_value) {
                                                                __auto_type body_expr = _mv_1701.value;
                                                                {
                                                                    __auto_type _ = infer_infer_expr(env, body_expr);
                                                                }
                                                            } else if (!_mv_1701.has_value) {
                                                            }
                                                        }
                                                        env_env_pop_scope(env);
                                                        return env_env_get_unit_type(env);
                                                    }
                                                }
                                            } else if (!_mv_1700.has_value) {
                                                return env_env_get_unit_type(env);
                                            }
                                            SLOP_UNREACHABLE();
                                        }
                                    }
                                } else if (!_mv_1699.has_value) {
                                    return env_env_get_unit_type(env);
                                }
                                SLOP_UNREACHABLE();
                            } else {
                                return env_env_get_unit_type(env);
                            }
                        }
                    } else {
                        return env_env_get_unit_type(env);
                    }
                } else if (!_mv_1698.has_value) {
                    return env_env_get_unit_type(env);
                }
                SLOP_UNREACHABLE();
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("while"))) {
            infer_infer_body_exprs(env, expr, 1);
            return env_env_get_unit_type(env);
        } else if (string_eq(op, SLOP_STR("@loop-invariant"))) {
            infer_infer_body_exprs(env, expr, 1);
            return env_env_get_unit_type(env);
        } else if (string_eq(op, SLOP_STR("fn"))) {
            env_env_push_scope(env);
            if (len >= 2) {
                __auto_type _mv_1702 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1702.has_value) {
                    __auto_type params_expr = _mv_1702.value;
                    if (parser_sexpr_is_list(params_expr)) {
                        {
                            __auto_type num_params = parser_sexpr_list_len(params_expr);
                            for (int64_t k = 0; k < num_params; k++) {
                                __auto_type _mv_1703 = parser_sexpr_list_get(params_expr, k);
                                if (_mv_1703.has_value) {
                                    __auto_type param_form = _mv_1703.value;
                                    infer_bind_param_from_form(env, param_form);
                                } else if (!_mv_1703.has_value) {
                                }
                            }
                        }
                    }
                } else if (!_mv_1702.has_value) {
                }
            }
            {
                __auto_type body_type = (((len > 2)) ? ({ ({ for (int64_t bi = 2; bi < (len - 1); bi++) { ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)bi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type body_expr = _mv.value; ((!(infer_is_annotation_expr(body_expr))) ? ({ ({ __auto_type _ = infer_infer_expr(env, body_expr); ({ (void)0; }); }); 0; }) : ({ (void)0; })); } else { ({ (void)0; }); } (void)0; }); } (void)0; }); ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)(len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type last_expr = _mv.value; ((infer_is_annotation_expr(last_expr)) ? env_env_get_unit_type(env) : infer_infer_expr(env, last_expr)); }) : (env_env_get_unit_type(env)); }); }) : env_env_get_unit_type(env));
                env_env_pop_scope(env);
                {
                    __auto_type arena = env_env_arena(env);
                    return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_function, SLOP_STR("Fn"), ((slop_option_string){.has_value = false}), SLOP_STR("void*"));
                }
            }
        } else if (string_eq(op, SLOP_STR("with-arena"))) {
            return infer_infer_with_arena_expr(env, expr);
        } else if (string_eq(op, SLOP_STR("set!"))) {
            if (len >= 4) {
                __auto_type _mv_1704 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1704.has_value) {
                    __auto_type val_expr = _mv_1704.value;
                    {
                        __auto_type _ = infer_infer_expr(env, val_expr);
                    }
                } else if (!_mv_1704.has_value) {
                }
            } else if (len >= 3) {
                __auto_type _mv_1705 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1705.has_value) {
                    __auto_type val_expr = _mv_1705.value;
                    {
                        __auto_type _ = infer_infer_expr(env, val_expr);
                    }
                } else if (!_mv_1705.has_value) {
                }
            } else {
            }
            return env_env_get_unit_type(env);
        } else if (string_eq(op, SLOP_STR("return"))) {
            if (len >= 2) {
                __auto_type _mv_1706 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1706.has_value) {
                    __auto_type ret_expr = _mv_1706.value;
                    {
                        __auto_type _ = infer_infer_expr(env, ret_expr);
                    }
                } else if (!_mv_1706.has_value) {
                }
            }
            return env_env_get_never_type(env);
        } else if (string_eq(op, SLOP_STR("break")) || string_eq(op, SLOP_STR("continue"))) {
            return env_env_get_never_type(env);
        } else if ((string_eq(op, SLOP_STR("=="))) || (string_eq(op, SLOP_STR("!="))) || (string_eq(op, SLOP_STR("<"))) || (string_eq(op, SLOP_STR("<="))) || (string_eq(op, SLOP_STR(">"))) || (string_eq(op, SLOP_STR(">="))) || (string_eq(op, SLOP_STR("and"))) || (string_eq(op, SLOP_STR("or"))) || (string_eq(op, SLOP_STR("not")))) {
            infer_infer_body_exprs(env, expr, 1);
            return env_env_get_bool_type(env);
        } else if ((string_eq(op, SLOP_STR("+"))) || (string_eq(op, SLOP_STR("-"))) || (string_eq(op, SLOP_STR("*"))) || (string_eq(op, SLOP_STR("/"))) || (string_eq(op, SLOP_STR("%")))) {
            infer_infer_body_exprs(env, expr, 1);
            return env_env_get_int_type(env);
        } else if (string_eq(op, SLOP_STR("deref"))) {
            if (len >= 2) {
                __auto_type _mv_1707 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1707.has_value) {
                    __auto_type ptr_expr = _mv_1707.value;
                    {
                        __auto_type ptr_type = infer_infer_expr(env, ptr_expr);
                        if (types_resolved_type_is_pointer(ptr_type)) {
                            __auto_type _mv_1708 = (*ptr_type).inner_type;
                            if (_mv_1708.has_value) {
                                __auto_type inner = _mv_1708.value;
                                return inner;
                            } else if (!_mv_1708.has_value) {
                                return env_env_get_unit_type(env);
                            }
                            SLOP_UNREACHABLE();
                        } else {
                            return ptr_type;
                        }
                    }
                } else if (!_mv_1707.has_value) {
                    return env_env_get_unit_type(env);
                }
                SLOP_UNREACHABLE();
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("addr"))) {
            if (len >= 2) {
                __auto_type _mv_1709 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1709.has_value) {
                    __auto_type inner_expr = _mv_1709.value;
                    {
                        __auto_type inner_type = infer_infer_expr(env, inner_expr);
                        return env_env_make_ptr_type(env, inner_type);
                    }
                } else if (!_mv_1709.has_value) {
                    return env_env_get_unit_type(env);
                }
                SLOP_UNREACHABLE();
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("cast"))) {
            if (len >= 2) {
                __auto_type _mv_1710 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1710.has_value) {
                    __auto_type type_expr = _mv_1710.value;
                    {
                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                        if (string_eq(type_name, SLOP_STR(""))) {
                            if (parser_sexpr_is_list(type_expr)) {
                                __auto_type _mv_1711 = parser_sexpr_list_get(type_expr, 0);
                                if (_mv_1711.has_value) {
                                    __auto_type head_expr = _mv_1711.value;
                                    {
                                        __auto_type head_name = parser_sexpr_get_symbol_name(head_expr);
                                        if (string_eq(head_name, SLOP_STR("Int"))) {
                                            return env_env_get_int_type(env);
                                        } else if (string_eq(head_name, SLOP_STR("Ptr"))) {
                                            {
                                                __auto_type inner_type = infer_resolve_ptr_inner_type(env, type_expr);
                                                return env_env_make_ptr_type(env, inner_type);
                                            }
                                        } else if (string_eq(head_name, SLOP_STR("U8"))) {
                                            return env_env_get_int_type(env);
                                        } else if (string_eq(head_name, SLOP_STR("U16"))) {
                                            return env_env_get_int_type(env);
                                        } else if (string_eq(head_name, SLOP_STR("U32"))) {
                                            return env_env_get_int_type(env);
                                        } else if (string_eq(head_name, SLOP_STR("U64"))) {
                                            return env_env_get_int_type(env);
                                        } else if (string_eq(head_name, SLOP_STR("I8"))) {
                                            return env_env_get_int_type(env);
                                        } else if (string_eq(head_name, SLOP_STR("I16"))) {
                                            return env_env_get_int_type(env);
                                        } else if (string_eq(head_name, SLOP_STR("I32"))) {
                                            return env_env_get_int_type(env);
                                        } else if (string_eq(head_name, SLOP_STR("I64"))) {
                                            return env_env_get_int_type(env);
                                        } else {
                                            return env_env_get_unknown_type(env);
                                        }
                                    }
                                } else if (!_mv_1711.has_value) {
                                    return env_env_get_unknown_type(env);
                                }
                                SLOP_UNREACHABLE();
                            } else {
                                return env_env_get_unknown_type(env);
                            }
                        } else {
                            __auto_type _mv_1712 = env_env_lookup_type(env, type_name);
                            if (_mv_1712.has_value) {
                                __auto_type t = _mv_1712.value;
                                return t;
                            } else if (!_mv_1712.has_value) {
                                if (string_eq(type_name, SLOP_STR("Int"))) {
                                    return env_env_get_int_type(env);
                                } else if (string_eq(type_name, SLOP_STR("Bool"))) {
                                    return env_env_get_bool_type(env);
                                } else if (string_eq(type_name, SLOP_STR("String"))) {
                                    return env_env_get_string_type(env);
                                } else if (string_eq(type_name, SLOP_STR("Unit"))) {
                                    return env_env_get_unit_type(env);
                                } else {
                                    return env_env_get_unknown_type(env);
                                }
                            }
                            SLOP_UNREACHABLE();
                        }
                    }
                } else if (!_mv_1710.has_value) {
                    return env_env_get_unknown_type(env);
                }
                SLOP_UNREACHABLE();
            } else {
                return env_env_get_unknown_type(env);
            }
        } else if (string_eq(op, SLOP_STR("quote"))) {
            if (len >= 2) {
                __auto_type _mv_1713 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1713.has_value) {
                    __auto_type variant_expr = _mv_1713.value;
                    {
                        __auto_type variant_name = parser_sexpr_get_symbol_name(variant_expr);
                        if (string_eq(variant_name, SLOP_STR(""))) {
                            return env_env_get_unknown_type(env);
                        } else {
                            __auto_type _mv_1714 = env_env_lookup_variant(env, variant_name);
                            if (_mv_1714.has_value) {
                                __auto_type enum_name = _mv_1714.value;
                                __auto_type _mv_1715 = env_env_lookup_type(env, enum_name);
                                if (_mv_1715.has_value) {
                                    __auto_type enum_type = _mv_1715.value;
                                    return enum_type;
                                } else if (!_mv_1715.has_value) {
                                    return env_env_get_unknown_type(env);
                                }
                                SLOP_UNREACHABLE();
                            } else if (!_mv_1714.has_value) {
                                return env_env_get_unknown_type(env);
                            }
                            SLOP_UNREACHABLE();
                        }
                    }
                } else if (!_mv_1713.has_value) {
                    return env_env_get_unknown_type(env);
                }
                SLOP_UNREACHABLE();
            } else {
                return env_env_get_unknown_type(env);
            }
        } else if (string_eq(op, SLOP_STR("."))) {
            return infer_infer_field_access(env, expr, lst, line, col);
        } else if (string_eq(op, SLOP_STR("some"))) {
            if (len >= 2) {
                __auto_type _mv_1716 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1716.has_value) {
                    __auto_type inner_expr = _mv_1716.value;
                    {
                        __auto_type inner_type = infer_infer_expr(env, inner_expr);
                        return env_env_make_option_type(env, inner_type);
                    }
                } else if (!_mv_1716.has_value) {
                    return env_env_make_option_type(env, NULL);
                }
                SLOP_UNREACHABLE();
            } else {
                return env_env_make_option_type(env, NULL);
            }
        } else if (string_eq(op, SLOP_STR("none"))) {
            return env_env_make_option_type(env, NULL);
        } else if (string_eq(op, SLOP_STR("record-new"))) {
            for (int64_t fi = 2; fi < len; fi++) {
                __auto_type _mv_1717 = ({ __auto_type _lst = items; size_t _idx = (size_t)fi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1717.has_value) {
                    __auto_type field_pair = _mv_1717.value;
                    if (parser_sexpr_is_list(field_pair) && (parser_sexpr_list_len(field_pair) >= 2)) {
                        __auto_type _mv_1718 = parser_sexpr_list_get(field_pair, 1);
                        if (_mv_1718.has_value) {
                            __auto_type val_expr = _mv_1718.value;
                            {
                                __auto_type _ = infer_infer_expr(env, val_expr);
                            }
                        } else if (!_mv_1718.has_value) {
                        }
                    }
                } else if (!_mv_1717.has_value) {
                }
            }
            if (len >= 2) {
                __auto_type _mv_1719 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1719.has_value) {
                    __auto_type type_expr = _mv_1719.value;
                    {
                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                        if (string_eq(type_name, SLOP_STR(""))) {
                            return env_env_get_unit_type(env);
                        } else {
                            __auto_type _mv_1720 = env_env_lookup_type(env, type_name);
                            if (_mv_1720.has_value) {
                                __auto_type t = _mv_1720.value;
                                return t;
                            } else if (!_mv_1720.has_value) {
                                return env_env_get_unit_type(env);
                            }
                            SLOP_UNREACHABLE();
                        }
                    }
                } else if (!_mv_1719.has_value) {
                    return env_env_get_unit_type(env);
                }
                SLOP_UNREACHABLE();
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("union-new"))) {
            if (len >= 4) {
                __auto_type _mv_1721 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1721.has_value) {
                    __auto_type val_expr = _mv_1721.value;
                    {
                        __auto_type _ = infer_infer_expr(env, val_expr);
                    }
                } else if (!_mv_1721.has_value) {
                }
            }
            if (len >= 2) {
                __auto_type _mv_1722 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1722.has_value) {
                    __auto_type type_expr = _mv_1722.value;
                    {
                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                        if (string_eq(type_name, SLOP_STR(""))) {
                            return env_env_get_unit_type(env);
                        } else {
                            __auto_type _mv_1723 = env_env_lookup_type(env, type_name);
                            if (_mv_1723.has_value) {
                                __auto_type t = _mv_1723.value;
                                return t;
                            } else if (!_mv_1723.has_value) {
                                return env_env_get_unit_type(env);
                            }
                            SLOP_UNREACHABLE();
                        }
                    }
                } else if (!_mv_1722.has_value) {
                    return env_env_get_unit_type(env);
                }
                SLOP_UNREACHABLE();
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("hole"))) {
            {
                __auto_type hole_type = infer_resolve_hole_type(env, items, len);
                __auto_type raw_prompt = infer_get_hole_prompt(items, len);
                __auto_type arena = env_env_arena(env);
                __auto_type hole_msg = string_concat(arena, SLOP_STR("Unfilled hole: "), raw_prompt);
                env_env_add_error(env, hole_msg, line, col);
                return hole_type;
            }
        } else if (infer_is_chan_buffered_op(op) || infer_is_chan_op(op)) {
            return infer_infer_threading_builtin(env, op, expr, items, len, line, col);
        } else {
            __auto_type _mv_1724 = env_env_lookup_function(env, op);
            if (_mv_1724.has_value) {
                __auto_type sig = _mv_1724.value;
                if (infer_has_type_params(sig)) {
                    return infer_infer_generic_call(env, sig, expr, line, col);
                } else {
                    infer_check_fn_call_args(env, sig, expr, line, col);
                    return (*sig).return_type;
                }
            } else if (!_mv_1724.has_value) {
                __auto_type _mv_1725 = env_env_lookup_type(env, op);
                if (_mv_1725.has_value) {
                    __auto_type the_type = _mv_1725.value;
                    return the_type;
                } else if (!_mv_1725.has_value) {
                    if (string_eq(op, SLOP_STR("list-get"))) {
                        infer_check_builtin_args(env, SLOP_STR("list-get"), 2, (len - 1), line, col);
                        infer_infer_builtin_args(env, expr);
                        {
                            types_ResolvedType* elem_type = NULL;
                            if (len >= 2) {
                                __auto_type _mv_1726 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1726.has_value) {
                                    __auto_type list_arg = _mv_1726.value;
                                    {
                                        __auto_type list_type = infer_infer_expr(env, list_arg);
                                        if ((*list_type).kind == types_ResolvedTypeKind_rk_list) {
                                            __auto_type _mv_1727 = (*list_type).inner_type;
                                            if (_mv_1727.has_value) {
                                                __auto_type inner = _mv_1727.value;
                                                elem_type = inner;
                                            } else if (!_mv_1727.has_value) {
                                            }
                                        }
                                    }
                                } else if (!_mv_1726.has_value) {
                                }
                            }
                            return env_env_make_option_type(env, elem_type);
                        }
                    } else if (string_eq(op, SLOP_STR("list-len"))) {
                        infer_check_builtin_args(env, SLOP_STR("list-len"), 1, (len - 1), line, col);
                        return env_env_get_int_type(env);
                    } else if ((string_eq(op, SLOP_STR("is-none")) || string_eq(op, SLOP_STR("is-some"))) && ({ __auto_type _mv = env_env_lookup_var(env, op); _mv.has_value ? ({ __auto_type v = _mv.value; 0; }) : (1); })) {
                        infer_check_builtin_args(env, op, 1, (len - 1), line, col);
                        infer_check_option_predicate_arg(env, op, items, len, line, col);
                        return env_env_get_bool_type(env);
                    } else if (string_eq(op, SLOP_STR("arena-alloc"))) {
                        if (len < 3) {
                            env_env_add_error(env, SLOP_STR("arena-alloc requires arena and type/size arguments"), line, col);
                            return env_env_get_int_type(env);
                        } else {
                            __auto_type _mv_1728 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1728.has_value) {
                                __auto_type type_expr = _mv_1728.value;
                                {
                                    __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                                    if (string_eq(type_name, SLOP_STR(""))) {
                                        if (parser_sexpr_is_list(type_expr)) {
                                            __auto_type _mv_1729 = parser_sexpr_list_get(type_expr, 0);
                                            if (_mv_1729.has_value) {
                                                __auto_type head_expr = _mv_1729.value;
                                                if (string_eq(parser_sexpr_get_symbol_name(head_expr), SLOP_STR("sizeof"))) {
                                                    __auto_type _mv_1730 = parser_sexpr_list_get(type_expr, 1);
                                                    if (_mv_1730.has_value) {
                                                        __auto_type sizeof_type_expr = _mv_1730.value;
                                                        {
                                                            __auto_type sizeof_type_name = parser_sexpr_get_symbol_name(sizeof_type_expr);
                                                            if (string_eq(sizeof_type_name, SLOP_STR(""))) {
                                                                return env_env_get_int_type(env);
                                                            } else {
                                                                __auto_type _mv_1731 = env_env_lookup_type(env, sizeof_type_name);
                                                                if (_mv_1731.has_value) {
                                                                    __auto_type resolved = _mv_1731.value;
                                                                    return env_env_make_ptr_type(env, resolved);
                                                                } else if (!_mv_1731.has_value) {
                                                                    return env_env_get_int_type(env);
                                                                }
                                                                SLOP_UNREACHABLE();
                                                            }
                                                        }
                                                    } else if (!_mv_1730.has_value) {
                                                        return env_env_get_int_type(env);
                                                    }
                                                    SLOP_UNREACHABLE();
                                                } else {
                                                    return env_env_get_int_type(env);
                                                }
                                            } else if (!_mv_1729.has_value) {
                                                return env_env_get_int_type(env);
                                            }
                                            SLOP_UNREACHABLE();
                                        } else {
                                            return env_env_get_int_type(env);
                                        }
                                    } else {
                                        __auto_type _mv_1732 = env_env_lookup_type(env, type_name);
                                        if (_mv_1732.has_value) {
                                            __auto_type resolved = _mv_1732.value;
                                            return env_env_make_ptr_type(env, resolved);
                                        } else if (!_mv_1732.has_value) {
                                            {
                                                __auto_type arena = env_env_arena(env);
                                                env_env_add_warning(env, string_concat(arena, SLOP_STR("arena-alloc: unknown type: "), type_name), line, col);
                                            }
                                            return env_env_get_int_type(env);
                                        }
                                        SLOP_UNREACHABLE();
                                    }
                                }
                            } else if (!_mv_1728.has_value) {
                                return env_env_get_int_type(env);
                            }
                            SLOP_UNREACHABLE();
                        }
                    } else if (string_eq(op, SLOP_STR("arena-new"))) {
                        infer_check_builtin_args(env, SLOP_STR("arena-new"), 1, (len - 1), line, col);
                        return env_env_get_arena_type(env);
                    } else if (string_eq(op, SLOP_STR("arena-free"))) {
                        infer_check_builtin_args(env, SLOP_STR("arena-free"), 1, (len - 1), line, col);
                        return env_env_get_unit_type(env);
                    } else if (string_eq(op, SLOP_STR("cast"))) {
                        return env_env_get_int_type(env);
                    } else if (string_eq(op, SLOP_STR("list-push"))) {
                        infer_check_builtin_args(env, SLOP_STR("list-push"), 2, (len - 1), line, col);
                        infer_infer_builtin_args(env, expr);
                        __auto_type _mv_1733 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1733.has_value) {
                            __auto_type list_arg = _mv_1733.value;
                            infer_check_list_target(env, SLOP_STR("list-push"), list_arg, line, col);
                        } else if (!_mv_1733.has_value) {
                        }
                        return env_env_get_unit_type(env);
                    } else if (string_eq(op, SLOP_STR("list-set"))) {
                        infer_check_builtin_args(env, SLOP_STR("list-set"), 3, (len - 1), line, col);
                        infer_infer_builtin_args(env, expr);
                        __auto_type _mv_1734 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1734.has_value) {
                            __auto_type list_arg = _mv_1734.value;
                            infer_check_list_target(env, SLOP_STR("list-set"), list_arg, line, col);
                        } else if (!_mv_1734.has_value) {
                        }
                        return env_env_get_bool_type(env);
                    } else if (string_eq(op, SLOP_STR("list-pop"))) {
                        infer_check_builtin_args(env, SLOP_STR("list-pop"), 1, (len - 1), line, col);
                        return env_env_make_option_type(env, NULL);
                    } else if (string_eq(op, SLOP_STR("list-new"))) {
                        infer_check_builtin_args(env, SLOP_STR("list-new"), 2, (len - 1), line, col);
                        {
                            __auto_type arena = env_env_arena(env);
                            __auto_type list_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_list, SLOP_STR("List"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_list_t*"));
                            if (len >= 3) {
                                __auto_type _mv_1735 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1735.has_value) {
                                    __auto_type type_expr = _mv_1735.value;
                                    {
                                        __auto_type elem_type = ((parser_sexpr_is_list(type_expr)) ? infer_resolve_complex_type_expr(env, type_expr) : ({ __auto_type tname = parser_sexpr_get_symbol_name(type_expr); ((string_eq(tname, SLOP_STR(""))) ? NULL : infer_resolve_simple_type(env, tname)); }));
                                        if (elem_type != NULL) {
                                            types_resolved_type_set_inner(list_type, elem_type);
                                        }
                                    }
                                } else if (!_mv_1735.has_value) {
                                }
                            }
                            return list_type;
                        }
                    } else if (string_eq(op, SLOP_STR("sexpr-is-list"))) {
                        return env_env_get_bool_type(env);
                    } else if (string_eq(op, SLOP_STR("sexpr-is-symbol"))) {
                        return env_env_get_bool_type(env);
                    } else if (string_eq(op, SLOP_STR("sexpr-list-len"))) {
                        return env_env_get_int_type(env);
                    } else if (string_eq(op, SLOP_STR("sexpr-list-get"))) {
                        return env_env_make_option_type(env, NULL);
                    } else if (string_eq(op, SLOP_STR("sexpr-get-symbol-name"))) {
                        return env_env_get_string_type(env);
                    } else if (string_eq(op, SLOP_STR("sexpr-line"))) {
                        return env_env_get_int_type(env);
                    } else if (string_eq(op, SLOP_STR("sexpr-col"))) {
                        return env_env_get_int_type(env);
                    } else if (string_eq(op, SLOP_STR("print"))) {
                        return env_env_get_unit_type(env);
                    } else if (string_eq(op, SLOP_STR("println"))) {
                        return env_env_get_unit_type(env);
                    } else if (string_eq(op, SLOP_STR("ok"))) {
                        {
                            __auto_type arena = env_env_arena(env);
                            __auto_type result_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_result, SLOP_STR("Result"), ((slop_option_string){.has_value = false}), SLOP_STR("Result"));
                            if (len >= 2) {
                                __auto_type _mv_1736 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1736.has_value) {
                                    __auto_type val_expr = _mv_1736.value;
                                    {
                                        __auto_type val_type = infer_infer_expr(env, val_expr);
                                        types_resolved_type_set_inner(result_type, val_type);
                                    }
                                } else if (!_mv_1736.has_value) {
                                }
                            }
                            return result_type;
                        }
                    } else if (string_eq(op, SLOP_STR("error"))) {
                        {
                            __auto_type arena = env_env_arena(env);
                            __auto_type result_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_result, SLOP_STR("Result"), ((slop_option_string){.has_value = false}), SLOP_STR("Result"));
                            if (len >= 2) {
                                __auto_type _mv_1737 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1737.has_value) {
                                    __auto_type val_expr = _mv_1737.value;
                                    {
                                        __auto_type val_type = infer_infer_expr(env, val_expr);
                                        types_resolved_type_set_inner2(result_type, val_type);
                                    }
                                } else if (!_mv_1737.has_value) {
                                }
                            }
                            return result_type;
                        }
                    } else if (string_eq(op, SLOP_STR("@"))) {
                        if (len >= 2) {
                            __auto_type _mv_1738 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1738.has_value) {
                                __auto_type ptr_expr = _mv_1738.value;
                                {
                                    __auto_type ptr_type = infer_infer_expr(env, ptr_expr);
                                    if (types_resolved_type_is_pointer(ptr_type)) {
                                        __auto_type _mv_1739 = (*ptr_type).inner_type;
                                        if (_mv_1739.has_value) {
                                            __auto_type inner = _mv_1739.value;
                                            return inner;
                                        } else if (!_mv_1739.has_value) {
                                            return env_env_get_int_type(env);
                                        }
                                        SLOP_UNREACHABLE();
                                    } else {
                                        return env_env_get_int_type(env);
                                    }
                                }
                            } else if (!_mv_1738.has_value) {
                                return env_env_get_int_type(env);
                            }
                            SLOP_UNREACHABLE();
                        } else {
                            return env_env_get_int_type(env);
                        }
                    } else if (string_eq(op, SLOP_STR("some"))) {
                        return env_env_make_option_type(env, NULL);
                    } else if (string_eq(op, SLOP_STR("c-inline"))) {
                        return env_env_get_generic_type(env);
                    } else if (string_eq(op, SLOP_STR("map-new"))) {
                        infer_check_builtin_args(env, SLOP_STR("map-new"), 3, (len - 1), line, col);
                        {
                            __auto_type arena = env_env_arena(env);
                            types_ResolvedType* key_type = NULL;
                            types_ResolvedType* val_type = NULL;
                            if (len >= 3) {
                                __auto_type _mv_1740 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1740.has_value) {
                                    __auto_type type_expr = _mv_1740.value;
                                    {
                                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                                        if (!(string_eq(type_name, SLOP_STR("")))) {
                                            __auto_type _mv_1741 = env_env_lookup_type(env, type_name);
                                            if (_mv_1741.has_value) {
                                                __auto_type t = _mv_1741.value;
                                                key_type = t;
                                            } else if (!_mv_1741.has_value) {
                                            }
                                        }
                                    }
                                } else if (!_mv_1740.has_value) {
                                }
                            }
                            if (len >= 4) {
                                __auto_type _mv_1742 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1742.has_value) {
                                    __auto_type type_expr = _mv_1742.value;
                                    {
                                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                                        if (!(string_eq(type_name, SLOP_STR("")))) {
                                            __auto_type _mv_1743 = env_env_lookup_type(env, type_name);
                                            if (_mv_1743.has_value) {
                                                __auto_type t = _mv_1743.value;
                                                val_type = t;
                                            } else if (!_mv_1743.has_value) {
                                            }
                                        }
                                    }
                                } else if (!_mv_1742.has_value) {
                                }
                            }
                            {
                                __auto_type map_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_map, SLOP_STR("Map"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_map*"));
                                if (key_type != NULL) {
                                    types_resolved_type_set_inner(map_type, key_type);
                                }
                                if (val_type != NULL) {
                                    types_resolved_type_set_inner2(map_type, val_type);
                                }
                                return map_type;
                            }
                        }
                    } else if (string_eq(op, SLOP_STR("map-get"))) {
                        infer_check_builtin_args(env, SLOP_STR("map-get"), 2, (len - 1), line, col);
                        {
                            types_ResolvedType* val_type = NULL;
                            if (len >= 2) {
                                __auto_type _mv_1744 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1744.has_value) {
                                    __auto_type map_expr = _mv_1744.value;
                                    {
                                        __auto_type map_type = infer_infer_expr(env, map_expr);
                                        __auto_type _mv_1745 = (*map_type).inner_type2;
                                        if (_mv_1745.has_value) {
                                            __auto_type inner = _mv_1745.value;
                                            val_type = inner;
                                        } else if (!_mv_1745.has_value) {
                                        }
                                    }
                                } else if (!_mv_1744.has_value) {
                                }
                            }
                            return env_env_make_option_type(env, val_type);
                        }
                    } else if (string_eq(op, SLOP_STR("map-put"))) {
                        infer_check_builtin_args(env, SLOP_STR("map-put"), 3, (len - 1), line, col);
                        return env_env_get_unit_type(env);
                    } else if (string_eq(op, SLOP_STR("map-has"))) {
                        infer_check_builtin_args(env, SLOP_STR("map-has"), 2, (len - 1), line, col);
                        if (len >= 2) {
                            __auto_type _mv_1746 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1746.has_value) {
                                __auto_type map_expr = _mv_1746.value;
                                {
                                    __auto_type map_type = infer_infer_expr(env, map_expr);
                                    __auto_type type_name = (*map_type).name;
                                    __auto_type arena = env_env_arena(env);
                                    if (strlib_starts_with(type_name, SLOP_STR("Option"))) {
                                        {
                                            __auto_type msg = string_concat(arena, SLOP_STR("map-has: expected Map, got "), string_concat(arena, type_name, SLOP_STR(" - use match to unwrap Option first")));
                                            env_env_add_error(env, msg, line, col);
                                        }
                                    }
                                }
                            } else if (!_mv_1746.has_value) {
                            }
                        }
                        return env_env_get_bool_type(env);
                    } else if (string_eq(op, SLOP_STR("map-keys"))) {
                        infer_check_builtin_args(env, SLOP_STR("map-keys"), 1, (len - 1), line, col);
                        {
                            __auto_type arena = env_env_arena(env);
                            types_ResolvedType* key_type = NULL;
                            if (len >= 2) {
                                __auto_type _mv_1747 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1747.has_value) {
                                    __auto_type map_expr = _mv_1747.value;
                                    {
                                        __auto_type map_type = infer_infer_expr(env, map_expr);
                                        __auto_type _mv_1748 = (*map_type).inner_type;
                                        if (_mv_1748.has_value) {
                                            __auto_type inner = _mv_1748.value;
                                            key_type = inner;
                                        } else if (!_mv_1748.has_value) {
                                        }
                                    }
                                } else if (!_mv_1747.has_value) {
                                }
                            }
                            {
                                __auto_type list_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_list, SLOP_STR("List"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_list_t*"));
                                if (key_type != NULL) {
                                    types_resolved_type_set_inner(list_type, key_type);
                                }
                                return list_type;
                            }
                        }
                    } else if (string_eq(op, SLOP_STR("map-remove"))) {
                        infer_check_builtin_args(env, SLOP_STR("map-remove"), 2, (len - 1), line, col);
                        return env_env_get_unit_type(env);
                    } else if (string_eq(op, SLOP_STR("set"))) {
                        {
                            __auto_type arena = env_env_arena(env);
                            return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Set"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_map*"));
                        }
                    } else if (string_eq(op, SLOP_STR("set-new"))) {
                        infer_check_builtin_args(env, SLOP_STR("set-new"), 2, (len - 1), line, col);
                        {
                            __auto_type arena = env_env_arena(env);
                            types_ResolvedType* elem_type = NULL;
                            if (len >= 3) {
                                __auto_type _mv_1749 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1749.has_value) {
                                    __auto_type type_expr = _mv_1749.value;
                                    {
                                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                                        if (!(string_eq(type_name, SLOP_STR("")))) {
                                            __auto_type _mv_1750 = env_env_lookup_type(env, type_name);
                                            if (_mv_1750.has_value) {
                                                __auto_type t = _mv_1750.value;
                                                elem_type = t;
                                            } else if (!_mv_1750.has_value) {
                                            }
                                        }
                                    }
                                } else if (!_mv_1749.has_value) {
                                }
                            }
                            {
                                __auto_type set_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Set"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_map*"));
                                if (elem_type != NULL) {
                                    types_resolved_type_set_inner(set_type, elem_type);
                                }
                                return set_type;
                            }
                        }
                    } else if (string_eq(op, SLOP_STR("set-put"))) {
                        infer_check_builtin_args(env, SLOP_STR("set-put"), 2, (len - 1), line, col);
                        return env_env_get_unit_type(env);
                    } else if (string_eq(op, SLOP_STR("set-has"))) {
                        infer_check_builtin_args(env, SLOP_STR("set-has"), 2, (len - 1), line, col);
                        return env_env_get_bool_type(env);
                    } else if (string_eq(op, SLOP_STR("set-remove"))) {
                        infer_check_builtin_args(env, SLOP_STR("set-remove"), 2, (len - 1), line, col);
                        return env_env_get_unit_type(env);
                    } else if (string_eq(op, SLOP_STR("set-elements"))) {
                        infer_check_builtin_args(env, SLOP_STR("set-elements"), 1, (len - 1), line, col);
                        {
                            __auto_type arena = env_env_arena(env);
                            types_ResolvedType* elem_type = NULL;
                            if (len >= 2) {
                                __auto_type _mv_1751 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1751.has_value) {
                                    __auto_type set_expr = _mv_1751.value;
                                    {
                                        __auto_type set_type = infer_infer_expr(env, set_expr);
                                        __auto_type _mv_1752 = (*set_type).inner_type;
                                        if (_mv_1752.has_value) {
                                            __auto_type inner = _mv_1752.value;
                                            elem_type = inner;
                                        } else if (!_mv_1752.has_value) {
                                        }
                                    }
                                } else if (!_mv_1751.has_value) {
                                }
                            }
                            {
                                __auto_type list_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_list, SLOP_STR("List"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_list_t*"));
                                if (elem_type != NULL) {
                                    types_resolved_type_set_inner(list_type, elem_type);
                                }
                                return list_type;
                            }
                        }
                    } else if (string_eq(op, SLOP_STR("exists")) || (string_eq(op, SLOP_STR("forall")) || string_eq(op, SLOP_STR("implies")))) {
                        return env_env_get_unit_type(env);
                    } else {
                        {
                            __auto_type arena = env_env_arena(env);
                            __auto_type _mv_1753 = env_env_lookup_variant(env, op);
                            if (_mv_1753.has_value) {
                                __auto_type parent_type = _mv_1753.value;
                                {
                                    __auto_type msg = string_concat(arena, SLOP_STR("'"), string_concat(arena, op, string_concat(arena, SLOP_STR("' is a variant of '"), string_concat(arena, parent_type, SLOP_STR("'. Use (union-new Type variant value) syntax")))));
                                    env_env_add_error(env, msg, line, col);
                                    return env_env_get_unknown_type(env);
                                }
                            } else if (!_mv_1753.has_value) {
                                if (strlib_starts_with(op, SLOP_STR("set-")) || (strlib_starts_with(op, SLOP_STR("map-")) || (strlib_starts_with(op, SLOP_STR("list-")) || strlib_starts_with(op, SLOP_STR("arena-"))))) {
                                    {
                                        __auto_type msg = string_concat(arena, SLOP_STR("Unknown builtin: '"), string_concat(arena, op, SLOP_STR("'")));
                                        env_env_add_error(env, msg, line, col);
                                        return env_env_get_unknown_type(env);
                                    }
                                } else {
                                    __auto_type _mv_1754 = env_env_lookup_var(env, op);
                                    if (_mv_1754.has_value) {
                                        __auto_type var_type = _mv_1754.value;
                                        infer_infer_builtin_args(env, expr);
                                        return var_type;
                                    } else if (!_mv_1754.has_value) {
                                        if (infer_string_contains_char(op, 45)) {
                                            {
                                                __auto_type msg = string_concat(arena, SLOP_STR("Unknown function: '"), string_concat(arena, op, SLOP_STR("' - did you forget to import it?")));
                                                env_env_add_error(env, msg, line, col);
                                            }
                                            infer_infer_builtin_args(env, expr);
                                            return env_env_get_unknown_type(env);
                                        } else {
                                            infer_infer_builtin_args(env, expr);
                                            return env_env_get_unknown_type(env);
                                        }
                                    }
                                    SLOP_UNREACHABLE();
                                }
                            }
                            SLOP_UNREACHABLE();
                        }
                    }
                }
                SLOP_UNREACHABLE();
            }
            SLOP_UNREACHABLE();
        }
    }
}

void infer_check_fn_call_args(env_TypeEnv* env, types_FnSignature* sig, types_SExpr* expr, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((sig != NULL)), "(!= sig nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type fn_name = (*sig).name;
        __auto_type params = (*sig).params;
        __auto_type num_params = ((int64_t)((params).len));
        __auto_type arena = env_env_arena(env);
        if (parser_sexpr_is_list(expr)) {
            {
                __auto_type num_args = (parser_sexpr_list_len(expr) - 1);
                if (num_args < num_params) {
                    {
                        __auto_type msg = string_concat(arena, SLOP_STR("'"), string_concat(arena, fn_name, string_concat(arena, SLOP_STR("' expects "), string_concat(arena, int_to_string(arena, num_params), string_concat(arena, SLOP_STR(" argument(s), got "), int_to_string(arena, num_args))))));
                        env_env_add_error(env, msg, line, col);
                    }
                } else if ((num_args > num_params) && !((*sig).is_variadic)) {
                    {
                        __auto_type msg = string_concat(arena, SLOP_STR("'"), string_concat(arena, fn_name, string_concat(arena, SLOP_STR("' expects "), string_concat(arena, int_to_string(arena, num_params), string_concat(arena, SLOP_STR(" argument(s), got "), int_to_string(arena, num_args))))));
                        env_env_add_error(env, msg, line, col);
                    }
                } else {
                    for (int64_t i = 0; i < num_params; i++) {
                        infer_check_single_arg(env, sig, expr, i, line, col);
                    }
                }
            }
        }
    }
}

void infer_check_single_arg(env_TypeEnv* env, types_FnSignature* sig, types_SExpr* expr, int64_t arg_idx, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((sig != NULL)), "(!= sig nil)");
    {
        __auto_type params = (*sig).params;
        __auto_type fn_name = (*sig).name;
        __auto_type arena = env_env_arena(env);
        __auto_type _mv_1755 = ({ __auto_type _lst = params; size_t _idx = (size_t)arg_idx; slop_option_types_ParamInfo _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1755.has_value) {
            __auto_type param_info = _mv_1755.value;
            {
                __auto_type expected_type = param_info.param_type;
                __auto_type _mv_1756 = parser_sexpr_list_get(expr, (arg_idx + 1));
                if (_mv_1756.has_value) {
                    __auto_type arg_expr = _mv_1756.value;
                    {
                        __auto_type actual_type = infer_infer_expr(env, arg_expr);
                        __auto_type expected_name = (*expected_type).name;
                        __auto_type actual_name = (*actual_type).name;
                        if (((string_eq(actual_name, SLOP_STR("Option_T")) || strlib_starts_with(actual_name, SLOP_STR("Option_")))) && (!(strlib_starts_with(expected_name, SLOP_STR("Option_")))) && (((*expected_type).kind != types_ResolvedTypeKind_rk_option))) {
                            {
                                __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                                ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("argument ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                ({ __auto_type _lst_p = &(parts); __auto_type _item = (int_to_string(arena, (arg_idx + 1))); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(" to '")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                ({ __auto_type _lst_p = &(parts); __auto_type _item = (fn_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("': expected ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                ({ __auto_type _lst_p = &(parts); __auto_type _item = (expected_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(", got ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                ({ __auto_type _lst_p = &(parts); __auto_type _item = (actual_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(" - use match to unwrap")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                env_env_add_error(env, strlib_string_build(arena, parts), line, col);
                            }
                        }
                        if ((!(infer_types_equal(expected_type, actual_type))) && (!(string_eq(actual_name, SLOP_STR("Unknown")))) && (!(string_eq(actual_name, SLOP_STR("T")))) && (!(string_eq(expected_name, SLOP_STR("Unknown")))) && (!(string_eq(expected_name, SLOP_STR("T")))) && (!((string_eq(actual_name, SLOP_STR("Option_T")) && strlib_starts_with(expected_name, SLOP_STR("Option_"))))) && (!(string_eq(actual_name, SLOP_STR("Ptr_T")))) && (!(strlib_starts_with(actual_name, SLOP_STR("Ptr_Ptr_")))) && (!((string_eq(actual_name, SLOP_STR("Unit")) && strlib_starts_with(expected_name, SLOP_STR("Ptr_"))))) && (!((strlib_starts_with(actual_name, SLOP_STR("Ptr_")) && string_eq(expected_name, SLOP_STR("Ptr_Void"))))) && (!((infer_is_integer_type(actual_name) && infer_is_integer_type(expected_name))))) {
                            {
                                __auto_type msg = string_concat(arena, SLOP_STR("argument "), string_concat(arena, int_to_string(arena, (arg_idx + 1)), string_concat(arena, SLOP_STR(" to '"), string_concat(arena, fn_name, string_concat(arena, SLOP_STR("': expected "), string_concat(arena, expected_name, string_concat(arena, SLOP_STR(", got "), actual_name)))))));
                                env_env_add_error(env, msg, line, col);
                            }
                        }
                    }
                } else if (!_mv_1756.has_value) {
                }
            }
        } else if (!_mv_1755.has_value) {
        }
    }
}

uint8_t infer_is_assignable_list_target(types_SExpr* expr) {
    if (!(parser_sexpr_is_list(expr))) {
        return 1;
    } else {
        {
            __auto_type head = parser_sexpr_list_get(expr, 0);
            __auto_type _mv_1757 = head;
            if (_mv_1757.has_value) {
                __auto_type h = _mv_1757.value;
                {
                    __auto_type name = parser_sexpr_get_symbol_name(h);
                    return (string_eq(name, SLOP_STR(".")) || string_eq(name, SLOP_STR("deref")));
                }
            } else if (!_mv_1757.has_value) {
                return 0;
            }
            SLOP_UNREACHABLE();
        }
    }
}

void infer_check_list_target(env_TypeEnv* env, slop_string op, types_SExpr* expr, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    if (!(infer_is_assignable_list_target(expr))) {
        {
            __auto_type arena = env_env_arena(env);
            __auto_type msg = string_concat(arena, SLOP_STR("'"), string_concat(arena, op, SLOP_STR("' needs a list it can write through: a variable, a field, or a dereferenced pointer - not the result of a call")));
            env_env_add_error(env, msg, line, col);
        }
    }
}

void infer_check_builtin_args(env_TypeEnv* env, slop_string op, int64_t expected, int64_t actual, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    if (actual != expected) {
        {
            __auto_type arena = env_env_arena(env);
            __auto_type msg = string_concat(arena, SLOP_STR("'"), string_concat(arena, op, string_concat(arena, SLOP_STR("' expects "), string_concat(arena, int_to_string(arena, expected), string_concat(arena, SLOP_STR(" argument(s), got "), int_to_string(arena, actual))))));
            env_env_add_error(env, msg, line, col);
        }
    }
}

types_ResolvedType* infer_resolve_alias_chain(types_ResolvedType* t) {
    SLOP_PRE(((t != NULL)), "(!= t nil)");
    {
        __auto_type cur = t;
        int64_t steps = 0;
        uint8_t done = 0;
        while (!(done) && (steps < 64)) {
            if (((*cur).kind == types_ResolvedTypeKind_rk_primitive) && !(strlib_ends_with((*cur).c_name, SLOP_STR("*")))) {
                __auto_type _mv_1758 = (*cur).inner_type;
                if (_mv_1758.has_value) {
                    __auto_type next = _mv_1758.value;
                    cur = next;
                    steps = (steps + 1);
                } else if (!_mv_1758.has_value) {
                    done = 1;
                }
            } else {
                done = 1;
            }
        }
        return cur;
    }
}

void infer_check_option_predicate_arg(env_TypeEnv* env, slop_string op, slop_list_types_SExpr_ptr items, int64_t len, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    if (len >= 2) {
        __auto_type _mv_1759 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1759.has_value) {
            __auto_type arg = _mv_1759.value;
            {
                __auto_type raw_type = infer_infer_expr(env, arg);
                __auto_type arg_type = infer_resolve_alias_chain(raw_type);
                __auto_type kind = (*arg_type).kind;
                __auto_type reported_name = (*raw_type).name;
                __auto_type resolved_name = (*arg_type).name;
                __auto_type resolved_c_name = (*arg_type).c_name;
                __auto_type arena = env_env_arena(env);
                if (kind == types_ResolvedTypeKind_rk_option) {
                } else if (kind == types_ResolvedTypeKind_rk_typevar) {
                    env_env_add_error(env, string_concat(arena, SLOP_STR("'"), string_concat(arena, op, string_concat(arena, SLOP_STR("' expects an (Option T), got type parameter "), string_concat(arena, reported_name, SLOP_STR(" - declare the parameter as (Option T)"))))), line, col);
                } else if (string_eq(resolved_name, SLOP_STR("Unknown"))) {
                } else if (((kind == types_ResolvedTypeKind_rk_primitive)) && (!(ctype_is_builtin_type(resolved_name))) && (!(strlib_ends_with(resolved_c_name, SLOP_STR("*"))))) {
                } else {
                    env_env_add_error(env, string_concat(arena, SLOP_STR("'"), string_concat(arena, op, string_concat(arena, SLOP_STR("' expects an (Option T), got "), reported_name))), line, col);
                }
            }
        } else if (!_mv_1759.has_value) {
        }
    }
}

void infer_infer_builtin_args(env_TypeEnv* env, types_SExpr* expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    if (parser_sexpr_is_list(expr)) {
        {
            __auto_type len = parser_sexpr_list_len(expr);
            for (int64_t i = 1; i < len; i++) {
                __auto_type _mv_1760 = parser_sexpr_list_get(expr, i);
                if (_mv_1760.has_value) {
                    __auto_type arg_expr = _mv_1760.value;
                    {
                        __auto_type _ = infer_infer_expr(env, arg_expr);
                    }
                } else if (!_mv_1760.has_value) {
                }
            }
        }
    }
}

void infer_infer_body_exprs(env_TypeEnv* env, types_SExpr* expr, int64_t start_idx) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    if (parser_sexpr_is_list(expr)) {
        {
            __auto_type len = parser_sexpr_list_len(expr);
            for (int64_t i = start_idx; i < len; i++) {
                __auto_type _mv_1761 = parser_sexpr_list_get(expr, i);
                if (_mv_1761.has_value) {
                    __auto_type body_expr = _mv_1761.value;
                    {
                        __auto_type _ = infer_infer_expr(env, body_expr);
                    }
                } else if (!_mv_1761.has_value) {
                }
            }
        }
    }
}

types_ResolvedType* infer_infer_field_access(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type items = lst.items;
        __auto_type len = ((int64_t)((items).len));
        if (len < 3) {
            return env_env_get_unit_type(env);
        } else {
            __auto_type _mv_1762 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (!_mv_1762.has_value) {
                return env_env_get_unit_type(env);
            } else if (_mv_1762.has_value) {
                __auto_type obj_expr = _mv_1762.value;
                {
                    __auto_type obj_type = infer_infer_expr(env, obj_expr);
                    __auto_type _mv_1763 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (!_mv_1763.has_value) {
                        return env_env_get_unit_type(env);
                    } else if (_mv_1763.has_value) {
                        __auto_type field_expr = _mv_1763.value;
                        __auto_type _mv_1764 = (*field_expr);
                        switch (_mv_1764.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type field_sym = _mv_1764.data.sym;
                                {
                                    __auto_type field_name = field_sym.name;
                                    return infer_check_field_exists(env, obj_type, field_name, line, col);
                                }
                            }
                            default: {
                                return env_env_get_unit_type(env);
                            }
                        }
                    }
                    SLOP_UNREACHABLE();
                }
            }
            SLOP_UNREACHABLE();
        }
    }
}

types_ResolvedType* infer_check_field_exists(env_TypeEnv* env, types_ResolvedType* obj_type, slop_string field_name, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((obj_type != NULL)), "(!= obj-type nil)");
    {
        __auto_type type_name = (*obj_type).name;
        __auto_type arena = env_env_arena(env);
        if (infer_type_is_null_pointer(obj_type)) {
            {
                __auto_type msg = string_concat(arena, SLOP_STR("cannot access field '"), string_concat(arena, field_name, SLOP_STR("' on nil")));
                env_env_add_error(env, msg, line, col);
                return env_env_get_unknown_type(env);
            }
        } else {
            if (types_resolved_type_is_record(obj_type)) {
                __auto_type _mv_1765 = types_resolved_type_get_field_type(obj_type, field_name);
                if (_mv_1765.has_value) {
                    __auto_type field_type = _mv_1765.value;
                    return field_type;
                } else if (!_mv_1765.has_value) {
                    {
                        __auto_type msg = string_concat(arena, SLOP_STR("Record '"), string_concat(arena, type_name, string_concat(arena, SLOP_STR("' has no field '"), string_concat(arena, field_name, SLOP_STR("'")))));
                        env_env_add_error(env, msg, line, col);
                        return env_env_get_unit_type(env);
                    }
                }
                SLOP_UNREACHABLE();
            } else {
                if (string_eq(type_name, SLOP_STR("T"))) {
                    return env_env_get_generic_type(env);
                } else {
                    if (string_eq(type_name, SLOP_STR("String"))) {
                        if (string_eq(field_name, SLOP_STR("data"))) {
                            return env_env_get_int_type(env);
                        } else if (string_eq(field_name, SLOP_STR("len"))) {
                            return env_env_get_int_type(env);
                        } else {
                            return env_env_get_unknown_type(env);
                        }
                    } else {
                        if (string_eq(type_name, SLOP_STR("Unknown"))) {
                            return env_env_get_unknown_type(env);
                        } else {
                            if (types_resolved_type_is_pointer(obj_type)) {
                                __auto_type _mv_1766 = (*obj_type).inner_type;
                                if (_mv_1766.has_value) {
                                    __auto_type inner_type = _mv_1766.value;
                                    return infer_check_field_exists(env, inner_type, field_name, line, col);
                                } else if (!_mv_1766.has_value) {
                                    return env_env_get_unknown_type(env);
                                }
                                SLOP_UNREACHABLE();
                            } else {
                                if (string_eq(type_name, SLOP_STR("Chan")) || string_eq(type_name, SLOP_STR("Thread"))) {
                                    return env_env_get_unknown_type(env);
                                } else {
                                    {
                                        __auto_type msg = string_concat(arena, SLOP_STR("Cannot access field '"), string_concat(arena, field_name, string_concat(arena, SLOP_STR("' on non-record type '"), string_concat(arena, type_name, SLOP_STR("'")))));
                                        env_env_add_error(env, msg, line, col);
                                        return env_env_get_unknown_type(env);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

types_ResolvedType* infer_infer_cond_expr(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type items = lst.items;
        __auto_type len = ((int64_t)((items).len));
        __auto_type line = parser_sexpr_line(expr);
        __auto_type col = parser_sexpr_col(expr);
        uint8_t has_result = 0;
        types_ResolvedType* result_type = env_env_get_unit_type(env);
        int64_t i = 1;
        while (i < len) {
            __auto_type _mv_1767 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1767.has_value) {
                __auto_type clause = _mv_1767.value;
                __auto_type _mv_1768 = (*clause);
                switch (_mv_1768.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type clause_lst = _mv_1768.data.lst;
                        {
                            __auto_type clause_items = clause_lst.items;
                            __auto_type clause_len = ((int64_t)((clause_items).len));
                            if (clause_len > 1) {
                                for (int64_t ci = 0; ci < (clause_len - 1); ci++) {
                                    __auto_type _mv_1769 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)ci; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_1769.has_value) {
                                        __auto_type clause_elem = _mv_1769.value;
                                        {
                                            __auto_type elem_name = parser_sexpr_get_symbol_name(clause_elem);
                                            if (!(string_eq(elem_name, SLOP_STR("else")))) {
                                                {
                                                    __auto_type _ = infer_infer_expr(env, clause_elem);
                                                }
                                            }
                                        }
                                    } else if (!_mv_1769.has_value) {
                                    }
                                }
                                __auto_type _mv_1770 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)(clause_len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1770.has_value) {
                                    __auto_type body = _mv_1770.value;
                                    {
                                        __auto_type body_type = infer_infer_expr(env, body);
                                        if (!(has_result)) {
                                            result_type = body_type;
                                            has_result = 1;
                                        } else {
                                            result_type = infer_unify_branch_types(env, result_type, body_type, line, col);
                                        }
                                    }
                                } else if (!_mv_1770.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1767.has_value) {
            }
            i = (i + 1);
        }
        return result_type;
    }
}

void infer_bind_match_pattern(env_TypeEnv* env, types_ResolvedType* scrutinee_type, types_SExpr* pattern) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((pattern != NULL)), "(!= pattern nil)");
    if (parser_sexpr_is_list(pattern)) {
        if (parser_sexpr_list_len(pattern) > 0) {
            __auto_type _mv_1771 = parser_sexpr_list_get(pattern, 0);
            if (_mv_1771.has_value) {
                __auto_type variant_expr = _mv_1771.value;
                {
                    __auto_type variant_name = parser_sexpr_get_symbol_name(variant_expr);
                    if (!(string_eq(variant_name, SLOP_STR("")))) {
                        if (parser_sexpr_list_len(pattern) > 1) {
                            __auto_type _mv_1772 = parser_sexpr_list_get(pattern, 1);
                            if (_mv_1772.has_value) {
                                __auto_type binding_expr = _mv_1772.value;
                                {
                                    __auto_type binding_name = parser_sexpr_get_symbol_name(binding_expr);
                                    if (!(string_eq(binding_name, SLOP_STR("")))) {
                                        {
                                            __auto_type scrutinee_name = (*scrutinee_type).name;
                                            __auto_type scrutinee_kind = (*scrutinee_type).kind;
                                            if (string_eq(scrutinee_name, SLOP_STR("T"))) {
                                                env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                            } else {
                                                if ((scrutinee_kind == types_ResolvedTypeKind_rk_option) && string_eq(variant_name, SLOP_STR("some"))) {
                                                    __auto_type _mv_1773 = (*scrutinee_type).inner_type;
                                                    if (_mv_1773.has_value) {
                                                        __auto_type inner = _mv_1773.value;
                                                        env_env_bind_var(env, binding_name, inner);
                                                    } else if (!_mv_1773.has_value) {
                                                        env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                                    }
                                                } else {
                                                    if (scrutinee_kind == types_ResolvedTypeKind_rk_result) {
                                                        if (string_eq(variant_name, SLOP_STR("ok"))) {
                                                            __auto_type _mv_1774 = (*scrutinee_type).inner_type;
                                                            if (_mv_1774.has_value) {
                                                                __auto_type inner = _mv_1774.value;
                                                                env_env_bind_var(env, binding_name, inner);
                                                            } else if (!_mv_1774.has_value) {
                                                                env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                                            }
                                                        } else if (string_eq(variant_name, SLOP_STR("error"))) {
                                                            __auto_type _mv_1775 = (*scrutinee_type).inner_type2;
                                                            if (_mv_1775.has_value) {
                                                                __auto_type inner2 = _mv_1775.value;
                                                                env_env_bind_var(env, binding_name, inner2);
                                                            } else if (!_mv_1775.has_value) {
                                                                env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                                            }
                                                        } else {
                                                            env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                                        }
                                                    } else {
                                                        {
                                                            __auto_type payload_types = types_resolved_type_get_variant_payloads(env_env_arena(env), scrutinee_type, variant_name);
                                                            if (((int64_t)((payload_types).len)) > 0) {
                                                                if (!(string_eq(binding_name, SLOP_STR("true"))) && !(string_eq(binding_name, SLOP_STR("false")))) {
                                                                    __auto_type _mv_1776 = ({ __auto_type _lst = payload_types; size_t _idx = (size_t)0; slop_option_types_ResolvedType_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                    if (_mv_1776.has_value) {
                                                                        __auto_type first_type = _mv_1776.value;
                                                                        env_env_bind_var(env, binding_name, first_type);
                                                                    } else if (!_mv_1776.has_value) {
                                                                        env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                                                    }
                                                                }
                                                                {
                                                                    __auto_type pat_len = parser_sexpr_list_len(pattern);
                                                                    __auto_type num_types = ((int64_t)((payload_types).len));
                                                                    for (int64_t pi = 2; pi < pat_len; pi++) {
                                                                        __auto_type _mv_1777 = parser_sexpr_list_get(pattern, pi);
                                                                        if (_mv_1777.has_value) {
                                                                            __auto_type extra_binding = _mv_1777.value;
                                                                            {
                                                                                __auto_type extra_name = parser_sexpr_get_symbol_name(extra_binding);
                                                                                if ((!(string_eq(extra_name, SLOP_STR("")))) && (!(string_eq(extra_name, SLOP_STR("_")))) && (!(string_eq(extra_name, SLOP_STR("true")))) && (!(string_eq(extra_name, SLOP_STR("false"))))) {
                                                                                    {
                                                                                        __auto_type type_idx = (pi - 1);
                                                                                        if (type_idx < num_types) {
                                                                                            __auto_type _mv_1778 = ({ __auto_type _lst = payload_types; size_t _idx = (size_t)type_idx; slop_option_types_ResolvedType_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                                            if (_mv_1778.has_value) {
                                                                                                __auto_type pt = _mv_1778.value;
                                                                                                env_env_bind_var(env, extra_name, pt);
                                                                                            } else if (!_mv_1778.has_value) {
                                                                                                env_env_bind_var(env, extra_name, env_env_get_generic_type(env));
                                                                                            }
                                                                                        } else {
                                                                                            env_env_bind_var(env, extra_name, env_env_get_generic_type(env));
                                                                                        }
                                                                                    }
                                                                                }
                                                                            }
                                                                        } else if (!_mv_1777.has_value) {
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            } else if (!_mv_1772.has_value) {
                            }
                        }
                    }
                }
            } else if (!_mv_1771.has_value) {
            }
        }
    }
}

slop_string infer_match_pattern_head(types_SExpr* pattern) {
    SLOP_PRE(((pattern != NULL)), "(!= pattern nil)");
    if (parser_sexpr_is_list(pattern)) {
        if (parser_sexpr_list_len(pattern) > 0) {
            __auto_type _mv_1779 = parser_sexpr_list_get(pattern, 0);
            if (_mv_1779.has_value) {
                __auto_type head = _mv_1779.value;
                return parser_sexpr_get_symbol_name(head);
            } else if (!_mv_1779.has_value) {
                return SLOP_STR("");
            }
            SLOP_UNREACHABLE();
        } else {
            return SLOP_STR("");
        }
    } else {
        return parser_sexpr_get_symbol_name(pattern);
    }
}

uint8_t infer_is_wildcard_head(slop_string head) {
    return (string_eq(head, SLOP_STR("_")) || string_eq(head, SLOP_STR("else")));
}

uint8_t infer_string_list_contains(slop_list_string names, slop_string name) {
    {
        __auto_type n = ((int64_t)((names).len));
        int64_t i = 0;
        uint8_t found = 0;
        while ((i < n) && !(found)) {
            __auto_type _mv_1780 = ({ __auto_type _lst = names; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1780.has_value) {
                __auto_type existing = _mv_1780.value;
                if (string_eq(existing, name)) {
                    found = 1;
                }
            } else if (!_mv_1780.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

slop_list_string infer_match_expected_variants(slop_arena* arena, types_ResolvedType* scrutinee_type) {
    SLOP_PRE(((scrutinee_type != NULL)), "(!= scrutinee-type nil)");
    {
        __auto_type kind = (*scrutinee_type).kind;
        __auto_type result = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        if ((kind == types_ResolvedTypeKind_rk_union) || (kind == types_ResolvedTypeKind_rk_enum)) {
            {
                __auto_type variants = (*scrutinee_type).variants;
                __auto_type n = ((int64_t)((variants).len));
                int64_t i = 0;
                while (i < n) {
                    __auto_type _mv_1781 = ({ __auto_type _lst = variants; size_t _idx = (size_t)i; slop_option_types_ResolvedVariant _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1781.has_value) {
                        __auto_type v = _mv_1781.value;
                        ({ __auto_type _lst_p = &(result); __auto_type _item = (v.name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    } else if (!_mv_1781.has_value) {
                    }
                    i = (i + 1);
                }
                return result;
            }
        } else if (kind == types_ResolvedTypeKind_rk_option) {
            ({ __auto_type _lst_p = &(result); __auto_type _item = (SLOP_STR("some")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            ({ __auto_type _lst_p = &(result); __auto_type _item = (SLOP_STR("none")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            return result;
        } else if (kind == types_ResolvedTypeKind_rk_result) {
            ({ __auto_type _lst_p = &(result); __auto_type _item = (SLOP_STR("ok")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            ({ __auto_type _lst_p = &(result); __auto_type _item = (SLOP_STR("error")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            return result;
        } else {
            return result;
        }
    }
}

void infer_check_match_exhaustive(env_TypeEnv* env, types_ResolvedType* scrutinee_type, slop_list_string covered, uint8_t has_wildcard, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((scrutinee_type != NULL)), "(!= scrutinee-type nil)");
    if (!(has_wildcard)) {
        {
            __auto_type arena = env_env_arena(env);
            __auto_type type_name = (*scrutinee_type).name;
            __auto_type expected = infer_match_expected_variants(arena, scrutinee_type);
            if ((((int64_t)((expected).len)) > 0) && !(string_eq(type_name, SLOP_STR("T")))) {
                {
                    __auto_type n = ((int64_t)((covered).len));
                    int64_t i = 0;
                    uint8_t all_known = 1;
                    __auto_type missing = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                    while (i < n) {
                        __auto_type _mv_1782 = ({ __auto_type _lst = covered; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1782.has_value) {
                            __auto_type head = _mv_1782.value;
                            if (!(infer_string_list_contains(expected, head))) {
                                all_known = 0;
                            }
                        } else if (!_mv_1782.has_value) {
                        }
                        i = (i + 1);
                    }
                    if (all_known) {
                        {
                            __auto_type e_len = ((int64_t)((expected).len));
                            int64_t j = 0;
                            while (j < e_len) {
                                __auto_type _mv_1783 = ({ __auto_type _lst = expected; size_t _idx = (size_t)j; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1783.has_value) {
                                    __auto_type want = _mv_1783.value;
                                    if (!(infer_string_list_contains(covered, want))) {
                                        ({ __auto_type _lst_p = &(missing); __auto_type _item = (want); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    }
                                } else if (!_mv_1783.has_value) {
                                }
                                j = (j + 1);
                            }
                            if (((int64_t)((missing).len)) > 0) {
                                {
                                    __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("non-exhaustive match on ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (type_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(": missing ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (strlib_join(arena, missing, SLOP_STR(", "))); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    env_env_add_warning(env, strlib_string_build(arena, parts), line, col);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

types_ResolvedType* infer_infer_match_expr(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type items = lst.items;
        __auto_type len = ((int64_t)((items).len));
        __auto_type line = parser_sexpr_line(expr);
        __auto_type col = parser_sexpr_col(expr);
        uint8_t has_result = 0;
        uint8_t has_wildcard = 0;
        __auto_type match_arena = env_env_arena(env);
        __auto_type covered = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(match_arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        types_ResolvedType* result_type = env_env_get_unit_type(env);
        __auto_type scrutinee_type = (((len >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type scrutinee = _mv.value; infer_infer_expr(env, scrutinee); }) : (env_env_get_unit_type(env)); }) : env_env_get_unit_type(env));
        int64_t i = 2;
        while (i < len) {
            __auto_type _mv_1784 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1784.has_value) {
                __auto_type clause = _mv_1784.value;
                __auto_type _mv_1785 = (*clause);
                switch (_mv_1785.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type clause_lst = _mv_1785.data.lst;
                        {
                            __auto_type clause_items = clause_lst.items;
                            __auto_type clause_len = ((int64_t)((clause_items).len));
                            if (clause_len > 0) {
                                __auto_type _mv_1786 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1786.has_value) {
                                    __auto_type pattern = _mv_1786.value;
                                    {
                                        __auto_type head = infer_match_pattern_head(pattern);
                                        if (infer_is_wildcard_head(head)) {
                                            has_wildcard = 1;
                                        } else {
                                            ({ __auto_type _lst_p = &(covered); __auto_type _item = (head); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(match_arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                        }
                                    }
                                } else if (!_mv_1786.has_value) {
                                }
                            }
                            if (clause_len > 1) {
                                env_env_push_scope(env);
                                __auto_type _mv_1787 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1787.has_value) {
                                    __auto_type pattern = _mv_1787.value;
                                    infer_bind_match_pattern(env, scrutinee_type, pattern);
                                } else if (!_mv_1787.has_value) {
                                }
                                for (int64_t bi = 1; bi < (clause_len - 1); bi++) {
                                    __auto_type _mv_1788 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)bi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_1788.has_value) {
                                        __auto_type body_expr = _mv_1788.value;
                                        {
                                            __auto_type _ = infer_infer_expr(env, body_expr);
                                        }
                                    } else if (!_mv_1788.has_value) {
                                    }
                                }
                                __auto_type _mv_1789 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)(clause_len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1789.has_value) {
                                    __auto_type body = _mv_1789.value;
                                    {
                                        __auto_type body_type = infer_infer_expr(env, body);
                                        if (!(has_result)) {
                                            result_type = body_type;
                                            has_result = 1;
                                        } else {
                                            result_type = infer_unify_branch_types(env, result_type, body_type, line, col);
                                        }
                                    }
                                } else if (!_mv_1789.has_value) {
                                }
                                env_env_pop_scope(env);
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1784.has_value) {
            }
            i = (i + 1);
        }
        infer_check_match_exhaustive(env, scrutinee_type, covered, has_wildcard, line, col);
        return result_type;
    }
}

void infer_check_return_type(env_TypeEnv* env, types_SExpr* fn_form, slop_string fn_name, types_ResolvedType* inferred_type, int64_t fn_line, int64_t fn_col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    SLOP_PRE(((inferred_type != NULL)), "(!= inferred-type nil)");
    __auto_type _mv_1790 = (*fn_form);
    switch (_mv_1790.tag) {
        case types_SExpr_lst:
        {
            __auto_type fn_lst = _mv_1790.data.lst;
            {
                __auto_type items = fn_lst.items;
                __auto_type len = ((int64_t)((items).len));
                for (int64_t i = 3; i < len; i++) {
                    __auto_type _mv_1791 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1791.has_value) {
                        __auto_type item = _mv_1791.value;
                        if (parser_is_form(item, SLOP_STR("@spec"))) {
                            infer_check_spec_return_type(env, item, fn_name, inferred_type, fn_line, fn_col);
                        }
                    } else if (!_mv_1791.has_value) {
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

void infer_check_spec_return_type(env_TypeEnv* env, types_SExpr* spec_form, slop_string fn_name, types_ResolvedType* inferred_type, int64_t fn_line, int64_t fn_col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((spec_form != NULL)), "(!= spec-form nil)");
    __auto_type _mv_1792 = (*spec_form);
    switch (_mv_1792.tag) {
        case types_SExpr_lst:
        {
            __auto_type spec_lst = _mv_1792.data.lst;
            {
                __auto_type spec_items = spec_lst.items;
                __auto_type _mv_1793 = ({ __auto_type _lst = spec_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1793.has_value) {
                    __auto_type spec_body = _mv_1793.value;
                    infer_check_spec_body_return(env, spec_body, fn_name, inferred_type, fn_line, fn_col);
                } else if (!_mv_1793.has_value) {
                }
            }
            break;
        }
        default: {
            break;
        }
    }
}

void infer_check_spec_body_return(env_TypeEnv* env, types_SExpr* spec_body, slop_string fn_name, types_ResolvedType* inferred_type, int64_t fn_line, int64_t fn_col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((spec_body != NULL)), "(!= spec-body nil)");
    __auto_type _mv_1794 = (*spec_body);
    switch (_mv_1794.tag) {
        case types_SExpr_lst:
        {
            __auto_type body_lst = _mv_1794.data.lst;
            {
                __auto_type body_items = body_lst.items;
                __auto_type body_len = ((int64_t)((body_items).len));
                __auto_type _mv_1795 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1795.has_value) {
                    __auto_type ret_expr = _mv_1795.value;
                    infer_check_return_expr(env, ret_expr, fn_name, inferred_type, fn_line, fn_col);
                } else if (!_mv_1795.has_value) {
                }
            }
            break;
        }
        default: {
            break;
        }
    }
}

uint8_t infer_checker_is_primitive_type(slop_string name) {
    return (string_eq(name, SLOP_STR("Int")) || (string_eq(name, SLOP_STR("Bool")) || (string_eq(name, SLOP_STR("String")) || (string_eq(name, SLOP_STR("Unit")) || (string_eq(name, SLOP_STR("Arena")) || (string_eq(name, SLOP_STR("I8")) || (string_eq(name, SLOP_STR("I16")) || (string_eq(name, SLOP_STR("I32")) || (string_eq(name, SLOP_STR("I64")) || (string_eq(name, SLOP_STR("U8")) || (string_eq(name, SLOP_STR("U16")) || (string_eq(name, SLOP_STR("U32")) || (string_eq(name, SLOP_STR("U64")) || (string_eq(name, SLOP_STR("F32")) || string_eq(name, SLOP_STR("F64"))))))))))))))));
}

uint8_t infer_is_integer_type(slop_string name) {
    return (string_eq(name, SLOP_STR("Int")) || (string_eq(name, SLOP_STR("I8")) || (string_eq(name, SLOP_STR("I16")) || (string_eq(name, SLOP_STR("I32")) || (string_eq(name, SLOP_STR("I64")) || (string_eq(name, SLOP_STR("U8")) || (string_eq(name, SLOP_STR("U16")) || (string_eq(name, SLOP_STR("U32")) || (string_eq(name, SLOP_STR("U64")) || string_eq(name, SLOP_STR("Size")))))))))));
}

void infer_check_return_expr(env_TypeEnv* env, types_SExpr* ret_expr, slop_string fn_name, types_ResolvedType* inferred_type, int64_t fn_line, int64_t fn_col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((ret_expr != NULL)), "(!= ret-expr nil)");
    __auto_type _mv_1796 = (*ret_expr);
    switch (_mv_1796.tag) {
        case types_SExpr_sym:
        {
            __auto_type ret_sym = _mv_1796.data.sym;
            {
                __auto_type declared_name = ret_sym.name;
                __auto_type inferred_name = (*inferred_type).name;
                if (!(string_eq(declared_name, inferred_name)) && ((infer_checker_is_primitive_type(declared_name) && infer_checker_is_primitive_type(inferred_name)) || (string_eq(inferred_name, SLOP_STR("<nil>")) && infer_checker_is_primitive_type(declared_name)))) {
                    {
                        __auto_type arena = env_env_arena(env);
                        __auto_type msg = string_concat(arena, SLOP_STR("return value of '"), string_concat(arena, fn_name, string_concat(arena, SLOP_STR("': expected "), string_concat(arena, declared_name, string_concat(arena, SLOP_STR(", got "), inferred_name)))));
                        env_env_add_error(env, msg, fn_line, fn_col);
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

void infer_bind_param_from_form(env_TypeEnv* env, types_SExpr* param_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((param_form != NULL)), "(!= param-form nil)");
    if (parser_sexpr_is_list(param_form) && (parser_sexpr_list_len(param_form) >= 2)) {
        __auto_type _mv_1797 = parser_sexpr_list_get(param_form, 0);
        if (_mv_1797.has_value) {
            __auto_type first_expr = _mv_1797.value;
            {
                __auto_type first_name = parser_sexpr_get_symbol_name(first_expr);
                if ((string_eq(first_name, SLOP_STR("in"))) || (string_eq(first_name, SLOP_STR("out"))) || (string_eq(first_name, SLOP_STR("mut")))) {
                    if (parser_sexpr_list_len(param_form) >= 3) {
                        __auto_type _mv_1798 = parser_sexpr_list_get(param_form, 1);
                        if (_mv_1798.has_value) {
                            __auto_type name_expr = _mv_1798.value;
                            {
                                __auto_type param_name = parser_sexpr_get_symbol_name(name_expr);
                                if (!(string_eq(param_name, SLOP_STR("")))) {
                                    {
                                        __auto_type param_type = infer_get_param_type_from_form(env, param_form);
                                        env_env_bind_var(env, param_name, param_type);
                                    }
                                }
                            }
                        } else if (!_mv_1798.has_value) {
                        }
                    }
                } else {
                    if (!(string_eq(first_name, SLOP_STR("")))) {
                        {
                            __auto_type param_type = infer_get_param_type_from_form(env, param_form);
                            env_env_bind_var(env, first_name, param_type);
                        }
                    }
                }
            }
        } else if (!_mv_1797.has_value) {
        }
    }
}

types_ResolvedType* infer_get_param_type_from_form(env_TypeEnv* env, types_SExpr* param_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((param_form != NULL)), "(!= param-form nil)");
    {
        __auto_type type_pos = ({ __auto_type _mv = parser_sexpr_list_get(param_form, 0); _mv.has_value ? ({ __auto_type first_expr = _mv.value; ({ __auto_type first_name = parser_sexpr_get_symbol_name(first_expr); ((((string_eq(first_name, SLOP_STR("in"))) || (string_eq(first_name, SLOP_STR("out"))) || (string_eq(first_name, SLOP_STR("mut"))))) ? 2 : 1); }); }) : (1); });
        __auto_type _mv_1799 = parser_sexpr_list_get(param_form, type_pos);
        if (_mv_1799.has_value) {
            __auto_type type_expr = _mv_1799.value;
            {
                __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                if (string_eq(type_name, SLOP_STR(""))) {
                    if (parser_sexpr_is_list(type_expr)) {
                        return infer_resolve_complex_type_expr(env, type_expr);
                    } else {
                        return env_env_get_unknown_type(env);
                    }
                } else {
                    return infer_resolve_simple_type(env, type_name);
                }
            }
        } else if (!_mv_1799.has_value) {
            return env_env_get_unknown_type(env);
        }
        SLOP_UNREACHABLE();
    }
}

types_ResolvedType* infer_resolve_complex_type_expr(env_TypeEnv* env, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_1800 = parser_sexpr_list_get(type_expr, 0);
    if (_mv_1800.has_value) {
        __auto_type head_expr = _mv_1800.value;
        {
            __auto_type head_name = parser_sexpr_get_symbol_name(head_expr);
            if (string_eq(head_name, SLOP_STR("Option"))) {
                {
                    __auto_type inner_type = infer_resolve_option_inner_type(env, type_expr);
                    return env_env_make_option_type(env, inner_type);
                }
            } else if (string_eq(head_name, SLOP_STR("Ptr"))) {
                {
                    __auto_type inner_type = infer_resolve_ptr_inner_type(env, type_expr);
                    return env_env_make_ptr_type(env, inner_type);
                }
            } else if (string_eq(head_name, SLOP_STR("List"))) {
                {
                    __auto_type arena = env_env_arena(env);
                    __auto_type inner_type = infer_resolve_ptr_inner_type(env, type_expr);
                    __auto_type list_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_list, SLOP_STR("List"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_list_t*"));
                    types_resolved_type_set_inner(list_type, inner_type);
                    return list_type;
                }
            } else if (string_eq(head_name, SLOP_STR("Map"))) {
                {
                    __auto_type arena = env_env_arena(env);
                    __auto_type key_type = infer_resolve_ptr_inner_type(env, type_expr);
                    __auto_type map_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_map, SLOP_STR("Map"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_map*"));
                    types_resolved_type_set_inner(map_type, key_type);
                    if (parser_sexpr_list_len(type_expr) >= 3) {
                        __auto_type _mv_1801 = parser_sexpr_list_get(type_expr, 2);
                        if (_mv_1801.has_value) {
                            __auto_type val_expr = _mv_1801.value;
                            {
                                __auto_type val_type = infer_resolve_simple_type(env, parser_sexpr_get_symbol_name(val_expr));
                                if (val_type != NULL) {
                                    types_resolved_type_set_inner2(map_type, val_type);
                                }
                            }
                        } else if (!_mv_1801.has_value) {
                        }
                    }
                    return map_type;
                }
            } else if (string_eq(head_name, SLOP_STR("Set"))) {
                {
                    __auto_type arena = env_env_arena(env);
                    __auto_type inner_type = infer_resolve_ptr_inner_type(env, type_expr);
                    __auto_type set_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Set"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_map*"));
                    types_resolved_type_set_inner(set_type, inner_type);
                    return set_type;
                }
            } else if (string_eq(head_name, SLOP_STR("Thread"))) {
                {
                    __auto_type inner_type = infer_resolve_ptr_inner_type(env, type_expr);
                    __auto_type arena = env_env_arena(env);
                    __auto_type t = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_thread, SLOP_STR("Thread"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_thread_int*"));
                    types_resolved_type_set_inner(t, inner_type);
                    return t;
                }
            } else if (string_eq(head_name, SLOP_STR("Chan"))) {
                {
                    __auto_type inner_type = infer_resolve_ptr_inner_type(env, type_expr);
                    __auto_type arena = env_env_arena(env);
                    __auto_type t = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_chan, SLOP_STR("Chan"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_chan_int*"));
                    types_resolved_type_set_inner(t, inner_type);
                    return t;
                }
            } else if (string_eq(head_name, SLOP_STR("Result"))) {
                {
                    __auto_type arena = env_env_arena(env);
                    __auto_type result_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_result, SLOP_STR("Result"), ((slop_option_string){.has_value = false}), SLOP_STR("Result"));
                    if (parser_sexpr_list_len(type_expr) >= 2) {
                        __auto_type _mv_1802 = parser_sexpr_list_get(type_expr, 1);
                        if (_mv_1802.has_value) {
                            __auto_type ok_expr = _mv_1802.value;
                            {
                                __auto_type ok_name = parser_sexpr_get_symbol_name(ok_expr);
                                {
                                    __auto_type ok_type = ((string_eq(ok_name, SLOP_STR(""))) ? ((parser_sexpr_is_list(ok_expr)) ? infer_resolve_complex_type_expr(env, ok_expr) : env_env_get_unknown_type(env)) : infer_resolve_type_lenient(env, ok_name));
                                    types_resolved_type_set_inner(result_type, ok_type);
                                }
                            }
                        } else if (!_mv_1802.has_value) {
                        }
                    }
                    if (parser_sexpr_list_len(type_expr) >= 3) {
                        __auto_type _mv_1803 = parser_sexpr_list_get(type_expr, 2);
                        if (_mv_1803.has_value) {
                            __auto_type err_expr = _mv_1803.value;
                            {
                                __auto_type err_name = parser_sexpr_get_symbol_name(err_expr);
                                {
                                    __auto_type err_type = ((string_eq(err_name, SLOP_STR(""))) ? ((parser_sexpr_is_list(err_expr)) ? infer_resolve_complex_type_expr(env, err_expr) : env_env_get_unknown_type(env)) : infer_resolve_type_lenient(env, err_name));
                                    types_resolved_type_set_inner2(result_type, err_type);
                                }
                            }
                        } else if (!_mv_1803.has_value) {
                        }
                    }
                    return result_type;
                }
            } else {
                __auto_type _mv_1804 = env_env_lookup_type(env, head_name);
                if (_mv_1804.has_value) {
                    __auto_type t = _mv_1804.value;
                    return t;
                } else if (!_mv_1804.has_value) {
                    return env_env_get_unknown_type(env);
                }
                SLOP_UNREACHABLE();
            }
        }
    } else if (!_mv_1800.has_value) {
        return env_env_get_unknown_type(env);
    }
    SLOP_UNREACHABLE();
}

types_ResolvedType* infer_resolve_option_inner_type(env_TypeEnv* env, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    if (parser_sexpr_list_len(type_expr) < 2) {
        return env_env_get_unknown_type(env);
    } else {
        __auto_type _mv_1805 = parser_sexpr_list_get(type_expr, 1);
        if (_mv_1805.has_value) {
            __auto_type inner_expr = _mv_1805.value;
            {
                __auto_type inner_name = parser_sexpr_get_symbol_name(inner_expr);
                if (string_eq(inner_name, SLOP_STR(""))) {
                    return env_env_get_unknown_type(env);
                } else {
                    return infer_resolve_simple_type(env, inner_name);
                }
            }
        } else if (!_mv_1805.has_value) {
            return env_env_get_unknown_type(env);
        }
        SLOP_UNREACHABLE();
    }
}

types_ResolvedType* infer_resolve_ptr_inner_type(env_TypeEnv* env, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    if (parser_sexpr_list_len(type_expr) < 2) {
        return env_env_get_unit_type(env);
    } else {
        __auto_type _mv_1806 = parser_sexpr_list_get(type_expr, 1);
        if (_mv_1806.has_value) {
            __auto_type inner_expr = _mv_1806.value;
            {
                __auto_type inner_name = parser_sexpr_get_symbol_name(inner_expr);
                if (string_eq(inner_name, SLOP_STR(""))) {
                    if (parser_sexpr_is_list(inner_expr)) {
                        return infer_resolve_complex_type_expr(env, inner_expr);
                    } else {
                        return env_env_get_unknown_type(env);
                    }
                } else {
                    return infer_resolve_simple_type(env, inner_name);
                }
            }
        } else if (!_mv_1806.has_value) {
            return env_env_get_unit_type(env);
        }
        SLOP_UNREACHABLE();
    }
}

types_ResolvedType* infer_resolve_type_lenient(env_TypeEnv* env, slop_string type_name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1807 = env_env_lookup_type(env, type_name);
    if (_mv_1807.has_value) {
        __auto_type t = _mv_1807.value;
        return t;
    } else if (!_mv_1807.has_value) {
        {
            __auto_type arena = env_env_arena(env);
            if (string_eq(type_name, SLOP_STR("Int"))) {
                return env_env_get_int_type(env);
            } else if (string_eq(type_name, SLOP_STR("Bool"))) {
                return env_env_get_bool_type(env);
            } else if (string_eq(type_name, SLOP_STR("String"))) {
                return env_env_get_string_type(env);
            } else if (string_eq(type_name, SLOP_STR("Unit"))) {
                return env_env_get_unit_type(env);
            } else if (string_eq(type_name, SLOP_STR("Arena"))) {
                return env_env_get_arena_type(env);
            } else {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, type_name, ((slop_option_string){.has_value = false}), type_name);
            }
        }
    }
    SLOP_UNREACHABLE();
}

types_ResolvedType* infer_resolve_simple_type(env_TypeEnv* env, slop_string type_name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1808 = env_env_lookup_type(env, type_name);
    if (_mv_1808.has_value) {
        __auto_type t = _mv_1808.value;
        return t;
    } else if (!_mv_1808.has_value) {
        {
            __auto_type arena = env_env_arena(env);
            if (string_eq(type_name, SLOP_STR("Int"))) {
                return env_env_get_int_type(env);
            } else if (string_eq(type_name, SLOP_STR("Bool"))) {
                return env_env_get_bool_type(env);
            } else if (string_eq(type_name, SLOP_STR("String"))) {
                return env_env_get_string_type(env);
            } else if (string_eq(type_name, SLOP_STR("Unit"))) {
                return env_env_get_unit_type(env);
            } else if (string_eq(type_name, SLOP_STR("Arena"))) {
                return env_env_get_arena_type(env);
            } else if (string_eq(type_name, SLOP_STR("Float"))) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Float"), ((slop_option_string){.has_value = false}), SLOP_STR("double"));
            } else if (string_eq(type_name, SLOP_STR("I8"))) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("I8"), ((slop_option_string){.has_value = false}), SLOP_STR("int8_t"));
            } else if (string_eq(type_name, SLOP_STR("I16"))) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("I16"), ((slop_option_string){.has_value = false}), SLOP_STR("int16_t"));
            } else if (string_eq(type_name, SLOP_STR("I32"))) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("I32"), ((slop_option_string){.has_value = false}), SLOP_STR("int32_t"));
            } else if (string_eq(type_name, SLOP_STR("I64"))) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("I64"), ((slop_option_string){.has_value = false}), SLOP_STR("int64_t"));
            } else if (string_eq(type_name, SLOP_STR("U8"))) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("U8"), ((slop_option_string){.has_value = false}), SLOP_STR("uint8_t"));
            } else if (string_eq(type_name, SLOP_STR("U16"))) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("U16"), ((slop_option_string){.has_value = false}), SLOP_STR("uint16_t"));
            } else if (string_eq(type_name, SLOP_STR("U32"))) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("U32"), ((slop_option_string){.has_value = false}), SLOP_STR("uint32_t"));
            } else if (string_eq(type_name, SLOP_STR("U64"))) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("U64"), ((slop_option_string){.has_value = false}), SLOP_STR("uint64_t"));
            } else if (string_eq(type_name, SLOP_STR("ThreadHandle"))) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("ThreadHandle"), ((slop_option_string){.has_value = false}), SLOP_STR("pthread_t"));
            } else if (string_eq(type_name, SLOP_STR("Char"))) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Char"), ((slop_option_string){.has_value = false}), SLOP_STR("char"));
            } else if (string_eq(type_name, SLOP_STR("Void"))) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Void"), ((slop_option_string){.has_value = false}), SLOP_STR("void"));
            } else if (string_eq(type_name, SLOP_STR("Bytes"))) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Bytes"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_bytes"));
            } else if (env_env_is_type_param(env, type_name)) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_typevar, type_name, ((slop_option_string){.has_value = false}), SLOP_STR("int64_t"));
            } else {
                {
                    __auto_type arena = env_env_arena(env);
                    __auto_type msg = string_concat(arena, SLOP_STR("Unknown type: "), type_name);
                    env_env_add_error(env, msg, 0, 0);
                    return env_env_get_generic_type(env);
                }
            }
        }
    }
    SLOP_UNREACHABLE();
}

void infer_bind_let_binding(env_TypeEnv* env, types_SExpr* binding_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((binding_form != NULL)), "(!= binding-form nil)");
    if (parser_sexpr_is_list(binding_form) && (parser_sexpr_list_len(binding_form) >= 2)) {
        __auto_type _mv_1809 = parser_sexpr_list_get(binding_form, 0);
        if (_mv_1809.has_value) {
            __auto_type first_expr = _mv_1809.value;
            {
                __auto_type first_name = parser_sexpr_get_symbol_name(first_expr);
                if (string_eq(first_name, SLOP_STR("mut"))) {
                    if (parser_sexpr_list_len(binding_form) >= 3) {
                        __auto_type _mv_1810 = parser_sexpr_list_get(binding_form, 1);
                        if (_mv_1810.has_value) {
                            __auto_type name_expr = _mv_1810.value;
                            {
                                __auto_type var_name = parser_sexpr_get_symbol_name(name_expr);
                                if (!(string_eq(var_name, SLOP_STR("")))) {
                                    {
                                        __auto_type binding_len = parser_sexpr_list_len(binding_form);
                                        __auto_type _mv_1811 = parser_sexpr_list_get(binding_form, (binding_len - 1));
                                        if (_mv_1811.has_value) {
                                            __auto_type val_expr = _mv_1811.value;
                                            {
                                                __auto_type val_type = infer_infer_expr(env, val_expr);
                                                __auto_type val_type_name = (*val_type).name;
                                                if ((binding_len == 3) && string_eq(val_type_name, SLOP_STR("Option_T"))) {
                                                    {
                                                        __auto_type arena = env_env_arena(env);
                                                        __auto_type line = parser_sexpr_line(binding_form);
                                                        __auto_type col = parser_sexpr_col(binding_form);
                                                        __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                                                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("mutable variable '")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (var_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("' has ambiguous Option type - add explicit type: (mut ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (var_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                        ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(" (Option T) ...)")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                        env_env_add_warning(env, strlib_string_build(arena, parts), line, col);
                                                        env_env_bind_var(env, var_name, val_type);
                                                    }
                                                } else {
                                                    env_env_bind_var(env, var_name, val_type);
                                                }
                                            }
                                        } else if (!_mv_1811.has_value) {
                                        }
                                    }
                                }
                            }
                        } else if (!_mv_1810.has_value) {
                        }
                    }
                } else {
                    if (!(string_eq(first_name, SLOP_STR("")))) {
                        {
                            __auto_type binding_len = parser_sexpr_list_len(binding_form);
                            if (binding_len == 3) {
                                __auto_type _mv_1812 = parser_sexpr_list_get(binding_form, 2);
                                if (_mv_1812.has_value) {
                                    __auto_type val_expr = _mv_1812.value;
                                    {
                                        __auto_type val_type = infer_infer_expr(env, val_expr);
                                        env_env_bind_var(env, first_name, val_type);
                                    }
                                } else if (!_mv_1812.has_value) {
                                }
                            } else {
                                __auto_type _mv_1813 = parser_sexpr_list_get(binding_form, 1);
                                if (_mv_1813.has_value) {
                                    __auto_type val_expr = _mv_1813.value;
                                    {
                                        __auto_type val_type = infer_infer_expr(env, val_expr);
                                        env_env_bind_var(env, first_name, val_type);
                                    }
                                } else if (!_mv_1813.has_value) {
                                }
                            }
                        }
                    }
                }
            }
        } else if (!_mv_1809.has_value) {
        }
    }
}

types_ResolvedType* infer_infer_let_expr(env_TypeEnv* env, types_SExpr* expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    env_env_push_scope(env);
    if (parser_sexpr_is_list(expr)) {
        __auto_type _mv_1814 = parser_sexpr_list_get(expr, 1);
        if (_mv_1814.has_value) {
            __auto_type bindings_expr = _mv_1814.value;
            if (parser_sexpr_is_list(bindings_expr)) {
                {
                    __auto_type num_bindings = parser_sexpr_list_len(bindings_expr);
                    for (int64_t i = 0; i < num_bindings; i++) {
                        __auto_type _mv_1815 = parser_sexpr_list_get(bindings_expr, i);
                        if (_mv_1815.has_value) {
                            __auto_type binding = _mv_1815.value;
                            infer_bind_let_binding(env, binding);
                        } else if (!_mv_1815.has_value) {
                        }
                    }
                }
            }
        } else if (!_mv_1814.has_value) {
        }
    }
    {
        __auto_type result_type = ((parser_sexpr_is_list(expr)) ? ({ __auto_type len = parser_sexpr_list_len(expr); types_ResolvedType* last_type = env_env_get_unit_type(env); ({ for (int64_t i = 2; i < len; i++) { ({ __auto_type _mv = parser_sexpr_list_get(expr, i); if (_mv.has_value) { __auto_type body_expr = _mv.value; ({ last_type = infer_infer_expr(env, body_expr); (void)0; }); } else { ({ (void)0; }); } (void)0; }); } (void)0; }); last_type; }) : env_env_get_unit_type(env));
        env_env_pop_scope(env);
        return result_type;
    }
}

types_ResolvedType* infer_infer_with_arena_expr(env_TypeEnv* env, types_SExpr* expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type len = parser_sexpr_list_len(expr);
        if (len < 2) {
            env_env_add_error(env, SLOP_STR("with-arena requires size argument"), parser_sexpr_line(expr), parser_sexpr_col(expr));
            return env_env_get_unit_type(env);
        } else {
            {
                __auto_type is_named = ({ __auto_type _mv = parser_sexpr_list_get(expr, 1); _mv.has_value ? ({ __auto_type item1 = _mv.value; string_eq(parser_sexpr_get_symbol_name(item1), SLOP_STR(":as")); }) : (0); });
                __auto_type arena_name = ((is_named) ? ({ __auto_type _mv = parser_sexpr_list_get(expr, 2); _mv.has_value ? ({ __auto_type name_expr = _mv.value; parser_sexpr_get_symbol_name(name_expr); }) : (SLOP_STR("arena")); }) : SLOP_STR("arena"));
                __auto_type size_idx = ((is_named) ? 3 : 1);
                __auto_type body_start = ((is_named) ? 4 : 2);
                if (is_named && (len < 4)) {
                    env_env_add_error(env, SLOP_STR("with-arena :as requires name and size"), parser_sexpr_line(expr), parser_sexpr_col(expr));
                    return env_env_get_unit_type(env);
                } else {
                    __auto_type _mv_1816 = parser_sexpr_list_get(expr, size_idx);
                    if (_mv_1816.has_value) {
                        __auto_type size_expr = _mv_1816.value;
                        __auto_type _mv_1817 = (*size_expr);
                        switch (_mv_1817.tag) {
                            case types_SExpr_num:
                            {
                                __auto_type num = _mv_1817.data.num;
                                if (num.int_value <= 0) {
                                    env_env_add_error(env, SLOP_STR("with-arena size must be positive"), num.line, num.col);
                                } else {
                                }
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_1816.has_value) {
                    }
                    env_env_push_scope(env);
                    env_env_bind_var(env, arena_name, env_env_get_arena_type(env));
                    {
                        types_ResolvedType* result_type = env_env_get_unit_type(env);
                        for (int64_t i = body_start; i < len; i++) {
                            __auto_type _mv_1818 = parser_sexpr_list_get(expr, i);
                            if (_mv_1818.has_value) {
                                __auto_type body_expr = _mv_1818.value;
                                result_type = infer_infer_expr(env, body_expr);
                            } else if (!_mv_1818.has_value) {
                            }
                        }
                        env_env_pop_scope(env);
                        return result_type;
                    }
                }
            }
        }
    }
}

slop_string infer_get_fn_name(types_SExpr* fn_form) {
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    if (!(parser_sexpr_is_list(fn_form))) {
        return SLOP_STR("unknown");
    } else {
        if (parser_sexpr_list_len(fn_form) < 2) {
            return SLOP_STR("unknown");
        } else {
            __auto_type _mv_1819 = parser_sexpr_list_get(fn_form, 1);
            if (_mv_1819.has_value) {
                __auto_type name_expr = _mv_1819.value;
                {
                    __auto_type name = parser_sexpr_get_symbol_name(name_expr);
                    if (string_eq(name, SLOP_STR(""))) {
                        return SLOP_STR("unknown");
                    } else {
                        return name;
                    }
                }
            } else if (!_mv_1819.has_value) {
                return SLOP_STR("unknown");
            }
            SLOP_UNREACHABLE();
        }
    }
}

types_ResolvedType* infer_resolve_hole_type(env_TypeEnv* env, slop_list_types_SExpr_ptr items, int64_t len) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    if (len < 2) {
        return env_env_get_unit_type(env);
    } else {
        __auto_type _mv_1820 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1820.has_value) {
            __auto_type type_expr = _mv_1820.value;
            {
                __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                if (string_eq(type_name, SLOP_STR(""))) {
                    return env_env_get_unit_type(env);
                } else {
                    __auto_type _mv_1821 = env_env_lookup_type(env, type_name);
                    if (_mv_1821.has_value) {
                        __auto_type t = _mv_1821.value;
                        return t;
                    } else if (!_mv_1821.has_value) {
                        if (string_eq(type_name, SLOP_STR("Int"))) {
                            return env_env_get_int_type(env);
                        } else if (string_eq(type_name, SLOP_STR("Bool"))) {
                            return env_env_get_bool_type(env);
                        } else if (string_eq(type_name, SLOP_STR("String"))) {
                            return env_env_get_string_type(env);
                        } else if (string_eq(type_name, SLOP_STR("Unit"))) {
                            return env_env_get_unit_type(env);
                        } else {
                            return env_env_get_unit_type(env);
                        }
                    }
                    SLOP_UNREACHABLE();
                }
            }
        } else if (!_mv_1820.has_value) {
            return env_env_get_unit_type(env);
        }
        SLOP_UNREACHABLE();
    }
}

slop_string infer_get_hole_prompt(slop_list_types_SExpr_ptr items, int64_t len) {
    if (len < 3) {
        return SLOP_STR("(no description)");
    } else {
        __auto_type _mv_1822 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1822.has_value) {
            __auto_type prompt_expr = _mv_1822.value;
            __auto_type _mv_1823 = (*prompt_expr);
            switch (_mv_1823.tag) {
                case types_SExpr_str:
                {
                    __auto_type str = _mv_1823.data.str;
                    return str.value;
                }
                default: {
                    return SLOP_STR("(no description)");
                }
            }
        } else if (!_mv_1822.has_value) {
            return SLOP_STR("(no description)");
        }
        SLOP_UNREACHABLE();
    }
}

int64_t infer_find_last_body_idx(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = (len - 1);
        while ((i >= 3) && infer_is_c_name_related(items, i)) {
            i = (i - 1);
        }
        return i;
    }
}

uint8_t infer_is_c_name_related(slop_list_types_SExpr_ptr items, int64_t idx) {
    __auto_type _mv_1824 = ({ __auto_type _lst = items; size_t _idx = (size_t)idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
    if (_mv_1824.has_value) {
        __auto_type item = _mv_1824.value;
        __auto_type _mv_1825 = (*item);
        switch (_mv_1825.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_1825.data.sym;
                return string_eq(sym.name, SLOP_STR(":c-name"));
            }
            case types_SExpr_str:
            {
                __auto_type _ = _mv_1825.data.str;
                if (idx > 0) {
                    __auto_type _mv_1826 = ({ __auto_type _lst = items; size_t _idx = (size_t)(idx - 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1826.has_value) {
                        __auto_type prev = _mv_1826.value;
                        __auto_type _mv_1827 = (*prev);
                        switch (_mv_1827.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1827.data.sym;
                                return string_eq(sym.name, SLOP_STR(":c-name"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1826.has_value) {
                        return 0;
                    }
                    SLOP_UNREACHABLE();
                } else {
                    return 0;
                }
            }
            default: {
                return 0;
            }
        }
    } else if (!_mv_1824.has_value) {
        return 0;
    }
    SLOP_UNREACHABLE();
}

uint8_t infer_is_annotation_expr(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    if (parser_sexpr_is_list(expr)) {
        __auto_type _mv_1828 = parser_sexpr_list_get(expr, 0);
        if (_mv_1828.has_value) {
            __auto_type head = _mv_1828.value;
            __auto_type _mv_1829 = (*head);
            switch (_mv_1829.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_1829.data.sym;
                    return strlib_starts_with(sym.name, SLOP_STR("@"));
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_1828.has_value) {
            return 0;
        }
        SLOP_UNREACHABLE();
    } else {
        return 0;
    }
}

uint8_t infer_is_checkable_annotation(types_SExpr* expr) {
    if (parser_sexpr_is_list(expr)) {
        __auto_type _mv_1830 = parser_sexpr_list_get(expr, 0);
        if (_mv_1830.has_value) {
            __auto_type head = _mv_1830.value;
            __auto_type _mv_1831 = (*head);
            switch (_mv_1831.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_1831.data.sym;
                    {
                        __auto_type name = sym.name;
                        return ((string_eq(name, SLOP_STR("@pre"))) || (string_eq(name, SLOP_STR("@post"))) || (string_eq(name, SLOP_STR("@assume"))) || (string_eq(name, SLOP_STR("@assert"))));
                    }
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_1830.has_value) {
            return 0;
        }
        SLOP_UNREACHABLE();
    } else {
        return 0;
    }
}

types_ResolvedType* infer_infer_fn_body(env_TypeEnv* env, types_SExpr* fn_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    SLOP_PRE((parser_is_form(fn_form, SLOP_STR("fn"))), "(is-form fn-form \"fn\")");
    {
        __auto_type fn_name = infer_get_fn_name(fn_form);
        __auto_type fn_line = parser_sexpr_line(fn_form);
        __auto_type fn_col = parser_sexpr_col(fn_form);
        __auto_type type_params = collect_find_fn_type_params(env_env_arena(env), fn_form);
        env_env_set_fn_type_params(env, type_params);
        env_env_push_scope(env);
        if (parser_sexpr_is_list(fn_form)) {
            {
                __auto_type params_len = parser_sexpr_list_len(fn_form);
                if (params_len > 2) {
                    __auto_type _mv_1832 = parser_sexpr_list_get(fn_form, 2);
                    if (_mv_1832.has_value) {
                        __auto_type params_expr = _mv_1832.value;
                        if (parser_sexpr_is_list(params_expr)) {
                            {
                                __auto_type num_params = parser_sexpr_list_len(params_expr);
                                for (int64_t k = 0; k < num_params; k++) {
                                    __auto_type _mv_1833 = parser_sexpr_list_get(params_expr, k);
                                    if (_mv_1833.has_value) {
                                        __auto_type param_form = _mv_1833.value;
                                        infer_bind_param_from_form(env, param_form);
                                    } else if (!_mv_1833.has_value) {
                                    }
                                }
                            }
                        }
                    } else if (!_mv_1832.has_value) {
                    }
                }
            }
        }
        {
            __auto_type result_type = ({ __auto_type _mv = (*fn_form); types_ResolvedType* _mr = {0}; switch (_mv.tag) { case types_SExpr_lst: { __auto_type fn_lst = _mv.data.lst; _mr = ({ __auto_type items = fn_lst.items; __auto_type item_len = ((int64_t)((items).len)); __auto_type last_body_idx = infer_find_last_body_idx(items); __auto_type body_type = env_env_get_unit_type(env); ({ for (int64_t bi = 3; bi < (last_body_idx + 1); bi++) { ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)bi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type body_expr = _mv.value; (((!(infer_is_annotation_expr(body_expr)) && !(infer_is_c_name_related(items, bi)))) ? ({ ({ body_type = infer_infer_expr(env, body_expr); (void)0; }); 0; }) : ({ (void)0; })); } else { ({ (void)0; }); } (void)0; }); } (void)0; }); env_env_bind_var(env, SLOP_STR("$result"), body_type); ({ __auto_type saved_diags = env_env_get_diagnostics(env); ({ for (int64_t bi = 3; bi < (last_body_idx + 1); bi++) { ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)bi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type ann_expr = _mv.value; ((infer_is_checkable_annotation(ann_expr)) ? ({ (void)(((parser_sexpr_is_list(ann_expr)) ? ({ ({ __auto_type _mv = parser_sexpr_list_get(ann_expr, 1); if (_mv.has_value) { __auto_type cond_expr = _mv.value; ({ __auto_type _ = infer_infer_expr(env, cond_expr); ({ (void)0; }); }); } else { ({ (void)0; }); } (void)0; }); 0; }) : ({ (void)0; }))); 0; }) : ({ (void)0; })); } else { ({ (void)0; }); } (void)0; }); } (void)0; }); ({ (*env).diagnostics = saved_diags; (void)0; }); }); body_type; }); break; } default: { _mr = env_env_get_unit_type(env); break; }  } _mr; });
            infer_check_return_type(env, fn_form, fn_name, result_type, fn_line, fn_col);
            env_env_pop_scope(env);
            env_env_clear_fn_type_params(env);
            return result_type;
        }
    }
}

void infer_check_match_patterns(env_TypeEnv* env, types_ResolvedType* scrutinee_type, slop_list_types_SExpr_ptr patterns) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((scrutinee_type != NULL)), "(!= scrutinee-type nil)");
    if (types_resolved_type_is_union(scrutinee_type)) {
        {
            __auto_type num_patterns = ((int64_t)((patterns).len));
            for (int64_t i = 0; i < num_patterns; i++) {
                __auto_type _mv_1834 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1834.has_value) {
                    __auto_type pattern_case = _mv_1834.value;
                    __auto_type _mv_1835 = (*pattern_case);
                    switch (_mv_1835.tag) {
                        case types_SExpr_lst:
                        {
                            __auto_type pattern_list = _mv_1835.data.lst;
                            if (((int64_t)((pattern_list.items).len)) > 0) {
                                __auto_type _mv_1836 = ({ __auto_type _lst = pattern_list.items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1836.has_value) {
                                    __auto_type pattern_expr = _mv_1836.value;
                                    __auto_type _mv_1837 = (*pattern_expr);
                                    switch (_mv_1837.tag) {
                                        case types_SExpr_lst:
                                        {
                                            __auto_type variant_list = _mv_1837.data.lst;
                                            {
                                                __auto_type variant_items = variant_list.items;
                                                if (((int64_t)((variant_items).len)) > 0) {
                                                    __auto_type _mv_1838 = ({ __auto_type _lst = variant_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_1838.has_value) {
                                                        __auto_type variant_name_expr = _mv_1838.value;
                                                        __auto_type _mv_1839 = (*variant_name_expr);
                                                        switch (_mv_1839.tag) {
                                                            case types_SExpr_sym:
                                                            {
                                                                __auto_type variant_sym = _mv_1839.data.sym;
                                                                {
                                                                    __auto_type variant_name = variant_sym.name;
                                                                    {
                                                                        __auto_type payload_types = types_resolved_type_get_variant_payloads(env_env_arena(env), scrutinee_type, variant_name);
                                                                        __auto_type num_pt = ((int64_t)((payload_types).len));
                                                                        if (num_pt > 0) {
                                                                            {
                                                                                __auto_type num_vt = ((int64_t)((variant_items).len));
                                                                                for (int64_t vi = 1; vi < num_vt; vi++) {
                                                                                    __auto_type _mv_1840 = ({ __auto_type _lst = variant_items; size_t _idx = (size_t)vi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                                    if (_mv_1840.has_value) {
                                                                                        __auto_type binding_expr = _mv_1840.value;
                                                                                        __auto_type _mv_1841 = (*binding_expr);
                                                                                        switch (_mv_1841.tag) {
                                                                                            case types_SExpr_sym:
                                                                                            {
                                                                                                __auto_type binding_sym = _mv_1841.data.sym;
                                                                                                {
                                                                                                    __auto_type bname = binding_sym.name;
                                                                                                    __auto_type type_idx = (vi - 1);
                                                                                                    if (!(string_eq(bname, SLOP_STR("_"))) && !(string_eq(bname, SLOP_STR("")))) {
                                                                                                        if (type_idx < num_pt) {
                                                                                                            __auto_type _mv_1842 = ({ __auto_type _lst = payload_types; size_t _idx = (size_t)type_idx; slop_option_types_ResolvedType_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                                                            if (_mv_1842.has_value) {
                                                                                                                __auto_type pt = _mv_1842.value;
                                                                                                                env_env_bind_var(env, bname, pt);
                                                                                                            } else if (!_mv_1842.has_value) {
                                                                                                                env_env_bind_var(env, bname, env_env_get_generic_type(env));
                                                                                                            }
                                                                                                        } else {
                                                                                                            env_env_bind_var(env, bname, env_env_get_generic_type(env));
                                                                                                        }
                                                                                                    }
                                                                                                }
                                                                                                break;
                                                                                            }
                                                                                            default: {
                                                                                                break;
                                                                                            }
                                                                                        }
                                                                                    } else if (!_mv_1840.has_value) {
                                                                                    }
                                                                                }
                                                                            }
                                                                        } else {
                                                                            __auto_type _mv_1843 = types_resolved_type_get_variant_index(scrutinee_type, variant_name);
                                                                            if (_mv_1843.has_value) {
                                                                                __auto_type _ = _mv_1843.value;
                                                                            } else if (!_mv_1843.has_value) {
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
                                                    } else if (!_mv_1838.has_value) {
                                                    }
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_1836.has_value) {
                                }
                            }
                            break;
                        }
                        default: {
                            break;
                        }
                    }
                } else if (!_mv_1834.has_value) {
                }
            }
        }
    }
}

