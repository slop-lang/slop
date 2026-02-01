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
types_ResolvedType* infer_infer_threading_builtin(env_TypeEnv* env, slop_string op, types_SExpr* expr, slop_list_types_SExpr_ptr items, int64_t len, int64_t line, int64_t col);
uint8_t infer_has_type_params(types_FnSignature* sig);
slop_option_types_ResolvedType_ptr infer_find_binding(slop_list_string bind_names, slop_list_types_ResolvedType_ptr bind_types, slop_string name);
void infer_unify_types(slop_arena* arena, types_ResolvedType* formal, types_ResolvedType* actual, slop_list_string bind_names, slop_list_types_ResolvedType_ptr bind_types);
types_ResolvedType* infer_substitute_type_vars(slop_arena* arena, types_ResolvedType* t, slop_list_string bind_names, slop_list_types_ResolvedType_ptr bind_types);
types_ResolvedType* infer_infer_generic_call(env_TypeEnv* env, types_FnSignature* sig, types_SExpr* expr, int64_t line, int64_t col);
uint8_t infer_types_equal(types_ResolvedType* a, types_ResolvedType* b);
uint8_t infer_types_compatible_with_range(types_ResolvedType* a, types_ResolvedType* b);
types_ResolvedType* infer_unify_branch_types(env_TypeEnv* env, types_ResolvedType* a, types_ResolvedType* b, int64_t line, int64_t col);
void infer_sexpr_set_resolved_type(types_SExpr* expr, types_ResolvedType* t);
types_ResolvedType* infer_infer_expr(env_TypeEnv* env, types_SExpr* expr);
types_ResolvedType* infer_infer_expr_inner(env_TypeEnv* env, types_SExpr* expr);
types_ResolvedType* infer_infer_list_expr(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst);
types_ResolvedType* infer_infer_special_form(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst, slop_string op);
void infer_check_fn_call_args(env_TypeEnv* env, types_FnSignature* sig, types_SExpr* expr, int64_t line, int64_t col);
void infer_check_single_arg(env_TypeEnv* env, types_FnSignature* sig, types_SExpr* expr, int64_t arg_idx, int64_t line, int64_t col);
void infer_check_builtin_args(env_TypeEnv* env, slop_string op, int64_t expected, int64_t actual, int64_t line, int64_t col);
void infer_infer_builtin_args(env_TypeEnv* env, types_SExpr* expr);
void infer_infer_body_exprs(env_TypeEnv* env, types_SExpr* expr, int64_t start_idx);
types_ResolvedType* infer_infer_field_access(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst, int64_t line, int64_t col);
types_ResolvedType* infer_check_field_exists(env_TypeEnv* env, types_ResolvedType* obj_type, slop_string field_name, int64_t line, int64_t col);
types_ResolvedType* infer_infer_cond_expr(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst);
void infer_bind_match_pattern(env_TypeEnv* env, types_ResolvedType* scrutinee_type, types_SExpr* pattern);
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
types_ResolvedType* infer_infer_fn_body(env_TypeEnv* env, types_SExpr* fn_form);
void infer_check_match_patterns(env_TypeEnv* env, types_ResolvedType* scrutinee_type, slop_list_types_SExpr_ptr patterns);

uint8_t infer_string_contains_char(slop_string s, int64_t c) {
    {
        __auto_type len = ((int64_t)(s.len));
        __auto_type data = s.data;
        __auto_type found = 0;
        for (int64_t i = 0; i < len; i++) {
            if ((!(found) && (((int64_t)(data[i])) == c))) {
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
        __auto_type result = -1;
        for (int64_t i = 0; i < len; i++) {
            if (((result == -1) && (((int64_t)(data[i])) == c))) {
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
        if ((new_len <= 0)) {
            return (slop_string){.len = 0, .data = ((uint8_t*)(SLOP_STR("").data))};
        } else {
            {
                __auto_type buf = ((uint8_t*)((uint8_t*)slop_arena_alloc(arena, (new_len + 1))));
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
    } else {
        infer_check_builtin_args(env, SLOP_STR("chan-buffered"), 2, (len - 1), line, col);
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
            __auto_type _mv_1353 = ({ __auto_type _lst = bind_names; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1353.has_value) {
                __auto_type bn = _mv_1353.value;
                if (string_eq(bn, name)) {
                    __auto_type _mv_1354 = ({ __auto_type _lst = bind_types; size_t _idx = (size_t)i; slop_option_types_ResolvedType_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1354.has_value) {
                        __auto_type bt = _mv_1354.value;
                        found = (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = bt};
                    } else if (!_mv_1354.has_value) {
                    }
                }
            } else if (!_mv_1353.has_value) {
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
        if ((f_kind == types_ResolvedTypeKind_rk_typevar)) {
            {
                __auto_type tv_name = (*formal).name;
                __auto_type _mv_1355 = infer_find_binding(bind_names, bind_types, tv_name);
                if (_mv_1355.has_value) {
                    __auto_type existing = _mv_1355.value;
                } else if (!_mv_1355.has_value) {
                    ({ __auto_type _lst_p = &(bind_names); __auto_type _item = (tv_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(bind_types); __auto_type _item = (actual); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                }
            }
        } else if ((f_kind == types_ResolvedTypeKind_rk_ptr)) {
            if (((*actual).kind == types_ResolvedTypeKind_rk_ptr)) {
                __auto_type _mv_1356 = (*formal).inner_type;
                if (_mv_1356.has_value) {
                    __auto_type f_inner = _mv_1356.value;
                    __auto_type _mv_1357 = (*actual).inner_type;
                    if (_mv_1357.has_value) {
                        __auto_type a_inner = _mv_1357.value;
                        infer_unify_types(arena, f_inner, a_inner, bind_names, bind_types);
                    } else if (!_mv_1357.has_value) {
                    }
                } else if (!_mv_1356.has_value) {
                }
            }
        } else if ((f_kind == types_ResolvedTypeKind_rk_chan)) {
            if (((*actual).kind == types_ResolvedTypeKind_rk_chan)) {
                __auto_type _mv_1358 = (*formal).inner_type;
                if (_mv_1358.has_value) {
                    __auto_type f_inner = _mv_1358.value;
                    __auto_type _mv_1359 = (*actual).inner_type;
                    if (_mv_1359.has_value) {
                        __auto_type a_inner = _mv_1359.value;
                        infer_unify_types(arena, f_inner, a_inner, bind_names, bind_types);
                    } else if (!_mv_1359.has_value) {
                    }
                } else if (!_mv_1358.has_value) {
                }
            }
        } else if ((f_kind == types_ResolvedTypeKind_rk_thread)) {
            if (((*actual).kind == types_ResolvedTypeKind_rk_thread)) {
                __auto_type _mv_1360 = (*formal).inner_type;
                if (_mv_1360.has_value) {
                    __auto_type f_inner = _mv_1360.value;
                    __auto_type _mv_1361 = (*actual).inner_type;
                    if (_mv_1361.has_value) {
                        __auto_type a_inner = _mv_1361.value;
                        infer_unify_types(arena, f_inner, a_inner, bind_names, bind_types);
                    } else if (!_mv_1361.has_value) {
                    }
                } else if (!_mv_1360.has_value) {
                }
            }
        } else if ((f_kind == types_ResolvedTypeKind_rk_list)) {
            if (((*actual).kind == types_ResolvedTypeKind_rk_list)) {
                __auto_type _mv_1362 = (*formal).inner_type;
                if (_mv_1362.has_value) {
                    __auto_type f_inner = _mv_1362.value;
                    __auto_type _mv_1363 = (*actual).inner_type;
                    if (_mv_1363.has_value) {
                        __auto_type a_inner = _mv_1363.value;
                        infer_unify_types(arena, f_inner, a_inner, bind_names, bind_types);
                    } else if (!_mv_1363.has_value) {
                    }
                } else if (!_mv_1362.has_value) {
                }
            }
        } else if ((f_kind == types_ResolvedTypeKind_rk_option)) {
            if (((*actual).kind == types_ResolvedTypeKind_rk_option)) {
                __auto_type _mv_1364 = (*formal).inner_type;
                if (_mv_1364.has_value) {
                    __auto_type f_inner = _mv_1364.value;
                    __auto_type _mv_1365 = (*actual).inner_type;
                    if (_mv_1365.has_value) {
                        __auto_type a_inner = _mv_1365.value;
                        infer_unify_types(arena, f_inner, a_inner, bind_names, bind_types);
                    } else if (!_mv_1365.has_value) {
                    }
                } else if (!_mv_1364.has_value) {
                }
            }
        } else if ((f_kind == types_ResolvedTypeKind_rk_result)) {
            if (((*actual).kind == types_ResolvedTypeKind_rk_result)) {
                __auto_type _mv_1366 = (*formal).inner_type;
                if (_mv_1366.has_value) {
                    __auto_type f_inner = _mv_1366.value;
                    __auto_type _mv_1367 = (*actual).inner_type;
                    if (_mv_1367.has_value) {
                        __auto_type a_inner = _mv_1367.value;
                        infer_unify_types(arena, f_inner, a_inner, bind_names, bind_types);
                    } else if (!_mv_1367.has_value) {
                    }
                } else if (!_mv_1366.has_value) {
                }
                __auto_type _mv_1368 = (*formal).inner_type2;
                if (_mv_1368.has_value) {
                    __auto_type f_inner2 = _mv_1368.value;
                    __auto_type _mv_1369 = (*actual).inner_type2;
                    if (_mv_1369.has_value) {
                        __auto_type a_inner2 = _mv_1369.value;
                        infer_unify_types(arena, f_inner2, a_inner2, bind_names, bind_types);
                    } else if (!_mv_1369.has_value) {
                    }
                } else if (!_mv_1368.has_value) {
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
        if ((kind == types_ResolvedTypeKind_rk_typevar)) {
            {
                __auto_type tv_name = (*t).name;
                __auto_type _mv_1370 = infer_find_binding(bind_names, bind_types, tv_name);
                if (_mv_1370.has_value) {
                    __auto_type bound = _mv_1370.value;
                    return bound;
                } else if (!_mv_1370.has_value) {
                    return t;
                }
            }
        } else if ((kind == types_ResolvedTypeKind_rk_ptr)) {
            __auto_type _mv_1371 = (*t).inner_type;
            if (_mv_1371.has_value) {
                __auto_type inner = _mv_1371.value;
                {
                    __auto_type new_inner = infer_substitute_type_vars(arena, inner, bind_names, bind_types);
                    __auto_type inner_name = (*new_inner).name;
                    __auto_type ptr_name = string_concat(arena, SLOP_STR("Ptr_"), inner_name);
                    __auto_type new_ptr = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_ptr, ptr_name, ((slop_option_string){.has_value = false}), SLOP_STR("void*"));
                    types_resolved_type_set_inner(new_ptr, new_inner);
                    return new_ptr;
                }
            } else if (!_mv_1371.has_value) {
                return t;
            }
        } else if ((kind == types_ResolvedTypeKind_rk_chan)) {
            __auto_type _mv_1372 = (*t).inner_type;
            if (_mv_1372.has_value) {
                __auto_type inner = _mv_1372.value;
                {
                    __auto_type new_inner = infer_substitute_type_vars(arena, inner, bind_names, bind_types);
                    __auto_type new_chan = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_chan, SLOP_STR("Chan"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_chan_int*"));
                    types_resolved_type_set_inner(new_chan, new_inner);
                    return new_chan;
                }
            } else if (!_mv_1372.has_value) {
                return t;
            }
        } else if ((kind == types_ResolvedTypeKind_rk_thread)) {
            __auto_type _mv_1373 = (*t).inner_type;
            if (_mv_1373.has_value) {
                __auto_type inner = _mv_1373.value;
                {
                    __auto_type new_inner = infer_substitute_type_vars(arena, inner, bind_names, bind_types);
                    __auto_type new_thread = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_thread, SLOP_STR("Thread"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_thread_int*"));
                    types_resolved_type_set_inner(new_thread, new_inner);
                    return new_thread;
                }
            } else if (!_mv_1373.has_value) {
                return t;
            }
        } else if ((kind == types_ResolvedTypeKind_rk_list)) {
            __auto_type _mv_1374 = (*t).inner_type;
            if (_mv_1374.has_value) {
                __auto_type inner = _mv_1374.value;
                {
                    __auto_type new_inner = infer_substitute_type_vars(arena, inner, bind_names, bind_types);
                    __auto_type new_list = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_list, SLOP_STR("List"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_list_t*"));
                    types_resolved_type_set_inner(new_list, new_inner);
                    return new_list;
                }
            } else if (!_mv_1374.has_value) {
                return t;
            }
        } else if ((kind == types_ResolvedTypeKind_rk_option)) {
            __auto_type _mv_1375 = (*t).inner_type;
            if (_mv_1375.has_value) {
                __auto_type inner = _mv_1375.value;
                {
                    __auto_type new_inner = infer_substitute_type_vars(arena, inner, bind_names, bind_types);
                    __auto_type inner_name = (*new_inner).name;
                    __auto_type opt_name = string_concat(arena, SLOP_STR("Option_"), inner_name);
                    __auto_type new_opt = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_option, opt_name, ((slop_option_string){.has_value = false}), SLOP_STR("slop_option"));
                    types_resolved_type_set_inner(new_opt, new_inner);
                    return new_opt;
                }
            } else if (!_mv_1375.has_value) {
                return t;
            }
        } else if ((kind == types_ResolvedTypeKind_rk_result)) {
            {
                __auto_type new_ok = ({ __auto_type _mv = (*t).inner_type; _mv.has_value ? ({ __auto_type ok = _mv.value; infer_substitute_type_vars(arena, ok, bind_names, bind_types); }) : (NULL); });
                __auto_type new_err = ({ __auto_type _mv = (*t).inner_type2; _mv.has_value ? ({ __auto_type err = _mv.value; infer_substitute_type_vars(arena, err, bind_names, bind_types); }) : (NULL); });
                if ((new_ok == NULL)) {
                    return t;
                } else {
                    {
                        __auto_type ok_name = (*new_ok).name;
                        __auto_type err_name = (((new_err != NULL)) ? (*new_err).name : SLOP_STR("Error"));
                        __auto_type result_name = string_concat(arena, SLOP_STR("Result_"), string_concat(arena, ok_name, string_concat(arena, SLOP_STR("_"), err_name)));
                        __auto_type new_result = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_result, result_name, ((slop_option_string){.has_value = false}), SLOP_STR("Result"));
                        types_resolved_type_set_inner(new_result, new_ok);
                        if ((new_err != NULL)) {
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
                if ((num_args != num_params)) {
                    {
                        __auto_type msg = string_concat(arena, SLOP_STR("'"), string_concat(arena, (*sig).name, string_concat(arena, SLOP_STR("' expects "), string_concat(arena, int_to_string(arena, num_params), string_concat(arena, SLOP_STR(" argument(s), got "), int_to_string(arena, num_args))))));
                        env_env_add_error(env, msg, line, col);
                    }
                }
                {
                    __auto_type limit = (((num_args < num_params)) ? num_args : num_params);
                    for (int64_t i = 0; i < limit; i++) {
                        __auto_type _mv_1376 = parser_sexpr_list_get(expr, (i + 1));
                        if (_mv_1376.has_value) {
                            __auto_type arg_expr = _mv_1376.value;
                            {
                                __auto_type actual_type = infer_infer_expr(env, arg_expr);
                                __auto_type _mv_1377 = ({ __auto_type _lst = params; size_t _idx = (size_t)i; slop_option_types_ParamInfo _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1377.has_value) {
                                    __auto_type param_info = _mv_1377.value;
                                    {
                                        __auto_type formal_type = param_info.param_type;
                                        infer_unify_types(arena, formal_type, actual_type, bind_names, bind_types);
                                    }
                                } else if (!_mv_1377.has_value) {
                                }
                            }
                        } else if (!_mv_1376.has_value) {
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

uint8_t infer_types_equal(types_ResolvedType* a, types_ResolvedType* b) {
    SLOP_PRE(((a != NULL)), "(!= a nil)");
    SLOP_PRE(((b != NULL)), "(!= b nil)");
    {
        __auto_type a_kind = (*a).kind;
        __auto_type b_kind = (*b).kind;
        __auto_type a_name = (*a).name;
        __auto_type b_name = (*b).name;
        if (string_eq(a_name, b_name)) {
            return 1;
        } else if (((a_kind == types_ResolvedTypeKind_rk_typevar) || (b_kind == types_ResolvedTypeKind_rk_typevar))) {
            return 1;
        } else if ((string_eq(a_name, SLOP_STR("T")) || string_eq(b_name, SLOP_STR("T")))) {
            return 1;
        } else if (((a_kind == types_ResolvedTypeKind_rk_option) && (b_kind == types_ResolvedTypeKind_rk_option))) {
            return (string_eq(a_name, SLOP_STR("Option_T")) || string_eq(b_name, SLOP_STR("Option_T")));
        } else if (((a_kind == types_ResolvedTypeKind_rk_result) && (b_kind == types_ResolvedTypeKind_rk_result))) {
            return (string_eq(a_name, SLOP_STR("Result")) || string_eq(b_name, SLOP_STR("Result")));
        } else if (((a_kind == types_ResolvedTypeKind_rk_range) || (b_kind == types_ResolvedTypeKind_rk_range))) {
            return infer_types_compatible_with_range(a, b);
        } else if (((a_kind == types_ResolvedTypeKind_rk_function) && (b_kind == types_ResolvedTypeKind_rk_function))) {
            return 1;
        } else if ((string_eq(a_name, SLOP_STR("Fn")) || string_eq(b_name, SLOP_STR("Fn")))) {
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
        if ((a_kind == types_ResolvedTypeKind_rk_range)) {
            __auto_type _mv_1378 = (*a).inner_type;
            if (_mv_1378.has_value) {
                __auto_type base = _mv_1378.value;
                return string_eq((*base).name, (*b).name);
            } else if (!_mv_1378.has_value) {
                return 0;
            }
        } else if ((b_kind == types_ResolvedTypeKind_rk_range)) {
            __auto_type _mv_1379 = (*b).inner_type;
            if (_mv_1379.has_value) {
                __auto_type base = _mv_1379.value;
                return string_eq((*a).name, (*base).name);
            } else if (!_mv_1379.has_value) {
                return 0;
            }
        } else {
            return 0;
        }
    }
}

types_ResolvedType* infer_unify_branch_types(env_TypeEnv* env, types_ResolvedType* a, types_ResolvedType* b, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((a != NULL)), "(!= a nil)");
    SLOP_PRE(((b != NULL)), "(!= b nil)");
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

void infer_sexpr_set_resolved_type(types_SExpr* expr, types_ResolvedType* t) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_1380 = (*expr);
    switch (_mv_1380.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1380.data.sym;
            (*expr) = ((types_SExpr){ .tag = types_SExpr_sym, .data.sym = (types_SExprSymbol){sym.name, sym.line, sym.col, (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = t}} });
            break;
        }
        case types_SExpr_str:
        {
            __auto_type str = _mv_1380.data.str;
            (*expr) = ((types_SExpr){ .tag = types_SExpr_str, .data.str = (types_SExprString){str.value, str.line, str.col, (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = t}} });
            break;
        }
        case types_SExpr_num:
        {
            __auto_type num = _mv_1380.data.num;
            (*expr) = ((types_SExpr){ .tag = types_SExpr_num, .data.num = (types_SExprNumber){num.int_value, num.float_value, num.is_float, num.raw, num.line, num.col, (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = t}} });
            break;
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1380.data.lst;
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
        if ((result != NULL)) {
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
        __auto_type _mv_1381 = (*expr);
        switch (_mv_1381.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_1381.data.sym;
                {
                    __auto_type name = sym.name;
                    if ((string_eq(name, SLOP_STR("true")) || string_eq(name, SLOP_STR("false")))) {
                        return env_env_get_bool_type(env);
                    } else if ((string_eq(name, SLOP_STR("nil")) || string_eq(name, SLOP_STR("unit")))) {
                        return env_env_get_unit_type(env);
                    } else if (string_eq(name, SLOP_STR("none"))) {
                        return env_env_make_option_type(env, NULL);
                    } else {
                        __auto_type _mv_1382 = env_env_lookup_var(env, name);
                        if (_mv_1382.has_value) {
                            __auto_type t = _mv_1382.value;
                            return t;
                        } else if (!_mv_1382.has_value) {
                            __auto_type _mv_1383 = env_env_lookup_constant(env, name);
                            if (_mv_1383.has_value) {
                                __auto_type t = _mv_1383.value;
                                return t;
                            } else if (!_mv_1383.has_value) {
                                __auto_type _mv_1384 = env_env_lookup_function(env, name);
                                if (_mv_1384.has_value) {
                                    __auto_type sig = _mv_1384.value;
                                    return env_env_make_fn_type(env, sig);
                                } else if (!_mv_1384.has_value) {
                                    if (infer_string_contains_char(name, 46)) {
                                        {
                                            __auto_type dot_pos = infer_string_index_of(name, 46);
                                            __auto_type arena = env_env_arena(env);
                                            __auto_type base_name = infer_string_substring(arena, name, 0, dot_pos);
                                            __auto_type field_name = infer_string_substring(arena, name, (dot_pos + 1), ((int64_t)(name.len)));
                                            __auto_type _mv_1385 = env_env_lookup_var(env, base_name);
                                            if (_mv_1385.has_value) {
                                                __auto_type obj_type = _mv_1385.value;
                                                return infer_check_field_exists(env, obj_type, field_name, line, col);
                                            } else if (!_mv_1385.has_value) {
                                                __auto_type _mv_1386 = env_env_lookup_type(env, base_name);
                                                if (_mv_1386.has_value) {
                                                    __auto_type type_info = _mv_1386.value;
                                                    return type_info;
                                                } else if (!_mv_1386.has_value) {
                                                    {
                                                        __auto_type msg = string_concat(arena, SLOP_STR("Undefined variable: "), name);
                                                        env_env_add_error(env, msg, line, col);
                                                        return env_env_get_int_type(env);
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        __auto_type _mv_1387 = env_env_lookup_type(env, name);
                                        if (_mv_1387.has_value) {
                                            __auto_type type_info = _mv_1387.value;
                                            return type_info;
                                        } else if (!_mv_1387.has_value) {
                                            {
                                                __auto_type arena = env_env_arena(env);
                                                __auto_type msg = string_concat(arena, SLOP_STR("Undefined variable: "), name);
                                                env_env_add_error(env, msg, line, col);
                                                return env_env_get_int_type(env);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            case types_SExpr_num:
            {
                __auto_type num = _mv_1381.data.num;
                return env_env_get_int_type(env);
            }
            case types_SExpr_str:
            {
                __auto_type str = _mv_1381.data.str;
                return env_env_get_string_type(env);
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1381.data.lst;
                return infer_infer_list_expr(env, expr, lst);
            }
        }
    }
}

types_ResolvedType* infer_infer_list_expr(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type items = lst.items;
        __auto_type len = ((int64_t)((items).len));
        if ((len == 0)) {
            return env_env_get_unit_type(env);
        } else {
            __auto_type _mv_1388 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (!_mv_1388.has_value) {
                return env_env_get_unit_type(env);
            } else if (_mv_1388.has_value) {
                __auto_type head = _mv_1388.value;
                __auto_type _mv_1389 = (*head);
                switch (_mv_1389.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_1389.data.sym;
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
            if ((len >= 4)) {
                __auto_type _mv_1390 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1390.has_value) {
                    __auto_type cond_expr = _mv_1390.value;
                    {
                        __auto_type _ = infer_infer_expr(env, cond_expr);
                    }
                } else if (!_mv_1390.has_value) {
                }
                __auto_type _mv_1391 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1391.has_value) {
                    __auto_type then_expr = _mv_1391.value;
                    {
                        __auto_type then_type = infer_infer_expr(env, then_expr);
                        __auto_type _mv_1392 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1392.has_value) {
                            __auto_type else_expr = _mv_1392.value;
                            {
                                __auto_type else_type = infer_infer_expr(env, else_expr);
                                return infer_unify_branch_types(env, then_type, else_type, line, col);
                            }
                        } else if (!_mv_1392.has_value) {
                            return then_type;
                        }
                    }
                } else if (!_mv_1391.has_value) {
                    return env_env_get_unit_type(env);
                }
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("cond"))) {
            return infer_infer_cond_expr(env, expr, lst);
        } else if (string_eq(op, SLOP_STR("match"))) {
            return infer_infer_match_expr(env, expr, lst);
        } else if (string_eq(op, SLOP_STR("do"))) {
            infer_infer_body_exprs(env, expr, 1);
            if ((len > 1)) {
                __auto_type _mv_1393 = ({ __auto_type _lst = items; size_t _idx = (size_t)(len - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1393.has_value) {
                    __auto_type last = _mv_1393.value;
                    return infer_infer_expr(env, last);
                } else if (!_mv_1393.has_value) {
                    return env_env_get_unit_type(env);
                }
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("let"))) {
            return infer_infer_let_expr(env, expr);
        } else if (string_eq(op, SLOP_STR("when"))) {
            infer_infer_body_exprs(env, expr, 1);
            return env_env_get_unit_type(env);
        } else if (string_eq(op, SLOP_STR("for"))) {
            if ((len >= 2)) {
                __auto_type _mv_1394 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1394.has_value) {
                    __auto_type binding_form = _mv_1394.value;
                    if (parser_sexpr_is_list(binding_form)) {
                        {
                            __auto_type bind_len = parser_sexpr_list_len(binding_form);
                            if ((bind_len >= 3)) {
                                __auto_type _mv_1395 = parser_sexpr_list_get(binding_form, 0);
                                if (_mv_1395.has_value) {
                                    __auto_type var_expr = _mv_1395.value;
                                    {
                                        __auto_type var_name = parser_sexpr_get_symbol_name(var_expr);
                                        if (!(string_eq(var_name, SLOP_STR("")))) {
                                            env_env_push_scope(env);
                                            env_env_bind_var(env, var_name, env_env_get_int_type(env));
                                            __auto_type _mv_1396 = parser_sexpr_list_get(binding_form, 1);
                                            if (_mv_1396.has_value) {
                                                __auto_type start_expr = _mv_1396.value;
                                                {
                                                    __auto_type _ = infer_infer_expr(env, start_expr);
                                                }
                                            } else if (!_mv_1396.has_value) {
                                            }
                                            __auto_type _mv_1397 = parser_sexpr_list_get(binding_form, 2);
                                            if (_mv_1397.has_value) {
                                                __auto_type end_expr = _mv_1397.value;
                                                {
                                                    __auto_type _ = infer_infer_expr(env, end_expr);
                                                }
                                            } else if (!_mv_1397.has_value) {
                                            }
                                            ({ for (int64_t body_idx = 2; body_idx < len; body_idx++) { ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)body_idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type body_expr = _mv.value; ({ __auto_type _ = infer_infer_expr(env, body_expr); ({ (void)0; }); }); } else { ({ (void)0; }); } (void)0; }); } 0; });
                                            env_env_pop_scope(env);
                                        }
                                    }
                                } else if (!_mv_1395.has_value) {
                                }
                            }
                        }
                    }
                } else if (!_mv_1394.has_value) {
                }
                return env_env_get_unit_type(env);
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("for-each"))) {
            if ((len >= 3)) {
                __auto_type _mv_1398 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1398.has_value) {
                    __auto_type binding_form = _mv_1398.value;
                    if (parser_sexpr_is_list(binding_form)) {
                        {
                            __auto_type bind_len = parser_sexpr_list_len(binding_form);
                            if ((bind_len >= 2)) {
                                __auto_type _mv_1399 = parser_sexpr_list_get(binding_form, 0);
                                if (_mv_1399.has_value) {
                                    __auto_type var_expr = _mv_1399.value;
                                    {
                                        __auto_type var_name = parser_sexpr_get_symbol_name(var_expr);
                                        if (string_eq(var_name, SLOP_STR(""))) {
                                            return env_env_get_unit_type(env);
                                        } else {
                                            __auto_type _mv_1400 = parser_sexpr_list_get(binding_form, 1);
                                            if (_mv_1400.has_value) {
                                                __auto_type coll_expr = _mv_1400.value;
                                                {
                                                    __auto_type coll_type = infer_infer_expr(env, coll_expr);
                                                    __auto_type coll_line = parser_sexpr_line(coll_expr);
                                                    __auto_type coll_col = parser_sexpr_col(coll_expr);
                                                    {
                                                        __auto_type elem_type = ({ __auto_type _mv = (*coll_type).inner_type; _mv.has_value ? ({ __auto_type inner = _mv.value; inner; }) : (({ __auto_type arena = env_env_arena(env); __auto_type coll_name = (*coll_type).name; __auto_type msg = string_concat(arena, SLOP_STR("for-each: cannot determine element type of '"), string_concat(arena, coll_name, SLOP_STR("' - collection has no inner type"))); env_env_add_error(env, msg, coll_line, coll_col); env_env_get_unknown_type(env); })); });
                                                        env_env_push_scope(env);
                                                        env_env_bind_var(env, var_name, elem_type);
                                                        ({ for (int64_t body_idx = 2; body_idx < len; body_idx++) { ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)body_idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type body_expr = _mv.value; ({ __auto_type _ = infer_infer_expr(env, body_expr); ({ (void)0; }); }); } else { ({ (void)0; }); } (void)0; }); } 0; });
                                                        env_env_pop_scope(env);
                                                        return env_env_get_unit_type(env);
                                                    }
                                                }
                                            } else if (!_mv_1400.has_value) {
                                                return env_env_get_unit_type(env);
                                            }
                                        }
                                    }
                                } else if (!_mv_1399.has_value) {
                                    return env_env_get_unit_type(env);
                                }
                            } else {
                                return env_env_get_unit_type(env);
                            }
                        }
                    } else {
                        return env_env_get_unit_type(env);
                    }
                } else if (!_mv_1398.has_value) {
                    return env_env_get_unit_type(env);
                }
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("while"))) {
            infer_infer_body_exprs(env, expr, 1);
            return env_env_get_unit_type(env);
        } else if (string_eq(op, SLOP_STR("@loop-invariant"))) {
            infer_infer_body_exprs(env, expr, 1);
            return env_env_get_unit_type(env);
        } else if (string_eq(op, SLOP_STR("with-arena"))) {
            return infer_infer_with_arena_expr(env, expr);
        } else if (string_eq(op, SLOP_STR("set!"))) {
            if ((len >= 4)) {
                __auto_type _mv_1401 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1401.has_value) {
                    __auto_type val_expr = _mv_1401.value;
                    {
                        __auto_type _ = infer_infer_expr(env, val_expr);
                    }
                } else if (!_mv_1401.has_value) {
                }
            } else if ((len >= 3)) {
                __auto_type _mv_1402 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1402.has_value) {
                    __auto_type val_expr = _mv_1402.value;
                    {
                        __auto_type _ = infer_infer_expr(env, val_expr);
                    }
                } else if (!_mv_1402.has_value) {
                }
            } else {
            }
            return env_env_get_unit_type(env);
        } else if (string_eq(op, SLOP_STR("return"))) {
            if ((len >= 2)) {
                __auto_type _mv_1403 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1403.has_value) {
                    __auto_type ret_expr = _mv_1403.value;
                    return infer_infer_expr(env, ret_expr);
                } else if (!_mv_1403.has_value) {
                    return env_env_get_unit_type(env);
                }
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (((string_eq(op, SLOP_STR("=="))) || (string_eq(op, SLOP_STR("!="))) || (string_eq(op, SLOP_STR("<"))) || (string_eq(op, SLOP_STR("<="))) || (string_eq(op, SLOP_STR(">"))) || (string_eq(op, SLOP_STR(">="))) || (string_eq(op, SLOP_STR("and"))) || (string_eq(op, SLOP_STR("or"))) || (string_eq(op, SLOP_STR("not"))))) {
            return env_env_get_bool_type(env);
        } else if (((string_eq(op, SLOP_STR("+"))) || (string_eq(op, SLOP_STR("-"))) || (string_eq(op, SLOP_STR("*"))) || (string_eq(op, SLOP_STR("/"))) || (string_eq(op, SLOP_STR("%"))))) {
            return env_env_get_int_type(env);
        } else if (string_eq(op, SLOP_STR("deref"))) {
            if ((len >= 2)) {
                __auto_type _mv_1404 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1404.has_value) {
                    __auto_type ptr_expr = _mv_1404.value;
                    {
                        __auto_type ptr_type = infer_infer_expr(env, ptr_expr);
                        if (types_resolved_type_is_pointer(ptr_type)) {
                            __auto_type _mv_1405 = (*ptr_type).inner_type;
                            if (_mv_1405.has_value) {
                                __auto_type inner = _mv_1405.value;
                                return inner;
                            } else if (!_mv_1405.has_value) {
                                return env_env_get_unit_type(env);
                            }
                        } else {
                            return ptr_type;
                        }
                    }
                } else if (!_mv_1404.has_value) {
                    return env_env_get_unit_type(env);
                }
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("addr"))) {
            if ((len >= 2)) {
                __auto_type _mv_1406 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1406.has_value) {
                    __auto_type inner_expr = _mv_1406.value;
                    {
                        __auto_type inner_type = infer_infer_expr(env, inner_expr);
                        return env_env_make_ptr_type(env, inner_type);
                    }
                } else if (!_mv_1406.has_value) {
                    return env_env_get_unit_type(env);
                }
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("cast"))) {
            if ((len >= 2)) {
                __auto_type _mv_1407 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1407.has_value) {
                    __auto_type type_expr = _mv_1407.value;
                    {
                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                        if (string_eq(type_name, SLOP_STR(""))) {
                            if (parser_sexpr_is_list(type_expr)) {
                                __auto_type _mv_1408 = parser_sexpr_list_get(type_expr, 0);
                                if (_mv_1408.has_value) {
                                    __auto_type head_expr = _mv_1408.value;
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
                                } else if (!_mv_1408.has_value) {
                                    return env_env_get_unknown_type(env);
                                }
                            } else {
                                return env_env_get_unknown_type(env);
                            }
                        } else {
                            __auto_type _mv_1409 = env_env_lookup_type(env, type_name);
                            if (_mv_1409.has_value) {
                                __auto_type t = _mv_1409.value;
                                return t;
                            } else if (!_mv_1409.has_value) {
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
                        }
                    }
                } else if (!_mv_1407.has_value) {
                    return env_env_get_unknown_type(env);
                }
            } else {
                return env_env_get_unknown_type(env);
            }
        } else if (string_eq(op, SLOP_STR("quote"))) {
            if ((len >= 2)) {
                __auto_type _mv_1410 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1410.has_value) {
                    __auto_type variant_expr = _mv_1410.value;
                    {
                        __auto_type variant_name = parser_sexpr_get_symbol_name(variant_expr);
                        if (string_eq(variant_name, SLOP_STR(""))) {
                            return env_env_get_unknown_type(env);
                        } else {
                            __auto_type _mv_1411 = env_env_lookup_variant(env, variant_name);
                            if (_mv_1411.has_value) {
                                __auto_type enum_name = _mv_1411.value;
                                __auto_type _mv_1412 = env_env_lookup_type(env, enum_name);
                                if (_mv_1412.has_value) {
                                    __auto_type enum_type = _mv_1412.value;
                                    return enum_type;
                                } else if (!_mv_1412.has_value) {
                                    return env_env_get_unknown_type(env);
                                }
                            } else if (!_mv_1411.has_value) {
                                return env_env_get_unknown_type(env);
                            }
                        }
                    }
                } else if (!_mv_1410.has_value) {
                    return env_env_get_unknown_type(env);
                }
            } else {
                return env_env_get_unknown_type(env);
            }
        } else if (string_eq(op, SLOP_STR("."))) {
            return infer_infer_field_access(env, expr, lst, line, col);
        } else if (string_eq(op, SLOP_STR("some"))) {
            if ((len >= 2)) {
                __auto_type _mv_1413 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1413.has_value) {
                    __auto_type inner_expr = _mv_1413.value;
                    {
                        __auto_type inner_type = infer_infer_expr(env, inner_expr);
                        return env_env_make_option_type(env, inner_type);
                    }
                } else if (!_mv_1413.has_value) {
                    return env_env_make_option_type(env, NULL);
                }
            } else {
                return env_env_make_option_type(env, NULL);
            }
        } else if (string_eq(op, SLOP_STR("none"))) {
            return env_env_make_option_type(env, NULL);
        } else if (string_eq(op, SLOP_STR("record-new"))) {
            for (int64_t fi = 2; fi < len; fi++) {
                __auto_type _mv_1414 = ({ __auto_type _lst = items; size_t _idx = (size_t)fi; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1414.has_value) {
                    __auto_type field_pair = _mv_1414.value;
                    if ((parser_sexpr_is_list(field_pair) && (parser_sexpr_list_len(field_pair) >= 2))) {
                        __auto_type _mv_1415 = parser_sexpr_list_get(field_pair, 1);
                        if (_mv_1415.has_value) {
                            __auto_type val_expr = _mv_1415.value;
                            {
                                __auto_type _ = infer_infer_expr(env, val_expr);
                            }
                        } else if (!_mv_1415.has_value) {
                        }
                    }
                } else if (!_mv_1414.has_value) {
                }
            }
            if ((len >= 2)) {
                __auto_type _mv_1416 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1416.has_value) {
                    __auto_type type_expr = _mv_1416.value;
                    {
                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                        if (string_eq(type_name, SLOP_STR(""))) {
                            return env_env_get_unit_type(env);
                        } else {
                            __auto_type _mv_1417 = env_env_lookup_type(env, type_name);
                            if (_mv_1417.has_value) {
                                __auto_type t = _mv_1417.value;
                                return t;
                            } else if (!_mv_1417.has_value) {
                                return env_env_get_unit_type(env);
                            }
                        }
                    }
                } else if (!_mv_1416.has_value) {
                    return env_env_get_unit_type(env);
                }
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("union-new"))) {
            if ((len >= 4)) {
                __auto_type _mv_1418 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1418.has_value) {
                    __auto_type val_expr = _mv_1418.value;
                    {
                        __auto_type _ = infer_infer_expr(env, val_expr);
                    }
                } else if (!_mv_1418.has_value) {
                }
            }
            if ((len >= 2)) {
                __auto_type _mv_1419 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1419.has_value) {
                    __auto_type type_expr = _mv_1419.value;
                    {
                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                        if (string_eq(type_name, SLOP_STR(""))) {
                            return env_env_get_unit_type(env);
                        } else {
                            __auto_type _mv_1420 = env_env_lookup_type(env, type_name);
                            if (_mv_1420.has_value) {
                                __auto_type t = _mv_1420.value;
                                return t;
                            } else if (!_mv_1420.has_value) {
                                return env_env_get_unit_type(env);
                            }
                        }
                    }
                } else if (!_mv_1419.has_value) {
                    return env_env_get_unit_type(env);
                }
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
        } else {
            __auto_type _mv_1421 = env_env_lookup_function(env, op);
            if (_mv_1421.has_value) {
                __auto_type sig = _mv_1421.value;
                if (infer_has_type_params(sig)) {
                    return infer_infer_generic_call(env, sig, expr, line, col);
                } else {
                    infer_check_fn_call_args(env, sig, expr, line, col);
                    return (*sig).return_type;
                }
            } else if (!_mv_1421.has_value) {
                __auto_type _mv_1422 = env_env_lookup_type(env, op);
                if (_mv_1422.has_value) {
                    __auto_type the_type = _mv_1422.value;
                    return the_type;
                } else if (!_mv_1422.has_value) {
                    if (string_eq(op, SLOP_STR("list-get"))) {
                        infer_check_builtin_args(env, SLOP_STR("list-get"), 2, (len - 1), line, col);
                        infer_infer_builtin_args(env, expr);
                        {
                            types_ResolvedType* elem_type = NULL;
                            if ((len >= 2)) {
                                __auto_type _mv_1423 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1423.has_value) {
                                    __auto_type list_arg = _mv_1423.value;
                                    {
                                        __auto_type list_type = infer_infer_expr(env, list_arg);
                                        if (((*list_type).kind == types_ResolvedTypeKind_rk_list)) {
                                            __auto_type _mv_1424 = (*list_type).inner_type;
                                            if (_mv_1424.has_value) {
                                                __auto_type inner = _mv_1424.value;
                                                elem_type = inner;
                                            } else if (!_mv_1424.has_value) {
                                            }
                                        }
                                    }
                                } else if (!_mv_1423.has_value) {
                                }
                            }
                            return env_env_make_option_type(env, elem_type);
                        }
                    } else if (string_eq(op, SLOP_STR("list-len"))) {
                        infer_check_builtin_args(env, SLOP_STR("list-len"), 1, (len - 1), line, col);
                        return env_env_get_int_type(env);
                    } else if (string_eq(op, SLOP_STR("arena-alloc"))) {
                        if ((len < 3)) {
                            env_env_add_error(env, SLOP_STR("arena-alloc requires arena and type/size arguments"), line, col);
                            return env_env_get_int_type(env);
                        } else {
                            __auto_type _mv_1425 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1425.has_value) {
                                __auto_type type_expr = _mv_1425.value;
                                {
                                    __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                                    if (string_eq(type_name, SLOP_STR(""))) {
                                        return env_env_get_int_type(env);
                                    } else {
                                        __auto_type _mv_1426 = env_env_lookup_type(env, type_name);
                                        if (_mv_1426.has_value) {
                                            __auto_type resolved = _mv_1426.value;
                                            return env_env_make_ptr_type(env, resolved);
                                        } else if (!_mv_1426.has_value) {
                                            {
                                                __auto_type arena = env_env_arena(env);
                                                env_env_add_warning(env, string_concat(arena, SLOP_STR("arena-alloc: unknown type: "), type_name), line, col);
                                            }
                                            return env_env_get_int_type(env);
                                        }
                                    }
                                }
                            } else if (!_mv_1425.has_value) {
                                return env_env_get_int_type(env);
                            }
                        }
                    } else if (string_eq(op, SLOP_STR("cast"))) {
                        return env_env_get_int_type(env);
                    } else if (string_eq(op, SLOP_STR("list-push"))) {
                        infer_check_builtin_args(env, SLOP_STR("list-push"), 2, (len - 1), line, col);
                        infer_infer_builtin_args(env, expr);
                        return env_env_get_unit_type(env);
                    } else if (string_eq(op, SLOP_STR("list-pop"))) {
                        infer_check_builtin_args(env, SLOP_STR("list-pop"), 1, (len - 1), line, col);
                        return env_env_make_option_type(env, NULL);
                    } else if (string_eq(op, SLOP_STR("list-new"))) {
                        infer_check_builtin_args(env, SLOP_STR("list-new"), 2, (len - 1), line, col);
                        {
                            __auto_type arena = env_env_arena(env);
                            __auto_type list_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_list, SLOP_STR("List"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_list_t*"));
                            if ((len >= 3)) {
                                __auto_type _mv_1427 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1427.has_value) {
                                    __auto_type type_expr = _mv_1427.value;
                                    {
                                        __auto_type elem_type = ((parser_sexpr_is_list(type_expr)) ? infer_resolve_complex_type_expr(env, type_expr) : ({ __auto_type tname = parser_sexpr_get_symbol_name(type_expr); ((string_eq(tname, SLOP_STR(""))) ? NULL : infer_resolve_simple_type(env, tname)); }));
                                        if ((elem_type != NULL)) {
                                            types_resolved_type_set_inner(list_type, elem_type);
                                        }
                                    }
                                } else if (!_mv_1427.has_value) {
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
                            if ((len >= 2)) {
                                __auto_type _mv_1428 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1428.has_value) {
                                    __auto_type val_expr = _mv_1428.value;
                                    {
                                        __auto_type val_type = infer_infer_expr(env, val_expr);
                                        types_resolved_type_set_inner(result_type, val_type);
                                    }
                                } else if (!_mv_1428.has_value) {
                                }
                            }
                            return result_type;
                        }
                    } else if (string_eq(op, SLOP_STR("error"))) {
                        {
                            __auto_type arena = env_env_arena(env);
                            __auto_type result_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_result, SLOP_STR("Result"), ((slop_option_string){.has_value = false}), SLOP_STR("Result"));
                            if ((len >= 2)) {
                                __auto_type _mv_1429 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1429.has_value) {
                                    __auto_type val_expr = _mv_1429.value;
                                    {
                                        __auto_type val_type = infer_infer_expr(env, val_expr);
                                        types_resolved_type_set_inner2(result_type, val_type);
                                    }
                                } else if (!_mv_1429.has_value) {
                                }
                            }
                            return result_type;
                        }
                    } else if (string_eq(op, SLOP_STR("@"))) {
                        if ((len >= 2)) {
                            __auto_type _mv_1430 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1430.has_value) {
                                __auto_type ptr_expr = _mv_1430.value;
                                {
                                    __auto_type ptr_type = infer_infer_expr(env, ptr_expr);
                                    if (types_resolved_type_is_pointer(ptr_type)) {
                                        __auto_type _mv_1431 = (*ptr_type).inner_type;
                                        if (_mv_1431.has_value) {
                                            __auto_type inner = _mv_1431.value;
                                            return inner;
                                        } else if (!_mv_1431.has_value) {
                                            return env_env_get_int_type(env);
                                        }
                                    } else {
                                        return env_env_get_int_type(env);
                                    }
                                }
                            } else if (!_mv_1430.has_value) {
                                return env_env_get_int_type(env);
                            }
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
                            if ((len >= 3)) {
                                __auto_type _mv_1432 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1432.has_value) {
                                    __auto_type type_expr = _mv_1432.value;
                                    {
                                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                                        if (!(string_eq(type_name, SLOP_STR("")))) {
                                            __auto_type _mv_1433 = env_env_lookup_type(env, type_name);
                                            if (_mv_1433.has_value) {
                                                __auto_type t = _mv_1433.value;
                                                key_type = t;
                                            } else if (!_mv_1433.has_value) {
                                            }
                                        }
                                    }
                                } else if (!_mv_1432.has_value) {
                                }
                            }
                            if ((len >= 4)) {
                                __auto_type _mv_1434 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1434.has_value) {
                                    __auto_type type_expr = _mv_1434.value;
                                    {
                                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                                        if (!(string_eq(type_name, SLOP_STR("")))) {
                                            __auto_type _mv_1435 = env_env_lookup_type(env, type_name);
                                            if (_mv_1435.has_value) {
                                                __auto_type t = _mv_1435.value;
                                                val_type = t;
                                            } else if (!_mv_1435.has_value) {
                                            }
                                        }
                                    }
                                } else if (!_mv_1434.has_value) {
                                }
                            }
                            {
                                __auto_type map_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_map, SLOP_STR("Map"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_map*"));
                                if ((key_type != NULL)) {
                                    types_resolved_type_set_inner(map_type, key_type);
                                }
                                if ((val_type != NULL)) {
                                    types_resolved_type_set_inner2(map_type, val_type);
                                }
                                return map_type;
                            }
                        }
                    } else if (string_eq(op, SLOP_STR("map-get"))) {
                        infer_check_builtin_args(env, SLOP_STR("map-get"), 2, (len - 1), line, col);
                        {
                            types_ResolvedType* val_type = NULL;
                            if ((len >= 2)) {
                                __auto_type _mv_1436 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1436.has_value) {
                                    __auto_type map_expr = _mv_1436.value;
                                    {
                                        __auto_type map_type = infer_infer_expr(env, map_expr);
                                        __auto_type _mv_1437 = (*map_type).inner_type2;
                                        if (_mv_1437.has_value) {
                                            __auto_type inner = _mv_1437.value;
                                            val_type = inner;
                                        } else if (!_mv_1437.has_value) {
                                        }
                                    }
                                } else if (!_mv_1436.has_value) {
                                }
                            }
                            return env_env_make_option_type(env, val_type);
                        }
                    } else if (string_eq(op, SLOP_STR("map-put"))) {
                        infer_check_builtin_args(env, SLOP_STR("map-put"), 3, (len - 1), line, col);
                        return env_env_get_unit_type(env);
                    } else if (string_eq(op, SLOP_STR("map-has"))) {
                        infer_check_builtin_args(env, SLOP_STR("map-has"), 2, (len - 1), line, col);
                        if ((len >= 2)) {
                            __auto_type _mv_1438 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1438.has_value) {
                                __auto_type map_expr = _mv_1438.value;
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
                            } else if (!_mv_1438.has_value) {
                            }
                        }
                        return env_env_get_bool_type(env);
                    } else if (string_eq(op, SLOP_STR("map-keys"))) {
                        infer_check_builtin_args(env, SLOP_STR("map-keys"), 1, (len - 1), line, col);
                        {
                            __auto_type arena = env_env_arena(env);
                            types_ResolvedType* key_type = NULL;
                            if ((len >= 2)) {
                                __auto_type _mv_1439 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1439.has_value) {
                                    __auto_type map_expr = _mv_1439.value;
                                    {
                                        __auto_type map_type = infer_infer_expr(env, map_expr);
                                        __auto_type _mv_1440 = (*map_type).inner_type;
                                        if (_mv_1440.has_value) {
                                            __auto_type inner = _mv_1440.value;
                                            key_type = inner;
                                        } else if (!_mv_1440.has_value) {
                                        }
                                    }
                                } else if (!_mv_1439.has_value) {
                                }
                            }
                            {
                                __auto_type list_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_list, SLOP_STR("List"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_list_t*"));
                                if ((key_type != NULL)) {
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
                            if ((len >= 3)) {
                                __auto_type _mv_1441 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1441.has_value) {
                                    __auto_type type_expr = _mv_1441.value;
                                    {
                                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                                        if (!(string_eq(type_name, SLOP_STR("")))) {
                                            __auto_type _mv_1442 = env_env_lookup_type(env, type_name);
                                            if (_mv_1442.has_value) {
                                                __auto_type t = _mv_1442.value;
                                                elem_type = t;
                                            } else if (!_mv_1442.has_value) {
                                            }
                                        }
                                    }
                                } else if (!_mv_1441.has_value) {
                                }
                            }
                            {
                                __auto_type set_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Set"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_map*"));
                                if ((elem_type != NULL)) {
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
                            if ((len >= 2)) {
                                __auto_type _mv_1443 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1443.has_value) {
                                    __auto_type set_expr = _mv_1443.value;
                                    {
                                        __auto_type set_type = infer_infer_expr(env, set_expr);
                                        __auto_type _mv_1444 = (*set_type).inner_type;
                                        if (_mv_1444.has_value) {
                                            __auto_type inner = _mv_1444.value;
                                            elem_type = inner;
                                        } else if (!_mv_1444.has_value) {
                                        }
                                    }
                                } else if (!_mv_1443.has_value) {
                                }
                            }
                            {
                                __auto_type list_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_list, SLOP_STR("List"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_list_t*"));
                                if ((elem_type != NULL)) {
                                    types_resolved_type_set_inner(list_type, elem_type);
                                }
                                return list_type;
                            }
                        }
                    } else if ((string_eq(op, SLOP_STR("exists")) || (string_eq(op, SLOP_STR("forall")) || string_eq(op, SLOP_STR("implies"))))) {
                        return env_env_get_unit_type(env);
                    } else {
                        {
                            __auto_type arena = env_env_arena(env);
                            __auto_type _mv_1445 = env_env_lookup_variant(env, op);
                            if (_mv_1445.has_value) {
                                __auto_type parent_type = _mv_1445.value;
                                {
                                    __auto_type msg = string_concat(arena, SLOP_STR("'"), string_concat(arena, op, string_concat(arena, SLOP_STR("' is a variant of '"), string_concat(arena, parent_type, SLOP_STR("'. Use (union-new Type variant value) syntax")))));
                                    env_env_add_error(env, msg, line, col);
                                    return env_env_get_unknown_type(env);
                                }
                            } else if (!_mv_1445.has_value) {
                                if ((strlib_starts_with(op, SLOP_STR("set-")) || (strlib_starts_with(op, SLOP_STR("map-")) || (strlib_starts_with(op, SLOP_STR("list-")) || strlib_starts_with(op, SLOP_STR("arena-")))))) {
                                    {
                                        __auto_type msg = string_concat(arena, SLOP_STR("Unknown builtin: '"), string_concat(arena, op, SLOP_STR("'")));
                                        env_env_add_error(env, msg, line, col);
                                        return env_env_get_unknown_type(env);
                                    }
                                } else {
                                    __auto_type _mv_1446 = env_env_lookup_var(env, op);
                                    if (_mv_1446.has_value) {
                                        __auto_type var_type = _mv_1446.value;
                                        infer_infer_builtin_args(env, expr);
                                        return var_type;
                                    } else if (!_mv_1446.has_value) {
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
                                }
                            }
                        }
                    }
                }
            }
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
                if ((num_args < num_params)) {
                    {
                        __auto_type msg = string_concat(arena, SLOP_STR("'"), string_concat(arena, fn_name, string_concat(arena, SLOP_STR("' expects "), string_concat(arena, int_to_string(arena, num_params), string_concat(arena, SLOP_STR(" argument(s), got "), int_to_string(arena, num_args))))));
                        env_env_add_error(env, msg, line, col);
                    }
                } else if ((num_args > num_params)) {
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
        __auto_type _mv_1447 = ({ __auto_type _lst = params; size_t _idx = (size_t)arg_idx; slop_option_types_ParamInfo _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1447.has_value) {
            __auto_type param_info = _mv_1447.value;
            {
                __auto_type expected_type = param_info.param_type;
                __auto_type _mv_1448 = parser_sexpr_list_get(expr, (arg_idx + 1));
                if (_mv_1448.has_value) {
                    __auto_type arg_expr = _mv_1448.value;
                    {
                        __auto_type actual_type = infer_infer_expr(env, arg_expr);
                        __auto_type expected_name = (*expected_type).name;
                        __auto_type actual_name = (*actual_type).name;
                        if (((string_eq(actual_name, SLOP_STR("Option_T")) || strlib_starts_with(actual_name, SLOP_STR("Option_"))) && !(strlib_starts_with(expected_name, SLOP_STR("Option_"))))) {
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
                        if (((!(infer_types_equal(expected_type, actual_type))) && (!(string_eq(actual_name, SLOP_STR("Unknown")))) && (!(string_eq(actual_name, SLOP_STR("T")))) && (!(string_eq(expected_name, SLOP_STR("Unknown")))) && (!(string_eq(expected_name, SLOP_STR("T")))) && (!((string_eq(actual_name, SLOP_STR("Option_T")) && strlib_starts_with(expected_name, SLOP_STR("Option_"))))) && (!(string_eq(actual_name, SLOP_STR("Ptr_T")))) && (!(strlib_starts_with(actual_name, SLOP_STR("Ptr_Ptr_")))) && (!((string_eq(actual_name, SLOP_STR("Unit")) && strlib_starts_with(expected_name, SLOP_STR("Ptr_"))))) && (!((strlib_starts_with(actual_name, SLOP_STR("Ptr_")) && string_eq(expected_name, SLOP_STR("Ptr_Void"))))) && (!((infer_is_integer_type(actual_name) && infer_is_integer_type(expected_name)))))) {
                            {
                                __auto_type msg = string_concat(arena, SLOP_STR("argument "), string_concat(arena, int_to_string(arena, (arg_idx + 1)), string_concat(arena, SLOP_STR(" to '"), string_concat(arena, fn_name, string_concat(arena, SLOP_STR("': expected "), string_concat(arena, expected_name, string_concat(arena, SLOP_STR(", got "), actual_name)))))));
                                env_env_add_error(env, msg, line, col);
                            }
                        }
                    }
                } else if (!_mv_1448.has_value) {
                }
            }
        } else if (!_mv_1447.has_value) {
        }
    }
}

void infer_check_builtin_args(env_TypeEnv* env, slop_string op, int64_t expected, int64_t actual, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    if ((actual != expected)) {
        {
            __auto_type arena = env_env_arena(env);
            __auto_type msg = string_concat(arena, SLOP_STR("'"), string_concat(arena, op, string_concat(arena, SLOP_STR("' expects "), string_concat(arena, int_to_string(arena, expected), string_concat(arena, SLOP_STR(" argument(s), got "), int_to_string(arena, actual))))));
            env_env_add_error(env, msg, line, col);
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
                __auto_type _mv_1449 = parser_sexpr_list_get(expr, i);
                if (_mv_1449.has_value) {
                    __auto_type arg_expr = _mv_1449.value;
                    {
                        __auto_type _ = infer_infer_expr(env, arg_expr);
                    }
                } else if (!_mv_1449.has_value) {
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
                __auto_type _mv_1450 = parser_sexpr_list_get(expr, i);
                if (_mv_1450.has_value) {
                    __auto_type body_expr = _mv_1450.value;
                    {
                        __auto_type _ = infer_infer_expr(env, body_expr);
                    }
                } else if (!_mv_1450.has_value) {
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
        if ((len < 3)) {
            return env_env_get_unit_type(env);
        } else {
            __auto_type _mv_1451 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (!_mv_1451.has_value) {
                return env_env_get_unit_type(env);
            } else if (_mv_1451.has_value) {
                __auto_type obj_expr = _mv_1451.value;
                {
                    __auto_type obj_type = infer_infer_expr(env, obj_expr);
                    __auto_type _mv_1452 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (!_mv_1452.has_value) {
                        return env_env_get_unit_type(env);
                    } else if (_mv_1452.has_value) {
                        __auto_type field_expr = _mv_1452.value;
                        __auto_type _mv_1453 = (*field_expr);
                        switch (_mv_1453.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type field_sym = _mv_1453.data.sym;
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
                }
            }
        }
    }
}

types_ResolvedType* infer_check_field_exists(env_TypeEnv* env, types_ResolvedType* obj_type, slop_string field_name, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((obj_type != NULL)), "(!= obj-type nil)");
    {
        __auto_type type_name = (*obj_type).name;
        __auto_type arena = env_env_arena(env);
        if (types_resolved_type_is_record(obj_type)) {
            __auto_type _mv_1454 = types_resolved_type_get_field_type(obj_type, field_name);
            if (_mv_1454.has_value) {
                __auto_type field_type = _mv_1454.value;
                return field_type;
            } else if (!_mv_1454.has_value) {
                {
                    __auto_type msg = string_concat(arena, SLOP_STR("Record '"), string_concat(arena, type_name, string_concat(arena, SLOP_STR("' has no field '"), string_concat(arena, field_name, SLOP_STR("'")))));
                    env_env_add_error(env, msg, line, col);
                    return env_env_get_unit_type(env);
                }
            }
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
                        if (strlib_starts_with(type_name, SLOP_STR("Ptr_"))) {
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

types_ResolvedType* infer_infer_cond_expr(env_TypeEnv* env, types_SExpr* expr, types_SExprList lst) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type items = lst.items;
        __auto_type len = ((int64_t)((items).len));
        __auto_type line = parser_sexpr_line(expr);
        __auto_type col = parser_sexpr_col(expr);
        uint8_t has_result = 0;
        types_ResolvedType* result_type = env_env_get_unit_type(env);
        __auto_type i = 1;
        while ((i < len)) {
            __auto_type _mv_1455 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1455.has_value) {
                __auto_type clause = _mv_1455.value;
                __auto_type _mv_1456 = (*clause);
                switch (_mv_1456.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type clause_lst = _mv_1456.data.lst;
                        {
                            __auto_type clause_items = clause_lst.items;
                            __auto_type clause_len = ((int64_t)((clause_items).len));
                            if ((clause_len > 1)) {
                                ({ for (int64_t ci = 0; ci < (clause_len - 1); ci++) { ({ __auto_type _mv = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)ci; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type clause_elem = _mv.value; ({ __auto_type elem_name = parser_sexpr_get_symbol_name(clause_elem); ((!(string_eq(elem_name, SLOP_STR("else")))) ? ({ ({ __auto_type _ = infer_infer_expr(env, clause_elem); ({ (void)0; }); }); 0; }) : ({ (void)0; })); }); } else { ({ (void)0; }); } (void)0; }); } 0; });
                                __auto_type _mv_1457 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)(clause_len - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1457.has_value) {
                                    __auto_type body = _mv_1457.value;
                                    {
                                        __auto_type body_type = infer_infer_expr(env, body);
                                        if (!(has_result)) {
                                            result_type = body_type;
                                            has_result = 1;
                                        } else {
                                            result_type = infer_unify_branch_types(env, result_type, body_type, line, col);
                                        }
                                    }
                                } else if (!_mv_1457.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1455.has_value) {
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
        if ((parser_sexpr_list_len(pattern) > 0)) {
            __auto_type _mv_1458 = parser_sexpr_list_get(pattern, 0);
            if (_mv_1458.has_value) {
                __auto_type variant_expr = _mv_1458.value;
                {
                    __auto_type variant_name = parser_sexpr_get_symbol_name(variant_expr);
                    if (!(string_eq(variant_name, SLOP_STR("")))) {
                        if ((parser_sexpr_list_len(pattern) > 1)) {
                            __auto_type _mv_1459 = parser_sexpr_list_get(pattern, 1);
                            if (_mv_1459.has_value) {
                                __auto_type binding_expr = _mv_1459.value;
                                {
                                    __auto_type binding_name = parser_sexpr_get_symbol_name(binding_expr);
                                    if (!(string_eq(binding_name, SLOP_STR("")))) {
                                        {
                                            __auto_type scrutinee_name = (*scrutinee_type).name;
                                            __auto_type scrutinee_kind = (*scrutinee_type).kind;
                                            if (string_eq(scrutinee_name, SLOP_STR("T"))) {
                                                env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                            } else {
                                                if (((scrutinee_kind == types_ResolvedTypeKind_rk_option) && string_eq(variant_name, SLOP_STR("some")))) {
                                                    __auto_type _mv_1460 = (*scrutinee_type).inner_type;
                                                    if (_mv_1460.has_value) {
                                                        __auto_type inner = _mv_1460.value;
                                                        env_env_bind_var(env, binding_name, inner);
                                                    } else if (!_mv_1460.has_value) {
                                                        env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                                    }
                                                } else {
                                                    if ((scrutinee_kind == types_ResolvedTypeKind_rk_result)) {
                                                        if (string_eq(variant_name, SLOP_STR("ok"))) {
                                                            __auto_type _mv_1461 = (*scrutinee_type).inner_type;
                                                            if (_mv_1461.has_value) {
                                                                __auto_type inner = _mv_1461.value;
                                                                env_env_bind_var(env, binding_name, inner);
                                                            } else if (!_mv_1461.has_value) {
                                                                env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                                            }
                                                        } else if (string_eq(variant_name, SLOP_STR("error"))) {
                                                            __auto_type _mv_1462 = (*scrutinee_type).inner_type2;
                                                            if (_mv_1462.has_value) {
                                                                __auto_type inner2 = _mv_1462.value;
                                                                env_env_bind_var(env, binding_name, inner2);
                                                            } else if (!_mv_1462.has_value) {
                                                                env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                                            }
                                                        } else {
                                                            env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                                        }
                                                    } else {
                                                        __auto_type _mv_1463 = types_resolved_type_get_variant_payload(scrutinee_type, variant_name);
                                                        if (_mv_1463.has_value) {
                                                            __auto_type payload_type = _mv_1463.value;
                                                            env_env_bind_var(env, binding_name, payload_type);
                                                        } else if (!_mv_1463.has_value) {
                                                            env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            } else if (!_mv_1459.has_value) {
                            }
                        }
                    }
                }
            } else if (!_mv_1458.has_value) {
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
        types_ResolvedType* result_type = env_env_get_unit_type(env);
        __auto_type scrutinee_type = (((len >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type scrutinee = _mv.value; infer_infer_expr(env, scrutinee); }) : (env_env_get_unit_type(env)); }) : env_env_get_unit_type(env));
        __auto_type i = 2;
        while ((i < len)) {
            __auto_type _mv_1464 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1464.has_value) {
                __auto_type clause = _mv_1464.value;
                __auto_type _mv_1465 = (*clause);
                switch (_mv_1465.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type clause_lst = _mv_1465.data.lst;
                        {
                            __auto_type clause_items = clause_lst.items;
                            __auto_type clause_len = ((int64_t)((clause_items).len));
                            if ((clause_len > 1)) {
                                env_env_push_scope(env);
                                __auto_type _mv_1466 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1466.has_value) {
                                    __auto_type pattern = _mv_1466.value;
                                    infer_bind_match_pattern(env, scrutinee_type, pattern);
                                } else if (!_mv_1466.has_value) {
                                }
                                ({ for (int64_t bi = 1; bi < (clause_len - 1); bi++) { ({ __auto_type _mv = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)bi; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type body_expr = _mv.value; ({ __auto_type _ = infer_infer_expr(env, body_expr); ({ (void)0; }); }); } else { ({ (void)0; }); } (void)0; }); } 0; });
                                __auto_type _mv_1467 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)(clause_len - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1467.has_value) {
                                    __auto_type body = _mv_1467.value;
                                    {
                                        __auto_type body_type = infer_infer_expr(env, body);
                                        if (!(has_result)) {
                                            result_type = body_type;
                                            has_result = 1;
                                        } else {
                                            result_type = infer_unify_branch_types(env, result_type, body_type, line, col);
                                        }
                                    }
                                } else if (!_mv_1467.has_value) {
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
            } else if (!_mv_1464.has_value) {
            }
            i = (i + 1);
        }
        return result_type;
    }
}

void infer_check_return_type(env_TypeEnv* env, types_SExpr* fn_form, slop_string fn_name, types_ResolvedType* inferred_type, int64_t fn_line, int64_t fn_col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    SLOP_PRE(((inferred_type != NULL)), "(!= inferred-type nil)");
    __auto_type _mv_1468 = (*fn_form);
    switch (_mv_1468.tag) {
        case types_SExpr_lst:
        {
            __auto_type fn_lst = _mv_1468.data.lst;
            {
                __auto_type items = fn_lst.items;
                __auto_type len = ((int64_t)((items).len));
                ({ for (int64_t i = 3; i < len; i++) { ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type item = _mv.value; ((parser_is_form(item, SLOP_STR("@spec"))) ? ({ infer_check_spec_return_type(env, item, fn_name, inferred_type, fn_line, fn_col); 0; }) : ({ (void)0; })); } else { ({ (void)0; }); } (void)0; }); } 0; });
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
    __auto_type _mv_1469 = (*spec_form);
    switch (_mv_1469.tag) {
        case types_SExpr_lst:
        {
            __auto_type spec_lst = _mv_1469.data.lst;
            {
                __auto_type spec_items = spec_lst.items;
                __auto_type _mv_1470 = ({ __auto_type _lst = spec_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1470.has_value) {
                    __auto_type spec_body = _mv_1470.value;
                    infer_check_spec_body_return(env, spec_body, fn_name, inferred_type, fn_line, fn_col);
                } else if (!_mv_1470.has_value) {
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
    __auto_type _mv_1471 = (*spec_body);
    switch (_mv_1471.tag) {
        case types_SExpr_lst:
        {
            __auto_type body_lst = _mv_1471.data.lst;
            {
                __auto_type body_items = body_lst.items;
                __auto_type body_len = ((int64_t)((body_items).len));
                __auto_type _mv_1472 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1472.has_value) {
                    __auto_type ret_expr = _mv_1472.value;
                    infer_check_return_expr(env, ret_expr, fn_name, inferred_type, fn_line, fn_col);
                } else if (!_mv_1472.has_value) {
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
    __auto_type _mv_1473 = (*ret_expr);
    switch (_mv_1473.tag) {
        case types_SExpr_sym:
        {
            __auto_type ret_sym = _mv_1473.data.sym;
            {
                __auto_type declared_name = ret_sym.name;
                __auto_type inferred_name = (*inferred_type).name;
                if ((!(string_eq(declared_name, inferred_name)) && (infer_checker_is_primitive_type(declared_name) && infer_checker_is_primitive_type(inferred_name)))) {
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
    if ((parser_sexpr_is_list(param_form) && (parser_sexpr_list_len(param_form) >= 2))) {
        __auto_type _mv_1474 = parser_sexpr_list_get(param_form, 0);
        if (_mv_1474.has_value) {
            __auto_type first_expr = _mv_1474.value;
            {
                __auto_type first_name = parser_sexpr_get_symbol_name(first_expr);
                if (((string_eq(first_name, SLOP_STR("in"))) || (string_eq(first_name, SLOP_STR("out"))) || (string_eq(first_name, SLOP_STR("mut"))))) {
                    if ((parser_sexpr_list_len(param_form) >= 3)) {
                        __auto_type _mv_1475 = parser_sexpr_list_get(param_form, 1);
                        if (_mv_1475.has_value) {
                            __auto_type name_expr = _mv_1475.value;
                            {
                                __auto_type param_name = parser_sexpr_get_symbol_name(name_expr);
                                if (!(string_eq(param_name, SLOP_STR("")))) {
                                    {
                                        __auto_type param_type = infer_get_param_type_from_form(env, param_form);
                                        env_env_bind_var(env, param_name, param_type);
                                    }
                                }
                            }
                        } else if (!_mv_1475.has_value) {
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
        } else if (!_mv_1474.has_value) {
        }
    }
}

types_ResolvedType* infer_get_param_type_from_form(env_TypeEnv* env, types_SExpr* param_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((param_form != NULL)), "(!= param-form nil)");
    {
        __auto_type type_pos = ({ __auto_type _mv = parser_sexpr_list_get(param_form, 0); _mv.has_value ? ({ __auto_type first_expr = _mv.value; ({ __auto_type first_name = parser_sexpr_get_symbol_name(first_expr); ((((string_eq(first_name, SLOP_STR("in"))) || (string_eq(first_name, SLOP_STR("out"))) || (string_eq(first_name, SLOP_STR("mut"))))) ? 2 : 1); }); }) : (1); });
        __auto_type _mv_1476 = parser_sexpr_list_get(param_form, type_pos);
        if (_mv_1476.has_value) {
            __auto_type type_expr = _mv_1476.value;
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
        } else if (!_mv_1476.has_value) {
            return env_env_get_unknown_type(env);
        }
    }
}

types_ResolvedType* infer_resolve_complex_type_expr(env_TypeEnv* env, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_1477 = parser_sexpr_list_get(type_expr, 0);
    if (_mv_1477.has_value) {
        __auto_type head_expr = _mv_1477.value;
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
                    if ((parser_sexpr_list_len(type_expr) >= 3)) {
                        __auto_type _mv_1478 = parser_sexpr_list_get(type_expr, 2);
                        if (_mv_1478.has_value) {
                            __auto_type val_expr = _mv_1478.value;
                            {
                                __auto_type val_type = infer_resolve_simple_type(env, parser_sexpr_get_symbol_name(val_expr));
                                if ((val_type != NULL)) {
                                    types_resolved_type_set_inner2(map_type, val_type);
                                }
                            }
                        } else if (!_mv_1478.has_value) {
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
                    if ((parser_sexpr_list_len(type_expr) >= 2)) {
                        __auto_type _mv_1479 = parser_sexpr_list_get(type_expr, 1);
                        if (_mv_1479.has_value) {
                            __auto_type ok_expr = _mv_1479.value;
                            {
                                __auto_type ok_name = parser_sexpr_get_symbol_name(ok_expr);
                                {
                                    __auto_type ok_type = ((string_eq(ok_name, SLOP_STR(""))) ? ((parser_sexpr_is_list(ok_expr)) ? infer_resolve_complex_type_expr(env, ok_expr) : env_env_get_unknown_type(env)) : infer_resolve_type_lenient(env, ok_name));
                                    types_resolved_type_set_inner(result_type, ok_type);
                                }
                            }
                        } else if (!_mv_1479.has_value) {
                        }
                    }
                    if ((parser_sexpr_list_len(type_expr) >= 3)) {
                        __auto_type _mv_1480 = parser_sexpr_list_get(type_expr, 2);
                        if (_mv_1480.has_value) {
                            __auto_type err_expr = _mv_1480.value;
                            {
                                __auto_type err_name = parser_sexpr_get_symbol_name(err_expr);
                                {
                                    __auto_type err_type = ((string_eq(err_name, SLOP_STR(""))) ? ((parser_sexpr_is_list(err_expr)) ? infer_resolve_complex_type_expr(env, err_expr) : env_env_get_unknown_type(env)) : infer_resolve_type_lenient(env, err_name));
                                    types_resolved_type_set_inner2(result_type, err_type);
                                }
                            }
                        } else if (!_mv_1480.has_value) {
                        }
                    }
                    return result_type;
                }
            } else {
                __auto_type _mv_1481 = env_env_lookup_type(env, head_name);
                if (_mv_1481.has_value) {
                    __auto_type t = _mv_1481.value;
                    return t;
                } else if (!_mv_1481.has_value) {
                    return env_env_get_unknown_type(env);
                }
            }
        }
    } else if (!_mv_1477.has_value) {
        return env_env_get_unknown_type(env);
    }
}

types_ResolvedType* infer_resolve_option_inner_type(env_TypeEnv* env, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    if ((parser_sexpr_list_len(type_expr) < 2)) {
        return env_env_get_unknown_type(env);
    } else {
        __auto_type _mv_1482 = parser_sexpr_list_get(type_expr, 1);
        if (_mv_1482.has_value) {
            __auto_type inner_expr = _mv_1482.value;
            {
                __auto_type inner_name = parser_sexpr_get_symbol_name(inner_expr);
                if (string_eq(inner_name, SLOP_STR(""))) {
                    return env_env_get_unknown_type(env);
                } else {
                    return infer_resolve_simple_type(env, inner_name);
                }
            }
        } else if (!_mv_1482.has_value) {
            return env_env_get_unknown_type(env);
        }
    }
}

types_ResolvedType* infer_resolve_ptr_inner_type(env_TypeEnv* env, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    if ((parser_sexpr_list_len(type_expr) < 2)) {
        return env_env_get_unit_type(env);
    } else {
        __auto_type _mv_1483 = parser_sexpr_list_get(type_expr, 1);
        if (_mv_1483.has_value) {
            __auto_type inner_expr = _mv_1483.value;
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
        } else if (!_mv_1483.has_value) {
            return env_env_get_unit_type(env);
        }
    }
}

types_ResolvedType* infer_resolve_type_lenient(env_TypeEnv* env, slop_string type_name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1484 = env_env_lookup_type(env, type_name);
    if (_mv_1484.has_value) {
        __auto_type t = _mv_1484.value;
        return t;
    } else if (!_mv_1484.has_value) {
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
}

types_ResolvedType* infer_resolve_simple_type(env_TypeEnv* env, slop_string type_name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1485 = env_env_lookup_type(env, type_name);
    if (_mv_1485.has_value) {
        __auto_type t = _mv_1485.value;
        return t;
    } else if (!_mv_1485.has_value) {
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
            } else if (string_eq(type_name, SLOP_STR("Char"))) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Char"), ((slop_option_string){.has_value = false}), SLOP_STR("char"));
            } else if (string_eq(type_name, SLOP_STR("Void"))) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Void"), ((slop_option_string){.has_value = false}), SLOP_STR("void"));
            } else if (string_eq(type_name, SLOP_STR("Bytes"))) {
                return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Bytes"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_bytes"));
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
}

void infer_bind_let_binding(env_TypeEnv* env, types_SExpr* binding_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((binding_form != NULL)), "(!= binding-form nil)");
    if ((parser_sexpr_is_list(binding_form) && (parser_sexpr_list_len(binding_form) >= 2))) {
        __auto_type _mv_1486 = parser_sexpr_list_get(binding_form, 0);
        if (_mv_1486.has_value) {
            __auto_type first_expr = _mv_1486.value;
            {
                __auto_type first_name = parser_sexpr_get_symbol_name(first_expr);
                if (string_eq(first_name, SLOP_STR("mut"))) {
                    if ((parser_sexpr_list_len(binding_form) >= 3)) {
                        __auto_type _mv_1487 = parser_sexpr_list_get(binding_form, 1);
                        if (_mv_1487.has_value) {
                            __auto_type name_expr = _mv_1487.value;
                            {
                                __auto_type var_name = parser_sexpr_get_symbol_name(name_expr);
                                if (!(string_eq(var_name, SLOP_STR("")))) {
                                    {
                                        __auto_type binding_len = parser_sexpr_list_len(binding_form);
                                        __auto_type _mv_1488 = parser_sexpr_list_get(binding_form, (binding_len - 1));
                                        if (_mv_1488.has_value) {
                                            __auto_type val_expr = _mv_1488.value;
                                            {
                                                __auto_type val_type = infer_infer_expr(env, val_expr);
                                                __auto_type val_type_name = (*val_type).name;
                                                if (((binding_len == 3) && string_eq(val_type_name, SLOP_STR("Option_T")))) {
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
                                                        env_env_add_error(env, strlib_string_build(arena, parts), line, col);
                                                        env_env_bind_var(env, var_name, val_type);
                                                    }
                                                } else {
                                                    env_env_bind_var(env, var_name, val_type);
                                                }
                                            }
                                        } else if (!_mv_1488.has_value) {
                                        }
                                    }
                                }
                            }
                        } else if (!_mv_1487.has_value) {
                        }
                    }
                } else {
                    if (!(string_eq(first_name, SLOP_STR("")))) {
                        {
                            __auto_type binding_len = parser_sexpr_list_len(binding_form);
                            if ((binding_len == 3)) {
                                __auto_type _mv_1489 = parser_sexpr_list_get(binding_form, 2);
                                if (_mv_1489.has_value) {
                                    __auto_type val_expr = _mv_1489.value;
                                    {
                                        __auto_type val_type = infer_infer_expr(env, val_expr);
                                        env_env_bind_var(env, first_name, val_type);
                                    }
                                } else if (!_mv_1489.has_value) {
                                }
                            } else {
                                __auto_type _mv_1490 = parser_sexpr_list_get(binding_form, 1);
                                if (_mv_1490.has_value) {
                                    __auto_type val_expr = _mv_1490.value;
                                    {
                                        __auto_type val_type = infer_infer_expr(env, val_expr);
                                        env_env_bind_var(env, first_name, val_type);
                                    }
                                } else if (!_mv_1490.has_value) {
                                }
                            }
                        }
                    }
                }
            }
        } else if (!_mv_1486.has_value) {
        }
    }
}

types_ResolvedType* infer_infer_let_expr(env_TypeEnv* env, types_SExpr* expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    env_env_push_scope(env);
    if (parser_sexpr_is_list(expr)) {
        __auto_type _mv_1491 = parser_sexpr_list_get(expr, 1);
        if (_mv_1491.has_value) {
            __auto_type bindings_expr = _mv_1491.value;
            if (parser_sexpr_is_list(bindings_expr)) {
                {
                    __auto_type num_bindings = parser_sexpr_list_len(bindings_expr);
                    ({ for (int64_t i = 0; i < num_bindings; i++) { ({ __auto_type _mv = parser_sexpr_list_get(bindings_expr, i); if (_mv.has_value) { __auto_type binding = _mv.value; infer_bind_let_binding(env, binding); } else { ({ (void)0; }); } (void)0; }); } 0; });
                }
            }
        } else if (!_mv_1491.has_value) {
        }
    }
    {
        __auto_type result_type = ((parser_sexpr_is_list(expr)) ? ({ __auto_type len = parser_sexpr_list_len(expr); types_ResolvedType* last_type = env_env_get_unit_type(env); ({ for (int64_t i = 2; i < len; i++) { ({ __auto_type _mv = parser_sexpr_list_get(expr, i); if (_mv.has_value) { __auto_type body_expr = _mv.value; ({ last_type = infer_infer_expr(env, body_expr); (void)0; }); } else { ({ (void)0; }); } (void)0; }); } 0; }); last_type; }) : env_env_get_unit_type(env));
        env_env_pop_scope(env);
        return result_type;
    }
}

types_ResolvedType* infer_infer_with_arena_expr(env_TypeEnv* env, types_SExpr* expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type len = parser_sexpr_list_len(expr);
        if ((len < 2)) {
            env_env_add_error(env, SLOP_STR("with-arena requires size argument"), parser_sexpr_line(expr), parser_sexpr_col(expr));
            return env_env_get_unit_type(env);
        } else {
            __auto_type _mv_1492 = parser_sexpr_list_get(expr, 1);
            if (_mv_1492.has_value) {
                __auto_type size_expr = _mv_1492.value;
                __auto_type _mv_1493 = (*size_expr);
                switch (_mv_1493.tag) {
                    case types_SExpr_num:
                    {
                        __auto_type num = _mv_1493.data.num;
                        if ((num.int_value <= 0)) {
                            env_env_add_error(env, SLOP_STR("with-arena size must be positive"), num.line, num.col);
                        } else {
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_1492.has_value) {
            }
            env_env_push_scope(env);
            env_env_bind_var(env, SLOP_STR("arena"), env_env_get_arena_type(env));
            {
                types_ResolvedType* result_type = env_env_get_unit_type(env);
                for (int64_t i = 2; i < len; i++) {
                    __auto_type _mv_1494 = parser_sexpr_list_get(expr, i);
                    if (_mv_1494.has_value) {
                        __auto_type body_expr = _mv_1494.value;
                        result_type = infer_infer_expr(env, body_expr);
                    } else if (!_mv_1494.has_value) {
                    }
                }
                env_env_pop_scope(env);
                return result_type;
            }
        }
    }
}

slop_string infer_get_fn_name(types_SExpr* fn_form) {
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    if (!(parser_sexpr_is_list(fn_form))) {
        return SLOP_STR("unknown");
    } else {
        if ((parser_sexpr_list_len(fn_form) < 2)) {
            return SLOP_STR("unknown");
        } else {
            __auto_type _mv_1495 = parser_sexpr_list_get(fn_form, 1);
            if (_mv_1495.has_value) {
                __auto_type name_expr = _mv_1495.value;
                {
                    __auto_type name = parser_sexpr_get_symbol_name(name_expr);
                    if (string_eq(name, SLOP_STR(""))) {
                        return SLOP_STR("unknown");
                    } else {
                        return name;
                    }
                }
            } else if (!_mv_1495.has_value) {
                return SLOP_STR("unknown");
            }
        }
    }
}

types_ResolvedType* infer_resolve_hole_type(env_TypeEnv* env, slop_list_types_SExpr_ptr items, int64_t len) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    if ((len < 2)) {
        return env_env_get_unit_type(env);
    } else {
        __auto_type _mv_1496 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1496.has_value) {
            __auto_type type_expr = _mv_1496.value;
            {
                __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                if (string_eq(type_name, SLOP_STR(""))) {
                    return env_env_get_unit_type(env);
                } else {
                    __auto_type _mv_1497 = env_env_lookup_type(env, type_name);
                    if (_mv_1497.has_value) {
                        __auto_type t = _mv_1497.value;
                        return t;
                    } else if (!_mv_1497.has_value) {
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
                }
            }
        } else if (!_mv_1496.has_value) {
            return env_env_get_unit_type(env);
        }
    }
}

slop_string infer_get_hole_prompt(slop_list_types_SExpr_ptr items, int64_t len) {
    if ((len < 3)) {
        return SLOP_STR("(no description)");
    } else {
        __auto_type _mv_1498 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_1498.has_value) {
            __auto_type prompt_expr = _mv_1498.value;
            __auto_type _mv_1499 = (*prompt_expr);
            switch (_mv_1499.tag) {
                case types_SExpr_str:
                {
                    __auto_type str = _mv_1499.data.str;
                    return str.value;
                }
                default: {
                    return SLOP_STR("(no description)");
                }
            }
        } else if (!_mv_1498.has_value) {
            return SLOP_STR("(no description)");
        }
    }
}

int64_t infer_find_last_body_idx(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = (len - 1);
        while (((i >= 3) && infer_is_c_name_related(items, i))) {
            i = (i - 1);
        }
        return i;
    }
}

uint8_t infer_is_c_name_related(slop_list_types_SExpr_ptr items, int64_t idx) {
    __auto_type _mv_1500 = ({ __auto_type _lst = items; size_t _idx = (size_t)idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
    if (_mv_1500.has_value) {
        __auto_type item = _mv_1500.value;
        __auto_type _mv_1501 = (*item);
        switch (_mv_1501.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_1501.data.sym;
                return string_eq(sym.name, SLOP_STR(":c-name"));
            }
            case types_SExpr_str:
            {
                __auto_type _ = _mv_1501.data.str;
                if ((idx > 0)) {
                    __auto_type _mv_1502 = ({ __auto_type _lst = items; size_t _idx = (size_t)(idx - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1502.has_value) {
                        __auto_type prev = _mv_1502.value;
                        __auto_type _mv_1503 = (*prev);
                        switch (_mv_1503.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1503.data.sym;
                                return string_eq(sym.name, SLOP_STR(":c-name"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1502.has_value) {
                        return 0;
                    }
                } else {
                    return 0;
                }
            }
            default: {
                return 0;
            }
        }
    } else if (!_mv_1500.has_value) {
        return 0;
    }
}

uint8_t infer_is_annotation_expr(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    if (parser_sexpr_is_list(expr)) {
        __auto_type _mv_1504 = parser_sexpr_list_get(expr, 0);
        if (_mv_1504.has_value) {
            __auto_type head = _mv_1504.value;
            __auto_type _mv_1505 = (*head);
            switch (_mv_1505.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_1505.data.sym;
                    return strlib_starts_with(sym.name, SLOP_STR("@"));
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_1504.has_value) {
            return 0;
        }
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
        env_env_push_scope(env);
        if (parser_sexpr_is_list(fn_form)) {
            {
                __auto_type params_len = parser_sexpr_list_len(fn_form);
                if ((params_len > 2)) {
                    __auto_type _mv_1506 = parser_sexpr_list_get(fn_form, 2);
                    if (_mv_1506.has_value) {
                        __auto_type params_expr = _mv_1506.value;
                        if (parser_sexpr_is_list(params_expr)) {
                            {
                                __auto_type num_params = parser_sexpr_list_len(params_expr);
                                ({ for (int64_t k = 0; k < num_params; k++) { ({ __auto_type _mv = parser_sexpr_list_get(params_expr, k); if (_mv.has_value) { __auto_type param_form = _mv.value; infer_bind_param_from_form(env, param_form); } else { ({ (void)0; }); } (void)0; }); } 0; });
                            }
                        }
                    } else if (!_mv_1506.has_value) {
                    }
                }
            }
        }
        {
            __auto_type result_type = ({ __auto_type _mv = (*fn_form); types_ResolvedType* _mr = {0}; switch (_mv.tag) { case types_SExpr_lst: { __auto_type fn_lst = _mv.data.lst; _mr = ({ __auto_type items = fn_lst.items; __auto_type item_len = ((int64_t)((items).len)); __auto_type last_body_idx = infer_find_last_body_idx(items); __auto_type body_type = env_env_get_unit_type(env); ({ for (int64_t bi = 3; bi < (last_body_idx + 1); bi++) { ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)bi; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type body_expr = _mv.value; (((!(infer_is_annotation_expr(body_expr)) && !(infer_is_c_name_related(items, bi)))) ? ({ ({ body_type = infer_infer_expr(env, body_expr); (void)0; }); 0; }) : ({ (void)0; })); } else { ({ (void)0; }); } (void)0; }); } 0; }); body_type; }); break; } default: { _mr = env_env_get_unit_type(env); break; }  } _mr; });
            infer_check_return_type(env, fn_form, fn_name, result_type, fn_line, fn_col);
            env_env_pop_scope(env);
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
                __auto_type _mv_1507 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1507.has_value) {
                    __auto_type pattern_case = _mv_1507.value;
                    __auto_type _mv_1508 = (*pattern_case);
                    switch (_mv_1508.tag) {
                        case types_SExpr_lst:
                        {
                            __auto_type pattern_list = _mv_1508.data.lst;
                            if ((((int64_t)((pattern_list.items).len)) > 0)) {
                                __auto_type _mv_1509 = ({ __auto_type _lst = pattern_list.items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1509.has_value) {
                                    __auto_type pattern_expr = _mv_1509.value;
                                    __auto_type _mv_1510 = (*pattern_expr);
                                    switch (_mv_1510.tag) {
                                        case types_SExpr_lst:
                                        {
                                            __auto_type variant_list = _mv_1510.data.lst;
                                            {
                                                __auto_type variant_items = variant_list.items;
                                                if ((((int64_t)((variant_items).len)) > 0)) {
                                                    __auto_type _mv_1511 = ({ __auto_type _lst = variant_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_1511.has_value) {
                                                        __auto_type variant_name_expr = _mv_1511.value;
                                                        __auto_type _mv_1512 = (*variant_name_expr);
                                                        switch (_mv_1512.tag) {
                                                            case types_SExpr_sym:
                                                            {
                                                                __auto_type variant_sym = _mv_1512.data.sym;
                                                                {
                                                                    __auto_type variant_name = variant_sym.name;
                                                                    __auto_type _mv_1513 = types_resolved_type_get_variant_payload(scrutinee_type, variant_name);
                                                                    if (_mv_1513.has_value) {
                                                                        __auto_type payload_type = _mv_1513.value;
                                                                        if ((((int64_t)((variant_items).len)) > 1)) {
                                                                            __auto_type _mv_1514 = ({ __auto_type _lst = variant_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                            if (_mv_1514.has_value) {
                                                                                __auto_type binding_expr = _mv_1514.value;
                                                                                __auto_type _mv_1515 = (*binding_expr);
                                                                                switch (_mv_1515.tag) {
                                                                                    case types_SExpr_sym:
                                                                                    {
                                                                                        __auto_type binding_sym = _mv_1515.data.sym;
                                                                                        env_env_bind_var(env, binding_sym.name, payload_type);
                                                                                        break;
                                                                                    }
                                                                                    default: {
                                                                                        break;
                                                                                    }
                                                                                }
                                                                            } else if (!_mv_1514.has_value) {
                                                                            }
                                                                        }
                                                                    } else if (!_mv_1513.has_value) {
                                                                        __auto_type _mv_1516 = types_resolved_type_get_variant_index(scrutinee_type, variant_name);
                                                                        if (_mv_1516.has_value) {
                                                                            __auto_type _ = _mv_1516.value;
                                                                        } else if (!_mv_1516.has_value) {
                                                                        }
                                                                    }
                                                                }
                                                                break;
                                                            }
                                                            default: {
                                                                break;
                                                            }
                                                        }
                                                    } else if (!_mv_1511.has_value) {
                                                    }
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_1509.has_value) {
                                }
                            }
                            break;
                        }
                        default: {
                            break;
                        }
                    }
                } else if (!_mv_1507.has_value) {
                }
            }
        }
    }
}

