#include "../runtime/slop_runtime.h"
#include "slop_infer.h"

uint8_t infer_types_equal(types_ResolvedType* a, types_ResolvedType* b);
uint8_t infer_types_compatible_with_range(types_ResolvedType* a, types_ResolvedType* b);
types_ResolvedType* infer_unify_branch_types(env_TypeEnv* env, types_ResolvedType* a, types_ResolvedType* b, int64_t line, int64_t col);
types_ResolvedType* infer_infer_expr(env_TypeEnv* env, types_SExpr* expr);
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
uint8_t infer_is_primitive_type(slop_string name);
void infer_check_return_expr(env_TypeEnv* env, types_SExpr* ret_expr, slop_string fn_name, types_ResolvedType* inferred_type, int64_t fn_line, int64_t fn_col);
void infer_bind_param_from_form(env_TypeEnv* env, types_SExpr* param_form);
types_ResolvedType* infer_get_param_type_from_form(env_TypeEnv* env, types_SExpr* param_form);
types_ResolvedType* infer_resolve_complex_type_expr(env_TypeEnv* env, types_SExpr* type_expr);
types_ResolvedType* infer_resolve_option_inner_type(env_TypeEnv* env, types_SExpr* type_expr);
types_ResolvedType* infer_resolve_ptr_inner_type(env_TypeEnv* env, types_SExpr* type_expr);
types_ResolvedType* infer_resolve_simple_type(env_TypeEnv* env, slop_string type_name);
void infer_bind_let_binding(env_TypeEnv* env, types_SExpr* binding_form);
types_ResolvedType* infer_infer_let_expr(env_TypeEnv* env, types_SExpr* expr);
types_ResolvedType* infer_infer_with_arena_expr(env_TypeEnv* env, types_SExpr* expr);
slop_string infer_get_fn_name(types_SExpr* fn_form);
types_ResolvedType* infer_resolve_hole_type(env_TypeEnv* env, slop_list_types_SExpr_ptr items, int64_t len);
slop_string infer_get_hole_prompt(slop_list_types_SExpr_ptr items, int64_t len);
int64_t infer_find_last_body_idx(slop_list_types_SExpr_ptr items);
uint8_t infer_is_c_name_related(slop_list_types_SExpr_ptr items, int64_t idx);
types_ResolvedType* infer_infer_fn_body(env_TypeEnv* env, types_SExpr* fn_form);
void infer_check_match_patterns(env_TypeEnv* env, types_ResolvedType* scrutinee_type, slop_list_types_SExpr_ptr patterns);

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
        } else if ((string_eq(a_name, SLOP_STR("T")) || string_eq(b_name, SLOP_STR("T")))) {
            return 1;
        } else if (((a_kind == types_ResolvedTypeKind_rk_option) && (b_kind == types_ResolvedTypeKind_rk_option))) {
            return (string_eq(a_name, SLOP_STR("Option_T")) || string_eq(b_name, SLOP_STR("Option_T")));
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
            __auto_type _mv_72 = (*a).inner_type;
            if (_mv_72.has_value) {
                __auto_type base = _mv_72.value;
                return string_eq((*base).name, (*b).name);
            } else if (!_mv_72.has_value) {
                return 0;
            }
        } else if ((b_kind == types_ResolvedTypeKind_rk_range)) {
            __auto_type _mv_73 = (*b).inner_type;
            if (_mv_73.has_value) {
                __auto_type base = _mv_73.value;
                return string_eq((*a).name, (*base).name);
            } else if (!_mv_73.has_value) {
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

types_ResolvedType* infer_infer_expr(env_TypeEnv* env, types_SExpr* expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type line = parser_sexpr_line(expr);
        __auto_type col = parser_sexpr_col(expr);
        __auto_type _mv_74 = (*expr);
        switch (_mv_74.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_74.data.sym;
                {
                    __auto_type name = sym.name;
                    if ((string_eq(name, SLOP_STR("true")) || string_eq(name, SLOP_STR("false")))) {
                        return env_env_get_bool_type(env);
                    } else if ((string_eq(name, SLOP_STR("nil")) || string_eq(name, SLOP_STR("unit")))) {
                        return env_env_get_unit_type(env);
                    } else if (string_eq(name, SLOP_STR("none"))) {
                        return env_env_make_option_type(env, NULL);
                    } else {
                        __auto_type _mv_75 = env_env_lookup_var(env, name);
                        if (_mv_75.has_value) {
                            __auto_type t = _mv_75.value;
                            return t;
                        } else if (!_mv_75.has_value) {
                            __auto_type _mv_76 = env_env_lookup_constant(env, name);
                            if (_mv_76.has_value) {
                                __auto_type t = _mv_76.value;
                                return t;
                            } else if (!_mv_76.has_value) {
                                __auto_type _mv_77 = env_env_lookup_function(env, name);
                                if (_mv_77.has_value) {
                                    __auto_type sig = _mv_77.value;
                                    return env_env_make_fn_type(env, sig);
                                } else if (!_mv_77.has_value) {
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
            case types_SExpr_num:
            {
                __auto_type num = _mv_74.data.num;
                return env_env_get_int_type(env);
            }
            case types_SExpr_str:
            {
                __auto_type str = _mv_74.data.str;
                return env_env_get_string_type(env);
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_74.data.lst;
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
            __auto_type _mv_78 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (!_mv_78.has_value) {
                return env_env_get_unit_type(env);
            } else if (_mv_78.has_value) {
                __auto_type head = _mv_78.value;
                __auto_type _mv_79 = (*head);
                switch (_mv_79.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type sym = _mv_79.data.sym;
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
                __auto_type _mv_80 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_80.has_value) {
                    __auto_type then_expr = _mv_80.value;
                    {
                        __auto_type then_type = infer_infer_expr(env, then_expr);
                        __auto_type _mv_81 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_81.has_value) {
                            __auto_type else_expr = _mv_81.value;
                            {
                                __auto_type else_type = infer_infer_expr(env, else_expr);
                                return infer_unify_branch_types(env, then_type, else_type, line, col);
                            }
                        } else if (!_mv_81.has_value) {
                            return then_type;
                        }
                    }
                } else if (!_mv_80.has_value) {
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
            if ((len > 1)) {
                __auto_type _mv_82 = ({ __auto_type _lst = items; size_t _idx = (size_t)(len - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_82.has_value) {
                    __auto_type last = _mv_82.value;
                    return infer_infer_expr(env, last);
                } else if (!_mv_82.has_value) {
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
            return env_env_get_unit_type(env);
        } else if (string_eq(op, SLOP_STR("for-each"))) {
            if ((len >= 3)) {
                __auto_type _mv_83 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_83.has_value) {
                    __auto_type binding_form = _mv_83.value;
                    if (parser_sexpr_is_list(binding_form)) {
                        {
                            __auto_type bind_len = parser_sexpr_list_len(binding_form);
                            if ((bind_len >= 2)) {
                                __auto_type _mv_84 = parser_sexpr_list_get(binding_form, 0);
                                if (_mv_84.has_value) {
                                    __auto_type var_expr = _mv_84.value;
                                    {
                                        __auto_type var_name = parser_sexpr_get_symbol_name(var_expr);
                                        if (string_eq(var_name, SLOP_STR(""))) {
                                            return env_env_get_unit_type(env);
                                        } else {
                                            __auto_type _mv_85 = parser_sexpr_list_get(binding_form, 1);
                                            if (_mv_85.has_value) {
                                                __auto_type coll_expr = _mv_85.value;
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
                                            } else if (!_mv_85.has_value) {
                                                return env_env_get_unit_type(env);
                                            }
                                        }
                                    }
                                } else if (!_mv_84.has_value) {
                                    return env_env_get_unit_type(env);
                                }
                            } else {
                                return env_env_get_unit_type(env);
                            }
                        }
                    } else {
                        return env_env_get_unit_type(env);
                    }
                } else if (!_mv_83.has_value) {
                    return env_env_get_unit_type(env);
                }
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("while"))) {
            infer_infer_body_exprs(env, expr, 1);
            return env_env_get_unit_type(env);
        } else if (string_eq(op, SLOP_STR("with-arena"))) {
            return infer_infer_with_arena_expr(env, expr);
        } else if (string_eq(op, SLOP_STR("set!"))) {
            if ((len >= 4)) {
                __auto_type _mv_86 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_86.has_value) {
                    __auto_type val_expr = _mv_86.value;
                    {
                        __auto_type _ = infer_infer_expr(env, val_expr);
                    }
                } else if (!_mv_86.has_value) {
                }
            } else if ((len >= 3)) {
                __auto_type _mv_87 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_87.has_value) {
                    __auto_type val_expr = _mv_87.value;
                    {
                        __auto_type _ = infer_infer_expr(env, val_expr);
                    }
                } else if (!_mv_87.has_value) {
                }
            } else {
            }
            return env_env_get_unit_type(env);
        } else if (string_eq(op, SLOP_STR("return"))) {
            if ((len >= 2)) {
                __auto_type _mv_88 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_88.has_value) {
                    __auto_type ret_expr = _mv_88.value;
                    return infer_infer_expr(env, ret_expr);
                } else if (!_mv_88.has_value) {
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
                __auto_type _mv_89 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_89.has_value) {
                    __auto_type ptr_expr = _mv_89.value;
                    {
                        __auto_type ptr_type = infer_infer_expr(env, ptr_expr);
                        if (types_resolved_type_is_pointer(ptr_type)) {
                            __auto_type _mv_90 = (*ptr_type).inner_type;
                            if (_mv_90.has_value) {
                                __auto_type inner = _mv_90.value;
                                return inner;
                            } else if (!_mv_90.has_value) {
                                return env_env_get_unit_type(env);
                            }
                        } else {
                            return ptr_type;
                        }
                    }
                } else if (!_mv_89.has_value) {
                    return env_env_get_unit_type(env);
                }
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("addr"))) {
            if ((len >= 2)) {
                __auto_type _mv_91 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_91.has_value) {
                    __auto_type inner_expr = _mv_91.value;
                    {
                        __auto_type inner_type = infer_infer_expr(env, inner_expr);
                        return env_env_make_ptr_type(env, inner_type);
                    }
                } else if (!_mv_91.has_value) {
                    return env_env_get_unit_type(env);
                }
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (string_eq(op, SLOP_STR("cast"))) {
            if ((len >= 2)) {
                __auto_type _mv_92 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_92.has_value) {
                    __auto_type type_expr = _mv_92.value;
                    {
                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                        if (string_eq(type_name, SLOP_STR(""))) {
                            if (parser_sexpr_is_list(type_expr)) {
                                __auto_type _mv_93 = parser_sexpr_list_get(type_expr, 0);
                                if (_mv_93.has_value) {
                                    __auto_type head_expr = _mv_93.value;
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
                                } else if (!_mv_93.has_value) {
                                    return env_env_get_unknown_type(env);
                                }
                            } else {
                                return env_env_get_unknown_type(env);
                            }
                        } else {
                            __auto_type _mv_94 = env_env_lookup_type(env, type_name);
                            if (_mv_94.has_value) {
                                __auto_type t = _mv_94.value;
                                return t;
                            } else if (!_mv_94.has_value) {
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
                } else if (!_mv_92.has_value) {
                    return env_env_get_unknown_type(env);
                }
            } else {
                return env_env_get_unknown_type(env);
            }
        } else if (string_eq(op, SLOP_STR("quote"))) {
            if ((len >= 2)) {
                __auto_type _mv_95 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_95.has_value) {
                    __auto_type variant_expr = _mv_95.value;
                    {
                        __auto_type variant_name = parser_sexpr_get_symbol_name(variant_expr);
                        if (string_eq(variant_name, SLOP_STR(""))) {
                            return env_env_get_unknown_type(env);
                        } else {
                            __auto_type _mv_96 = env_env_lookup_variant(env, variant_name);
                            if (_mv_96.has_value) {
                                __auto_type enum_name = _mv_96.value;
                                __auto_type _mv_97 = env_env_lookup_type(env, enum_name);
                                if (_mv_97.has_value) {
                                    __auto_type enum_type = _mv_97.value;
                                    return enum_type;
                                } else if (!_mv_97.has_value) {
                                    return env_env_get_unknown_type(env);
                                }
                            } else if (!_mv_96.has_value) {
                                return env_env_get_unknown_type(env);
                            }
                        }
                    }
                } else if (!_mv_95.has_value) {
                    return env_env_get_unknown_type(env);
                }
            } else {
                return env_env_get_unknown_type(env);
            }
        } else if (string_eq(op, SLOP_STR("."))) {
            return infer_infer_field_access(env, expr, lst, line, col);
        } else if (string_eq(op, SLOP_STR("some"))) {
            if ((len >= 2)) {
                __auto_type _mv_98 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_98.has_value) {
                    __auto_type inner_expr = _mv_98.value;
                    {
                        __auto_type inner_type = infer_infer_expr(env, inner_expr);
                        return env_env_make_option_type(env, inner_type);
                    }
                } else if (!_mv_98.has_value) {
                    return env_env_make_option_type(env, NULL);
                }
            } else {
                return env_env_make_option_type(env, NULL);
            }
        } else if (string_eq(op, SLOP_STR("none"))) {
            return env_env_make_option_type(env, NULL);
        } else if (string_eq(op, SLOP_STR("record-new"))) {
            if ((len >= 2)) {
                __auto_type _mv_99 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_99.has_value) {
                    __auto_type type_expr = _mv_99.value;
                    {
                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                        if (string_eq(type_name, SLOP_STR(""))) {
                            return env_env_get_unit_type(env);
                        } else {
                            __auto_type _mv_100 = env_env_lookup_type(env, type_name);
                            if (_mv_100.has_value) {
                                __auto_type t = _mv_100.value;
                                return t;
                            } else if (!_mv_100.has_value) {
                                return env_env_get_unit_type(env);
                            }
                        }
                    }
                } else if (!_mv_99.has_value) {
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
            __auto_type _mv_101 = env_env_lookup_function(env, op);
            if (_mv_101.has_value) {
                __auto_type sig = _mv_101.value;
                infer_check_fn_call_args(env, sig, expr, line, col);
                return (*sig).return_type;
            } else if (!_mv_101.has_value) {
                __auto_type _mv_102 = env_env_lookup_type(env, op);
                if (_mv_102.has_value) {
                    __auto_type the_type = _mv_102.value;
                    return the_type;
                } else if (!_mv_102.has_value) {
                    if (string_eq(op, SLOP_STR("list-get"))) {
                        infer_check_builtin_args(env, SLOP_STR("list-get"), 2, (len - 1), line, col);
                        return env_env_make_option_type(env, NULL);
                    } else if (string_eq(op, SLOP_STR("list-len"))) {
                        infer_check_builtin_args(env, SLOP_STR("list-len"), 1, (len - 1), line, col);
                        return env_env_get_int_type(env);
                    } else if (string_eq(op, SLOP_STR("arena-alloc"))) {
                        if ((len >= 3)) {
                            __auto_type _mv_103 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_103.has_value) {
                                __auto_type type_expr = _mv_103.value;
                                {
                                    __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                                    if (string_eq(type_name, SLOP_STR(""))) {
                                        return env_env_get_int_type(env);
                                    } else {
                                        __auto_type _mv_104 = env_env_lookup_type(env, type_name);
                                        if (_mv_104.has_value) {
                                            __auto_type resolved = _mv_104.value;
                                            return env_env_make_ptr_type(env, resolved);
                                        } else if (!_mv_104.has_value) {
                                            return env_env_get_int_type(env);
                                        }
                                    }
                                }
                            } else if (!_mv_103.has_value) {
                                return env_env_get_int_type(env);
                            }
                        } else {
                            return env_env_get_int_type(env);
                        }
                    } else if (string_eq(op, SLOP_STR("cast"))) {
                        return env_env_get_int_type(env);
                    } else if (string_eq(op, SLOP_STR("string-eq"))) {
                        return env_env_get_bool_type(env);
                    } else if (string_eq(op, SLOP_STR("string-concat"))) {
                        return env_env_get_string_type(env);
                    } else if (string_eq(op, SLOP_STR("string-len"))) {
                        return env_env_get_int_type(env);
                    } else if (string_eq(op, SLOP_STR("string-copy"))) {
                        return env_env_get_string_type(env);
                    } else if (string_eq(op, SLOP_STR("string-new"))) {
                        return env_env_get_string_type(env);
                    } else if (string_eq(op, SLOP_STR("string-slice"))) {
                        return env_env_get_string_type(env);
                    } else if (string_eq(op, SLOP_STR("int-to-string"))) {
                        return env_env_get_string_type(env);
                    } else if (string_eq(op, SLOP_STR("char-at"))) {
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
                            return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("List"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_list_t*"));
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
                        return env_env_make_result_type(env);
                    } else if (string_eq(op, SLOP_STR("error"))) {
                        return env_env_make_result_type(env);
                    } else if (string_eq(op, SLOP_STR("@"))) {
                        if ((len >= 2)) {
                            __auto_type _mv_105 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_105.has_value) {
                                __auto_type ptr_expr = _mv_105.value;
                                {
                                    __auto_type ptr_type = infer_infer_expr(env, ptr_expr);
                                    if (types_resolved_type_is_pointer(ptr_type)) {
                                        __auto_type _mv_106 = (*ptr_type).inner_type;
                                        if (_mv_106.has_value) {
                                            __auto_type inner = _mv_106.value;
                                            return inner;
                                        } else if (!_mv_106.has_value) {
                                            return env_env_get_int_type(env);
                                        }
                                    } else {
                                        return env_env_get_int_type(env);
                                    }
                                }
                            } else if (!_mv_105.has_value) {
                                return env_env_get_int_type(env);
                            }
                        } else {
                            return env_env_get_int_type(env);
                        }
                    } else if (string_eq(op, SLOP_STR("some"))) {
                        return env_env_make_option_type(env, NULL);
                    } else if (string_eq(op, SLOP_STR("map-new"))) {
                        infer_check_builtin_args(env, SLOP_STR("map-new"), 3, (len - 1), line, col);
                        {
                            __auto_type arena = env_env_arena(env);
                            types_ResolvedType* key_type = NULL;
                            types_ResolvedType* val_type = NULL;
                            if ((len >= 3)) {
                                __auto_type _mv_107 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_107.has_value) {
                                    __auto_type type_expr = _mv_107.value;
                                    {
                                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                                        if (!(string_eq(type_name, SLOP_STR("")))) {
                                            __auto_type _mv_108 = env_env_lookup_type(env, type_name);
                                            if (_mv_108.has_value) {
                                                __auto_type t = _mv_108.value;
                                                key_type = t;
                                            } else if (!_mv_108.has_value) {
                                            }
                                        }
                                    }
                                } else if (!_mv_107.has_value) {
                                }
                            }
                            if ((len >= 4)) {
                                __auto_type _mv_109 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_109.has_value) {
                                    __auto_type type_expr = _mv_109.value;
                                    {
                                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                                        if (!(string_eq(type_name, SLOP_STR("")))) {
                                            __auto_type _mv_110 = env_env_lookup_type(env, type_name);
                                            if (_mv_110.has_value) {
                                                __auto_type t = _mv_110.value;
                                                val_type = t;
                                            } else if (!_mv_110.has_value) {
                                            }
                                        }
                                    }
                                } else if (!_mv_109.has_value) {
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
                                __auto_type _mv_111 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_111.has_value) {
                                    __auto_type map_expr = _mv_111.value;
                                    {
                                        __auto_type map_type = infer_infer_expr(env, map_expr);
                                        __auto_type _mv_112 = (*map_type).inner_type2;
                                        if (_mv_112.has_value) {
                                            __auto_type inner = _mv_112.value;
                                            val_type = inner;
                                        } else if (!_mv_112.has_value) {
                                        }
                                    }
                                } else if (!_mv_111.has_value) {
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
                            __auto_type _mv_113 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_113.has_value) {
                                __auto_type map_expr = _mv_113.value;
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
                            } else if (!_mv_113.has_value) {
                            }
                        }
                        return env_env_get_bool_type(env);
                    } else if (string_eq(op, SLOP_STR("map-keys"))) {
                        infer_check_builtin_args(env, SLOP_STR("map-keys"), 1, (len - 1), line, col);
                        {
                            __auto_type arena = env_env_arena(env);
                            types_ResolvedType* key_type = NULL;
                            if ((len >= 2)) {
                                __auto_type _mv_114 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_114.has_value) {
                                    __auto_type map_expr = _mv_114.value;
                                    {
                                        __auto_type map_type = infer_infer_expr(env, map_expr);
                                        __auto_type _mv_115 = (*map_type).inner_type;
                                        if (_mv_115.has_value) {
                                            __auto_type inner = _mv_115.value;
                                            key_type = inner;
                                        } else if (!_mv_115.has_value) {
                                        }
                                    }
                                } else if (!_mv_114.has_value) {
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
                                __auto_type _mv_116 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_116.has_value) {
                                    __auto_type type_expr = _mv_116.value;
                                    {
                                        __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                                        if (!(string_eq(type_name, SLOP_STR("")))) {
                                            __auto_type _mv_117 = env_env_lookup_type(env, type_name);
                                            if (_mv_117.has_value) {
                                                __auto_type t = _mv_117.value;
                                                elem_type = t;
                                            } else if (!_mv_117.has_value) {
                                            }
                                        }
                                    }
                                } else if (!_mv_116.has_value) {
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
                                __auto_type _mv_118 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_118.has_value) {
                                    __auto_type set_expr = _mv_118.value;
                                    {
                                        __auto_type set_type = infer_infer_expr(env, set_expr);
                                        __auto_type _mv_119 = (*set_type).inner_type;
                                        if (_mv_119.has_value) {
                                            __auto_type inner = _mv_119.value;
                                            elem_type = inner;
                                        } else if (!_mv_119.has_value) {
                                        }
                                    }
                                } else if (!_mv_118.has_value) {
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
                    } else {
                        {
                            __auto_type arena = env_env_arena(env);
                            __auto_type _mv_120 = env_env_lookup_variant(env, op);
                            if (_mv_120.has_value) {
                                __auto_type parent_type = _mv_120.value;
                                {
                                    __auto_type msg = string_concat(arena, SLOP_STR("'"), string_concat(arena, op, string_concat(arena, SLOP_STR("' is a variant of '"), string_concat(arena, parent_type, SLOP_STR("'. Use (union-new Type variant value) syntax")))));
                                    env_env_add_error(env, msg, line, col);
                                    return env_env_get_unknown_type(env);
                                }
                            } else if (!_mv_120.has_value) {
                                if ((strlib_starts_with(op, SLOP_STR("set-")) || (strlib_starts_with(op, SLOP_STR("map-")) || (strlib_starts_with(op, SLOP_STR("list-")) || strlib_starts_with(op, SLOP_STR("arena-")))))) {
                                    {
                                        __auto_type msg = string_concat(arena, SLOP_STR("Unknown builtin: '"), string_concat(arena, op, SLOP_STR("'")));
                                        env_env_add_error(env, msg, line, col);
                                        return env_env_get_unknown_type(env);
                                    }
                                } else {
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
        __auto_type _mv_121 = ({ __auto_type _lst = params; size_t _idx = (size_t)arg_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_121.has_value) {
            __auto_type param_info = _mv_121.value;
            {
                __auto_type expected_type = param_info.param_type;
                __auto_type _mv_122 = parser_sexpr_list_get(expr, (arg_idx + 1));
                if (_mv_122.has_value) {
                    __auto_type arg_expr = _mv_122.value;
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
                        if (((!(infer_types_equal(expected_type, actual_type))) && (!(string_eq(actual_name, SLOP_STR("Unknown")))) && (!(string_eq(actual_name, SLOP_STR("T")))) && (!(string_eq(expected_name, SLOP_STR("Unknown")))) && (!(string_eq(expected_name, SLOP_STR("T")))) && (!((string_eq(actual_name, SLOP_STR("Option_T")) && strlib_starts_with(expected_name, SLOP_STR("Option_"))))) && (!(string_eq(actual_name, SLOP_STR("Ptr_T")))) && (!(strlib_starts_with(actual_name, SLOP_STR("Ptr_Ptr_")))) && (!((string_eq(actual_name, SLOP_STR("Unit")) && strlib_starts_with(expected_name, SLOP_STR("Ptr_"))))))) {
                            {
                                __auto_type msg = string_concat(arena, SLOP_STR("argument "), string_concat(arena, int_to_string(arena, (arg_idx + 1)), string_concat(arena, SLOP_STR(" to '"), string_concat(arena, fn_name, string_concat(arena, SLOP_STR("': expected "), string_concat(arena, expected_name, string_concat(arena, SLOP_STR(", got "), actual_name)))))));
                                env_env_add_error(env, msg, line, col);
                            }
                        }
                    }
                } else if (!_mv_122.has_value) {
                }
            }
        } else if (!_mv_121.has_value) {
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
                __auto_type _mv_123 = parser_sexpr_list_get(expr, i);
                if (_mv_123.has_value) {
                    __auto_type arg_expr = _mv_123.value;
                    {
                        __auto_type _ = infer_infer_expr(env, arg_expr);
                    }
                } else if (!_mv_123.has_value) {
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
                __auto_type _mv_124 = parser_sexpr_list_get(expr, i);
                if (_mv_124.has_value) {
                    __auto_type body_expr = _mv_124.value;
                    {
                        __auto_type _ = infer_infer_expr(env, body_expr);
                    }
                } else if (!_mv_124.has_value) {
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
            __auto_type _mv_125 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (!_mv_125.has_value) {
                return env_env_get_unit_type(env);
            } else if (_mv_125.has_value) {
                __auto_type obj_expr = _mv_125.value;
                {
                    __auto_type obj_type = infer_infer_expr(env, obj_expr);
                    __auto_type _mv_126 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (!_mv_126.has_value) {
                        return env_env_get_unit_type(env);
                    } else if (_mv_126.has_value) {
                        __auto_type field_expr = _mv_126.value;
                        __auto_type _mv_127 = (*field_expr);
                        switch (_mv_127.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type field_sym = _mv_127.data.sym;
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
            __auto_type _mv_128 = types_resolved_type_get_field_type(obj_type, field_name);
            if (_mv_128.has_value) {
                __auto_type field_type = _mv_128.value;
                return field_type;
            } else if (!_mv_128.has_value) {
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
            __auto_type _mv_129 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_129.has_value) {
                __auto_type clause = _mv_129.value;
                __auto_type _mv_130 = (*clause);
                switch (_mv_130.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type clause_lst = _mv_130.data.lst;
                        {
                            __auto_type clause_items = clause_lst.items;
                            __auto_type clause_len = ((int64_t)((clause_items).len));
                            if ((clause_len > 1)) {
                                __auto_type _mv_131 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)(clause_len - 1); struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_131.has_value) {
                                    __auto_type body = _mv_131.value;
                                    {
                                        __auto_type body_type = infer_infer_expr(env, body);
                                        if (!(has_result)) {
                                            result_type = body_type;
                                            has_result = 1;
                                        } else {
                                            result_type = infer_unify_branch_types(env, result_type, body_type, line, col);
                                        }
                                    }
                                } else if (!_mv_131.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_129.has_value) {
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
            __auto_type _mv_132 = parser_sexpr_list_get(pattern, 0);
            if (_mv_132.has_value) {
                __auto_type variant_expr = _mv_132.value;
                {
                    __auto_type variant_name = parser_sexpr_get_symbol_name(variant_expr);
                    if (!(string_eq(variant_name, SLOP_STR("")))) {
                        if ((parser_sexpr_list_len(pattern) > 1)) {
                            __auto_type _mv_133 = parser_sexpr_list_get(pattern, 1);
                            if (_mv_133.has_value) {
                                __auto_type binding_expr = _mv_133.value;
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
                                                    __auto_type _mv_134 = (*scrutinee_type).inner_type;
                                                    if (_mv_134.has_value) {
                                                        __auto_type inner = _mv_134.value;
                                                        env_env_bind_var(env, binding_name, inner);
                                                    } else if (!_mv_134.has_value) {
                                                        env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                                    }
                                                } else {
                                                    if ((scrutinee_kind == types_ResolvedTypeKind_rk_result)) {
                                                        if (string_eq(variant_name, SLOP_STR("ok"))) {
                                                            __auto_type _mv_135 = (*scrutinee_type).inner_type;
                                                            if (_mv_135.has_value) {
                                                                __auto_type inner = _mv_135.value;
                                                                env_env_bind_var(env, binding_name, inner);
                                                            } else if (!_mv_135.has_value) {
                                                                env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                                            }
                                                        } else if (string_eq(variant_name, SLOP_STR("error"))) {
                                                            __auto_type _mv_136 = (*scrutinee_type).inner_type2;
                                                            if (_mv_136.has_value) {
                                                                __auto_type inner2 = _mv_136.value;
                                                                env_env_bind_var(env, binding_name, inner2);
                                                            } else if (!_mv_136.has_value) {
                                                                env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                                            }
                                                        } else {
                                                            env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                                        }
                                                    } else {
                                                        __auto_type _mv_137 = types_resolved_type_get_variant_payload(scrutinee_type, variant_name);
                                                        if (_mv_137.has_value) {
                                                            __auto_type payload_type = _mv_137.value;
                                                            env_env_bind_var(env, binding_name, payload_type);
                                                        } else if (!_mv_137.has_value) {
                                                            env_env_bind_var(env, binding_name, env_env_get_generic_type(env));
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            } else if (!_mv_133.has_value) {
                            }
                        }
                    }
                }
            } else if (!_mv_132.has_value) {
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
            __auto_type _mv_138 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_138.has_value) {
                __auto_type clause = _mv_138.value;
                __auto_type _mv_139 = (*clause);
                switch (_mv_139.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type clause_lst = _mv_139.data.lst;
                        {
                            __auto_type clause_items = clause_lst.items;
                            __auto_type clause_len = ((int64_t)((clause_items).len));
                            if ((clause_len > 1)) {
                                env_env_push_scope(env);
                                __auto_type _mv_140 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_140.has_value) {
                                    __auto_type pattern = _mv_140.value;
                                    infer_bind_match_pattern(env, scrutinee_type, pattern);
                                } else if (!_mv_140.has_value) {
                                }
                                __auto_type _mv_141 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)(clause_len - 1); struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_141.has_value) {
                                    __auto_type body = _mv_141.value;
                                    {
                                        __auto_type body_type = infer_infer_expr(env, body);
                                        if (!(has_result)) {
                                            result_type = body_type;
                                            has_result = 1;
                                        } else {
                                            result_type = infer_unify_branch_types(env, result_type, body_type, line, col);
                                        }
                                    }
                                } else if (!_mv_141.has_value) {
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
            } else if (!_mv_138.has_value) {
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
    __auto_type _mv_142 = (*fn_form);
    switch (_mv_142.tag) {
        case types_SExpr_lst:
        {
            __auto_type fn_lst = _mv_142.data.lst;
            {
                __auto_type items = fn_lst.items;
                __auto_type len = ((int64_t)((items).len));
                ({ for (int64_t i = 3; i < len; i++) { ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type item = _mv.value; ((parser_is_form(item, SLOP_STR("@spec"))) ? ({ infer_check_spec_return_type(env, item, fn_name, inferred_type, fn_line, fn_col); 0; }) : ({ (void)0; })); } else { ({ (void)0; }); } (void)0; }); } 0; });
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
    __auto_type _mv_143 = (*spec_form);
    switch (_mv_143.tag) {
        case types_SExpr_lst:
        {
            __auto_type spec_lst = _mv_143.data.lst;
            {
                __auto_type spec_items = spec_lst.items;
                __auto_type _mv_144 = ({ __auto_type _lst = spec_items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_144.has_value) {
                    __auto_type spec_body = _mv_144.value;
                    infer_check_spec_body_return(env, spec_body, fn_name, inferred_type, fn_line, fn_col);
                } else if (!_mv_144.has_value) {
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
    __auto_type _mv_145 = (*spec_body);
    switch (_mv_145.tag) {
        case types_SExpr_lst:
        {
            __auto_type body_lst = _mv_145.data.lst;
            {
                __auto_type body_items = body_lst.items;
                __auto_type body_len = ((int64_t)((body_items).len));
                __auto_type _mv_146 = ({ __auto_type _lst = body_items; size_t _idx = (size_t)(body_len - 1); struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_146.has_value) {
                    __auto_type ret_expr = _mv_146.value;
                    infer_check_return_expr(env, ret_expr, fn_name, inferred_type, fn_line, fn_col);
                } else if (!_mv_146.has_value) {
                }
            }
            break;
        }
        default: {
            break;
        }
    }
}

uint8_t infer_is_primitive_type(slop_string name) {
    return (string_eq(name, SLOP_STR("Int")) || (string_eq(name, SLOP_STR("Bool")) || (string_eq(name, SLOP_STR("String")) || (string_eq(name, SLOP_STR("Unit")) || (string_eq(name, SLOP_STR("Arena")) || (string_eq(name, SLOP_STR("I8")) || (string_eq(name, SLOP_STR("I16")) || (string_eq(name, SLOP_STR("I32")) || (string_eq(name, SLOP_STR("I64")) || (string_eq(name, SLOP_STR("U8")) || (string_eq(name, SLOP_STR("U16")) || (string_eq(name, SLOP_STR("U32")) || (string_eq(name, SLOP_STR("U64")) || (string_eq(name, SLOP_STR("F32")) || string_eq(name, SLOP_STR("F64"))))))))))))))));
}

void infer_check_return_expr(env_TypeEnv* env, types_SExpr* ret_expr, slop_string fn_name, types_ResolvedType* inferred_type, int64_t fn_line, int64_t fn_col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((ret_expr != NULL)), "(!= ret-expr nil)");
    __auto_type _mv_147 = (*ret_expr);
    switch (_mv_147.tag) {
        case types_SExpr_sym:
        {
            __auto_type ret_sym = _mv_147.data.sym;
            {
                __auto_type declared_name = ret_sym.name;
                __auto_type inferred_name = (*inferred_type).name;
                if ((!(string_eq(declared_name, inferred_name)) && (infer_is_primitive_type(declared_name) && infer_is_primitive_type(inferred_name)))) {
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
        __auto_type _mv_148 = parser_sexpr_list_get(param_form, 0);
        if (_mv_148.has_value) {
            __auto_type first_expr = _mv_148.value;
            {
                __auto_type first_name = parser_sexpr_get_symbol_name(first_expr);
                if (((string_eq(first_name, SLOP_STR("in"))) || (string_eq(first_name, SLOP_STR("out"))) || (string_eq(first_name, SLOP_STR("mut"))))) {
                    if ((parser_sexpr_list_len(param_form) >= 3)) {
                        __auto_type _mv_149 = parser_sexpr_list_get(param_form, 1);
                        if (_mv_149.has_value) {
                            __auto_type name_expr = _mv_149.value;
                            {
                                __auto_type param_name = parser_sexpr_get_symbol_name(name_expr);
                                if (!(string_eq(param_name, SLOP_STR("")))) {
                                    {
                                        __auto_type param_type = infer_get_param_type_from_form(env, param_form);
                                        env_env_bind_var(env, param_name, param_type);
                                    }
                                }
                            }
                        } else if (!_mv_149.has_value) {
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
        } else if (!_mv_148.has_value) {
        }
    }
}

types_ResolvedType* infer_get_param_type_from_form(env_TypeEnv* env, types_SExpr* param_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((param_form != NULL)), "(!= param-form nil)");
    {
        __auto_type type_pos = ({ __auto_type _mv = parser_sexpr_list_get(param_form, 0); _mv.has_value ? ({ __auto_type first_expr = _mv.value; ({ __auto_type first_name = parser_sexpr_get_symbol_name(first_expr); ((((string_eq(first_name, SLOP_STR("in"))) || (string_eq(first_name, SLOP_STR("out"))) || (string_eq(first_name, SLOP_STR("mut"))))) ? 2 : 1); }); }) : (1); });
        __auto_type _mv_150 = parser_sexpr_list_get(param_form, type_pos);
        if (_mv_150.has_value) {
            __auto_type type_expr = _mv_150.value;
            {
                __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                if (string_eq(type_name, SLOP_STR(""))) {
                    if (parser_sexpr_is_list(type_expr)) {
                        return infer_resolve_complex_type_expr(env, type_expr);
                    } else {
                        return env_env_get_unknown_type(env);
                    }
                } else {
                    __auto_type _mv_151 = env_env_lookup_type(env, type_name);
                    if (_mv_151.has_value) {
                        __auto_type t = _mv_151.value;
                        return t;
                    } else if (!_mv_151.has_value) {
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
        } else if (!_mv_150.has_value) {
            return env_env_get_unknown_type(env);
        }
    }
}

types_ResolvedType* infer_resolve_complex_type_expr(env_TypeEnv* env, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_152 = parser_sexpr_list_get(type_expr, 0);
    if (_mv_152.has_value) {
        __auto_type head_expr = _mv_152.value;
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
                        __auto_type _mv_153 = parser_sexpr_list_get(type_expr, 2);
                        if (_mv_153.has_value) {
                            __auto_type val_expr = _mv_153.value;
                            {
                                __auto_type val_type = infer_resolve_simple_type(env, parser_sexpr_get_symbol_name(val_expr));
                                if ((val_type != NULL)) {
                                    types_resolved_type_set_inner2(map_type, val_type);
                                }
                            }
                        } else if (!_mv_153.has_value) {
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
                    return env_env_make_ptr_type(env, inner_type);
                }
            } else if (string_eq(head_name, SLOP_STR("Chan"))) {
                {
                    __auto_type inner_type = infer_resolve_ptr_inner_type(env, type_expr);
                    return env_env_make_ptr_type(env, inner_type);
                }
            } else {
                __auto_type _mv_154 = env_env_lookup_type(env, head_name);
                if (_mv_154.has_value) {
                    __auto_type t = _mv_154.value;
                    return t;
                } else if (!_mv_154.has_value) {
                    return env_env_get_unknown_type(env);
                }
            }
        }
    } else if (!_mv_152.has_value) {
        return env_env_get_unknown_type(env);
    }
}

types_ResolvedType* infer_resolve_option_inner_type(env_TypeEnv* env, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    if ((parser_sexpr_list_len(type_expr) < 2)) {
        return env_env_get_unknown_type(env);
    } else {
        __auto_type _mv_155 = parser_sexpr_list_get(type_expr, 1);
        if (_mv_155.has_value) {
            __auto_type inner_expr = _mv_155.value;
            {
                __auto_type inner_name = parser_sexpr_get_symbol_name(inner_expr);
                if (string_eq(inner_name, SLOP_STR(""))) {
                    return env_env_get_unknown_type(env);
                } else {
                    return infer_resolve_simple_type(env, inner_name);
                }
            }
        } else if (!_mv_155.has_value) {
            return env_env_get_unknown_type(env);
        }
    }
}

types_ResolvedType* infer_resolve_ptr_inner_type(env_TypeEnv* env, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    if ((parser_sexpr_list_len(type_expr) < 2)) {
        return env_env_get_unit_type(env);
    } else {
        __auto_type _mv_156 = parser_sexpr_list_get(type_expr, 1);
        if (_mv_156.has_value) {
            __auto_type inner_expr = _mv_156.value;
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
        } else if (!_mv_156.has_value) {
            return env_env_get_unit_type(env);
        }
    }
}

types_ResolvedType* infer_resolve_simple_type(env_TypeEnv* env, slop_string type_name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_157 = env_env_lookup_type(env, type_name);
    if (_mv_157.has_value) {
        __auto_type t = _mv_157.value;
        return t;
    } else if (!_mv_157.has_value) {
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
            } else {
                {
                    __auto_type arena = env_env_arena(env);
                    __auto_type msg = string_concat(arena, SLOP_STR("Unknown type in parameter: "), type_name);
                    env_env_add_warning(env, msg, 0, 0);
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
        __auto_type _mv_158 = parser_sexpr_list_get(binding_form, 0);
        if (_mv_158.has_value) {
            __auto_type first_expr = _mv_158.value;
            {
                __auto_type first_name = parser_sexpr_get_symbol_name(first_expr);
                if (string_eq(first_name, SLOP_STR("mut"))) {
                    if ((parser_sexpr_list_len(binding_form) >= 3)) {
                        __auto_type _mv_159 = parser_sexpr_list_get(binding_form, 1);
                        if (_mv_159.has_value) {
                            __auto_type name_expr = _mv_159.value;
                            {
                                __auto_type var_name = parser_sexpr_get_symbol_name(name_expr);
                                if (!(string_eq(var_name, SLOP_STR("")))) {
                                    __auto_type _mv_160 = parser_sexpr_list_get(binding_form, (parser_sexpr_list_len(binding_form) - 1));
                                    if (_mv_160.has_value) {
                                        __auto_type val_expr = _mv_160.value;
                                        {
                                            __auto_type val_type = infer_infer_expr(env, val_expr);
                                            env_env_bind_var(env, var_name, val_type);
                                        }
                                    } else if (!_mv_160.has_value) {
                                    }
                                }
                            }
                        } else if (!_mv_159.has_value) {
                        }
                    }
                } else {
                    if (!(string_eq(first_name, SLOP_STR("")))) {
                        {
                            __auto_type binding_len = parser_sexpr_list_len(binding_form);
                            if ((binding_len == 3)) {
                                __auto_type _mv_161 = parser_sexpr_list_get(binding_form, 2);
                                if (_mv_161.has_value) {
                                    __auto_type val_expr = _mv_161.value;
                                    {
                                        __auto_type val_type = infer_infer_expr(env, val_expr);
                                        env_env_bind_var(env, first_name, val_type);
                                    }
                                } else if (!_mv_161.has_value) {
                                }
                            } else {
                                __auto_type _mv_162 = parser_sexpr_list_get(binding_form, 1);
                                if (_mv_162.has_value) {
                                    __auto_type val_expr = _mv_162.value;
                                    {
                                        __auto_type val_type = infer_infer_expr(env, val_expr);
                                        env_env_bind_var(env, first_name, val_type);
                                    }
                                } else if (!_mv_162.has_value) {
                                }
                            }
                        }
                    }
                }
            }
        } else if (!_mv_158.has_value) {
        }
    }
}

types_ResolvedType* infer_infer_let_expr(env_TypeEnv* env, types_SExpr* expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    env_env_push_scope(env);
    if (parser_sexpr_is_list(expr)) {
        __auto_type _mv_163 = parser_sexpr_list_get(expr, 1);
        if (_mv_163.has_value) {
            __auto_type bindings_expr = _mv_163.value;
            if (parser_sexpr_is_list(bindings_expr)) {
                {
                    __auto_type num_bindings = parser_sexpr_list_len(bindings_expr);
                    ({ for (int64_t i = 0; i < num_bindings; i++) { ({ __auto_type _mv = parser_sexpr_list_get(bindings_expr, i); if (_mv.has_value) { __auto_type binding = _mv.value; infer_bind_let_binding(env, binding); } else { ({ (void)0; }); } (void)0; }); } 0; });
                }
            }
        } else if (!_mv_163.has_value) {
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
    env_env_push_scope(env);
    env_env_bind_var(env, SLOP_STR("arena"), env_env_get_arena_type(env));
    {
        __auto_type len = parser_sexpr_list_len(expr);
        types_ResolvedType* result_type = env_env_get_unit_type(env);
        for (int64_t i = 2; i < len; i++) {
            __auto_type _mv_164 = parser_sexpr_list_get(expr, i);
            if (_mv_164.has_value) {
                __auto_type body_expr = _mv_164.value;
                result_type = infer_infer_expr(env, body_expr);
            } else if (!_mv_164.has_value) {
            }
        }
        env_env_pop_scope(env);
        return result_type;
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
            __auto_type _mv_165 = parser_sexpr_list_get(fn_form, 1);
            if (_mv_165.has_value) {
                __auto_type name_expr = _mv_165.value;
                {
                    __auto_type name = parser_sexpr_get_symbol_name(name_expr);
                    if (string_eq(name, SLOP_STR(""))) {
                        return SLOP_STR("unknown");
                    } else {
                        return name;
                    }
                }
            } else if (!_mv_165.has_value) {
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
        __auto_type _mv_166 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_166.has_value) {
            __auto_type type_expr = _mv_166.value;
            {
                __auto_type type_name = parser_sexpr_get_symbol_name(type_expr);
                if (string_eq(type_name, SLOP_STR(""))) {
                    return env_env_get_unit_type(env);
                } else {
                    __auto_type _mv_167 = env_env_lookup_type(env, type_name);
                    if (_mv_167.has_value) {
                        __auto_type t = _mv_167.value;
                        return t;
                    } else if (!_mv_167.has_value) {
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
        } else if (!_mv_166.has_value) {
            return env_env_get_unit_type(env);
        }
    }
}

slop_string infer_get_hole_prompt(slop_list_types_SExpr_ptr items, int64_t len) {
    if ((len < 3)) {
        return SLOP_STR("(no description)");
    } else {
        __auto_type _mv_168 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_168.has_value) {
            __auto_type prompt_expr = _mv_168.value;
            __auto_type _mv_169 = (*prompt_expr);
            switch (_mv_169.tag) {
                case types_SExpr_str:
                {
                    __auto_type str = _mv_169.data.str;
                    return str.value;
                }
                default: {
                    return SLOP_STR("(no description)");
                }
            }
        } else if (!_mv_168.has_value) {
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
    __auto_type _mv_170 = ({ __auto_type _lst = items; size_t _idx = (size_t)idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
    if (_mv_170.has_value) {
        __auto_type item = _mv_170.value;
        __auto_type _mv_171 = (*item);
        switch (_mv_171.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_171.data.sym;
                return string_eq(sym.name, SLOP_STR(":c-name"));
            }
            case types_SExpr_str:
            {
                __auto_type _ = _mv_171.data.str;
                if ((idx > 0)) {
                    __auto_type _mv_172 = ({ __auto_type _lst = items; size_t _idx = (size_t)(idx - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_172.has_value) {
                        __auto_type prev = _mv_172.value;
                        __auto_type _mv_173 = (*prev);
                        switch (_mv_173.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_173.data.sym;
                                return string_eq(sym.name, SLOP_STR(":c-name"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_172.has_value) {
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
    } else if (!_mv_170.has_value) {
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
                    __auto_type _mv_174 = parser_sexpr_list_get(fn_form, 2);
                    if (_mv_174.has_value) {
                        __auto_type params_expr = _mv_174.value;
                        if (parser_sexpr_is_list(params_expr)) {
                            {
                                __auto_type num_params = parser_sexpr_list_len(params_expr);
                                ({ for (int64_t k = 0; k < num_params; k++) { ({ __auto_type _mv = parser_sexpr_list_get(params_expr, k); if (_mv.has_value) { __auto_type param_form = _mv.value; infer_bind_param_from_form(env, param_form); } else { ({ (void)0; }); } (void)0; }); } 0; });
                            }
                        }
                    } else if (!_mv_174.has_value) {
                    }
                }
            }
        }
        {
            __auto_type result_type = ({ __auto_type _mv = (*fn_form); types_ResolvedType* _mr = {0}; switch (_mv.tag) { case types_SExpr_lst: { __auto_type fn_lst = _mv.data.lst; _mr = ({ __auto_type items = fn_lst.items; __auto_type item_len = ((int64_t)((items).len)); __auto_type last_body_idx = infer_find_last_body_idx(items); ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)last_body_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type body = _mv.value; infer_infer_expr(env, body); }) : (env_env_get_unit_type(env)); }); }); break; } default: { _mr = env_env_get_unit_type(env); break; }  } _mr; });
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
                __auto_type _mv_175 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_175.has_value) {
                    __auto_type pattern_case = _mv_175.value;
                    __auto_type _mv_176 = (*pattern_case);
                    switch (_mv_176.tag) {
                        case types_SExpr_lst:
                        {
                            __auto_type pattern_list = _mv_176.data.lst;
                            if ((((int64_t)((pattern_list.items).len)) > 0)) {
                                __auto_type _mv_177 = ({ __auto_type _lst = pattern_list.items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_177.has_value) {
                                    __auto_type pattern_expr = _mv_177.value;
                                    __auto_type _mv_178 = (*pattern_expr);
                                    switch (_mv_178.tag) {
                                        case types_SExpr_lst:
                                        {
                                            __auto_type variant_list = _mv_178.data.lst;
                                            {
                                                __auto_type variant_items = variant_list.items;
                                                if ((((int64_t)((variant_items).len)) > 0)) {
                                                    __auto_type _mv_179 = ({ __auto_type _lst = variant_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_179.has_value) {
                                                        __auto_type variant_name_expr = _mv_179.value;
                                                        __auto_type _mv_180 = (*variant_name_expr);
                                                        switch (_mv_180.tag) {
                                                            case types_SExpr_sym:
                                                            {
                                                                __auto_type variant_sym = _mv_180.data.sym;
                                                                {
                                                                    __auto_type variant_name = variant_sym.name;
                                                                    __auto_type _mv_181 = types_resolved_type_get_variant_payload(scrutinee_type, variant_name);
                                                                    if (_mv_181.has_value) {
                                                                        __auto_type payload_type = _mv_181.value;
                                                                        if ((((int64_t)((variant_items).len)) > 1)) {
                                                                            __auto_type _mv_182 = ({ __auto_type _lst = variant_items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                            if (_mv_182.has_value) {
                                                                                __auto_type binding_expr = _mv_182.value;
                                                                                __auto_type _mv_183 = (*binding_expr);
                                                                                switch (_mv_183.tag) {
                                                                                    case types_SExpr_sym:
                                                                                    {
                                                                                        __auto_type binding_sym = _mv_183.data.sym;
                                                                                        env_env_bind_var(env, binding_sym.name, payload_type);
                                                                                        break;
                                                                                    }
                                                                                    default: {
                                                                                        break;
                                                                                    }
                                                                                }
                                                                            } else if (!_mv_182.has_value) {
                                                                            }
                                                                        }
                                                                    } else if (!_mv_181.has_value) {
                                                                        __auto_type _mv_184 = types_resolved_type_get_variant_index(scrutinee_type, variant_name);
                                                                        if (_mv_184.has_value) {
                                                                            __auto_type _ = _mv_184.value;
                                                                        } else if (!_mv_184.has_value) {
                                                                        }
                                                                    }
                                                                }
                                                                break;
                                                            }
                                                            default: {
                                                                break;
                                                            }
                                                        }
                                                    } else if (!_mv_179.has_value) {
                                                    }
                                                }
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_177.has_value) {
                                }
                            }
                            break;
                        }
                        default: {
                            break;
                        }
                    }
                } else if (!_mv_175.has_value) {
                }
            }
        }
    }
}

