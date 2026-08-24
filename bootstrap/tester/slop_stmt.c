#include "../runtime/slop_runtime.h"
#include "slop_stmt.h"

slop_string stmt_sexpr_to_type_string(slop_arena* arena, types_SExpr* expr);
slop_option_string stmt_get_arena_alloc_ptr_type(context_TranspileContext* ctx, types_SExpr* expr);
slop_option_string stmt_extract_sizeof_type_opt(context_TranspileContext* ctx, types_SExpr* expr);
uint8_t stmt_is_stmt_form(types_SExpr* expr);
void stmt_transpile_let(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return);
void stmt_transpile_bindings(context_TranspileContext* ctx, slop_list_types_SExpr_ptr bindings);
void stmt_transpile_single_binding(context_TranspileContext* ctx, types_SExpr* binding);
uint8_t stmt_binding_has_mut(slop_list_types_SExpr_ptr items);
uint8_t stmt_is_simple_primitive_c_type(slop_string t);
slop_option_types_SExpr_ptr stmt_get_some_value(types_SExpr* expr);
uint8_t stmt_is_none_form(types_SExpr* expr);
void stmt_transpile_if(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return);
void stmt_transpile_when(context_TranspileContext* ctx, types_SExpr* expr);
void stmt_transpile_while(context_TranspileContext* ctx, types_SExpr* expr);
void stmt_transpile_set(context_TranspileContext* ctx, types_SExpr* expr);
slop_option_string stmt_get_var_c_type(context_TranspileContext* ctx, types_SExpr* expr);
uint8_t stmt_is_pointer_target(context_TranspileContext* ctx, types_SExpr* expr);
void stmt_transpile_field_set(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void stmt_transpile_typed_field_set(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
uint8_t stmt_is_deref_expr(types_SExpr* expr);
types_SExpr* stmt_get_deref_inner(types_SExpr* expr);
slop_string stmt_get_symbol_name(slop_arena* arena, types_SExpr* expr);
void stmt_transpile_do(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return);
void stmt_transpile_with_arena(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return);
void stmt_transpile_cond(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return);
void stmt_transpile_cond_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start, uint8_t is_return);
void stmt_transpile_for(context_TranspileContext* ctx, types_SExpr* expr);
void stmt_transpile_for_each_set(context_TranspileContext* ctx, slop_string var_name, types_SExprSymbol var_sym, slop_string coll_c, slop_string resolved_type, slop_list_types_SExpr_ptr items, int64_t len);
void stmt_transpile_for_each_map_keys(context_TranspileContext* ctx, slop_string var_name, types_SExprSymbol var_sym, slop_string coll_c, slop_string resolved_type, slop_list_types_SExpr_ptr items, int64_t len);
void stmt_transpile_for_each_map_kv(context_TranspileContext* ctx, slop_list_types_SExpr_ptr binding_items, slop_list_types_SExpr_ptr items, int64_t len);
void stmt_transpile_for_each(context_TranspileContext* ctx, types_SExpr* expr);
void stmt_transpile_stmt(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return);
void stmt_emit_typed_return_expr(context_TranspileContext* ctx, types_SExpr* expr);
void stmt_emit_return_with_typed_none(context_TranspileContext* ctx, slop_string code);

slop_string stmt_sexpr_to_type_string(slop_arena* arena, types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_809 = (*expr);
    switch (_mv_809.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_809.data.sym;
            return sym.name;
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_809.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type result = SLOP_STR("(");
                __auto_type i = 0;
                while (i < len) {
                    __auto_type _mv_810 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_810.has_value) {
                        __auto_type item_expr = _mv_810.value;
                        {
                            __auto_type item_str = ctype_sexpr_to_type_string(arena, item_expr);
                            if (i > 0) {
                                result = string_concat(arena, result, string_concat(arena, SLOP_STR(" "), item_str));
                            } else {
                                result = string_concat(arena, result, item_str);
                            }
                        }
                    } else if (!_mv_810.has_value) {
                    }
                    i = (i + 1);
                }
                return string_concat(arena, result, SLOP_STR(")"));
            }
        }
        default: {
            return SLOP_STR("");
        }
    }
}

slop_option_string stmt_get_arena_alloc_ptr_type(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_811 = (*expr);
        switch (_mv_811.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_811.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) >= 3) {
                        __auto_type _mv_812 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_812.has_value) {
                            __auto_type head_ptr = _mv_812.value;
                            __auto_type _mv_813 = (*head_ptr);
                            switch (_mv_813.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_813.data.sym;
                                    {
                                        __auto_type op = head_sym.name;
                                        if (string_eq(op, SLOP_STR("arena-alloc"))) {
                                            __auto_type _mv_814 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_814.has_value) {
                                                __auto_type size_expr = _mv_814.value;
                                                return stmt_extract_sizeof_type_opt(ctx, size_expr);
                                            } else if (!_mv_814.has_value) {
                                                return (slop_option_string){.has_value = false};
                                            }
                                            SLOP_UNREACHABLE();
                                        } else if (string_eq(op, SLOP_STR("cast")) && (((int64_t)((items).len)) >= 3)) {
                                            __auto_type _mv_815 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_815.has_value) {
                                                __auto_type inner_expr = _mv_815.value;
                                                return stmt_get_arena_alloc_ptr_type(ctx, inner_expr);
                                            } else if (!_mv_815.has_value) {
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
                        } else if (!_mv_812.has_value) {
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

slop_option_string stmt_extract_sizeof_type_opt(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_816 = (*expr);
        switch (_mv_816.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_816.data.sym;
                {
                    __auto_type type_name = sym.name;
                    __auto_type _mv_817 = context_ctx_lookup_type(ctx, type_name);
                    if (_mv_817.has_value) {
                        __auto_type entry = _mv_817.value;
                        return (slop_option_string){.has_value = 1, .value = context_ctx_str(ctx, entry.c_name, SLOP_STR("*"))};
                    } else if (!_mv_817.has_value) {
                        return (slop_option_string){.has_value = false};
                    }
                    SLOP_UNREACHABLE();
                }
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_816.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) >= 2) {
                        __auto_type _mv_818 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_818.has_value) {
                            __auto_type head_ptr = _mv_818.value;
                            __auto_type _mv_819 = (*head_ptr);
                            switch (_mv_819.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_819.data.sym;
                                    if (string_eq(head_sym.name, SLOP_STR("sizeof"))) {
                                        __auto_type _mv_820 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_820.has_value) {
                                            __auto_type type_expr = _mv_820.value;
                                            {
                                                __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                return (slop_option_string){.has_value = 1, .value = context_ctx_str(ctx, c_type, SLOP_STR("*"))};
                                            }
                                        } else if (!_mv_820.has_value) {
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
                        } else if (!_mv_818.has_value) {
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

uint8_t stmt_is_stmt_form(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_821 = (*expr);
    switch (_mv_821.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_821.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_822 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_822.has_value) {
                        __auto_type head_expr = _mv_822.value;
                        __auto_type _mv_823 = (*head_expr);
                        switch (_mv_823.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_823.data.sym;
                                {
                                    __auto_type name = sym.name;
                                    return ((string_eq(name, SLOP_STR("let"))) || (string_eq(name, SLOP_STR("let*"))) || (string_eq(name, SLOP_STR("if"))) || (string_eq(name, SLOP_STR("when"))) || (string_eq(name, SLOP_STR("while"))) || (string_eq(name, SLOP_STR("for"))) || (string_eq(name, SLOP_STR("for-each"))) || (string_eq(name, SLOP_STR("set!"))) || (string_eq(name, SLOP_STR("do"))) || (string_eq(name, SLOP_STR("match"))) || (string_eq(name, SLOP_STR("cond"))) || (string_eq(name, SLOP_STR("with-arena"))));
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_822.has_value) {
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

void stmt_transpile_let(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_824 = (*expr);
        switch (_mv_824.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_824.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len < 2) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid let: missing bindings"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    } else {
                        context_ctx_emit(ctx, SLOP_STR("{"));
                        context_ctx_indent(ctx);
                        context_ctx_push_scope(ctx);
                        __auto_type _mv_825 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_825.has_value) {
                            __auto_type bindings_expr = _mv_825.value;
                            __auto_type _mv_826 = (*bindings_expr);
                            switch (_mv_826.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type bindings_lst = _mv_826.data.lst;
                                    stmt_transpile_bindings(ctx, bindings_lst.items);
                                    break;
                                }
                                default: {
                                    context_ctx_add_error_at(ctx, SLOP_STR("invalid bindings"), context_ctx_sexpr_line(bindings_expr), context_ctx_sexpr_col(bindings_expr));
                                    break;
                                }
                            }
                        } else if (!_mv_825.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing bindings"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                        }
                        {
                            __auto_type i = 2;
                            while (i < len) {
                                __auto_type _mv_827 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_827.has_value) {
                                    __auto_type body_expr = _mv_827.value;
                                    {
                                        __auto_type is_last = (i == (len - 1));
                                        stmt_transpile_stmt(ctx, body_expr, (is_return && is_last));
                                    }
                                } else if (!_mv_827.has_value) {
                                }
                                i = (i + 1);
                            }
                        }
                        context_ctx_pop_scope(ctx);
                        context_ctx_dedent(ctx);
                        context_ctx_emit(ctx, SLOP_STR("}"));
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid let"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                break;
            }
        }
    }
}

void stmt_transpile_bindings(context_TranspileContext* ctx, slop_list_types_SExpr_ptr bindings) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((bindings).len));
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_828 = ({ __auto_type _lst = bindings; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_828.has_value) {
                __auto_type binding_expr = _mv_828.value;
                stmt_transpile_single_binding(ctx, binding_expr);
            } else if (!_mv_828.has_value) {
            }
            i = (i + 1);
        }
    }
}

void stmt_transpile_single_binding(context_TranspileContext* ctx, types_SExpr* binding) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((binding != NULL)), "(!= binding nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_829 = (*binding);
        switch (_mv_829.tag) {
            case types_SExpr_lst:
            {
                __auto_type binding_lst = _mv_829.data.lst;
                {
                    __auto_type items = binding_lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    {
                        __auto_type has_mut = stmt_binding_has_mut(items);
                        __auto_type start_idx = ((stmt_binding_has_mut(items)) ? 1 : 0);
                        if ((len - start_idx) < 2) {
                            context_ctx_add_error_at(ctx, SLOP_STR("invalid binding: need name and value"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                        } else {
                            __auto_type _mv_830 = ({ __auto_type _lst = items; size_t _idx = (size_t)start_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_830.has_value) {
                                __auto_type name_expr = _mv_830.value;
                                __auto_type _mv_831 = (*name_expr);
                                switch (_mv_831.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type name_sym = _mv_831.data.sym;
                                        {
                                            __auto_type raw_name = name_sym.name;
                                            __auto_type var_name = ctype_to_c_name(arena, raw_name);
                                            if ((len - start_idx) >= 3) {
                                                __auto_type _mv_832 = ({ __auto_type _lst = items; size_t _idx = (size_t)(start_idx + 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_832.has_value) {
                                                    __auto_type type_expr = _mv_832.value;
                                                    __auto_type _mv_833 = ({ __auto_type _lst = items; size_t _idx = (size_t)(start_idx + 2); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_833.has_value) {
                                                        __auto_type init_expr = _mv_833.value;
                                                        {
                                                            __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                            {
                                                                __auto_type final_init = ((context_ctx_is_option_c_type(ctx, c_type)) ? ({ __auto_type some_val = stmt_get_some_value(init_expr); ({ __auto_type _mv = some_val; _mv.has_value ? ({ __auto_type val_expr = _mv.value; ({ __auto_type val_c = expr_transpile_expr(ctx, val_expr); context_ctx_str5(ctx, SLOP_STR("("), c_type, SLOP_STR("){.has_value = 1, .value = "), val_c, SLOP_STR("}")); }); }) : (((stmt_is_none_form(init_expr)) ? context_ctx_str3(ctx, SLOP_STR("("), c_type, SLOP_STR("){.has_value = false}")) : expr_transpile_expr(ctx, init_expr))); }); }) : expr_transpile_expr(ctx, init_expr));
                                                                context_ctx_emit(ctx, context_ctx_str5(ctx, c_type, SLOP_STR(" "), var_name, SLOP_STR(" = "), context_ctx_str(ctx, final_init, SLOP_STR(";"))));
                                                                {
                                                                    __auto_type slop_type_str = stmt_sexpr_to_type_string(arena, type_expr);
                                                                    context_ctx_bind_var(ctx, (context_VarEntry){raw_name, var_name, c_type, slop_type_str, 0, has_mut, 0, SLOP_STR(""), SLOP_STR("")});
                                                                }
                                                            }
                                                        }
                                                    } else if (!_mv_833.has_value) {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("missing init"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                                                    }
                                                } else if (!_mv_832.has_value) {
                                                    context_ctx_add_error_at(ctx, SLOP_STR("missing type"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                                                }
                                            } else {
                                                __auto_type _mv_834 = ({ __auto_type _lst = items; size_t _idx = (size_t)(start_idx + 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_834.has_value) {
                                                    __auto_type init_expr = _mv_834.value;
                                                    {
                                                        __auto_type init_c = expr_transpile_expr(ctx, init_expr);
                                                        __auto_type inferred_slop_type = expr_infer_expr_slop_type(ctx, init_expr);
                                                        __auto_type ptr_type_opt = stmt_get_arena_alloc_ptr_type(ctx, init_expr);
                                                        __auto_type _mv_835 = ptr_type_opt;
                                                        if (_mv_835.has_value) {
                                                            __auto_type ptr_type = _mv_835.value;
                                                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("__auto_type "), var_name, SLOP_STR(" = "), init_c, SLOP_STR(";")));
                                                            context_ctx_bind_var(ctx, (context_VarEntry){raw_name, var_name, ptr_type, inferred_slop_type, 1, has_mut, 0, SLOP_STR(""), SLOP_STR("")});
                                                        } else if (!_mv_835.has_value) {
                                                            {
                                                                __auto_type inferred_type = expr_infer_expr_c_type(ctx, init_expr);
                                                                __auto_type lambda_info = context_ctx_get_last_lambda_info(ctx);
                                                                __auto_type is_init_lambda = ({ __auto_type _mv = (*init_expr); uint8_t _mr = {0}; switch (_mv.tag) { case types_SExpr_lst: { __auto_type init_lst = _mv.data.lst; _mr = ({ __auto_type _mv = ({ __auto_type _lst = init_lst.items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type head = _mv.value; string_eq(parser_sexpr_get_symbol_name(head), SLOP_STR("fn")); }) : (0); }); break; } default: { _mr = 0; break; }  } _mr; });
                                                                __auto_type use_explicit_type = (has_mut && stmt_is_simple_primitive_c_type(inferred_type));
                                                                __auto_type decl_type = ((use_explicit_type) ? context_ctx_str(ctx, inferred_type, SLOP_STR(" ")) : SLOP_STR("__auto_type "));
                                                                context_ctx_emit(ctx, context_ctx_str5(ctx, decl_type, var_name, SLOP_STR(" = "), init_c, SLOP_STR(";")));
                                                                if (lambda_info.is_closure && is_init_lambda) {
                                                                    context_ctx_bind_var(ctx, (context_VarEntry){raw_name, var_name, SLOP_STR("slop_closure_t"), inferred_slop_type, 0, has_mut, 1, lambda_info.env_type, lambda_info.lambda_name});
                                                                    context_ctx_clear_last_lambda_info(ctx);
                                                                } else {
                                                                    context_ctx_bind_var(ctx, (context_VarEntry){raw_name, var_name, inferred_type, inferred_slop_type, strlib_ends_with(inferred_type, SLOP_STR("*")), has_mut, 0, SLOP_STR(""), SLOP_STR("")});
                                                                }
                                                            }
                                                        }
                                                    }
                                                } else if (!_mv_834.has_value) {
                                                    context_ctx_add_error_at(ctx, SLOP_STR("missing init"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                                                }
                                            }
                                        }
                                        break;
                                    }
                                    default: {
                                        context_ctx_add_error_at(ctx, SLOP_STR("binding name must be symbol"), context_ctx_sexpr_line(name_expr), context_ctx_sexpr_col(name_expr));
                                        break;
                                    }
                                }
                            } else if (!_mv_830.has_value) {
                                context_ctx_add_error_at(ctx, SLOP_STR("missing binding name"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                            }
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("binding must be a list"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                break;
            }
        }
    }
}

uint8_t stmt_binding_has_mut(slop_list_types_SExpr_ptr items) {
    if (((int64_t)((items).len)) < 1) {
        return 0;
    } else {
        __auto_type _mv_836 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_836.has_value) {
            __auto_type first = _mv_836.value;
            __auto_type _mv_837 = (*first);
            switch (_mv_837.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_837.data.sym;
                    return string_eq(sym.name, SLOP_STR("mut"));
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_836.has_value) {
            return 0;
        }
        SLOP_UNREACHABLE();
    }
}

uint8_t stmt_is_simple_primitive_c_type(slop_string t) {
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
    } else if (string_eq(t, SLOP_STR("size_t"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("bool"))) {
        return 1;
    } else if (string_eq(t, SLOP_STR("int"))) {
        return 1;
    } else {
        return 0;
    }
}

slop_option_types_SExpr_ptr stmt_get_some_value(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        slop_option_types_SExpr_ptr result = (slop_option_types_SExpr_ptr){.has_value = false};
        __auto_type _mv_838 = (*expr);
        switch (_mv_838.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_838.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) >= 2) {
                        __auto_type _mv_839 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_839.has_value) {
                            __auto_type head_expr = _mv_839.value;
                            __auto_type _mv_840 = (*head_expr);
                            switch (_mv_840.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_840.data.sym;
                                    if (string_eq(sym.name, SLOP_STR("some"))) {
                                        __auto_type _mv_841 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_841.has_value) {
                                            __auto_type val = _mv_841.value;
                                            result = (slop_option_types_SExpr_ptr){.has_value = 1, .value = val};
                                        } else if (!_mv_841.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_839.has_value) {
                        }
                    }
                }
                break;
            }
            default: {
                break;
            }
        }
        return result;
    }
}

uint8_t stmt_is_none_form(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_842 = (*expr);
    switch (_mv_842.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_842.data.sym;
            return string_eq(sym.name, SLOP_STR("none"));
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_842.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) == 1) {
                    __auto_type _mv_843 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_843.has_value) {
                        __auto_type head = _mv_843.value;
                        __auto_type _mv_844 = (*head);
                        switch (_mv_844.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_844.data.sym;
                                return string_eq(sym.name, SLOP_STR("none"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_843.has_value) {
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

void stmt_transpile_if(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_845 = (*expr);
    switch (_mv_845.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_845.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if (len < 3) {
                    context_ctx_add_error_at(ctx, SLOP_STR("invalid if: need condition and then-branch"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                } else {
                    __auto_type _mv_846 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_846.has_value) {
                        __auto_type cond_expr = _mv_846.value;
                        {
                            __auto_type cond_c = context_ctx_strip_cond_parens(ctx, expr_transpile_expr(ctx, cond_expr));
                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), cond_c, SLOP_STR(") {")));
                            context_ctx_indent(ctx);
                            __auto_type _mv_847 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_847.has_value) {
                                __auto_type then_expr = _mv_847.value;
                                stmt_transpile_stmt(ctx, then_expr, is_return);
                            } else if (!_mv_847.has_value) {
                            }
                            context_ctx_dedent(ctx);
                            if (len >= 4) {
                                context_ctx_emit(ctx, SLOP_STR("} else {"));
                                context_ctx_indent(ctx);
                                __auto_type _mv_848 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_848.has_value) {
                                    __auto_type else_expr = _mv_848.value;
                                    stmt_transpile_stmt(ctx, else_expr, is_return);
                                } else if (!_mv_848.has_value) {
                                }
                                context_ctx_dedent(ctx);
                                context_ctx_emit(ctx, SLOP_STR("}"));
                            } else {
                                context_ctx_emit(ctx, SLOP_STR("}"));
                            }
                        }
                    } else if (!_mv_846.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing if condition"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    }
                }
            }
            break;
        }
        default: {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid if"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
            break;
        }
    }
}

void stmt_transpile_when(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_849 = (*expr);
    switch (_mv_849.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_849.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if (len < 3) {
                    context_ctx_add_error_at(ctx, SLOP_STR("invalid when: need condition and body"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                } else {
                    __auto_type _mv_850 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_850.has_value) {
                        __auto_type cond_expr = _mv_850.value;
                        {
                            __auto_type cond_c = context_ctx_strip_cond_parens(ctx, expr_transpile_expr(ctx, cond_expr));
                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), cond_c, SLOP_STR(") {")));
                            context_ctx_indent(ctx);
                            {
                                __auto_type i = 2;
                                while (i < len) {
                                    __auto_type _mv_851 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_851.has_value) {
                                        __auto_type body_expr = _mv_851.value;
                                        stmt_transpile_stmt(ctx, body_expr, 0);
                                    } else if (!_mv_851.has_value) {
                                    }
                                    i = (i + 1);
                                }
                            }
                            context_ctx_dedent(ctx);
                            context_ctx_emit(ctx, SLOP_STR("}"));
                        }
                    } else if (!_mv_850.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing when condition"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    }
                }
            }
            break;
        }
        default: {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid when"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
            break;
        }
    }
}

void stmt_transpile_while(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_852 = (*expr);
    switch (_mv_852.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_852.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if (len < 3) {
                    context_ctx_add_error_at(ctx, SLOP_STR("invalid while: need condition and body"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                } else {
                    __auto_type _mv_853 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_853.has_value) {
                        __auto_type cond_expr = _mv_853.value;
                        {
                            __auto_type cond_c = context_ctx_strip_cond_parens(ctx, expr_transpile_expr(ctx, cond_expr));
                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("while ("), cond_c, SLOP_STR(") {")));
                            context_ctx_indent(ctx);
                            {
                                __auto_type i = 2;
                                while (i < len) {
                                    __auto_type _mv_854 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_854.has_value) {
                                        __auto_type body_expr = _mv_854.value;
                                        stmt_transpile_stmt(ctx, body_expr, 0);
                                    } else if (!_mv_854.has_value) {
                                    }
                                    i = (i + 1);
                                }
                            }
                            context_ctx_dedent(ctx);
                            context_ctx_emit(ctx, SLOP_STR("}"));
                        }
                    } else if (!_mv_853.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing while condition"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    }
                }
            }
            break;
        }
        default: {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid while"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
            break;
        }
    }
}

void stmt_transpile_set(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_855 = (*expr);
        switch (_mv_855.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_855.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (expr_set_is_self_assign(items)) {
                    } else if (len == 5) {
                        stmt_transpile_typed_field_set(ctx, items);
                    } else if (len == 4) {
                        stmt_transpile_field_set(ctx, items);
                    } else if (len == 3) {
                        __auto_type _mv_856 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_856.has_value) {
                            __auto_type target_expr = _mv_856.value;
                            __auto_type _mv_857 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_857.has_value) {
                                __auto_type value_expr = _mv_857.value;
                                {
                                    __auto_type target_c = expr_transpile_expr(ctx, target_expr);
                                    __auto_type target_type_opt = stmt_get_var_c_type(ctx, target_expr);
                                    __auto_type _mv_858 = target_type_opt;
                                    if (_mv_858.has_value) {
                                        __auto_type target_type = _mv_858.value;
                                        if (context_ctx_is_option_c_type(ctx, target_type)) {
                                            {
                                                __auto_type some_val_opt = stmt_get_some_value(value_expr);
                                                __auto_type _mv_859 = some_val_opt;
                                                if (_mv_859.has_value) {
                                                    __auto_type val_expr = _mv_859.value;
                                                    {
                                                        __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                        context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str5(ctx, SLOP_STR(" = ("), target_type, SLOP_STR("){.has_value = 1, .value = "), val_c, SLOP_STR("};"))));
                                                    }
                                                } else if (!_mv_859.has_value) {
                                                    if (stmt_is_none_form(value_expr)) {
                                                        context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str3(ctx, SLOP_STR(" = ("), target_type, SLOP_STR("){.has_value = false};"))));
                                                    } else {
                                                        {
                                                            __auto_type value_c = expr_transpile_expr(ctx, value_expr);
                                                            context_ctx_emit(ctx, context_ctx_str4(ctx, target_c, SLOP_STR(" = "), value_c, SLOP_STR(";")));
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            {
                                                __auto_type value_c = expr_transpile_expr(ctx, value_expr);
                                                context_ctx_emit(ctx, context_ctx_str4(ctx, target_c, SLOP_STR(" = "), value_c, SLOP_STR(";")));
                                            }
                                        }
                                    } else if (!_mv_858.has_value) {
                                        {
                                            __auto_type some_val_opt = stmt_get_some_value(value_expr);
                                            __auto_type _mv_860 = some_val_opt;
                                            if (_mv_860.has_value) {
                                                __auto_type inner_expr = _mv_860.value;
                                                {
                                                    __auto_type inner_c = expr_transpile_expr(ctx, inner_expr);
                                                    __auto_type inner_type = expr_infer_expr_c_type(ctx, inner_expr);
                                                    __auto_type option_type = expr_c_type_to_option_type_name(ctx, inner_type);
                                                    context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str5(ctx, SLOP_STR(" = ("), option_type, SLOP_STR("){.has_value = 1, .value = "), inner_c, SLOP_STR("};"))));
                                                }
                                            } else if (!_mv_860.has_value) {
                                                if (stmt_is_none_form(value_expr)) {
                                                    __auto_type _mv_861 = context_ctx_get_current_return_type(ctx);
                                                    if (_mv_861.has_value) {
                                                        __auto_type ret_type = _mv_861.value;
                                                        if (context_ctx_is_option_c_type(ctx, ret_type)) {
                                                            context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str3(ctx, SLOP_STR(" = ("), ret_type, SLOP_STR("){.has_value = false};"))));
                                                        } else {
                                                            {
                                                                __auto_type value_c = expr_transpile_expr(ctx, value_expr);
                                                                context_ctx_emit(ctx, context_ctx_str4(ctx, target_c, SLOP_STR(" = "), value_c, SLOP_STR(";")));
                                                            }
                                                        }
                                                    } else if (!_mv_861.has_value) {
                                                        {
                                                            __auto_type value_c = expr_transpile_expr(ctx, value_expr);
                                                            context_ctx_emit(ctx, context_ctx_str4(ctx, target_c, SLOP_STR(" = "), value_c, SLOP_STR(";")));
                                                        }
                                                    }
                                                } else {
                                                    {
                                                        __auto_type value_c = expr_transpile_expr(ctx, value_expr);
                                                        context_ctx_emit(ctx, context_ctx_str4(ctx, target_c, SLOP_STR(" = "), value_c, SLOP_STR(";")));
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            } else if (!_mv_857.has_value) {
                                context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                            }
                        } else if (!_mv_856.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                        }
                    } else {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid set!: need target and value"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid set!"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                break;
            }
        }
    }
}

slop_option_string stmt_get_var_c_type(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    __auto_type _mv_862 = (*expr);
    switch (_mv_862.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_862.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_863 = context_ctx_lookup_var(ctx, name);
                if (_mv_863.has_value) {
                    __auto_type var_entry = _mv_863.value;
                    return (slop_option_string){.has_value = 1, .value = var_entry.c_type};
                } else if (!_mv_863.has_value) {
                    return (slop_option_string){.has_value = false};
                }
                SLOP_UNREACHABLE();
            }
        }
        default: {
            return (slop_option_string){.has_value = false};
        }
    }
}

uint8_t stmt_is_pointer_target(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_864 = (*expr);
    switch (_mv_864.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_864.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_865 = context_ctx_lookup_var(ctx, name);
                if (_mv_865.has_value) {
                    __auto_type var_entry = _mv_865.value;
                    return (var_entry.is_pointer || ({ __auto_type c_type = var_entry.c_type; strlib_ends_with(c_type, SLOP_STR("*")); }));
                } else if (!_mv_865.has_value) {
                    return 0;
                }
                SLOP_UNREACHABLE();
            }
        }
        default: {
            return 0;
        }
    }
}

void stmt_transpile_field_set(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_866 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_866.has_value) {
            __auto_type target_expr = _mv_866.value;
            __auto_type _mv_867 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_867.has_value) {
                __auto_type field_expr = _mv_867.value;
                __auto_type _mv_868 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_868.has_value) {
                    __auto_type value_expr = _mv_868.value;
                    {
                        __auto_type field_name = stmt_get_symbol_name(arena, field_expr);
                        __auto_type value_c = expr_transpile_expr(ctx, value_expr);
                        if (stmt_is_deref_expr(target_expr)) {
                            {
                                __auto_type inner_expr = stmt_get_deref_inner(target_expr);
                                __auto_type inner_c = expr_transpile_expr(ctx, inner_expr);
                                context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("(*"), context_ctx_str(ctx, inner_c, context_ctx_str(ctx, SLOP_STR(")."), context_ctx_str(ctx, field_name, context_ctx_str(ctx, SLOP_STR(" = "), context_ctx_str(ctx, value_c, SLOP_STR(";"))))))));
                            }
                        } else {
                            {
                                __auto_type target_c = expr_transpile_expr(ctx, target_expr);
                                __auto_type is_ptr = stmt_is_pointer_target(ctx, target_expr);
                                if (is_ptr) {
                                    context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str(ctx, SLOP_STR("->"), context_ctx_str(ctx, field_name, context_ctx_str(ctx, SLOP_STR(" = "), context_ctx_str(ctx, value_c, SLOP_STR(";")))))));
                                } else {
                                    context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str(ctx, SLOP_STR("."), context_ctx_str(ctx, field_name, context_ctx_str(ctx, SLOP_STR(" = "), context_ctx_str(ctx, value_c, SLOP_STR(";")))))));
                                }
                            }
                        }
                    }
                } else if (!_mv_868.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_ctx_sexpr_line(target_expr), context_ctx_sexpr_col(target_expr));
                }
            } else if (!_mv_867.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing set! field"), context_ctx_sexpr_line(target_expr), context_ctx_sexpr_col(target_expr));
            }
        } else if (!_mv_866.has_value) {
            context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        }
    }
}

void stmt_transpile_typed_field_set(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_869 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_869.has_value) {
            __auto_type target_expr = _mv_869.value;
            __auto_type _mv_870 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_870.has_value) {
                __auto_type field_expr = _mv_870.value;
                __auto_type _mv_871 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_871.has_value) {
                    __auto_type type_expr = _mv_871.value;
                    __auto_type _mv_872 = ({ __auto_type _lst = items; size_t _idx = (size_t)4; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_872.has_value) {
                        __auto_type value_expr = _mv_872.value;
                        {
                            __auto_type field_name = stmt_get_symbol_name(arena, field_expr);
                            __auto_type c_type = ctype_to_c_type(arena, type_expr);
                            {
                                __auto_type target_access = ((stmt_is_deref_expr(target_expr)) ? ({ __auto_type inner_expr = stmt_get_deref_inner(target_expr); __auto_type inner_c = expr_transpile_expr(ctx, inner_expr); context_ctx_str(ctx, SLOP_STR("(*"), context_ctx_str(ctx, inner_c, SLOP_STR(")."))); }) : ({ __auto_type target_c = expr_transpile_expr(ctx, target_expr); __auto_type is_ptr = stmt_is_pointer_target(ctx, target_expr); ((is_ptr) ? context_ctx_str(ctx, target_c, SLOP_STR("->")) : context_ctx_str(ctx, target_c, SLOP_STR("."))); }));
                                if (context_ctx_is_option_c_type(ctx, c_type)) {
                                    if (stmt_is_none_form(value_expr)) {
                                        context_ctx_emit(ctx, context_ctx_str(ctx, target_access, context_ctx_str(ctx, field_name, context_ctx_str3(ctx, SLOP_STR(" = ("), c_type, SLOP_STR("){.has_value = false};")))));
                                    } else {
                                        __auto_type _mv_873 = stmt_get_some_value(value_expr);
                                        if (_mv_873.has_value) {
                                            __auto_type inner_val = _mv_873.value;
                                            {
                                                __auto_type val_c = expr_transpile_expr(ctx, inner_val);
                                                context_ctx_emit(ctx, context_ctx_str(ctx, target_access, context_ctx_str(ctx, field_name, context_ctx_str5(ctx, SLOP_STR(" = ("), c_type, SLOP_STR("){.has_value = 1, .value = "), val_c, SLOP_STR("};")))));
                                            }
                                        } else if (!_mv_873.has_value) {
                                            {
                                                __auto_type val_c = expr_transpile_expr(ctx, value_expr);
                                                context_ctx_emit(ctx, context_ctx_str(ctx, target_access, context_ctx_str(ctx, field_name, context_ctx_str(ctx, SLOP_STR(" = "), context_ctx_str(ctx, val_c, SLOP_STR(";"))))));
                                            }
                                        }
                                    }
                                } else {
                                    {
                                        __auto_type val_c = expr_transpile_expr(ctx, value_expr);
                                        context_ctx_emit(ctx, context_ctx_str(ctx, target_access, context_ctx_str(ctx, field_name, context_ctx_str(ctx, SLOP_STR(" = "), context_ctx_str(ctx, val_c, SLOP_STR(";"))))));
                                    }
                                }
                            }
                        }
                    } else if (!_mv_872.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_ctx_sexpr_line(type_expr), context_ctx_sexpr_col(type_expr));
                    }
                } else if (!_mv_871.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("missing set! type"), context_ctx_sexpr_line(field_expr), context_ctx_sexpr_col(field_expr));
                }
            } else if (!_mv_870.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing set! field"), context_ctx_sexpr_line(target_expr), context_ctx_sexpr_col(target_expr));
            }
        } else if (!_mv_869.has_value) {
            context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        }
    }
}

uint8_t stmt_is_deref_expr(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_874 = (*expr);
    switch (_mv_874.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_874.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return 0;
                } else {
                    __auto_type _mv_875 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_875.has_value) {
                        __auto_type head = _mv_875.value;
                        __auto_type _mv_876 = (*head);
                        switch (_mv_876.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_876.data.sym;
                                return string_eq(sym.name, SLOP_STR("deref"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_875.has_value) {
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

types_SExpr* stmt_get_deref_inner(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_877 = (*expr);
    switch (_mv_877.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_877.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type _mv_878 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_878.has_value) {
                    __auto_type inner = _mv_878.value;
                    return inner;
                } else if (!_mv_878.has_value) {
                    return expr;
                }
                SLOP_UNREACHABLE();
            }
        }
        default: {
            return expr;
        }
    }
}

slop_string stmt_get_symbol_name(slop_arena* arena, types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_879 = (*expr);
    switch (_mv_879.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_879.data.sym;
            return ctype_to_c_name(arena, sym.name);
        }
        default: {
            return SLOP_STR("/* unknown field */");
        }
    }
}

void stmt_transpile_do(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_880 = (*expr);
    switch (_mv_880.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_880.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type i = 1;
                while (i < len) {
                    __auto_type _mv_881 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_881.has_value) {
                        __auto_type body_expr = _mv_881.value;
                        {
                            __auto_type is_last = (i == (len - 1));
                            stmt_transpile_stmt(ctx, body_expr, (is_return && is_last));
                        }
                    } else if (!_mv_881.has_value) {
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
}

void stmt_transpile_with_arena(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_882 = (*expr);
    switch (_mv_882.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_882.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if (len < 2) {
                    context_ctx_add_error_at(ctx, SLOP_STR("invalid with-arena: need size"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                } else {
                    {
                        __auto_type is_named = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type item1 = _mv.value; string_eq(parser_sexpr_get_symbol_name(item1), SLOP_STR(":as")); }) : (0); });
                        __auto_type arena_name = ((is_named) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type name_expr = _mv.value; parser_sexpr_get_symbol_name(name_expr); }) : (SLOP_STR("arena")); }) : SLOP_STR("arena"));
                        __auto_type size_idx = ((is_named) ? 3 : 1);
                        __auto_type body_start = ((is_named) ? 4 : 2);
                        __auto_type c_arena_name = ctype_to_c_name((*ctx).arena, arena_name);
                        __auto_type c_local = ((is_named) ? string_concat((*ctx).arena, SLOP_STR("_arena_"), c_arena_name) : SLOP_STR("_arena"));
                        if (is_named && (len < 4)) {
                            context_ctx_add_error_at(ctx, SLOP_STR("with-arena :as requires name and size"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                        } else {
                            context_ctx_emit(ctx, SLOP_STR("{"));
                            context_ctx_indent(ctx);
                            context_ctx_push_scope(ctx);
                            __auto_type _mv_883 = ({ __auto_type _lst = items; size_t _idx = (size_t)size_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_883.has_value) {
                                __auto_type size_expr = _mv_883.value;
                                {
                                    __auto_type size_c = expr_transpile_expr(ctx, size_expr);
                                    context_ctx_emit(ctx, SLOP_STR("#ifdef SLOP_DEBUG"));
                                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("SLOP_PRE(("), size_c, SLOP_STR(") > 0, \"with-arena size must be positive\");")));
                                    context_ctx_emit(ctx, SLOP_STR("#endif"));
                                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("slop_arena "), c_local, SLOP_STR(" = slop_arena_new("), size_c, SLOP_STR(");")));
                                    context_ctx_emit(ctx, SLOP_STR("#ifdef SLOP_DEBUG"));
                                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("SLOP_PRE("), c_local, SLOP_STR(".base != NULL, \"arena allocation failed\");")));
                                    context_ctx_emit(ctx, SLOP_STR("#endif"));
                                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("slop_arena* "), c_arena_name, SLOP_STR(" = &"), c_local, SLOP_STR(";")));
                                }
                            } else if (!_mv_883.has_value) {
                                context_ctx_add_error_at(ctx, SLOP_STR("missing size"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                            }
                            context_ctx_bind_var(ctx, (context_VarEntry){arena_name, c_arena_name, SLOP_STR("slop_arena*"), SLOP_STR(""), 1, 0, 0, SLOP_STR(""), SLOP_STR("")});
                            {
                                __auto_type i = body_start;
                                while (i < len) {
                                    __auto_type _mv_884 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_884.has_value) {
                                        __auto_type body_expr = _mv_884.value;
                                        {
                                            __auto_type is_last = (i == (len - 1));
                                            stmt_transpile_stmt(ctx, body_expr, (is_return && is_last));
                                        }
                                    } else if (!_mv_884.has_value) {
                                    }
                                    i = (i + 1);
                                }
                            }
                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("slop_arena_free("), c_arena_name, SLOP_STR(");")));
                            context_ctx_pop_scope(ctx);
                            context_ctx_dedent(ctx);
                            context_ctx_emit(ctx, SLOP_STR("}"));
                        }
                    }
                }
            }
            break;
        }
        default: {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid with-arena"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
            break;
        }
    }
}

void stmt_transpile_cond(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_885 = (*expr);
    switch (_mv_885.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_885.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type i = 1;
                __auto_type first = 1;
                while (i < len) {
                    __auto_type _mv_886 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_886.has_value) {
                        __auto_type clause_expr = _mv_886.value;
                        __auto_type _mv_887 = (*clause_expr);
                        switch (_mv_887.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type clause_lst = _mv_887.data.lst;
                                {
                                    __auto_type clause_items = clause_lst.items;
                                    __auto_type clause_len = ((int64_t)((clause_items).len));
                                    if (clause_len < 1) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("invalid cond clause"), context_ctx_sexpr_line(clause_expr), context_ctx_sexpr_col(clause_expr));
                                    } else {
                                        __auto_type _mv_888 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_888.has_value) {
                                            __auto_type test_expr = _mv_888.value;
                                            __auto_type _mv_889 = (*test_expr);
                                            switch (_mv_889.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type sym = _mv_889.data.sym;
                                                    if (string_eq(sym.name, SLOP_STR("else"))) {
                                                        context_ctx_emit(ctx, SLOP_STR("} else {"));
                                                        context_ctx_indent(ctx);
                                                        stmt_transpile_cond_body(ctx, clause_items, 1, is_return);
                                                        context_ctx_dedent(ctx);
                                                    } else {
                                                        {
                                                            __auto_type cond_c = context_ctx_strip_cond_parens(ctx, expr_transpile_expr(ctx, test_expr));
                                                            if (first) {
                                                                context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), cond_c, SLOP_STR(") {")));
                                                                first = 0;
                                                            } else {
                                                                context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("} else if ("), cond_c, SLOP_STR(") {")));
                                                            }
                                                            context_ctx_indent(ctx);
                                                            stmt_transpile_cond_body(ctx, clause_items, 1, is_return);
                                                            context_ctx_dedent(ctx);
                                                        }
                                                    }
                                                    break;
                                                }
                                                default: {
                                                    {
                                                        __auto_type cond_c = context_ctx_strip_cond_parens(ctx, expr_transpile_expr(ctx, test_expr));
                                                        if (first) {
                                                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), cond_c, SLOP_STR(") {")));
                                                            first = 0;
                                                        } else {
                                                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("} else if ("), cond_c, SLOP_STR(") {")));
                                                        }
                                                        context_ctx_indent(ctx);
                                                        stmt_transpile_cond_body(ctx, clause_items, 1, is_return);
                                                        context_ctx_dedent(ctx);
                                                    }
                                                    break;
                                                }
                                            }
                                        } else if (!_mv_888.has_value) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("missing test"), context_ctx_sexpr_line(clause_expr), context_ctx_sexpr_col(clause_expr));
                                        }
                                    }
                                }
                                break;
                            }
                            default: {
                                context_ctx_add_error_at(ctx, SLOP_STR("cond clause must be list"), context_ctx_sexpr_line(clause_expr), context_ctx_sexpr_col(clause_expr));
                                break;
                            }
                        }
                    } else if (!_mv_886.has_value) {
                    }
                    i = (i + 1);
                }
                if (!(first)) {
                    context_ctx_emit(ctx, SLOP_STR("}"));
                }
            }
            break;
        }
        default: {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid cond"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
            break;
        }
    }
}

void stmt_transpile_cond_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = start;
        while (i < len) {
            __auto_type _mv_890 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_890.has_value) {
                __auto_type body_expr = _mv_890.value;
                {
                    __auto_type is_last = (i == (len - 1));
                    stmt_transpile_stmt(ctx, body_expr, (is_return && is_last));
                }
            } else if (!_mv_890.has_value) {
            }
            i = (i + 1);
        }
    }
}

void stmt_transpile_for(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_891 = (*expr);
        switch (_mv_891.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_891.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len < 2) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid for: need binding"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    } else {
                        __auto_type _mv_892 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_892.has_value) {
                            __auto_type binding_expr = _mv_892.value;
                            __auto_type _mv_893 = (*binding_expr);
                            switch (_mv_893.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type binding_lst = _mv_893.data.lst;
                                    {
                                        __auto_type binding_items = binding_lst.items;
                                        __auto_type binding_len = ((int64_t)((binding_items).len));
                                        if (binding_len < 3) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("for binding needs (var start end)"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                                        } else {
                                            __auto_type _mv_894 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_894.has_value) {
                                                __auto_type var_expr = _mv_894.value;
                                                __auto_type _mv_895 = (*var_expr);
                                                switch (_mv_895.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type var_sym = _mv_895.data.sym;
                                                        {
                                                            __auto_type var_name = ctype_to_c_name(arena, var_sym.name);
                                                            __auto_type _mv_896 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_896.has_value) {
                                                                __auto_type start_expr = _mv_896.value;
                                                                __auto_type _mv_897 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                if (_mv_897.has_value) {
                                                                    __auto_type end_expr = _mv_897.value;
                                                                    {
                                                                        __auto_type start_c = expr_transpile_expr(ctx, start_expr);
                                                                        __auto_type end_c = expr_transpile_expr(ctx, end_expr);
                                                                        context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("for (int64_t "), var_name, SLOP_STR(" = "), start_c, context_ctx_str5(ctx, SLOP_STR("; "), var_name, SLOP_STR(" < "), end_c, context_ctx_str3(ctx, SLOP_STR("; "), var_name, SLOP_STR("++) {")))));
                                                                        context_ctx_indent(ctx);
                                                                        context_ctx_push_scope(ctx);
                                                                        context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, SLOP_STR("int64_t"), SLOP_STR(""), 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                                                        {
                                                                            __auto_type i = 2;
                                                                            while (i < len) {
                                                                                __auto_type _mv_898 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                                if (_mv_898.has_value) {
                                                                                    __auto_type body_expr = _mv_898.value;
                                                                                    stmt_transpile_stmt(ctx, body_expr, 0);
                                                                                } else if (!_mv_898.has_value) {
                                                                                }
                                                                                i = (i + 1);
                                                                            }
                                                                        }
                                                                        context_ctx_pop_scope(ctx);
                                                                        context_ctx_dedent(ctx);
                                                                        context_ctx_emit(ctx, SLOP_STR("}"));
                                                                    }
                                                                } else if (!_mv_897.has_value) {
                                                                    context_ctx_add_error_at(ctx, SLOP_STR("missing end"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                                                                }
                                                            } else if (!_mv_896.has_value) {
                                                                context_ctx_add_error_at(ctx, SLOP_STR("missing start"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                                                            }
                                                        }
                                                        break;
                                                    }
                                                    default: {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("for var must be symbol"), context_ctx_sexpr_line(var_expr), context_ctx_sexpr_col(var_expr));
                                                        break;
                                                    }
                                                }
                                            } else if (!_mv_894.has_value) {
                                                context_ctx_add_error_at(ctx, SLOP_STR("missing var"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                                            }
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    context_ctx_add_error_at(ctx, SLOP_STR("for binding must be list"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                                    break;
                                }
                            }
                        } else if (!_mv_892.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing binding"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid for"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                break;
            }
        }
    }
}

void stmt_transpile_for_each_set(context_TranspileContext* ctx, slop_string var_name, types_SExprSymbol var_sym, slop_string coll_c, slop_string resolved_type, slop_list_types_SExpr_ptr items, int64_t len) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type elem_slop_type = expr_extract_set_elem_from_slop_type(arena, resolved_type);
        __auto_type elem_c_type = expr_slop_value_type_to_c_type(ctx, elem_slop_type);
        context_ctx_emit(ctx, SLOP_STR("{"));
        context_ctx_indent(ctx);
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("slop_map* _coll = (slop_map*)"), expr_deref_container_c(ctx, coll_c, resolved_type), SLOP_STR(";")));
        context_ctx_emit(ctx, SLOP_STR("for (size_t _i = 0; _i < _coll->cap; _i++) {"));
        context_ctx_indent(ctx);
        context_ctx_emit(ctx, SLOP_STR("if (_coll->entries[_i].occupied) {"));
        context_ctx_indent(ctx);
        {
            __auto_type cast_part = context_ctx_str(ctx, elem_c_type, SLOP_STR("*)_coll->entries[_i].key"));
            __auto_type assign_prefix = context_ctx_str4(ctx, elem_c_type, SLOP_STR(" "), var_name, SLOP_STR(" = *("));
            __auto_type assign_part = context_ctx_str3(ctx, assign_prefix, cast_part, SLOP_STR(";"));
            context_ctx_emit(ctx, assign_part);
        }
        context_ctx_push_scope(ctx);
        context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, elem_c_type, elem_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
        {
            int64_t i = 2;
            while (i < len) {
                __auto_type _mv_899 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_899.has_value) {
                    __auto_type body_expr = _mv_899.value;
                    stmt_transpile_stmt(ctx, body_expr, 0);
                } else if (!_mv_899.has_value) {
                }
                i = (i + 1);
            }
        }
        context_ctx_pop_scope(ctx);
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
    }
}

void stmt_transpile_for_each_map_keys(context_TranspileContext* ctx, slop_string var_name, types_SExprSymbol var_sym, slop_string coll_c, slop_string resolved_type, slop_list_types_SExpr_ptr items, int64_t len) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type key_slop_type = expr_extract_map_key_from_slop_type(arena, resolved_type);
        __auto_type key_c_type = expr_slop_value_type_to_c_type(ctx, key_slop_type);
        context_ctx_emit(ctx, SLOP_STR("{"));
        context_ctx_indent(ctx);
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("slop_map* _coll = (slop_map*)"), expr_deref_container_c(ctx, coll_c, resolved_type), SLOP_STR(";")));
        context_ctx_emit(ctx, SLOP_STR("for (size_t _i = 0; _i < _coll->cap; _i++) {"));
        context_ctx_indent(ctx);
        context_ctx_emit(ctx, SLOP_STR("if (_coll->entries[_i].occupied) {"));
        context_ctx_indent(ctx);
        {
            __auto_type cast_part = context_ctx_str(ctx, key_c_type, SLOP_STR("*)_coll->entries[_i].key"));
            __auto_type assign_prefix = context_ctx_str4(ctx, key_c_type, SLOP_STR(" "), var_name, SLOP_STR(" = *("));
            __auto_type assign_part = context_ctx_str3(ctx, assign_prefix, cast_part, SLOP_STR(";"));
            context_ctx_emit(ctx, assign_part);
        }
        context_ctx_push_scope(ctx);
        context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, key_c_type, key_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
        {
            int64_t i = 2;
            while (i < len) {
                __auto_type _mv_900 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_900.has_value) {
                    __auto_type body_expr = _mv_900.value;
                    stmt_transpile_stmt(ctx, body_expr, 0);
                } else if (!_mv_900.has_value) {
                }
                i = (i + 1);
            }
        }
        context_ctx_pop_scope(ctx);
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
    }
}

void stmt_transpile_for_each_map_kv(context_TranspileContext* ctx, slop_list_types_SExpr_ptr binding_items, slop_list_types_SExpr_ptr items, int64_t len) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_901 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_901.has_value) {
            __auto_type kv_list_expr = _mv_901.value;
            __auto_type _mv_902 = (*kv_list_expr);
            switch (_mv_902.tag) {
                case types_SExpr_lst:
                {
                    __auto_type kv_lst = _mv_902.data.lst;
                    {
                        __auto_type kv_items = kv_lst.items;
                        if (((int64_t)((kv_items).len)) < 2) {
                            context_ctx_add_error(ctx, SLOP_STR("Map for-each needs ((k v) map)"));
                        } else {
                            __auto_type _mv_903 = ({ __auto_type _lst = kv_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_903.has_value) {
                                __auto_type k_expr = _mv_903.value;
                                __auto_type _mv_904 = ({ __auto_type _lst = kv_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_904.has_value) {
                                    __auto_type v_expr = _mv_904.value;
                                    __auto_type _mv_905 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_905.has_value) {
                                        __auto_type map_expr = _mv_905.value;
                                        __auto_type _mv_906 = (*k_expr);
                                        switch (_mv_906.tag) {
                                            case types_SExpr_sym:
                                            {
                                                __auto_type k_sym = _mv_906.data.sym;
                                                __auto_type _mv_907 = (*v_expr);
                                                switch (_mv_907.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type v_sym = _mv_907.data.sym;
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
                                                            context_ctx_emit(ctx, SLOP_STR("{"));
                                                            context_ctx_indent(ctx);
                                                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("slop_map* _coll = (slop_map*)"), expr_deref_container_c(ctx, map_c, resolved_type), SLOP_STR(";")));
                                                            context_ctx_emit(ctx, SLOP_STR("for (size_t _i = 0; _i < _coll->cap; _i++) {"));
                                                            context_ctx_indent(ctx);
                                                            context_ctx_emit(ctx, SLOP_STR("if (_coll->entries[_i].occupied) {"));
                                                            context_ctx_indent(ctx);
                                                            {
                                                                __auto_type k_cast = context_ctx_str(ctx, key_c_type, SLOP_STR("*)_coll->entries[_i].key"));
                                                                __auto_type k_prefix = context_ctx_str4(ctx, key_c_type, SLOP_STR(" "), k_name, SLOP_STR(" = *("));
                                                                __auto_type k_assign = context_ctx_str3(ctx, k_prefix, k_cast, SLOP_STR(";"));
                                                                context_ctx_emit(ctx, k_assign);
                                                            }
                                                            {
                                                                __auto_type v_cast = context_ctx_str(ctx, val_c_type, SLOP_STR("*)_coll->entries[_i].value"));
                                                                __auto_type v_prefix = context_ctx_str4(ctx, val_c_type, SLOP_STR(" "), v_name, SLOP_STR(" = *("));
                                                                __auto_type v_assign = context_ctx_str3(ctx, v_prefix, v_cast, SLOP_STR(";"));
                                                                context_ctx_emit(ctx, v_assign);
                                                            }
                                                            context_ctx_push_scope(ctx);
                                                            context_ctx_bind_var(ctx, (context_VarEntry){k_sym.name, k_name, key_c_type, key_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                                            context_ctx_bind_var(ctx, (context_VarEntry){v_sym.name, v_name, val_c_type, val_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                                            {
                                                                __auto_type i = 2;
                                                                while (i < len) {
                                                                    __auto_type _mv_908 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                    if (_mv_908.has_value) {
                                                                        __auto_type body_expr = _mv_908.value;
                                                                        stmt_transpile_stmt(ctx, body_expr, 0);
                                                                    } else if (!_mv_908.has_value) {
                                                                    }
                                                                    i = (i + 1);
                                                                }
                                                            }
                                                            context_ctx_pop_scope(ctx);
                                                            context_ctx_dedent(ctx);
                                                            context_ctx_emit(ctx, SLOP_STR("}"));
                                                            context_ctx_dedent(ctx);
                                                            context_ctx_emit(ctx, SLOP_STR("}"));
                                                            context_ctx_dedent(ctx);
                                                            context_ctx_emit(ctx, SLOP_STR("}"));
                                                        }
                                                        break;
                                                    }
                                                    default: {
                                                        context_ctx_add_error(ctx, SLOP_STR("Map for-each value must be symbol"));
                                                        break;
                                                    }
                                                }
                                                break;
                                            }
                                            default: {
                                                context_ctx_add_error(ctx, SLOP_STR("Map for-each key must be symbol"));
                                                break;
                                            }
                                        }
                                    } else if (!_mv_905.has_value) {
                                        context_ctx_add_error(ctx, SLOP_STR("Missing map expression"));
                                    }
                                } else if (!_mv_904.has_value) {
                                    context_ctx_add_error(ctx, SLOP_STR("Missing value binding"));
                                }
                            } else if (!_mv_903.has_value) {
                                context_ctx_add_error(ctx, SLOP_STR("Missing key binding"));
                            }
                        }
                    }
                    break;
                }
                default: {
                    context_ctx_add_error(ctx, SLOP_STR("Invalid Map binding"));
                    break;
                }
            }
        } else if (!_mv_901.has_value) {
            context_ctx_add_error(ctx, SLOP_STR("Missing binding"));
        }
    }
}

void stmt_transpile_for_each(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_909 = (*expr);
        switch (_mv_909.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_909.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len < 2) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid for-each: need binding"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    } else {
                        __auto_type _mv_910 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_910.has_value) {
                            __auto_type binding_expr = _mv_910.value;
                            __auto_type _mv_911 = (*binding_expr);
                            switch (_mv_911.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type binding_lst = _mv_911.data.lst;
                                    {
                                        __auto_type binding_items = binding_lst.items;
                                        __auto_type binding_len = ((int64_t)((binding_items).len));
                                        if (binding_len < 2) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("for-each binding needs (var coll)"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                                        } else {
                                            __auto_type _mv_912 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_912.has_value) {
                                                __auto_type first_elem = _mv_912.value;
                                                __auto_type _mv_913 = (*first_elem);
                                                switch (_mv_913.tag) {
                                                    case types_SExpr_lst:
                                                    {
                                                        __auto_type _ = _mv_913.data.lst;
                                                        stmt_transpile_for_each_map_kv(ctx, binding_items, items, len);
                                                        break;
                                                    }
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type var_sym = _mv_913.data.sym;
                                                        {
                                                            __auto_type var_name = ctype_to_c_name(arena, var_sym.name);
                                                            __auto_type _mv_914 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_914.has_value) {
                                                                __auto_type coll_expr = _mv_914.value;
                                                                {
                                                                    __auto_type coll_slop_type = expr_infer_expr_slop_type(ctx, coll_expr);
                                                                    __auto_type resolved_type = expr_resolve_type_alias(ctx, coll_slop_type);
                                                                    if (expr_is_set_type(resolved_type)) {
                                                                        {
                                                                            __auto_type coll_c = expr_transpile_expr(ctx, coll_expr);
                                                                            stmt_transpile_for_each_set(ctx, var_name, var_sym, coll_c, resolved_type, items, len);
                                                                        }
                                                                    } else if (expr_is_map_type(resolved_type)) {
                                                                        {
                                                                            __auto_type coll_c = expr_transpile_expr(ctx, coll_expr);
                                                                            stmt_transpile_for_each_map_keys(ctx, var_name, var_sym, coll_c, resolved_type, items, len);
                                                                        }
                                                                    } else {
                                                                        {
                                                                            __auto_type coll_c = expr_transpile_expr(ctx, coll_expr);
                                                                            context_ctx_emit(ctx, SLOP_STR("{"));
                                                                            context_ctx_indent(ctx);
                                                                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("__auto_type _coll = "), coll_c, SLOP_STR(";")));
                                                                            context_ctx_emit(ctx, SLOP_STR("for (size_t _i = 0; _i < _coll.len; _i++) {"));
                                                                            context_ctx_indent(ctx);
                                                                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("__auto_type "), var_name, SLOP_STR(" = _coll.data[_i];")));
                                                                            context_ctx_push_scope(ctx);
                                                                            {
                                                                                __auto_type elem_slop_type = expr_infer_collection_element_slop_type(ctx, coll_expr);
                                                                                __auto_type is_ptr_elem = strlib_starts_with(elem_slop_type, SLOP_STR("(Ptr "));
                                                                                __auto_type elem_c_type = ((is_ptr_elem) ? expr_slop_value_type_to_c_type(ctx, elem_slop_type) : SLOP_STR("auto"));
                                                                                context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, elem_c_type, elem_slop_type, is_ptr_elem, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                                                            }
                                                                            {
                                                                                __auto_type i = 2;
                                                                                while (i < len) {
                                                                                    __auto_type _mv_915 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                                    if (_mv_915.has_value) {
                                                                                        __auto_type body_expr = _mv_915.value;
                                                                                        stmt_transpile_stmt(ctx, body_expr, 0);
                                                                                    } else if (!_mv_915.has_value) {
                                                                                    }
                                                                                    i = (i + 1);
                                                                                }
                                                                            }
                                                                            context_ctx_pop_scope(ctx);
                                                                            context_ctx_dedent(ctx);
                                                                            context_ctx_emit(ctx, SLOP_STR("}"));
                                                                            context_ctx_dedent(ctx);
                                                                            context_ctx_emit(ctx, SLOP_STR("}"));
                                                                        }
                                                                    }
                                                                }
                                                            } else if (!_mv_914.has_value) {
                                                                context_ctx_add_error_at(ctx, SLOP_STR("missing collection"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                                                            }
                                                        }
                                                        break;
                                                    }
                                                    default: {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("for-each var must be symbol or list"), context_ctx_sexpr_line(first_elem), context_ctx_sexpr_col(first_elem));
                                                        break;
                                                    }
                                                }
                                            } else if (!_mv_912.has_value) {
                                                context_ctx_add_error_at(ctx, SLOP_STR("missing var"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                                            }
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    context_ctx_add_error_at(ctx, SLOP_STR("for-each binding must be list"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                                    break;
                                }
                            }
                        } else if (!_mv_910.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing binding"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid for-each"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                break;
            }
        }
    }
}

void stmt_transpile_stmt(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_916 = (*expr);
    switch (_mv_916.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_916.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    context_ctx_add_error_at(ctx, SLOP_STR("empty list"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                } else {
                    __auto_type _mv_917 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_917.has_value) {
                        __auto_type head_expr = _mv_917.value;
                        __auto_type _mv_918 = (*head_expr);
                        switch (_mv_918.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_918.data.sym;
                                {
                                    __auto_type op = sym.name;
                                    if (string_eq(op, SLOP_STR("let")) || string_eq(op, SLOP_STR("let*"))) {
                                        stmt_transpile_let(ctx, expr, is_return);
                                    } else if (string_eq(op, SLOP_STR("if"))) {
                                        stmt_transpile_if(ctx, expr, is_return);
                                    } else if (string_eq(op, SLOP_STR("when"))) {
                                        stmt_transpile_when(ctx, expr);
                                    } else if (string_eq(op, SLOP_STR("while"))) {
                                        stmt_transpile_while(ctx, expr);
                                    } else if (string_eq(op, SLOP_STR("cond"))) {
                                        stmt_transpile_cond(ctx, expr, is_return);
                                    } else if (string_eq(op, SLOP_STR("for"))) {
                                        stmt_transpile_for(ctx, expr);
                                    } else if (string_eq(op, SLOP_STR("for-each"))) {
                                        stmt_transpile_for_each(ctx, expr);
                                    } else if (string_eq(op, SLOP_STR("match"))) {
                                        match_transpile_match(ctx, expr, is_return);
                                    } else if (string_eq(op, SLOP_STR("set!"))) {
                                        stmt_transpile_set(ctx, expr);
                                    } else if (string_eq(op, SLOP_STR("do"))) {
                                        stmt_transpile_do(ctx, expr, is_return);
                                    } else if (string_eq(op, SLOP_STR("with-arena"))) {
                                        stmt_transpile_with_arena(ctx, expr, is_return);
                                    } else if (string_eq(op, SLOP_STR("return"))) {
                                        if (((int64_t)((items).len)) < 2) {
                                            context_ctx_emit(ctx, SLOP_STR("return;"));
                                        } else {
                                            __auto_type _mv_919 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_919.has_value) {
                                                __auto_type val_expr = _mv_919.value;
                                                stmt_emit_typed_return_expr(ctx, val_expr);
                                            } else if (!_mv_919.has_value) {
                                                context_ctx_emit(ctx, SLOP_STR("return;"));
                                            }
                                        }
                                    } else if (string_eq(op, SLOP_STR("break"))) {
                                        context_ctx_emit(ctx, SLOP_STR("break;"));
                                    } else if (string_eq(op, SLOP_STR("continue"))) {
                                        context_ctx_emit(ctx, SLOP_STR("continue;"));
                                    } else if (strlib_starts_with(op, SLOP_STR("@")) && !(string_eq(op, SLOP_STR("@")))) {
                                    } else {
                                        if (is_return) {
                                            stmt_emit_typed_return_expr(ctx, expr);
                                        } else {
                                            if (!(string_eq(parser_sexpr_get_symbol_name(expr), SLOP_STR("unit")))) {
                                                context_ctx_emit(ctx, context_ctx_str(ctx, expr_transpile_expr(ctx, expr), SLOP_STR(";")));
                                            }
                                        }
                                    }
                                }
                                break;
                            }
                            default: {
                                if (is_return) {
                                    stmt_emit_typed_return_expr(ctx, expr);
                                } else {
                                    if (!(string_eq(parser_sexpr_get_symbol_name(expr), SLOP_STR("unit")))) {
                                        context_ctx_emit(ctx, context_ctx_str(ctx, expr_transpile_expr(ctx, expr), SLOP_STR(";")));
                                    }
                                }
                                break;
                            }
                        }
                    } else if (!_mv_917.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("empty"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    }
                }
            }
            break;
        }
        default: {
            if (is_return) {
                stmt_emit_typed_return_expr(ctx, expr);
            } else {
                if (!(string_eq(parser_sexpr_get_symbol_name(expr), SLOP_STR("unit")))) {
                    context_ctx_emit(ctx, context_ctx_str(ctx, expr_transpile_expr(ctx, expr), SLOP_STR(";")));
                }
            }
            break;
        }
    }
}

void stmt_emit_typed_return_expr(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_920 = (*expr);
    switch (_mv_920.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_920.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                } else {
                    __auto_type _mv_921 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_921.has_value) {
                        __auto_type head = _mv_921.value;
                        __auto_type _mv_922 = (*head);
                        switch (_mv_922.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_922.data.sym;
                                {
                                    __auto_type op = sym.name;
                                    if (string_eq(op, SLOP_STR("some"))) {
                                        __auto_type _mv_923 = context_ctx_get_current_return_type(ctx);
                                        if (_mv_923.has_value) {
                                            __auto_type ret_type = _mv_923.value;
                                            if (context_ctx_is_option_c_type(ctx, ret_type)) {
                                                if (((int64_t)((items).len)) < 2) {
                                                    stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                                } else {
                                                    __auto_type _mv_924 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_924.has_value) {
                                                        __auto_type inner_expr = _mv_924.value;
                                                        {
                                                            __auto_type inner_c = expr_transpile_expr(ctx, inner_expr);
                                                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("return ("), ret_type, SLOP_STR("){.has_value = 1, .value = "), inner_c, SLOP_STR("};")));
                                                        }
                                                    } else if (!_mv_924.has_value) {
                                                        stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                                    }
                                                }
                                            } else {
                                                stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                            }
                                        } else if (!_mv_923.has_value) {
                                            stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                        }
                                    } else if (string_eq(op, SLOP_STR("none"))) {
                                        __auto_type _mv_925 = context_ctx_get_current_return_type(ctx);
                                        if (_mv_925.has_value) {
                                            __auto_type ret_type = _mv_925.value;
                                            if (context_ctx_is_option_c_type(ctx, ret_type)) {
                                                context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("return ("), ret_type, SLOP_STR("){.has_value = false};")));
                                            } else {
                                                stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                            }
                                        } else if (!_mv_925.has_value) {
                                            stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                        }
                                    } else {
                                        stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                    }
                                }
                                break;
                            }
                            default: {
                                stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                break;
                            }
                        }
                    } else if (!_mv_921.has_value) {
                        stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                    }
                }
            }
            break;
        }
        default: {
            stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
            break;
        }
    }
}

void stmt_emit_return_with_typed_none(context_TranspileContext* ctx, slop_string code) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type final_code = code;
        if (string_eq(code, SLOP_STR("none"))) {
            __auto_type _mv_926 = context_ctx_get_current_return_type(ctx);
            if (_mv_926.has_value) {
                __auto_type ret_type = _mv_926.value;
                if (context_ctx_is_option_c_type(ctx, ret_type)) {
                    final_code = context_ctx_str3(ctx, SLOP_STR("("), ret_type, SLOP_STR("){.has_value = false}"));
                }
            } else if (!_mv_926.has_value) {
            }
        } else {
            __auto_type _mv_927 = context_ctx_get_current_return_type(ctx);
            if (_mv_927.has_value) {
                __auto_type ret_type = _mv_927.value;
                if (context_ctx_is_option_c_type(ctx, ret_type)) {
                    __auto_type _mv_928 = context_ctx_lookup_var(ctx, code);
                    if (_mv_928.has_value) {
                        __auto_type var_entry = _mv_928.value;
                        {
                            __auto_type var_type = var_entry.c_type;
                            if (string_eq(var_type, SLOP_STR("_slop_option_generic")) || string_eq(var_type, SLOP_STR("auto"))) {
                                {
                                    __auto_type s1 = context_ctx_str(ctx, SLOP_STR("(("), ret_type);
                                    __auto_type s2 = context_ctx_str(ctx, s1, SLOP_STR("){.has_value = "));
                                    __auto_type s3 = context_ctx_str(ctx, s2, code);
                                    __auto_type s4 = context_ctx_str(ctx, s3, SLOP_STR(".has_value, .value = "));
                                    __auto_type s5 = context_ctx_str(ctx, s4, code);
                                    __auto_type s6 = context_ctx_str(ctx, s5, SLOP_STR(".value})"));
                                    final_code = s6;
                                }
                            }
                        }
                    } else if (!_mv_928.has_value) {
                    }
                }
            } else if (!_mv_927.has_value) {
            }
        }
        if (context_ctx_is_capture_retval(ctx)) {
            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("_retval = "), final_code, SLOP_STR(";")));
        } else {
            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("return "), final_code, SLOP_STR(";")));
        }
    }
}

