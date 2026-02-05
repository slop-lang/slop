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
void stmt_transpile_for_each(context_TranspileContext* ctx, types_SExpr* expr);
void stmt_transpile_stmt(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return);
void stmt_emit_typed_return_expr(context_TranspileContext* ctx, types_SExpr* expr);
void stmt_emit_return_with_typed_none(context_TranspileContext* ctx, slop_string code);

slop_string stmt_sexpr_to_type_string(slop_arena* arena, types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_707 = (*expr);
    switch (_mv_707.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_707.data.sym;
            return sym.name;
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_707.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type result = SLOP_STR("(");
                __auto_type i = 0;
                while ((i < len)) {
                    __auto_type _mv_708 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_708.has_value) {
                        __auto_type item_expr = _mv_708.value;
                        {
                            __auto_type item_str = stmt_sexpr_to_type_string(arena, item_expr);
                            if ((i > 0)) {
                                result = string_concat(arena, result, string_concat(arena, SLOP_STR(" "), item_str));
                            } else {
                                result = string_concat(arena, result, item_str);
                            }
                        }
                    } else if (!_mv_708.has_value) {
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
        __auto_type _mv_709 = (*expr);
        switch (_mv_709.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_709.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 3)) {
                        __auto_type _mv_710 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_710.has_value) {
                            __auto_type head_ptr = _mv_710.value;
                            __auto_type _mv_711 = (*head_ptr);
                            switch (_mv_711.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_711.data.sym;
                                    if (string_eq(head_sym.name, SLOP_STR("arena-alloc"))) {
                                        __auto_type _mv_712 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_712.has_value) {
                                            __auto_type size_expr = _mv_712.value;
                                            return stmt_extract_sizeof_type_opt(ctx, size_expr);
                                        } else if (!_mv_712.has_value) {
                                            return (slop_option_string){.has_value = false};
                                        }
                                    } else {
                                        return (slop_option_string){.has_value = false};
                                    }
                                }
                                default: {
                                    return (slop_option_string){.has_value = false};
                                }
                            }
                        } else if (!_mv_710.has_value) {
                            return (slop_option_string){.has_value = false};
                        }
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
        __auto_type _mv_713 = (*expr);
        switch (_mv_713.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_713.data.sym;
                {
                    __auto_type type_name = sym.name;
                    __auto_type _mv_714 = context_ctx_lookup_type(ctx, type_name);
                    if (_mv_714.has_value) {
                        __auto_type entry = _mv_714.value;
                        return (slop_option_string){.has_value = 1, .value = context_ctx_str(ctx, entry.c_name, SLOP_STR("*"))};
                    } else if (!_mv_714.has_value) {
                        return (slop_option_string){.has_value = false};
                    }
                }
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_713.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 2)) {
                        __auto_type _mv_715 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_715.has_value) {
                            __auto_type head_ptr = _mv_715.value;
                            __auto_type _mv_716 = (*head_ptr);
                            switch (_mv_716.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_716.data.sym;
                                    if (string_eq(head_sym.name, SLOP_STR("sizeof"))) {
                                        __auto_type _mv_717 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_717.has_value) {
                                            __auto_type type_expr = _mv_717.value;
                                            {
                                                __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                return (slop_option_string){.has_value = 1, .value = context_ctx_str(ctx, c_type, SLOP_STR("*"))};
                                            }
                                        } else if (!_mv_717.has_value) {
                                            return (slop_option_string){.has_value = false};
                                        }
                                    } else {
                                        return (slop_option_string){.has_value = false};
                                    }
                                }
                                default: {
                                    return (slop_option_string){.has_value = false};
                                }
                            }
                        } else if (!_mv_715.has_value) {
                            return (slop_option_string){.has_value = false};
                        }
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
    __auto_type _mv_718 = (*expr);
    switch (_mv_718.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_718.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_719 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_719.has_value) {
                        __auto_type head_expr = _mv_719.value;
                        __auto_type _mv_720 = (*head_expr);
                        switch (_mv_720.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_720.data.sym;
                                {
                                    __auto_type name = sym.name;
                                    return ((string_eq(name, SLOP_STR("let"))) || (string_eq(name, SLOP_STR("let*"))) || (string_eq(name, SLOP_STR("if"))) || (string_eq(name, SLOP_STR("when"))) || (string_eq(name, SLOP_STR("while"))) || (string_eq(name, SLOP_STR("for"))) || (string_eq(name, SLOP_STR("for-each"))) || (string_eq(name, SLOP_STR("set!"))) || (string_eq(name, SLOP_STR("do"))) || (string_eq(name, SLOP_STR("match"))) || (string_eq(name, SLOP_STR("cond"))) || (string_eq(name, SLOP_STR("with-arena"))));
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_719.has_value) {
                        return 0;
                    }
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
        __auto_type _mv_721 = (*expr);
        switch (_mv_721.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_721.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 2)) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid let: missing bindings"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    } else {
                        context_ctx_emit(ctx, SLOP_STR("{"));
                        context_ctx_indent(ctx);
                        context_ctx_push_scope(ctx);
                        __auto_type _mv_722 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_722.has_value) {
                            __auto_type bindings_expr = _mv_722.value;
                            __auto_type _mv_723 = (*bindings_expr);
                            switch (_mv_723.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type bindings_lst = _mv_723.data.lst;
                                    stmt_transpile_bindings(ctx, bindings_lst.items);
                                    break;
                                }
                                default: {
                                    context_ctx_add_error_at(ctx, SLOP_STR("invalid bindings"), context_ctx_sexpr_line(bindings_expr), context_ctx_sexpr_col(bindings_expr));
                                    break;
                                }
                            }
                        } else if (!_mv_722.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing bindings"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                        }
                        {
                            __auto_type i = 2;
                            while ((i < len)) {
                                __auto_type _mv_724 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_724.has_value) {
                                    __auto_type body_expr = _mv_724.value;
                                    {
                                        __auto_type is_last = (i == (len - 1));
                                        stmt_transpile_stmt(ctx, body_expr, (is_return && is_last));
                                    }
                                } else if (!_mv_724.has_value) {
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
        while ((i < len)) {
            __auto_type _mv_725 = ({ __auto_type _lst = bindings; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_725.has_value) {
                __auto_type binding_expr = _mv_725.value;
                stmt_transpile_single_binding(ctx, binding_expr);
            } else if (!_mv_725.has_value) {
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
        __auto_type _mv_726 = (*binding);
        switch (_mv_726.tag) {
            case types_SExpr_lst:
            {
                __auto_type binding_lst = _mv_726.data.lst;
                {
                    __auto_type items = binding_lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    {
                        __auto_type has_mut = stmt_binding_has_mut(items);
                        __auto_type start_idx = ((stmt_binding_has_mut(items)) ? 1 : 0);
                        if (((len - start_idx) < 2)) {
                            context_ctx_add_error_at(ctx, SLOP_STR("invalid binding: need name and value"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                        } else {
                            __auto_type _mv_727 = ({ __auto_type _lst = items; size_t _idx = (size_t)start_idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_727.has_value) {
                                __auto_type name_expr = _mv_727.value;
                                __auto_type _mv_728 = (*name_expr);
                                switch (_mv_728.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type name_sym = _mv_728.data.sym;
                                        {
                                            __auto_type raw_name = name_sym.name;
                                            __auto_type var_name = ctype_to_c_name(arena, raw_name);
                                            if (((len - start_idx) >= 3)) {
                                                __auto_type _mv_729 = ({ __auto_type _lst = items; size_t _idx = (size_t)(start_idx + 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_729.has_value) {
                                                    __auto_type type_expr = _mv_729.value;
                                                    __auto_type _mv_730 = ({ __auto_type _lst = items; size_t _idx = (size_t)(start_idx + 2); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_730.has_value) {
                                                        __auto_type init_expr = _mv_730.value;
                                                        {
                                                            __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                            {
                                                                __auto_type final_init = ((strlib_starts_with(c_type, SLOP_STR("slop_option_"))) ? ({ __auto_type some_val = stmt_get_some_value(init_expr); ({ __auto_type _mv = some_val; _mv.has_value ? ({ __auto_type val_expr = _mv.value; ({ __auto_type val_c = expr_transpile_expr(ctx, val_expr); context_ctx_str5(ctx, SLOP_STR("("), c_type, SLOP_STR("){.has_value = 1, .value = "), val_c, SLOP_STR("}")); }); }) : (((stmt_is_none_form(init_expr)) ? context_ctx_str3(ctx, SLOP_STR("("), c_type, SLOP_STR("){.has_value = false}")) : expr_transpile_expr(ctx, init_expr))); }); }) : expr_transpile_expr(ctx, init_expr));
                                                                context_ctx_emit(ctx, context_ctx_str5(ctx, c_type, SLOP_STR(" "), var_name, SLOP_STR(" = "), context_ctx_str(ctx, final_init, SLOP_STR(";"))));
                                                                {
                                                                    __auto_type slop_type_str = stmt_sexpr_to_type_string(arena, type_expr);
                                                                    context_ctx_bind_var(ctx, (context_VarEntry){raw_name, var_name, c_type, slop_type_str, 0, has_mut, 0, SLOP_STR(""), SLOP_STR("")});
                                                                }
                                                            }
                                                        }
                                                    } else if (!_mv_730.has_value) {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("missing init"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                                                    }
                                                } else if (!_mv_729.has_value) {
                                                    context_ctx_add_error_at(ctx, SLOP_STR("missing type"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                                                }
                                            } else {
                                                __auto_type _mv_731 = ({ __auto_type _lst = items; size_t _idx = (size_t)(start_idx + 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_731.has_value) {
                                                    __auto_type init_expr = _mv_731.value;
                                                    {
                                                        __auto_type init_c = expr_transpile_expr(ctx, init_expr);
                                                        __auto_type inferred_slop_type = expr_infer_expr_slop_type(ctx, init_expr);
                                                        __auto_type ptr_type_opt = stmt_get_arena_alloc_ptr_type(ctx, init_expr);
                                                        __auto_type _mv_732 = ptr_type_opt;
                                                        if (_mv_732.has_value) {
                                                            __auto_type ptr_type = _mv_732.value;
                                                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("__auto_type "), var_name, SLOP_STR(" = "), init_c, SLOP_STR(";")));
                                                            context_ctx_bind_var(ctx, (context_VarEntry){raw_name, var_name, ptr_type, inferred_slop_type, 1, has_mut, 0, SLOP_STR(""), SLOP_STR("")});
                                                        } else if (!_mv_732.has_value) {
                                                            {
                                                                __auto_type inferred_type = expr_infer_expr_c_type(ctx, init_expr);
                                                                __auto_type lambda_info = context_ctx_get_last_lambda_info(ctx);
                                                                __auto_type use_explicit_type = (has_mut && stmt_is_simple_primitive_c_type(inferred_type));
                                                                __auto_type decl_type = ((use_explicit_type) ? context_ctx_str(ctx, inferred_type, SLOP_STR(" ")) : SLOP_STR("__auto_type "));
                                                                context_ctx_emit(ctx, context_ctx_str5(ctx, decl_type, var_name, SLOP_STR(" = "), init_c, SLOP_STR(";")));
                                                                if (lambda_info.is_closure) {
                                                                    context_ctx_bind_var(ctx, (context_VarEntry){raw_name, var_name, SLOP_STR("slop_closure_t"), inferred_slop_type, 0, has_mut, 1, lambda_info.env_type, lambda_info.lambda_name});
                                                                    context_ctx_clear_last_lambda_info(ctx);
                                                                } else {
                                                                    context_ctx_bind_var(ctx, (context_VarEntry){raw_name, var_name, inferred_type, inferred_slop_type, strlib_ends_with(inferred_type, SLOP_STR("*")), has_mut, 0, SLOP_STR(""), SLOP_STR("")});
                                                                }
                                                            }
                                                        }
                                                    }
                                                } else if (!_mv_731.has_value) {
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
                            } else if (!_mv_727.has_value) {
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
    if ((((int64_t)((items).len)) < 1)) {
        return 0;
    } else {
        __auto_type _mv_733 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_733.has_value) {
            __auto_type first = _mv_733.value;
            __auto_type _mv_734 = (*first);
            switch (_mv_734.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_734.data.sym;
                    return string_eq(sym.name, SLOP_STR("mut"));
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_733.has_value) {
            return 0;
        }
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
        __auto_type _mv_735 = (*expr);
        switch (_mv_735.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_735.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 2)) {
                        __auto_type _mv_736 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_736.has_value) {
                            __auto_type head_expr = _mv_736.value;
                            __auto_type _mv_737 = (*head_expr);
                            switch (_mv_737.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_737.data.sym;
                                    if (string_eq(sym.name, SLOP_STR("some"))) {
                                        __auto_type _mv_738 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_738.has_value) {
                                            __auto_type val = _mv_738.value;
                                            result = (slop_option_types_SExpr_ptr){.has_value = 1, .value = val};
                                        } else if (!_mv_738.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_736.has_value) {
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
    __auto_type _mv_739 = (*expr);
    switch (_mv_739.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_739.data.sym;
            return string_eq(sym.name, SLOP_STR("none"));
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_739.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 1)) {
                    __auto_type _mv_740 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_740.has_value) {
                        __auto_type head = _mv_740.value;
                        __auto_type _mv_741 = (*head);
                        switch (_mv_741.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_741.data.sym;
                                return string_eq(sym.name, SLOP_STR("none"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_740.has_value) {
                        return 0;
                    }
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
    __auto_type _mv_742 = (*expr);
    switch (_mv_742.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_742.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len < 3)) {
                    context_ctx_add_error_at(ctx, SLOP_STR("invalid if: need condition and then-branch"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                } else {
                    __auto_type _mv_743 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_743.has_value) {
                        __auto_type cond_expr = _mv_743.value;
                        {
                            __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), cond_c, SLOP_STR(") {")));
                            context_ctx_indent(ctx);
                            __auto_type _mv_744 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_744.has_value) {
                                __auto_type then_expr = _mv_744.value;
                                stmt_transpile_stmt(ctx, then_expr, is_return);
                            } else if (!_mv_744.has_value) {
                            }
                            context_ctx_dedent(ctx);
                            if ((len >= 4)) {
                                context_ctx_emit(ctx, SLOP_STR("} else {"));
                                context_ctx_indent(ctx);
                                __auto_type _mv_745 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_745.has_value) {
                                    __auto_type else_expr = _mv_745.value;
                                    stmt_transpile_stmt(ctx, else_expr, is_return);
                                } else if (!_mv_745.has_value) {
                                }
                                context_ctx_dedent(ctx);
                                context_ctx_emit(ctx, SLOP_STR("}"));
                            } else {
                                context_ctx_emit(ctx, SLOP_STR("}"));
                            }
                        }
                    } else if (!_mv_743.has_value) {
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
    __auto_type _mv_746 = (*expr);
    switch (_mv_746.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_746.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len < 3)) {
                    context_ctx_add_error_at(ctx, SLOP_STR("invalid when: need condition and body"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                } else {
                    __auto_type _mv_747 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_747.has_value) {
                        __auto_type cond_expr = _mv_747.value;
                        {
                            __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), cond_c, SLOP_STR(") {")));
                            context_ctx_indent(ctx);
                            {
                                __auto_type i = 2;
                                while ((i < len)) {
                                    __auto_type _mv_748 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_748.has_value) {
                                        __auto_type body_expr = _mv_748.value;
                                        stmt_transpile_stmt(ctx, body_expr, 0);
                                    } else if (!_mv_748.has_value) {
                                    }
                                    i = (i + 1);
                                }
                            }
                            context_ctx_dedent(ctx);
                            context_ctx_emit(ctx, SLOP_STR("}"));
                        }
                    } else if (!_mv_747.has_value) {
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
    __auto_type _mv_749 = (*expr);
    switch (_mv_749.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_749.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len < 3)) {
                    context_ctx_add_error_at(ctx, SLOP_STR("invalid while: need condition and body"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                } else {
                    __auto_type _mv_750 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_750.has_value) {
                        __auto_type cond_expr = _mv_750.value;
                        {
                            __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("while ("), cond_c, SLOP_STR(") {")));
                            context_ctx_indent(ctx);
                            {
                                __auto_type i = 2;
                                while ((i < len)) {
                                    __auto_type _mv_751 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_751.has_value) {
                                        __auto_type body_expr = _mv_751.value;
                                        stmt_transpile_stmt(ctx, body_expr, 0);
                                    } else if (!_mv_751.has_value) {
                                    }
                                    i = (i + 1);
                                }
                            }
                            context_ctx_dedent(ctx);
                            context_ctx_emit(ctx, SLOP_STR("}"));
                        }
                    } else if (!_mv_750.has_value) {
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
        __auto_type _mv_752 = (*expr);
        switch (_mv_752.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_752.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len == 5)) {
                        stmt_transpile_typed_field_set(ctx, items);
                    } else if ((len == 4)) {
                        stmt_transpile_field_set(ctx, items);
                    } else if ((len == 3)) {
                        __auto_type _mv_753 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_753.has_value) {
                            __auto_type target_expr = _mv_753.value;
                            __auto_type _mv_754 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_754.has_value) {
                                __auto_type value_expr = _mv_754.value;
                                {
                                    __auto_type target_c = expr_transpile_expr(ctx, target_expr);
                                    __auto_type target_type_opt = stmt_get_var_c_type(ctx, target_expr);
                                    __auto_type _mv_755 = target_type_opt;
                                    if (_mv_755.has_value) {
                                        __auto_type target_type = _mv_755.value;
                                        if (strlib_starts_with(target_type, SLOP_STR("slop_option_"))) {
                                            {
                                                __auto_type some_val_opt = stmt_get_some_value(value_expr);
                                                __auto_type _mv_756 = some_val_opt;
                                                if (_mv_756.has_value) {
                                                    __auto_type val_expr = _mv_756.value;
                                                    {
                                                        __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                        context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str5(ctx, SLOP_STR(" = ("), target_type, SLOP_STR("){.has_value = 1, .value = "), val_c, SLOP_STR("};"))));
                                                    }
                                                } else if (!_mv_756.has_value) {
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
                                    } else if (!_mv_755.has_value) {
                                        {
                                            __auto_type some_val_opt = stmt_get_some_value(value_expr);
                                            __auto_type _mv_757 = some_val_opt;
                                            if (_mv_757.has_value) {
                                                __auto_type inner_expr = _mv_757.value;
                                                {
                                                    __auto_type inner_c = expr_transpile_expr(ctx, inner_expr);
                                                    __auto_type inner_type = expr_infer_expr_c_type(ctx, inner_expr);
                                                    __auto_type option_type = expr_c_type_to_option_type_name(ctx, inner_type);
                                                    context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str5(ctx, SLOP_STR(" = ("), option_type, SLOP_STR("){.has_value = 1, .value = "), inner_c, SLOP_STR("};"))));
                                                }
                                            } else if (!_mv_757.has_value) {
                                                if (stmt_is_none_form(value_expr)) {
                                                    __auto_type _mv_758 = context_ctx_get_current_return_type(ctx);
                                                    if (_mv_758.has_value) {
                                                        __auto_type ret_type = _mv_758.value;
                                                        if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                                                            context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str3(ctx, SLOP_STR(" = ("), ret_type, SLOP_STR("){.has_value = false};"))));
                                                        } else {
                                                            {
                                                                __auto_type value_c = expr_transpile_expr(ctx, value_expr);
                                                                context_ctx_emit(ctx, context_ctx_str4(ctx, target_c, SLOP_STR(" = "), value_c, SLOP_STR(";")));
                                                            }
                                                        }
                                                    } else if (!_mv_758.has_value) {
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
                            } else if (!_mv_754.has_value) {
                                context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                            }
                        } else if (!_mv_753.has_value) {
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
    __auto_type _mv_759 = (*expr);
    switch (_mv_759.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_759.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_760 = context_ctx_lookup_var(ctx, name);
                if (_mv_760.has_value) {
                    __auto_type var_entry = _mv_760.value;
                    return (slop_option_string){.has_value = 1, .value = var_entry.c_type};
                } else if (!_mv_760.has_value) {
                    return (slop_option_string){.has_value = false};
                }
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
    __auto_type _mv_761 = (*expr);
    switch (_mv_761.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_761.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_762 = context_ctx_lookup_var(ctx, name);
                if (_mv_762.has_value) {
                    __auto_type var_entry = _mv_762.value;
                    {
                        __auto_type c_type = var_entry.c_type;
                        return strlib_ends_with(c_type, SLOP_STR("*"));
                    }
                } else if (!_mv_762.has_value) {
                    return 0;
                }
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
        __auto_type _mv_763 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_763.has_value) {
            __auto_type target_expr = _mv_763.value;
            __auto_type _mv_764 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_764.has_value) {
                __auto_type field_expr = _mv_764.value;
                __auto_type _mv_765 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_765.has_value) {
                    __auto_type value_expr = _mv_765.value;
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
                } else if (!_mv_765.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_ctx_sexpr_line(target_expr), context_ctx_sexpr_col(target_expr));
                }
            } else if (!_mv_764.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing set! field"), context_ctx_sexpr_line(target_expr), context_ctx_sexpr_col(target_expr));
            }
        } else if (!_mv_763.has_value) {
            context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        }
    }
}

void stmt_transpile_typed_field_set(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_766 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_766.has_value) {
            __auto_type target_expr = _mv_766.value;
            __auto_type _mv_767 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_767.has_value) {
                __auto_type field_expr = _mv_767.value;
                __auto_type _mv_768 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_768.has_value) {
                    __auto_type type_expr = _mv_768.value;
                    __auto_type _mv_769 = ({ __auto_type _lst = items; size_t _idx = (size_t)4; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_769.has_value) {
                        __auto_type value_expr = _mv_769.value;
                        {
                            __auto_type field_name = stmt_get_symbol_name(arena, field_expr);
                            __auto_type c_type = ctype_to_c_type(arena, type_expr);
                            {
                                __auto_type target_access = ((stmt_is_deref_expr(target_expr)) ? ({ __auto_type inner_expr = stmt_get_deref_inner(target_expr); __auto_type inner_c = expr_transpile_expr(ctx, inner_expr); context_ctx_str(ctx, SLOP_STR("(*"), context_ctx_str(ctx, inner_c, SLOP_STR(")."))); }) : ({ __auto_type target_c = expr_transpile_expr(ctx, target_expr); __auto_type is_ptr = stmt_is_pointer_target(ctx, target_expr); ((is_ptr) ? context_ctx_str(ctx, target_c, SLOP_STR("->")) : context_ctx_str(ctx, target_c, SLOP_STR("."))); }));
                                if (strlib_starts_with(c_type, SLOP_STR("slop_option_"))) {
                                    if (stmt_is_none_form(value_expr)) {
                                        context_ctx_emit(ctx, context_ctx_str(ctx, target_access, context_ctx_str(ctx, field_name, context_ctx_str3(ctx, SLOP_STR(" = ("), c_type, SLOP_STR("){.has_value = false};")))));
                                    } else {
                                        __auto_type _mv_770 = stmt_get_some_value(value_expr);
                                        if (_mv_770.has_value) {
                                            __auto_type inner_val = _mv_770.value;
                                            {
                                                __auto_type val_c = expr_transpile_expr(ctx, inner_val);
                                                context_ctx_emit(ctx, context_ctx_str(ctx, target_access, context_ctx_str(ctx, field_name, context_ctx_str5(ctx, SLOP_STR(" = ("), c_type, SLOP_STR("){.has_value = 1, .value = "), val_c, SLOP_STR("};")))));
                                            }
                                        } else if (!_mv_770.has_value) {
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
                    } else if (!_mv_769.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_ctx_sexpr_line(type_expr), context_ctx_sexpr_col(type_expr));
                    }
                } else if (!_mv_768.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("missing set! type"), context_ctx_sexpr_line(field_expr), context_ctx_sexpr_col(field_expr));
                }
            } else if (!_mv_767.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing set! field"), context_ctx_sexpr_line(target_expr), context_ctx_sexpr_col(target_expr));
            }
        } else if (!_mv_766.has_value) {
            context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        }
    }
}

uint8_t stmt_is_deref_expr(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_771 = (*expr);
    switch (_mv_771.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_771.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_772 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_772.has_value) {
                        __auto_type head = _mv_772.value;
                        __auto_type _mv_773 = (*head);
                        switch (_mv_773.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_773.data.sym;
                                return string_eq(sym.name, SLOP_STR("deref"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_772.has_value) {
                        return 0;
                    }
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
    __auto_type _mv_774 = (*expr);
    switch (_mv_774.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_774.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type _mv_775 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_775.has_value) {
                    __auto_type inner = _mv_775.value;
                    return inner;
                } else if (!_mv_775.has_value) {
                    return expr;
                }
            }
        }
        default: {
            return expr;
        }
    }
}

slop_string stmt_get_symbol_name(slop_arena* arena, types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_776 = (*expr);
    switch (_mv_776.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_776.data.sym;
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
    __auto_type _mv_777 = (*expr);
    switch (_mv_777.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_777.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type i = 1;
                while ((i < len)) {
                    __auto_type _mv_778 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_778.has_value) {
                        __auto_type body_expr = _mv_778.value;
                        {
                            __auto_type is_last = (i == (len - 1));
                            stmt_transpile_stmt(ctx, body_expr, (is_return && is_last));
                        }
                    } else if (!_mv_778.has_value) {
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
    __auto_type _mv_779 = (*expr);
    switch (_mv_779.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_779.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len < 2)) {
                    context_ctx_add_error_at(ctx, SLOP_STR("invalid with-arena: need size"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                } else {
                    {
                        __auto_type is_named = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type item1 = _mv.value; string_eq(parser_sexpr_get_symbol_name(item1), SLOP_STR(":as")); }) : (0); });
                        __auto_type arena_name = ((is_named) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type name_expr = _mv.value; parser_sexpr_get_symbol_name(name_expr); }) : (SLOP_STR("arena")); }) : SLOP_STR("arena"));
                        __auto_type size_idx = ((is_named) ? 3 : 1);
                        __auto_type body_start = ((is_named) ? 4 : 2);
                        __auto_type c_local = ((is_named) ? string_concat((*ctx).arena, SLOP_STR("_arena_"), arena_name) : SLOP_STR("_arena"));
                        if ((is_named && (len < 4))) {
                            context_ctx_add_error_at(ctx, SLOP_STR("with-arena :as requires name and size"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                        } else {
                            context_ctx_emit(ctx, SLOP_STR("{"));
                            context_ctx_indent(ctx);
                            context_ctx_push_scope(ctx);
                            __auto_type _mv_780 = ({ __auto_type _lst = items; size_t _idx = (size_t)size_idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_780.has_value) {
                                __auto_type size_expr = _mv_780.value;
                                {
                                    __auto_type size_c = expr_transpile_expr(ctx, size_expr);
                                    context_ctx_emit(ctx, SLOP_STR("#ifdef SLOP_DEBUG"));
                                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("SLOP_PRE(("), size_c, SLOP_STR(") > 0, \"with-arena size must be positive\");")));
                                    context_ctx_emit(ctx, SLOP_STR("#endif"));
                                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("slop_arena "), c_local, SLOP_STR(" = slop_arena_new("), size_c, SLOP_STR(");")));
                                    context_ctx_emit(ctx, SLOP_STR("#ifdef SLOP_DEBUG"));
                                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("SLOP_PRE("), c_local, SLOP_STR(".base != NULL, \"arena allocation failed\");")));
                                    context_ctx_emit(ctx, SLOP_STR("#endif"));
                                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("slop_arena* "), arena_name, SLOP_STR(" = &"), c_local, SLOP_STR(";")));
                                }
                            } else if (!_mv_780.has_value) {
                                context_ctx_add_error_at(ctx, SLOP_STR("missing size"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                            }
                            context_ctx_bind_var(ctx, (context_VarEntry){arena_name, arena_name, SLOP_STR("slop_arena*"), SLOP_STR(""), 1, 0, 0, SLOP_STR(""), SLOP_STR("")});
                            {
                                __auto_type i = body_start;
                                while ((i < len)) {
                                    __auto_type _mv_781 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_781.has_value) {
                                        __auto_type body_expr = _mv_781.value;
                                        {
                                            __auto_type is_last = (i == (len - 1));
                                            stmt_transpile_stmt(ctx, body_expr, (is_return && is_last));
                                        }
                                    } else if (!_mv_781.has_value) {
                                    }
                                    i = (i + 1);
                                }
                            }
                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("slop_arena_free("), arena_name, SLOP_STR(");")));
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
    __auto_type _mv_782 = (*expr);
    switch (_mv_782.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_782.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type i = 1;
                __auto_type first = 1;
                while ((i < len)) {
                    __auto_type _mv_783 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_783.has_value) {
                        __auto_type clause_expr = _mv_783.value;
                        __auto_type _mv_784 = (*clause_expr);
                        switch (_mv_784.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type clause_lst = _mv_784.data.lst;
                                {
                                    __auto_type clause_items = clause_lst.items;
                                    __auto_type clause_len = ((int64_t)((clause_items).len));
                                    if ((clause_len < 1)) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("invalid cond clause"), context_ctx_sexpr_line(clause_expr), context_ctx_sexpr_col(clause_expr));
                                    } else {
                                        __auto_type _mv_785 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_785.has_value) {
                                            __auto_type test_expr = _mv_785.value;
                                            __auto_type _mv_786 = (*test_expr);
                                            switch (_mv_786.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type sym = _mv_786.data.sym;
                                                    if (string_eq(sym.name, SLOP_STR("else"))) {
                                                        context_ctx_emit(ctx, SLOP_STR("} else {"));
                                                        context_ctx_indent(ctx);
                                                        stmt_transpile_cond_body(ctx, clause_items, 1, is_return);
                                                        context_ctx_dedent(ctx);
                                                    } else {
                                                        {
                                                            __auto_type cond_c = expr_transpile_expr(ctx, test_expr);
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
                                                        __auto_type cond_c = expr_transpile_expr(ctx, test_expr);
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
                                        } else if (!_mv_785.has_value) {
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
                    } else if (!_mv_783.has_value) {
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
        while ((i < len)) {
            __auto_type _mv_787 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_787.has_value) {
                __auto_type body_expr = _mv_787.value;
                {
                    __auto_type is_last = (i == (len - 1));
                    stmt_transpile_stmt(ctx, body_expr, (is_return && is_last));
                }
            } else if (!_mv_787.has_value) {
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
        __auto_type _mv_788 = (*expr);
        switch (_mv_788.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_788.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 2)) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid for: need binding"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    } else {
                        __auto_type _mv_789 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_789.has_value) {
                            __auto_type binding_expr = _mv_789.value;
                            __auto_type _mv_790 = (*binding_expr);
                            switch (_mv_790.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type binding_lst = _mv_790.data.lst;
                                    {
                                        __auto_type binding_items = binding_lst.items;
                                        __auto_type binding_len = ((int64_t)((binding_items).len));
                                        if ((binding_len < 3)) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("for binding needs (var start end)"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                                        } else {
                                            __auto_type _mv_791 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_791.has_value) {
                                                __auto_type var_expr = _mv_791.value;
                                                __auto_type _mv_792 = (*var_expr);
                                                switch (_mv_792.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type var_sym = _mv_792.data.sym;
                                                        {
                                                            __auto_type var_name = ctype_to_c_name(arena, var_sym.name);
                                                            __auto_type _mv_793 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_793.has_value) {
                                                                __auto_type start_expr = _mv_793.value;
                                                                __auto_type _mv_794 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                if (_mv_794.has_value) {
                                                                    __auto_type end_expr = _mv_794.value;
                                                                    {
                                                                        __auto_type start_c = expr_transpile_expr(ctx, start_expr);
                                                                        __auto_type end_c = expr_transpile_expr(ctx, end_expr);
                                                                        context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("for (int64_t "), var_name, SLOP_STR(" = "), start_c, context_ctx_str5(ctx, SLOP_STR("; "), var_name, SLOP_STR(" < "), end_c, context_ctx_str3(ctx, SLOP_STR("; "), var_name, SLOP_STR("++) {")))));
                                                                        context_ctx_indent(ctx);
                                                                        context_ctx_push_scope(ctx);
                                                                        context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, SLOP_STR("int64_t"), SLOP_STR(""), 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                                                        {
                                                                            __auto_type i = 2;
                                                                            while ((i < len)) {
                                                                                __auto_type _mv_795 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                                if (_mv_795.has_value) {
                                                                                    __auto_type body_expr = _mv_795.value;
                                                                                    stmt_transpile_stmt(ctx, body_expr, 0);
                                                                                } else if (!_mv_795.has_value) {
                                                                                }
                                                                                i = (i + 1);
                                                                            }
                                                                        }
                                                                        context_ctx_pop_scope(ctx);
                                                                        context_ctx_dedent(ctx);
                                                                        context_ctx_emit(ctx, SLOP_STR("}"));
                                                                    }
                                                                } else if (!_mv_794.has_value) {
                                                                    context_ctx_add_error_at(ctx, SLOP_STR("missing end"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                                                                }
                                                            } else if (!_mv_793.has_value) {
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
                                            } else if (!_mv_791.has_value) {
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
                        } else if (!_mv_789.has_value) {
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

void stmt_transpile_for_each(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_796 = (*expr);
        switch (_mv_796.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_796.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 2)) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid for-each: need binding"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    } else {
                        __auto_type _mv_797 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_797.has_value) {
                            __auto_type binding_expr = _mv_797.value;
                            __auto_type _mv_798 = (*binding_expr);
                            switch (_mv_798.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type binding_lst = _mv_798.data.lst;
                                    {
                                        __auto_type binding_items = binding_lst.items;
                                        __auto_type binding_len = ((int64_t)((binding_items).len));
                                        if ((binding_len < 2)) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("for-each binding needs (var coll)"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                                        } else {
                                            __auto_type _mv_799 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_799.has_value) {
                                                __auto_type var_expr = _mv_799.value;
                                                __auto_type _mv_800 = (*var_expr);
                                                switch (_mv_800.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type var_sym = _mv_800.data.sym;
                                                        {
                                                            __auto_type var_name = ctype_to_c_name(arena, var_sym.name);
                                                            __auto_type _mv_801 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_801.has_value) {
                                                                __auto_type coll_expr = _mv_801.value;
                                                                {
                                                                    __auto_type coll_c = expr_transpile_expr(ctx, coll_expr);
                                                                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("for (size_t _i = 0; _i < "), coll_c, SLOP_STR(".len; _i++) {")));
                                                                    context_ctx_indent(ctx);
                                                                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("__auto_type "), var_name, SLOP_STR(" = "), coll_c, SLOP_STR(".data[_i];")));
                                                                    context_ctx_push_scope(ctx);
                                                                    {
                                                                        __auto_type elem_slop_type = expr_infer_collection_element_slop_type(ctx, coll_expr);
                                                                        context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, SLOP_STR("auto"), elem_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                                                    }
                                                                    {
                                                                        __auto_type i = 2;
                                                                        while ((i < len)) {
                                                                            __auto_type _mv_802 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                            if (_mv_802.has_value) {
                                                                                __auto_type body_expr = _mv_802.value;
                                                                                stmt_transpile_stmt(ctx, body_expr, 0);
                                                                            } else if (!_mv_802.has_value) {
                                                                            }
                                                                            i = (i + 1);
                                                                        }
                                                                    }
                                                                    context_ctx_pop_scope(ctx);
                                                                    context_ctx_dedent(ctx);
                                                                    context_ctx_emit(ctx, SLOP_STR("}"));
                                                                }
                                                            } else if (!_mv_801.has_value) {
                                                                context_ctx_add_error_at(ctx, SLOP_STR("missing collection"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                                                            }
                                                        }
                                                        break;
                                                    }
                                                    default: {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("for-each var must be symbol"), context_ctx_sexpr_line(var_expr), context_ctx_sexpr_col(var_expr));
                                                        break;
                                                    }
                                                }
                                            } else if (!_mv_799.has_value) {
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
                        } else if (!_mv_797.has_value) {
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
    __auto_type _mv_803 = (*expr);
    switch (_mv_803.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_803.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    context_ctx_add_error_at(ctx, SLOP_STR("empty list"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                } else {
                    __auto_type _mv_804 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_804.has_value) {
                        __auto_type head_expr = _mv_804.value;
                        __auto_type _mv_805 = (*head_expr);
                        switch (_mv_805.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_805.data.sym;
                                {
                                    __auto_type op = sym.name;
                                    if ((string_eq(op, SLOP_STR("let")) || string_eq(op, SLOP_STR("let*")))) {
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
                                        if ((((int64_t)((items).len)) < 2)) {
                                            context_ctx_emit(ctx, SLOP_STR("return;"));
                                        } else {
                                            __auto_type _mv_806 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_806.has_value) {
                                                __auto_type val_expr = _mv_806.value;
                                                stmt_emit_typed_return_expr(ctx, val_expr);
                                            } else if (!_mv_806.has_value) {
                                                context_ctx_emit(ctx, SLOP_STR("return;"));
                                            }
                                        }
                                    } else if (string_eq(op, SLOP_STR("break"))) {
                                        context_ctx_emit(ctx, SLOP_STR("break;"));
                                    } else if (string_eq(op, SLOP_STR("continue"))) {
                                        context_ctx_emit(ctx, SLOP_STR("continue;"));
                                    } else {
                                        if (is_return) {
                                            stmt_emit_typed_return_expr(ctx, expr);
                                        } else {
                                            context_ctx_emit(ctx, context_ctx_str(ctx, expr_transpile_expr(ctx, expr), SLOP_STR(";")));
                                        }
                                    }
                                }
                                break;
                            }
                            default: {
                                if (is_return) {
                                    stmt_emit_typed_return_expr(ctx, expr);
                                } else {
                                    context_ctx_emit(ctx, context_ctx_str(ctx, expr_transpile_expr(ctx, expr), SLOP_STR(";")));
                                }
                                break;
                            }
                        }
                    } else if (!_mv_804.has_value) {
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
                context_ctx_emit(ctx, context_ctx_str(ctx, expr_transpile_expr(ctx, expr), SLOP_STR(";")));
            }
            break;
        }
    }
}

void stmt_emit_typed_return_expr(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_807 = (*expr);
    switch (_mv_807.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_807.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                } else {
                    __auto_type _mv_808 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_808.has_value) {
                        __auto_type head = _mv_808.value;
                        __auto_type _mv_809 = (*head);
                        switch (_mv_809.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_809.data.sym;
                                {
                                    __auto_type op = sym.name;
                                    if (string_eq(op, SLOP_STR("some"))) {
                                        __auto_type _mv_810 = context_ctx_get_current_return_type(ctx);
                                        if (_mv_810.has_value) {
                                            __auto_type ret_type = _mv_810.value;
                                            if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                                                if ((((int64_t)((items).len)) < 2)) {
                                                    stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                                } else {
                                                    __auto_type _mv_811 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_811.has_value) {
                                                        __auto_type inner_expr = _mv_811.value;
                                                        {
                                                            __auto_type inner_c = expr_transpile_expr(ctx, inner_expr);
                                                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("return ("), ret_type, SLOP_STR("){.has_value = 1, .value = "), inner_c, SLOP_STR("};")));
                                                        }
                                                    } else if (!_mv_811.has_value) {
                                                        stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                                    }
                                                }
                                            } else {
                                                stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                            }
                                        } else if (!_mv_810.has_value) {
                                            stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                        }
                                    } else if (string_eq(op, SLOP_STR("none"))) {
                                        __auto_type _mv_812 = context_ctx_get_current_return_type(ctx);
                                        if (_mv_812.has_value) {
                                            __auto_type ret_type = _mv_812.value;
                                            if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                                                context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("return ("), ret_type, SLOP_STR("){.has_value = false};")));
                                            } else {
                                                stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                            }
                                        } else if (!_mv_812.has_value) {
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
                    } else if (!_mv_808.has_value) {
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
            __auto_type _mv_813 = context_ctx_get_current_return_type(ctx);
            if (_mv_813.has_value) {
                __auto_type ret_type = _mv_813.value;
                if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                    final_code = context_ctx_str3(ctx, SLOP_STR("("), ret_type, SLOP_STR("){.has_value = false}"));
                }
            } else if (!_mv_813.has_value) {
            }
        } else {
            __auto_type _mv_814 = context_ctx_get_current_return_type(ctx);
            if (_mv_814.has_value) {
                __auto_type ret_type = _mv_814.value;
                if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                    __auto_type _mv_815 = context_ctx_lookup_var(ctx, code);
                    if (_mv_815.has_value) {
                        __auto_type var_entry = _mv_815.value;
                        {
                            __auto_type var_type = var_entry.c_type;
                            if ((string_eq(var_type, SLOP_STR("_slop_option_generic")) || string_eq(var_type, SLOP_STR("auto")))) {
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
                    } else if (!_mv_815.has_value) {
                    }
                }
            } else if (!_mv_814.has_value) {
            }
        }
        if (context_ctx_is_capture_retval(ctx)) {
            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("_retval = "), final_code, SLOP_STR(";")));
        } else {
            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("return "), final_code, SLOP_STR(";")));
        }
    }
}

