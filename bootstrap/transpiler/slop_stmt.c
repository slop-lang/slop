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
    __auto_type _mv_578 = (*expr);
    switch (_mv_578.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_578.data.sym;
            return sym.name;
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_578.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type result = SLOP_STR("(");
                __auto_type i = 0;
                while ((i < len)) {
                    __auto_type _mv_579 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_579.has_value) {
                        __auto_type item_expr = _mv_579.value;
                        {
                            __auto_type item_str = ctype_sexpr_to_type_string(arena, item_expr);
                            if ((i > 0)) {
                                result = string_concat(arena, result, string_concat(arena, SLOP_STR(" "), item_str));
                            } else {
                                result = string_concat(arena, result, item_str);
                            }
                        }
                    } else if (!_mv_579.has_value) {
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
        __auto_type _mv_580 = (*expr);
        switch (_mv_580.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_580.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 3)) {
                        __auto_type _mv_581 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_581.has_value) {
                            __auto_type head_ptr = _mv_581.value;
                            __auto_type _mv_582 = (*head_ptr);
                            switch (_mv_582.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_582.data.sym;
                                    if (string_eq(head_sym.name, SLOP_STR("arena-alloc"))) {
                                        __auto_type _mv_583 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_583.has_value) {
                                            __auto_type size_expr = _mv_583.value;
                                            return stmt_extract_sizeof_type_opt(ctx, size_expr);
                                        } else if (!_mv_583.has_value) {
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
                        } else if (!_mv_581.has_value) {
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
        __auto_type _mv_584 = (*expr);
        switch (_mv_584.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_584.data.sym;
                {
                    __auto_type type_name = sym.name;
                    __auto_type _mv_585 = context_ctx_lookup_type(ctx, type_name);
                    if (_mv_585.has_value) {
                        __auto_type entry = _mv_585.value;
                        return (slop_option_string){.has_value = 1, .value = context_ctx_str(ctx, entry.c_name, SLOP_STR("*"))};
                    } else if (!_mv_585.has_value) {
                        return (slop_option_string){.has_value = false};
                    }
                }
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_584.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 2)) {
                        __auto_type _mv_586 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_586.has_value) {
                            __auto_type head_ptr = _mv_586.value;
                            __auto_type _mv_587 = (*head_ptr);
                            switch (_mv_587.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_587.data.sym;
                                    if (string_eq(head_sym.name, SLOP_STR("sizeof"))) {
                                        __auto_type _mv_588 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_588.has_value) {
                                            __auto_type type_expr = _mv_588.value;
                                            {
                                                __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                return (slop_option_string){.has_value = 1, .value = context_ctx_str(ctx, c_type, SLOP_STR("*"))};
                                            }
                                        } else if (!_mv_588.has_value) {
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
                        } else if (!_mv_586.has_value) {
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
    __auto_type _mv_589 = (*expr);
    switch (_mv_589.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_589.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_590 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_590.has_value) {
                        __auto_type head_expr = _mv_590.value;
                        __auto_type _mv_591 = (*head_expr);
                        switch (_mv_591.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_591.data.sym;
                                {
                                    __auto_type name = sym.name;
                                    return ((string_eq(name, SLOP_STR("let"))) || (string_eq(name, SLOP_STR("let*"))) || (string_eq(name, SLOP_STR("if"))) || (string_eq(name, SLOP_STR("when"))) || (string_eq(name, SLOP_STR("while"))) || (string_eq(name, SLOP_STR("for"))) || (string_eq(name, SLOP_STR("for-each"))) || (string_eq(name, SLOP_STR("set!"))) || (string_eq(name, SLOP_STR("do"))) || (string_eq(name, SLOP_STR("match"))) || (string_eq(name, SLOP_STR("cond"))) || (string_eq(name, SLOP_STR("with-arena"))));
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_590.has_value) {
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
        __auto_type _mv_592 = (*expr);
        switch (_mv_592.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_592.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 2)) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid let: missing bindings"), context_sexpr_line(expr), context_sexpr_col(expr));
                    } else {
                        context_ctx_emit(ctx, SLOP_STR("{"));
                        context_ctx_indent(ctx);
                        context_ctx_push_scope(ctx);
                        __auto_type _mv_593 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_593.has_value) {
                            __auto_type bindings_expr = _mv_593.value;
                            __auto_type _mv_594 = (*bindings_expr);
                            switch (_mv_594.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type bindings_lst = _mv_594.data.lst;
                                    stmt_transpile_bindings(ctx, bindings_lst.items);
                                    break;
                                }
                                default: {
                                    context_ctx_add_error_at(ctx, SLOP_STR("invalid bindings"), context_sexpr_line(bindings_expr), context_sexpr_col(bindings_expr));
                                    break;
                                }
                            }
                        } else if (!_mv_593.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing bindings"), context_sexpr_line(expr), context_sexpr_col(expr));
                        }
                        {
                            __auto_type i = 2;
                            while ((i < len)) {
                                __auto_type _mv_595 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_595.has_value) {
                                    __auto_type body_expr = _mv_595.value;
                                    {
                                        __auto_type is_last = (i == (len - 1));
                                        stmt_transpile_stmt(ctx, body_expr, (is_return && is_last));
                                    }
                                } else if (!_mv_595.has_value) {
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
                context_ctx_add_error_at(ctx, SLOP_STR("invalid let"), context_sexpr_line(expr), context_sexpr_col(expr));
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
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_596 = ({ __auto_type _lst = bindings; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_596.has_value) {
                __auto_type binding_expr = _mv_596.value;
                stmt_transpile_single_binding(ctx, binding_expr);
            } else if (!_mv_596.has_value) {
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
        __auto_type _mv_597 = (*binding);
        switch (_mv_597.tag) {
            case types_SExpr_lst:
            {
                __auto_type binding_lst = _mv_597.data.lst;
                {
                    __auto_type items = binding_lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    {
                        __auto_type has_mut = expr_binding_has_mut(items);
                        __auto_type start_idx = ((expr_binding_has_mut(items)) ? 1 : 0);
                        if (((len - start_idx) < 2)) {
                            context_ctx_add_error_at(ctx, SLOP_STR("invalid binding: need name and value"), context_sexpr_line(binding), context_sexpr_col(binding));
                        } else {
                            __auto_type _mv_598 = ({ __auto_type _lst = items; size_t _idx = (size_t)start_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_598.has_value) {
                                __auto_type name_expr = _mv_598.value;
                                __auto_type _mv_599 = (*name_expr);
                                switch (_mv_599.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type name_sym = _mv_599.data.sym;
                                        {
                                            __auto_type raw_name = name_sym.name;
                                            __auto_type var_name = ctype_to_c_name(arena, raw_name);
                                            if (((len - start_idx) >= 3)) {
                                                __auto_type _mv_600 = ({ __auto_type _lst = items; size_t _idx = (size_t)(start_idx + 1); struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_600.has_value) {
                                                    __auto_type type_expr = _mv_600.value;
                                                    __auto_type _mv_601 = ({ __auto_type _lst = items; size_t _idx = (size_t)(start_idx + 2); struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_601.has_value) {
                                                        __auto_type init_expr = _mv_601.value;
                                                        {
                                                            __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                            {
                                                                __auto_type final_init = ((strlib_starts_with(c_type, SLOP_STR("slop_option_"))) ? ({ __auto_type some_val = stmt_get_some_value(init_expr); ({ __auto_type _mv = some_val; _mv.has_value ? ({ __auto_type val_expr = _mv.value; ({ __auto_type val_c = expr_transpile_expr(ctx, val_expr); context_ctx_str5(ctx, SLOP_STR("("), c_type, SLOP_STR("){.has_value = 1, .value = "), val_c, SLOP_STR("}")); }); }) : (((stmt_is_none_form(init_expr)) ? context_ctx_str3(ctx, SLOP_STR("("), c_type, SLOP_STR("){.has_value = false}")) : expr_transpile_expr(ctx, init_expr))); }); }) : expr_transpile_expr(ctx, init_expr));
                                                                context_ctx_emit(ctx, context_ctx_str5(ctx, c_type, SLOP_STR(" "), var_name, SLOP_STR(" = "), context_ctx_str(ctx, final_init, SLOP_STR(";"))));
                                                                {
                                                                    __auto_type slop_type_str = ctype_sexpr_to_type_string(arena, type_expr);
                                                                    context_ctx_bind_var(ctx, (context_VarEntry){raw_name, var_name, c_type, slop_type_str, 0, has_mut});
                                                                }
                                                            }
                                                        }
                                                    } else if (!_mv_601.has_value) {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("missing init"), context_sexpr_line(binding), context_sexpr_col(binding));
                                                    }
                                                } else if (!_mv_600.has_value) {
                                                    context_ctx_add_error_at(ctx, SLOP_STR("missing type"), context_sexpr_line(binding), context_sexpr_col(binding));
                                                }
                                            } else {
                                                __auto_type _mv_602 = ({ __auto_type _lst = items; size_t _idx = (size_t)(start_idx + 1); struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_602.has_value) {
                                                    __auto_type init_expr = _mv_602.value;
                                                    {
                                                        __auto_type init_c = expr_transpile_expr(ctx, init_expr);
                                                        __auto_type inferred_slop_type = expr_infer_expr_slop_type(ctx, init_expr);
                                                        __auto_type ptr_type_opt = stmt_get_arena_alloc_ptr_type(ctx, init_expr);
                                                        __auto_type _mv_603 = ptr_type_opt;
                                                        if (_mv_603.has_value) {
                                                            __auto_type ptr_type = _mv_603.value;
                                                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("__auto_type "), var_name, SLOP_STR(" = "), init_c, SLOP_STR(";")));
                                                            context_ctx_bind_var(ctx, (context_VarEntry){raw_name, var_name, ptr_type, inferred_slop_type, 1, has_mut});
                                                        } else if (!_mv_603.has_value) {
                                                            {
                                                                __auto_type inferred_type = expr_infer_expr_c_type(ctx, init_expr);
                                                                context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("__auto_type "), var_name, SLOP_STR(" = "), init_c, SLOP_STR(";")));
                                                                context_ctx_bind_var(ctx, (context_VarEntry){raw_name, var_name, inferred_type, inferred_slop_type, strlib_ends_with(inferred_type, SLOP_STR("*")), has_mut});
                                                            }
                                                        }
                                                    }
                                                } else if (!_mv_602.has_value) {
                                                    context_ctx_add_error_at(ctx, SLOP_STR("missing init"), context_sexpr_line(binding), context_sexpr_col(binding));
                                                }
                                            }
                                        }
                                        break;
                                    }
                                    default: {
                                        context_ctx_add_error_at(ctx, SLOP_STR("binding name must be symbol"), context_sexpr_line(name_expr), context_sexpr_col(name_expr));
                                        break;
                                    }
                                }
                            } else if (!_mv_598.has_value) {
                                context_ctx_add_error_at(ctx, SLOP_STR("missing binding name"), context_sexpr_line(binding), context_sexpr_col(binding));
                            }
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("binding must be a list"), context_sexpr_line(binding), context_sexpr_col(binding));
                break;
            }
        }
    }
}

uint8_t stmt_binding_has_mut(slop_list_types_SExpr_ptr items) {
    if ((((int64_t)((items).len)) < 1)) {
        return 0;
    } else {
        __auto_type _mv_604 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_604.has_value) {
            __auto_type first = _mv_604.value;
            __auto_type _mv_605 = (*first);
            switch (_mv_605.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_605.data.sym;
                    return string_eq(sym.name, SLOP_STR("mut"));
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_604.has_value) {
            return 0;
        }
    }
}

slop_option_types_SExpr_ptr stmt_get_some_value(types_SExpr* expr) {
    {
        slop_option_types_SExpr_ptr result = (slop_option_types_SExpr_ptr){.has_value = false};
        __auto_type _mv_606 = (*expr);
        switch (_mv_606.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_606.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 2)) {
                        __auto_type _mv_607 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_607.has_value) {
                            __auto_type head_expr = _mv_607.value;
                            __auto_type _mv_608 = (*head_expr);
                            switch (_mv_608.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_608.data.sym;
                                    if (string_eq(sym.name, SLOP_STR("some"))) {
                                        __auto_type _mv_609 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_609.has_value) {
                                            __auto_type val = _mv_609.value;
                                            result = (slop_option_types_SExpr_ptr){.has_value = 1, .value = val};
                                        } else if (!_mv_609.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_607.has_value) {
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
    __auto_type _mv_610 = (*expr);
    switch (_mv_610.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_610.data.sym;
            return string_eq(sym.name, SLOP_STR("none"));
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_610.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 1)) {
                    __auto_type _mv_611 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_611.has_value) {
                        __auto_type head = _mv_611.value;
                        __auto_type _mv_612 = (*head);
                        switch (_mv_612.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_612.data.sym;
                                return string_eq(sym.name, SLOP_STR("none"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_611.has_value) {
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
    __auto_type _mv_613 = (*expr);
    switch (_mv_613.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_613.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len < 3)) {
                    context_ctx_add_error_at(ctx, SLOP_STR("invalid if: need condition and then-branch"), context_sexpr_line(expr), context_sexpr_col(expr));
                } else {
                    __auto_type _mv_614 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_614.has_value) {
                        __auto_type cond_expr = _mv_614.value;
                        {
                            __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), cond_c, SLOP_STR(") {")));
                            context_ctx_indent(ctx);
                            __auto_type _mv_615 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_615.has_value) {
                                __auto_type then_expr = _mv_615.value;
                                stmt_transpile_stmt(ctx, then_expr, is_return);
                            } else if (!_mv_615.has_value) {
                            }
                            context_ctx_dedent(ctx);
                            if ((len >= 4)) {
                                context_ctx_emit(ctx, SLOP_STR("} else {"));
                                context_ctx_indent(ctx);
                                __auto_type _mv_616 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_616.has_value) {
                                    __auto_type else_expr = _mv_616.value;
                                    stmt_transpile_stmt(ctx, else_expr, is_return);
                                } else if (!_mv_616.has_value) {
                                }
                                context_ctx_dedent(ctx);
                                context_ctx_emit(ctx, SLOP_STR("}"));
                            } else {
                                context_ctx_emit(ctx, SLOP_STR("}"));
                            }
                        }
                    } else if (!_mv_614.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing if condition"), context_sexpr_line(expr), context_sexpr_col(expr));
                    }
                }
            }
            break;
        }
        default: {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid if"), context_sexpr_line(expr), context_sexpr_col(expr));
            break;
        }
    }
}

void stmt_transpile_when(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_617 = (*expr);
    switch (_mv_617.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_617.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len < 3)) {
                    context_ctx_add_error_at(ctx, SLOP_STR("invalid when: need condition and body"), context_sexpr_line(expr), context_sexpr_col(expr));
                } else {
                    __auto_type _mv_618 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_618.has_value) {
                        __auto_type cond_expr = _mv_618.value;
                        {
                            __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), cond_c, SLOP_STR(") {")));
                            context_ctx_indent(ctx);
                            {
                                __auto_type i = 2;
                                while ((i < len)) {
                                    __auto_type _mv_619 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_619.has_value) {
                                        __auto_type body_expr = _mv_619.value;
                                        stmt_transpile_stmt(ctx, body_expr, 0);
                                    } else if (!_mv_619.has_value) {
                                    }
                                    i = (i + 1);
                                }
                            }
                            context_ctx_dedent(ctx);
                            context_ctx_emit(ctx, SLOP_STR("}"));
                        }
                    } else if (!_mv_618.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing when condition"), context_sexpr_line(expr), context_sexpr_col(expr));
                    }
                }
            }
            break;
        }
        default: {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid when"), context_sexpr_line(expr), context_sexpr_col(expr));
            break;
        }
    }
}

void stmt_transpile_while(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_620 = (*expr);
    switch (_mv_620.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_620.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len < 3)) {
                    context_ctx_add_error_at(ctx, SLOP_STR("invalid while: need condition and body"), context_sexpr_line(expr), context_sexpr_col(expr));
                } else {
                    __auto_type _mv_621 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_621.has_value) {
                        __auto_type cond_expr = _mv_621.value;
                        {
                            __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("while ("), cond_c, SLOP_STR(") {")));
                            context_ctx_indent(ctx);
                            {
                                __auto_type i = 2;
                                while ((i < len)) {
                                    __auto_type _mv_622 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_622.has_value) {
                                        __auto_type body_expr = _mv_622.value;
                                        stmt_transpile_stmt(ctx, body_expr, 0);
                                    } else if (!_mv_622.has_value) {
                                    }
                                    i = (i + 1);
                                }
                            }
                            context_ctx_dedent(ctx);
                            context_ctx_emit(ctx, SLOP_STR("}"));
                        }
                    } else if (!_mv_621.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing while condition"), context_sexpr_line(expr), context_sexpr_col(expr));
                    }
                }
            }
            break;
        }
        default: {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid while"), context_sexpr_line(expr), context_sexpr_col(expr));
            break;
        }
    }
}

void stmt_transpile_set(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_623 = (*expr);
        switch (_mv_623.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_623.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len == 5)) {
                        stmt_transpile_typed_field_set(ctx, items);
                    } else if ((len == 4)) {
                        stmt_transpile_field_set(ctx, items);
                    } else if ((len == 3)) {
                        __auto_type _mv_624 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_624.has_value) {
                            __auto_type target_expr = _mv_624.value;
                            __auto_type _mv_625 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_625.has_value) {
                                __auto_type value_expr = _mv_625.value;
                                {
                                    __auto_type target_c = expr_transpile_expr(ctx, target_expr);
                                    __auto_type target_type_opt = stmt_get_var_c_type(ctx, target_expr);
                                    __auto_type _mv_626 = target_type_opt;
                                    if (_mv_626.has_value) {
                                        __auto_type target_type = _mv_626.value;
                                        if (strlib_starts_with(target_type, SLOP_STR("slop_option_"))) {
                                            {
                                                __auto_type some_val_opt = stmt_get_some_value(value_expr);
                                                __auto_type _mv_627 = some_val_opt;
                                                if (_mv_627.has_value) {
                                                    __auto_type val_expr = _mv_627.value;
                                                    {
                                                        __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                        context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str5(ctx, SLOP_STR(" = ("), target_type, SLOP_STR("){.has_value = 1, .value = "), val_c, SLOP_STR("};"))));
                                                    }
                                                } else if (!_mv_627.has_value) {
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
                                    } else if (!_mv_626.has_value) {
                                        {
                                            __auto_type value_c = expr_transpile_expr(ctx, value_expr);
                                            context_ctx_emit(ctx, context_ctx_str4(ctx, target_c, SLOP_STR(" = "), value_c, SLOP_STR(";")));
                                        }
                                    }
                                }
                            } else if (!_mv_625.has_value) {
                                context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_sexpr_line(expr), context_sexpr_col(expr));
                            }
                        } else if (!_mv_624.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_sexpr_line(expr), context_sexpr_col(expr));
                        }
                    } else {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid set!: need target and value"), context_sexpr_line(expr), context_sexpr_col(expr));
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid set!"), context_sexpr_line(expr), context_sexpr_col(expr));
                break;
            }
        }
    }
}

slop_option_string stmt_get_var_c_type(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    __auto_type _mv_628 = (*expr);
    switch (_mv_628.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_628.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_629 = context_ctx_lookup_var(ctx, name);
                if (_mv_629.has_value) {
                    __auto_type var_entry = _mv_629.value;
                    return (slop_option_string){.has_value = 1, .value = var_entry.c_type};
                } else if (!_mv_629.has_value) {
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
    __auto_type _mv_630 = (*expr);
    switch (_mv_630.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_630.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_631 = context_ctx_lookup_var(ctx, name);
                if (_mv_631.has_value) {
                    __auto_type var_entry = _mv_631.value;
                    {
                        __auto_type c_type = var_entry.c_type;
                        return strlib_ends_with(c_type, SLOP_STR("*"));
                    }
                } else if (!_mv_631.has_value) {
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
        __auto_type _mv_632 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_632.has_value) {
            __auto_type target_expr = _mv_632.value;
            __auto_type _mv_633 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_633.has_value) {
                __auto_type field_expr = _mv_633.value;
                __auto_type _mv_634 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_634.has_value) {
                    __auto_type value_expr = _mv_634.value;
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
                } else if (!_mv_634.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_sexpr_line(target_expr), context_sexpr_col(target_expr));
                }
            } else if (!_mv_633.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing set! field"), context_sexpr_line(target_expr), context_sexpr_col(target_expr));
            }
        } else if (!_mv_632.has_value) {
            context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_list_first_line(items), context_list_first_col(items));
        }
    }
}

void stmt_transpile_typed_field_set(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_635 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_635.has_value) {
            __auto_type target_expr = _mv_635.value;
            __auto_type _mv_636 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_636.has_value) {
                __auto_type field_expr = _mv_636.value;
                __auto_type _mv_637 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_637.has_value) {
                    __auto_type type_expr = _mv_637.value;
                    __auto_type _mv_638 = ({ __auto_type _lst = items; size_t _idx = (size_t)4; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_638.has_value) {
                        __auto_type value_expr = _mv_638.value;
                        {
                            __auto_type field_name = stmt_get_symbol_name(arena, field_expr);
                            __auto_type c_type = ctype_to_c_type(arena, type_expr);
                            {
                                __auto_type target_access = ((stmt_is_deref_expr(target_expr)) ? ({ __auto_type inner_expr = stmt_get_deref_inner(target_expr); __auto_type inner_c = expr_transpile_expr(ctx, inner_expr); context_ctx_str(ctx, SLOP_STR("(*"), context_ctx_str(ctx, inner_c, SLOP_STR(")."))); }) : ({ __auto_type target_c = expr_transpile_expr(ctx, target_expr); __auto_type is_ptr = stmt_is_pointer_target(ctx, target_expr); ((is_ptr) ? context_ctx_str(ctx, target_c, SLOP_STR("->")) : context_ctx_str(ctx, target_c, SLOP_STR("."))); }));
                                if (strlib_starts_with(c_type, SLOP_STR("slop_option_"))) {
                                    if (stmt_is_none_form(value_expr)) {
                                        context_ctx_emit(ctx, context_ctx_str(ctx, target_access, context_ctx_str(ctx, field_name, context_ctx_str3(ctx, SLOP_STR(" = ("), c_type, SLOP_STR("){.has_value = false};")))));
                                    } else {
                                        __auto_type _mv_639 = stmt_get_some_value(value_expr);
                                        if (_mv_639.has_value) {
                                            __auto_type inner_val = _mv_639.value;
                                            {
                                                __auto_type val_c = expr_transpile_expr(ctx, inner_val);
                                                context_ctx_emit(ctx, context_ctx_str(ctx, target_access, context_ctx_str(ctx, field_name, context_ctx_str5(ctx, SLOP_STR(" = ("), c_type, SLOP_STR("){.has_value = 1, .value = "), val_c, SLOP_STR("};")))));
                                            }
                                        } else if (!_mv_639.has_value) {
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
                    } else if (!_mv_638.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_sexpr_line(type_expr), context_sexpr_col(type_expr));
                    }
                } else if (!_mv_637.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("missing set! type"), context_sexpr_line(field_expr), context_sexpr_col(field_expr));
                }
            } else if (!_mv_636.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing set! field"), context_sexpr_line(target_expr), context_sexpr_col(target_expr));
            }
        } else if (!_mv_635.has_value) {
            context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_list_first_line(items), context_list_first_col(items));
        }
    }
}

uint8_t stmt_is_deref_expr(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_640 = (*expr);
    switch (_mv_640.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_640.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return 0;
                } else {
                    __auto_type _mv_641 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_641.has_value) {
                        __auto_type head = _mv_641.value;
                        __auto_type _mv_642 = (*head);
                        switch (_mv_642.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_642.data.sym;
                                return string_eq(sym.name, SLOP_STR("deref"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_641.has_value) {
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
    __auto_type _mv_643 = (*expr);
    switch (_mv_643.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_643.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type _mv_644 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_644.has_value) {
                    __auto_type inner = _mv_644.value;
                    return inner;
                } else if (!_mv_644.has_value) {
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
    __auto_type _mv_645 = (*expr);
    switch (_mv_645.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_645.data.sym;
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
    __auto_type _mv_646 = (*expr);
    switch (_mv_646.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_646.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type i = 1;
                while ((i < len)) {
                    __auto_type _mv_647 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_647.has_value) {
                        __auto_type body_expr = _mv_647.value;
                        {
                            __auto_type is_last = (i == (len - 1));
                            stmt_transpile_stmt(ctx, body_expr, (is_return && is_last));
                        }
                    } else if (!_mv_647.has_value) {
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
    __auto_type _mv_648 = (*expr);
    switch (_mv_648.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_648.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                if ((len < 2)) {
                    context_ctx_add_error_at(ctx, SLOP_STR("invalid with-arena: need size"), context_sexpr_line(expr), context_sexpr_col(expr));
                } else {
                    context_ctx_emit(ctx, SLOP_STR("{"));
                    context_ctx_indent(ctx);
                    context_ctx_push_scope(ctx);
                    __auto_type _mv_649 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_649.has_value) {
                        __auto_type size_expr = _mv_649.value;
                        {
                            __auto_type size_c = expr_transpile_expr(ctx, size_expr);
                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("slop_arena _arena = slop_arena_new("), size_c, SLOP_STR(");")));
                            context_ctx_emit(ctx, SLOP_STR("slop_arena* arena = &_arena;"));
                        }
                    } else if (!_mv_649.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing size"), context_sexpr_line(expr), context_sexpr_col(expr));
                    }
                    context_ctx_bind_var(ctx, (context_VarEntry){SLOP_STR("arena"), SLOP_STR("arena"), SLOP_STR("slop_arena*"), SLOP_STR(""), 1, 0});
                    {
                        __auto_type i = 2;
                        while ((i < len)) {
                            __auto_type _mv_650 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_650.has_value) {
                                __auto_type body_expr = _mv_650.value;
                                {
                                    __auto_type is_last = (i == (len - 1));
                                    stmt_transpile_stmt(ctx, body_expr, (is_return && is_last));
                                }
                            } else if (!_mv_650.has_value) {
                            }
                            i = (i + 1);
                        }
                    }
                    context_ctx_emit(ctx, SLOP_STR("slop_arena_free(arena);"));
                    context_ctx_pop_scope(ctx);
                    context_ctx_dedent(ctx);
                    context_ctx_emit(ctx, SLOP_STR("}"));
                }
            }
            break;
        }
        default: {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid with-arena"), context_sexpr_line(expr), context_sexpr_col(expr));
            break;
        }
    }
}

void stmt_transpile_cond(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_651 = (*expr);
    switch (_mv_651.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_651.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type i = 1;
                __auto_type first = 1;
                while ((i < len)) {
                    __auto_type _mv_652 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_652.has_value) {
                        __auto_type clause_expr = _mv_652.value;
                        __auto_type _mv_653 = (*clause_expr);
                        switch (_mv_653.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type clause_lst = _mv_653.data.lst;
                                {
                                    __auto_type clause_items = clause_lst.items;
                                    __auto_type clause_len = ((int64_t)((clause_items).len));
                                    if ((clause_len < 1)) {
                                        context_ctx_add_error_at(ctx, SLOP_STR("invalid cond clause"), context_sexpr_line(clause_expr), context_sexpr_col(clause_expr));
                                    } else {
                                        __auto_type _mv_654 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_654.has_value) {
                                            __auto_type test_expr = _mv_654.value;
                                            __auto_type _mv_655 = (*test_expr);
                                            switch (_mv_655.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type sym = _mv_655.data.sym;
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
                                        } else if (!_mv_654.has_value) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("missing test"), context_sexpr_line(clause_expr), context_sexpr_col(clause_expr));
                                        }
                                    }
                                }
                                break;
                            }
                            default: {
                                context_ctx_add_error_at(ctx, SLOP_STR("cond clause must be list"), context_sexpr_line(clause_expr), context_sexpr_col(clause_expr));
                                break;
                            }
                        }
                    } else if (!_mv_652.has_value) {
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
            context_ctx_add_error_at(ctx, SLOP_STR("invalid cond"), context_sexpr_line(expr), context_sexpr_col(expr));
            break;
        }
    }
}

void stmt_transpile_cond_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = start;
        while ((i < len)) {
            __auto_type _mv_656 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_656.has_value) {
                __auto_type body_expr = _mv_656.value;
                {
                    __auto_type is_last = (i == (len - 1));
                    stmt_transpile_stmt(ctx, body_expr, (is_return && is_last));
                }
            } else if (!_mv_656.has_value) {
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
        __auto_type _mv_657 = (*expr);
        switch (_mv_657.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_657.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 2)) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid for: need binding"), context_sexpr_line(expr), context_sexpr_col(expr));
                    } else {
                        __auto_type _mv_658 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_658.has_value) {
                            __auto_type binding_expr = _mv_658.value;
                            __auto_type _mv_659 = (*binding_expr);
                            switch (_mv_659.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type binding_lst = _mv_659.data.lst;
                                    {
                                        __auto_type binding_items = binding_lst.items;
                                        __auto_type binding_len = ((int64_t)((binding_items).len));
                                        if ((binding_len < 3)) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("for binding needs (var start end)"), context_sexpr_line(binding_expr), context_sexpr_col(binding_expr));
                                        } else {
                                            __auto_type _mv_660 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_660.has_value) {
                                                __auto_type var_expr = _mv_660.value;
                                                __auto_type _mv_661 = (*var_expr);
                                                switch (_mv_661.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type var_sym = _mv_661.data.sym;
                                                        {
                                                            __auto_type var_name = ctype_to_c_name(arena, var_sym.name);
                                                            __auto_type _mv_662 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_662.has_value) {
                                                                __auto_type start_expr = _mv_662.value;
                                                                __auto_type _mv_663 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                if (_mv_663.has_value) {
                                                                    __auto_type end_expr = _mv_663.value;
                                                                    {
                                                                        __auto_type start_c = expr_transpile_expr(ctx, start_expr);
                                                                        __auto_type end_c = expr_transpile_expr(ctx, end_expr);
                                                                        context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("for (int64_t "), var_name, SLOP_STR(" = "), start_c, context_ctx_str5(ctx, SLOP_STR("; "), var_name, SLOP_STR(" < "), end_c, context_ctx_str3(ctx, SLOP_STR("; "), var_name, SLOP_STR("++) {")))));
                                                                        context_ctx_indent(ctx);
                                                                        context_ctx_push_scope(ctx);
                                                                        context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, SLOP_STR("int64_t"), SLOP_STR(""), 0, 0});
                                                                        {
                                                                            __auto_type i = 2;
                                                                            while ((i < len)) {
                                                                                __auto_type _mv_664 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                                if (_mv_664.has_value) {
                                                                                    __auto_type body_expr = _mv_664.value;
                                                                                    stmt_transpile_stmt(ctx, body_expr, 0);
                                                                                } else if (!_mv_664.has_value) {
                                                                                }
                                                                                i = (i + 1);
                                                                            }
                                                                        }
                                                                        context_ctx_pop_scope(ctx);
                                                                        context_ctx_dedent(ctx);
                                                                        context_ctx_emit(ctx, SLOP_STR("}"));
                                                                    }
                                                                } else if (!_mv_663.has_value) {
                                                                    context_ctx_add_error_at(ctx, SLOP_STR("missing end"), context_sexpr_line(binding_expr), context_sexpr_col(binding_expr));
                                                                }
                                                            } else if (!_mv_662.has_value) {
                                                                context_ctx_add_error_at(ctx, SLOP_STR("missing start"), context_sexpr_line(binding_expr), context_sexpr_col(binding_expr));
                                                            }
                                                        }
                                                        break;
                                                    }
                                                    default: {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("for var must be symbol"), context_sexpr_line(var_expr), context_sexpr_col(var_expr));
                                                        break;
                                                    }
                                                }
                                            } else if (!_mv_660.has_value) {
                                                context_ctx_add_error_at(ctx, SLOP_STR("missing var"), context_sexpr_line(binding_expr), context_sexpr_col(binding_expr));
                                            }
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    context_ctx_add_error_at(ctx, SLOP_STR("for binding must be list"), context_sexpr_line(binding_expr), context_sexpr_col(binding_expr));
                                    break;
                                }
                            }
                        } else if (!_mv_658.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing binding"), context_sexpr_line(expr), context_sexpr_col(expr));
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid for"), context_sexpr_line(expr), context_sexpr_col(expr));
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
        __auto_type _mv_665 = (*expr);
        switch (_mv_665.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_665.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 2)) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid for-each: need binding"), context_sexpr_line(expr), context_sexpr_col(expr));
                    } else {
                        __auto_type _mv_666 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_666.has_value) {
                            __auto_type binding_expr = _mv_666.value;
                            __auto_type _mv_667 = (*binding_expr);
                            switch (_mv_667.tag) {
                                case types_SExpr_lst:
                                {
                                    __auto_type binding_lst = _mv_667.data.lst;
                                    {
                                        __auto_type binding_items = binding_lst.items;
                                        __auto_type binding_len = ((int64_t)((binding_items).len));
                                        if ((binding_len < 2)) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("for-each binding needs (var coll)"), context_sexpr_line(binding_expr), context_sexpr_col(binding_expr));
                                        } else {
                                            __auto_type _mv_668 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_668.has_value) {
                                                __auto_type var_expr = _mv_668.value;
                                                __auto_type _mv_669 = (*var_expr);
                                                switch (_mv_669.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type var_sym = _mv_669.data.sym;
                                                        {
                                                            __auto_type var_name = ctype_to_c_name(arena, var_sym.name);
                                                            __auto_type _mv_670 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_670.has_value) {
                                                                __auto_type coll_expr = _mv_670.value;
                                                                {
                                                                    __auto_type coll_c = expr_transpile_expr(ctx, coll_expr);
                                                                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("for (size_t _i = 0; _i < "), coll_c, SLOP_STR(".len; _i++) {")));
                                                                    context_ctx_indent(ctx);
                                                                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("__auto_type "), var_name, SLOP_STR(" = "), coll_c, SLOP_STR(".data[_i];")));
                                                                    context_ctx_push_scope(ctx);
                                                                    {
                                                                        __auto_type elem_slop_type = expr_infer_collection_element_slop_type(ctx, coll_expr);
                                                                        context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, SLOP_STR("auto"), elem_slop_type, 0, 0});
                                                                    }
                                                                    {
                                                                        __auto_type i = 2;
                                                                        while ((i < len)) {
                                                                            __auto_type _mv_671 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                                            if (_mv_671.has_value) {
                                                                                __auto_type body_expr = _mv_671.value;
                                                                                stmt_transpile_stmt(ctx, body_expr, 0);
                                                                            } else if (!_mv_671.has_value) {
                                                                            }
                                                                            i = (i + 1);
                                                                        }
                                                                    }
                                                                    context_ctx_pop_scope(ctx);
                                                                    context_ctx_dedent(ctx);
                                                                    context_ctx_emit(ctx, SLOP_STR("}"));
                                                                }
                                                            } else if (!_mv_670.has_value) {
                                                                context_ctx_add_error_at(ctx, SLOP_STR("missing collection"), context_sexpr_line(binding_expr), context_sexpr_col(binding_expr));
                                                            }
                                                        }
                                                        break;
                                                    }
                                                    default: {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("for-each var must be symbol"), context_sexpr_line(var_expr), context_sexpr_col(var_expr));
                                                        break;
                                                    }
                                                }
                                            } else if (!_mv_668.has_value) {
                                                context_ctx_add_error_at(ctx, SLOP_STR("missing var"), context_sexpr_line(binding_expr), context_sexpr_col(binding_expr));
                                            }
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    context_ctx_add_error_at(ctx, SLOP_STR("for-each binding must be list"), context_sexpr_line(binding_expr), context_sexpr_col(binding_expr));
                                    break;
                                }
                            }
                        } else if (!_mv_666.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing binding"), context_sexpr_line(expr), context_sexpr_col(expr));
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid for-each"), context_sexpr_line(expr), context_sexpr_col(expr));
                break;
            }
        }
    }
}

void stmt_transpile_stmt(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_672 = (*expr);
    switch (_mv_672.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_672.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    context_ctx_add_error_at(ctx, SLOP_STR("empty list"), context_sexpr_line(expr), context_sexpr_col(expr));
                } else {
                    __auto_type _mv_673 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_673.has_value) {
                        __auto_type head_expr = _mv_673.value;
                        __auto_type _mv_674 = (*head_expr);
                        switch (_mv_674.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_674.data.sym;
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
                                            __auto_type _mv_675 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_675.has_value) {
                                                __auto_type val_expr = _mv_675.value;
                                                match_emit_typed_return_expr(ctx, val_expr);
                                            } else if (!_mv_675.has_value) {
                                                context_ctx_emit(ctx, SLOP_STR("return;"));
                                            }
                                        }
                                    } else if (string_eq(op, SLOP_STR("break"))) {
                                        context_ctx_emit(ctx, SLOP_STR("break;"));
                                    } else if (string_eq(op, SLOP_STR("continue"))) {
                                        context_ctx_emit(ctx, SLOP_STR("continue;"));
                                    } else {
                                        if (is_return) {
                                            match_emit_typed_return_expr(ctx, expr);
                                        } else {
                                            context_ctx_emit(ctx, context_ctx_str(ctx, expr_transpile_expr(ctx, expr), SLOP_STR(";")));
                                        }
                                    }
                                }
                                break;
                            }
                            default: {
                                if (is_return) {
                                    match_emit_typed_return_expr(ctx, expr);
                                } else {
                                    context_ctx_emit(ctx, context_ctx_str(ctx, expr_transpile_expr(ctx, expr), SLOP_STR(";")));
                                }
                                break;
                            }
                        }
                    } else if (!_mv_673.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("empty"), context_list_first_line(items), context_list_first_col(items));
                    }
                }
            }
            break;
        }
        default: {
            if (is_return) {
                match_emit_typed_return_expr(ctx, expr);
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
    __auto_type _mv_676 = (*expr);
    switch (_mv_676.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_676.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                } else {
                    __auto_type _mv_677 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_677.has_value) {
                        __auto_type head = _mv_677.value;
                        __auto_type _mv_678 = (*head);
                        switch (_mv_678.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_678.data.sym;
                                {
                                    __auto_type op = sym.name;
                                    if (string_eq(op, SLOP_STR("some"))) {
                                        __auto_type _mv_679 = context_ctx_get_current_return_type(ctx);
                                        if (_mv_679.has_value) {
                                            __auto_type ret_type = _mv_679.value;
                                            if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                                                if ((((int64_t)((items).len)) < 2)) {
                                                    stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                                } else {
                                                    __auto_type _mv_680 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_680.has_value) {
                                                        __auto_type inner_expr = _mv_680.value;
                                                        {
                                                            __auto_type inner_c = expr_transpile_expr(ctx, inner_expr);
                                                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("return ("), ret_type, SLOP_STR("){.has_value = 1, .value = "), inner_c, SLOP_STR("};")));
                                                        }
                                                    } else if (!_mv_680.has_value) {
                                                        stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                                    }
                                                }
                                            } else {
                                                stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                            }
                                        } else if (!_mv_679.has_value) {
                                            stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                        }
                                    } else if (string_eq(op, SLOP_STR("none"))) {
                                        __auto_type _mv_681 = context_ctx_get_current_return_type(ctx);
                                        if (_mv_681.has_value) {
                                            __auto_type ret_type = _mv_681.value;
                                            if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                                                context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("return ("), ret_type, SLOP_STR("){.has_value = false};")));
                                            } else {
                                                stmt_emit_return_with_typed_none(ctx, expr_transpile_expr(ctx, expr));
                                            }
                                        } else if (!_mv_681.has_value) {
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
                    } else if (!_mv_677.has_value) {
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
            __auto_type _mv_682 = context_ctx_get_current_return_type(ctx);
            if (_mv_682.has_value) {
                __auto_type ret_type = _mv_682.value;
                if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                    final_code = context_ctx_str3(ctx, SLOP_STR("("), ret_type, SLOP_STR("){.has_value = false}"));
                }
            } else if (!_mv_682.has_value) {
            }
        } else {
            __auto_type _mv_683 = context_ctx_get_current_return_type(ctx);
            if (_mv_683.has_value) {
                __auto_type ret_type = _mv_683.value;
                if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                    __auto_type _mv_684 = context_ctx_lookup_var(ctx, code);
                    if (_mv_684.has_value) {
                        __auto_type var_entry = _mv_684.value;
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
                    } else if (!_mv_684.has_value) {
                    }
                }
            } else if (!_mv_683.has_value) {
            }
        }
        if (context_ctx_is_capture_retval(ctx)) {
            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("_retval = "), final_code, SLOP_STR(";")));
        } else {
            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("return "), final_code, SLOP_STR(";")));
        }
    }
}

