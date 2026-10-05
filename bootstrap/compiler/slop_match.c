#include "../runtime/slop_runtime.h"
#include "slop_match.h"

uint8_t match_is_option_match(slop_list_types_SExpr_ptr patterns);
uint8_t match_is_result_match(slop_list_types_SExpr_ptr patterns);
uint8_t match_is_enum_match(slop_list_types_SExpr_ptr patterns);
uint8_t match_is_literal_match(slop_list_types_SExpr_ptr patterns);
uint8_t match_is_union_match(context_TranspileContext* ctx, slop_list_types_SExpr_ptr patterns);
slop_string match_get_pattern_tag(types_SExpr* pat_expr);
slop_option_string match_extract_binding_name(types_SExpr* pat_expr);
int64_t match_count_pattern_bindings(types_SExpr* pat_expr);
void match_transpile_match(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return);
slop_list_types_SExpr_ptr match_collect_patterns(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void match_transpile_option_match(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* scrutinee_expr, slop_list_types_SExpr_ptr patterns, slop_list_types_SExpr_ptr items, uint8_t is_return);
void match_emit_option_some_branch(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* scrutinee_expr, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, uint8_t is_return, uint8_t first);
void match_emit_option_none_branch(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr branch_items, uint8_t is_return, uint8_t first);
void match_transpile_result_match(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* scrutinee_expr, slop_list_types_SExpr_ptr patterns, slop_list_types_SExpr_ptr items, uint8_t is_return);
void match_emit_result_ok_branch(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* scrutinee_expr, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, uint8_t is_return, uint8_t first);
void match_emit_result_error_branch(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* scrutinee_expr, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, uint8_t is_return, uint8_t first);
void match_transpile_enum_match(context_TranspileContext* ctx, slop_string scrutinee_c, slop_string scrut_c_type, slop_list_types_SExpr_ptr items, uint8_t is_return);
void match_emit_enum_case(context_TranspileContext* ctx, slop_string scrut_c_type, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, uint8_t is_return);
void match_transpile_literal_match(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr items, uint8_t is_return);
void match_emit_literal_case(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, uint8_t is_return, uint8_t first);
void match_transpile_union_match(context_TranspileContext* ctx, slop_string scrutinee_c, slop_string scrut_c_type, slop_list_types_SExpr_ptr patterns, slop_list_types_SExpr_ptr items, uint8_t is_return);
void match_emit_union_case(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* pattern, slop_string tag, slop_string union_type_name, slop_list_types_SExpr_ptr branch_items, uint8_t is_return);
void match_transpile_generic_match(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr items, uint8_t is_return);
void match_emit_match_fallthrough_trap(context_TranspileContext* ctx, uint8_t is_return, uint8_t has_else);
void match_emit_else_branch(context_TranspileContext* ctx, slop_list_types_SExpr_ptr branch_items, uint8_t is_return, uint8_t first);
void match_emit_branch_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr branch_items, uint8_t is_return);
void match_emit_branch_body_item(context_TranspileContext* ctx, types_SExpr* body_expr, uint8_t is_return, uint8_t is_last);
void match_emit_inline_let(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, uint8_t is_return, uint8_t is_last);
void match_emit_inline_bindings(context_TranspileContext* ctx, types_SExpr* bindings_expr);
void match_emit_single_inline_binding(context_TranspileContext* ctx, types_SExpr* binding);
slop_string match_let_decl_type(context_TranspileContext* ctx, uint8_t has_mut, slop_string inferred_type);
uint8_t match_binding_starts_with_mut(slop_list_types_SExpr_ptr items);
uint8_t match_is_type_expr(types_SExpr* expr);
uint8_t match_is_none_form_inline(types_SExpr* expr);
slop_string match_to_c_type_simple(slop_arena* arena, types_SExpr* type_expr);
slop_option_string match_get_arena_alloc_ptr_type_inline(context_TranspileContext* ctx, types_SExpr* expr);
slop_option_string match_extract_sizeof_type_inline(context_TranspileContext* ctx, types_SExpr* expr);
void match_emit_inline_do(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, uint8_t is_return, uint8_t is_last);
void match_emit_inline_if(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, uint8_t is_return);
void match_emit_inline_while(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
slop_option_string match_get_var_c_type_inline(context_TranspileContext* ctx, types_SExpr* expr);
slop_option_types_SExpr_ptr match_get_some_value_inline(types_SExpr* expr);
void match_emit_inline_set(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
uint8_t match_is_deref_inline(types_SExpr* expr);
slop_string match_get_deref_inner_inline(context_TranspileContext* ctx, types_SExpr* expr);
slop_string match_get_field_name_inline(context_TranspileContext* ctx, types_SExpr* expr);
void match_emit_inline_when(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void match_emit_inline_cond(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, uint8_t is_return, uint8_t is_last);
void match_emit_inline_cond_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start, uint8_t is_return, uint8_t is_last);
void match_emit_inline_with_arena(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, uint8_t is_return);
void match_emit_inline_body_items(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
slop_string match_emit_inline_loop_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start);
void match_emit_inline_for(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void match_emit_inline_for_each_set(context_TranspileContext* ctx, slop_string var_name, types_SExprSymbol var_sym, slop_string coll_c, slop_string resolved_type, slop_list_types_SExpr_ptr items, int64_t len);
void match_emit_inline_for_each_map_keys(context_TranspileContext* ctx, slop_string var_name, types_SExprSymbol var_sym, slop_string coll_c, slop_string resolved_type, slop_list_types_SExpr_ptr items, int64_t len);
void match_emit_inline_for_each_map_kv(context_TranspileContext* ctx, slop_list_types_SExpr_ptr binding_items, slop_list_types_SExpr_ptr items, int64_t len);
void match_emit_inline_for_each(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void match_emit_inline_return(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void match_emit_return_typed(context_TranspileContext* ctx, slop_string code);
void match_emit_typed_return_expr(context_TranspileContext* ctx, types_SExpr* expr);
uint8_t match_is_pattern_literal(types_SExpr* expr);
slop_string match_pattern_literal_to_c(types_SExpr* expr);
uint8_t match_has_literal_in_union_arm(types_SExpr* pat_expr);
uint8_t match_has_literal_in_patterns(slop_list_types_SExpr_ptr patterns);
slop_string match_build_literal_guard_cond(context_TranspileContext* ctx, slop_string scrutinee_c, slop_string c_tag, slop_string tag_cond, types_SExpr* pattern, uint8_t is_multi);
void match_emit_union_literal_bindings(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* pattern, slop_string tag, slop_string union_type_name, slop_string c_tag, uint8_t is_multi);
void match_transpile_union_match_with_literals(context_TranspileContext* ctx, slop_string scrutinee_c, slop_string scrut_c_type, slop_list_types_SExpr_ptr patterns, slop_list_types_SExpr_ptr items, uint8_t is_return);

uint8_t match_is_option_match(slop_list_types_SExpr_ptr patterns) {
    {
        __auto_type len = ((int64_t)((patterns).len));
        uint8_t has_some = 0;
        uint8_t has_none = 0;
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_759 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_759.has_value) {
                __auto_type pat_expr = _mv_759.value;
                {
                    __auto_type tag = match_get_pattern_tag(pat_expr);
                    if (string_eq(tag, SLOP_STR("some"))) {
                        has_some = 1;
                    } else if (string_eq(tag, SLOP_STR("none"))) {
                        has_none = 1;
                    } else {
                    }
                }
            } else if (!_mv_759.has_value) {
            }
            i = (i + 1);
        }
        return (has_some || has_none);
    }
}

uint8_t match_is_result_match(slop_list_types_SExpr_ptr patterns) {
    {
        __auto_type len = ((int64_t)((patterns).len));
        uint8_t has_ok = 0;
        uint8_t has_error = 0;
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_760 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_760.has_value) {
                __auto_type pat_expr = _mv_760.value;
                {
                    __auto_type tag = match_get_pattern_tag(pat_expr);
                    if (string_eq(tag, SLOP_STR("ok"))) {
                        has_ok = 1;
                    } else if (string_eq(tag, SLOP_STR("error"))) {
                        has_error = 1;
                    } else {
                    }
                }
            } else if (!_mv_760.has_value) {
            }
            i = (i + 1);
        }
        return (has_ok || has_error);
    }
}

uint8_t match_is_enum_match(slop_list_types_SExpr_ptr patterns) {
    {
        __auto_type len = ((int64_t)((patterns).len));
        uint8_t all_symbols = 1;
        int64_t i = 0;
        while ((i < len) && all_symbols) {
            __auto_type _mv_761 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_761.has_value) {
                __auto_type pat_expr = _mv_761.value;
                __auto_type _mv_762 = (*pat_expr);
                switch (_mv_762.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type _ = _mv_762.data.sym;
                        break;
                    }
                    default: {
                        all_symbols = 0;
                        break;
                    }
                }
            } else if (!_mv_761.has_value) {
            }
            i = (i + 1);
        }
        return all_symbols;
    }
}

uint8_t match_is_literal_match(slop_list_types_SExpr_ptr patterns) {
    {
        __auto_type len = ((int64_t)((patterns).len));
        uint8_t has_literal = 0;
        int64_t i = 0;
        while ((i < len) && !(has_literal)) {
            __auto_type _mv_763 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_763.has_value) {
                __auto_type pat_expr = _mv_763.value;
                __auto_type _mv_764 = (*pat_expr);
                switch (_mv_764.tag) {
                    case types_SExpr_num:
                    {
                        __auto_type _ = _mv_764.data.num;
                        has_literal = 1;
                        break;
                    }
                    case types_SExpr_str:
                    {
                        __auto_type _ = _mv_764.data.str;
                        has_literal = 1;
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_763.has_value) {
            }
            i = (i + 1);
        }
        return has_literal;
    }
}

uint8_t match_is_union_match(context_TranspileContext* ctx, slop_list_types_SExpr_ptr patterns) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((patterns).len));
        uint8_t has_union_variant = 0;
        int64_t i = 0;
        while ((i < len) && !(has_union_variant)) {
            __auto_type _mv_765 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_765.has_value) {
                __auto_type pat_expr = _mv_765.value;
                {
                    __auto_type tag = match_get_pattern_tag(pat_expr);
                    if ((!(string_eq(tag, SLOP_STR("")))) && (!(string_eq(tag, SLOP_STR("some")))) && (!(string_eq(tag, SLOP_STR("none")))) && (!(string_eq(tag, SLOP_STR("ok")))) && (!(string_eq(tag, SLOP_STR("error")))) && (!(string_eq(tag, SLOP_STR("else")))) && (!(string_eq(tag, SLOP_STR("_"))))) {
                        if (context_ctx_enum_variant_known(ctx, tag)) {
                            has_union_variant = 1;
                        }
                    }
                }
            } else if (!_mv_765.has_value) {
            }
            i = (i + 1);
        }
        return has_union_variant;
    }
}

slop_string match_get_pattern_tag(types_SExpr* pat_expr) {
    SLOP_PRE(((pat_expr != NULL)), "(!= pat-expr nil)");
    __auto_type _mv_766 = (*pat_expr);
    switch (_mv_766.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_766.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_767 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_767.has_value) {
                        __auto_type head = _mv_767.value;
                        __auto_type _mv_768 = (*head);
                        switch (_mv_768.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_768.data.sym;
                                return sym.name;
                            }
                            default: {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_767.has_value) {
                        return SLOP_STR("");
                    }
                    SLOP_UNREACHABLE();
                }
            }
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_766.data.sym;
            return sym.name;
        }
        default: {
            return SLOP_STR("");
        }
    }
}

slop_option_string match_extract_binding_name(types_SExpr* pat_expr) {
    SLOP_PRE(((pat_expr != NULL)), "(!= pat-expr nil)");
    __auto_type _mv_769 = (*pat_expr);
    switch (_mv_769.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_769.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 2) {
                    return (slop_option_string){.has_value = false};
                } else {
                    __auto_type _mv_770 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_770.has_value) {
                        __auto_type binding = _mv_770.value;
                        __auto_type _mv_771 = (*binding);
                        switch (_mv_771.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_771.data.sym;
                                return (slop_option_string){.has_value = 1, .value = sym.name};
                            }
                            default: {
                                return (slop_option_string){.has_value = false};
                            }
                        }
                    } else if (!_mv_770.has_value) {
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

int64_t match_count_pattern_bindings(types_SExpr* pat_expr) {
    SLOP_PRE(((pat_expr != NULL)), "(!= pat-expr nil)");
    __auto_type _mv_772 = (*pat_expr);
    switch (_mv_772.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_772.data.lst;
            {
                __auto_type len = ((int64_t)((lst.items).len));
                if (len > 1) {
                    return (len - 1);
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

void match_transpile_match(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_773 = (*expr);
        switch (_mv_773.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_773.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if (len < 3) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid match: need value and at least one branch"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    } else {
                        __auto_type _mv_774 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_774.has_value) {
                            __auto_type scrutinee = _mv_774.value;
                            {
                                __auto_type scrutinee_c = expr_transpile_expr(ctx, scrutinee);
                                __auto_type patterns = match_collect_patterns(ctx, items);
                                __auto_type scrutinee_var = context_ctx_gensym(ctx, SLOP_STR("_mv"));
                                __auto_type scrut_c_type = expr_infer_expr_c_type(ctx, scrutinee);
                                {
                                    __auto_type needs_deref = (context_ends_with_star(scrut_c_type) || expr_is_pointer_expr(ctx, scrutinee));
                                    if (needs_deref) {
                                        context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), scrutinee_var, SLOP_STR(" = *("), context_ctx_str(ctx, scrutinee_c, SLOP_STR(");"))));
                                    } else {
                                        context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), scrutinee_var, SLOP_STR(" = "), context_ctx_str(ctx, scrutinee_c, SLOP_STR(";"))));
                                    }
                                }
                                if (match_is_option_match(patterns)) {
                                    {
                                        __auto_type scrut_type = expr_resolve_type_alias(ctx, expr_infer_expr_slop_type(ctx, scrutinee));
                                        if (strlib_starts_with(scrut_type, SLOP_STR("(Result "))) {
                                            context_ctx_add_error_at(ctx, SLOP_STR("match uses Option patterns (some/none) but scrutinee has Result type - use (ok)/(error) patterns"), context_ctx_sexpr_line(scrutinee), context_ctx_sexpr_col(scrutinee));
                                        }
                                    }
                                    match_transpile_option_match(ctx, scrutinee_var, scrutinee, patterns, items, is_return);
                                } else if (match_is_result_match(patterns)) {
                                    match_transpile_result_match(ctx, scrutinee_var, scrutinee, patterns, items, is_return);
                                } else if (match_is_enum_match(patterns)) {
                                    match_transpile_enum_match(ctx, scrutinee_var, scrut_c_type, items, is_return);
                                } else if (match_is_literal_match(patterns)) {
                                    match_transpile_literal_match(ctx, scrutinee_var, items, is_return);
                                } else if (match_is_union_match(ctx, patterns)) {
                                    match_transpile_union_match(ctx, scrutinee_var, scrut_c_type, patterns, items, is_return);
                                } else {
                                    match_transpile_generic_match(ctx, scrutinee_var, items, is_return);
                                }
                            }
                        } else if (!_mv_774.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing match scrutinee"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid match"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                break;
            }
        }
    }
}

slop_list_types_SExpr_ptr match_collect_patterns(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type result = ((slop_list_types_SExpr_ptr){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
        int64_t i = 2;
        while (i < len) {
            __auto_type _mv_775 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_775.has_value) {
                __auto_type branch = _mv_775.value;
                __auto_type _mv_776 = (*branch);
                switch (_mv_776.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_776.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if (((int64_t)((branch_items).len)) >= 1) {
                                __auto_type _mv_777 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_777.has_value) {
                                    __auto_type pattern = _mv_777.value;
                                    ({ __auto_type _lst_p = &(result); __auto_type _item = (pattern); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                } else if (!_mv_777.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_775.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

void match_transpile_option_match(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* scrutinee_expr, slop_list_types_SExpr_ptr patterns, slop_list_types_SExpr_ptr items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 2;
        uint8_t first = 1;
        uint8_t has_else = 0;
        while (i < len) {
            __auto_type _mv_778 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_778.has_value) {
                __auto_type branch = _mv_778.value;
                __auto_type _mv_779 = (*branch);
                switch (_mv_779.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_779.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if (((int64_t)((branch_items).len)) >= 2) {
                                __auto_type _mv_780 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_780.has_value) {
                                    __auto_type pattern = _mv_780.value;
                                    {
                                        __auto_type tag = match_get_pattern_tag(pattern);
                                        if (expr_pattern_has_literal_payload(pattern)) {
                                            expr_unsupported_payload_literal(ctx, pattern);
                                        } else if (string_eq(tag, SLOP_STR("some"))) {
                                            match_emit_option_some_branch(ctx, scrutinee_c, scrutinee_expr, pattern, branch_items, is_return, first);
                                            first = 0;
                                        } else if (string_eq(tag, SLOP_STR("none"))) {
                                            match_emit_option_none_branch(ctx, scrutinee_c, branch_items, is_return, first);
                                            first = 0;
                                        } else if (string_eq(tag, SLOP_STR("else")) || string_eq(tag, SLOP_STR("_"))) {
                                            match_emit_else_branch(ctx, branch_items, is_return, first);
                                            has_else = 1;
                                            first = 0;
                                        } else {
                                            context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("unknown pattern '"), tag, SLOP_STR("' in Option match")), context_ctx_sexpr_line(pattern), context_ctx_sexpr_col(pattern));
                                        }
                                    }
                                } else if (!_mv_780.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_778.has_value) {
            }
            i = (i + 1);
        }
        if (!(first)) {
            context_ctx_emit(ctx, SLOP_STR("}"));
        }
        match_emit_match_fallthrough_trap(ctx, is_return, has_else);
    }
}

void match_emit_option_some_branch(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* scrutinee_expr, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, uint8_t is_return, uint8_t first) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((pattern != NULL)), "(!= pattern nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (first) {
            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), scrutinee_c, SLOP_STR(".has_value) {")));
        } else {
            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("} else if ("), scrutinee_c, SLOP_STR(".has_value) {")));
        }
        context_ctx_indent(ctx);
        context_ctx_push_scope(ctx);
        __auto_type _mv_781 = match_extract_binding_name(pattern);
        if (_mv_781.has_value) {
            __auto_type binding_name = _mv_781.value;
            {
                __auto_type c_name = ctype_to_c_name(arena, binding_name);
                __auto_type inner_slop_type = expr_infer_option_inner_slop_type(ctx, scrutinee_expr);
                __auto_type is_ptr = strlib_starts_with(inner_slop_type, SLOP_STR("(Ptr "));
                __auto_type inner_c_type = ((is_ptr) ? expr_slop_value_type_to_c_type(ctx, inner_slop_type) : SLOP_STR("auto"));
                context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, scrutinee_c, SLOP_STR(".value;"))));
                context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_name, inner_c_type, inner_slop_type, is_ptr, 0, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_bound});
            }
        } else if (!_mv_781.has_value) {
        }
        match_emit_branch_body(ctx, branch_items, is_return);
        context_ctx_pop_scope(ctx);
        context_ctx_dedent(ctx);
    }
}

void match_emit_option_none_branch(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr branch_items, uint8_t is_return, uint8_t first) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (first) {
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if (!"), scrutinee_c, SLOP_STR(".has_value) {")));
    } else {
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("} else if (!"), scrutinee_c, SLOP_STR(".has_value) {")));
    }
    context_ctx_indent(ctx);
    match_emit_branch_body(ctx, branch_items, is_return);
    context_ctx_dedent(ctx);
}

void match_transpile_result_match(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* scrutinee_expr, slop_list_types_SExpr_ptr patterns, slop_list_types_SExpr_ptr items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((scrutinee_expr != NULL)), "(!= scrutinee-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 2;
        uint8_t first = 1;
        uint8_t has_else = 0;
        while (i < len) {
            __auto_type _mv_782 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_782.has_value) {
                __auto_type branch = _mv_782.value;
                __auto_type _mv_783 = (*branch);
                switch (_mv_783.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_783.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if (((int64_t)((branch_items).len)) >= 2) {
                                __auto_type _mv_784 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_784.has_value) {
                                    __auto_type pattern = _mv_784.value;
                                    {
                                        __auto_type tag = match_get_pattern_tag(pattern);
                                        if (expr_pattern_has_literal_payload(pattern)) {
                                            expr_unsupported_payload_literal(ctx, pattern);
                                        } else if (string_eq(tag, SLOP_STR("ok"))) {
                                            match_emit_result_ok_branch(ctx, scrutinee_c, scrutinee_expr, pattern, branch_items, is_return, first);
                                            first = 0;
                                        } else if (string_eq(tag, SLOP_STR("error"))) {
                                            match_emit_result_error_branch(ctx, scrutinee_c, scrutinee_expr, pattern, branch_items, is_return, first);
                                            first = 0;
                                        } else if (string_eq(tag, SLOP_STR("else")) || string_eq(tag, SLOP_STR("_"))) {
                                            match_emit_else_branch(ctx, branch_items, is_return, first);
                                            has_else = 1;
                                            first = 0;
                                        } else {
                                            context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("unknown pattern '"), tag, SLOP_STR("' in Result match")), context_ctx_sexpr_line(pattern), context_ctx_sexpr_col(pattern));
                                        }
                                    }
                                } else if (!_mv_784.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_782.has_value) {
            }
            i = (i + 1);
        }
        if (!(first)) {
            context_ctx_emit(ctx, SLOP_STR("}"));
        }
        match_emit_match_fallthrough_trap(ctx, is_return, has_else);
    }
}

void match_emit_result_ok_branch(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* scrutinee_expr, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, uint8_t is_return, uint8_t first) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((scrutinee_expr != NULL)), "(!= scrutinee-expr nil)");
    SLOP_PRE(((pattern != NULL)), "(!= pattern nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (first) {
            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), scrutinee_c, SLOP_STR(".is_ok) {")));
        } else {
            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("} else if ("), scrutinee_c, SLOP_STR(".is_ok) {")));
        }
        context_ctx_indent(ctx);
        context_ctx_push_scope(ctx);
        __auto_type _mv_785 = match_extract_binding_name(pattern);
        if (_mv_785.has_value) {
            __auto_type binding_name = _mv_785.value;
            {
                __auto_type c_name = ctype_to_c_name(arena, binding_name);
                __auto_type ok_slop_type = expr_infer_result_ok_slop_type(ctx, scrutinee_expr);
                __auto_type is_ptr = strlib_starts_with(ok_slop_type, SLOP_STR("(Ptr "));
                __auto_type ok_c_type = ((is_ptr) ? expr_slop_value_type_to_c_type(ctx, ok_slop_type) : SLOP_STR("auto"));
                context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, scrutinee_c, SLOP_STR(".data.ok;"))));
                context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_name, ok_c_type, ok_slop_type, is_ptr, 0, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_bound});
            }
        } else if (!_mv_785.has_value) {
        }
        match_emit_branch_body(ctx, branch_items, is_return);
        context_ctx_pop_scope(ctx);
        context_ctx_dedent(ctx);
    }
}

void match_emit_result_error_branch(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* scrutinee_expr, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, uint8_t is_return, uint8_t first) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((scrutinee_expr != NULL)), "(!= scrutinee-expr nil)");
    SLOP_PRE(((pattern != NULL)), "(!= pattern nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (first) {
            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if (!"), scrutinee_c, SLOP_STR(".is_ok) {")));
        } else {
            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("} else if (!"), scrutinee_c, SLOP_STR(".is_ok) {")));
        }
        context_ctx_indent(ctx);
        context_ctx_push_scope(ctx);
        __auto_type _mv_786 = match_extract_binding_name(pattern);
        if (_mv_786.has_value) {
            __auto_type binding_name = _mv_786.value;
            {
                __auto_type c_name = ctype_to_c_name(arena, binding_name);
                __auto_type err_slop_type = expr_infer_result_err_slop_type(ctx, scrutinee_expr);
                __auto_type is_ptr = strlib_starts_with(err_slop_type, SLOP_STR("(Ptr "));
                __auto_type err_c_type = ((is_ptr) ? expr_slop_value_type_to_c_type(ctx, err_slop_type) : SLOP_STR("auto"));
                context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, scrutinee_c, SLOP_STR(".data.err;"))));
                context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_name, err_c_type, err_slop_type, is_ptr, 0, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_bound});
            }
        } else if (!_mv_786.has_value) {
        }
        match_emit_branch_body(ctx, branch_items, is_return);
        context_ctx_pop_scope(ctx);
        context_ctx_dedent(ctx);
    }
}

void match_transpile_enum_match(context_TranspileContext* ctx, slop_string scrutinee_c, slop_string scrut_c_type, slop_list_types_SExpr_ptr items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 2;
        uint8_t has_else = 0;
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("switch ("), scrutinee_c, SLOP_STR(") {")));
        context_ctx_indent(ctx);
        context_ctx_enter_switch(ctx);
        while (i < len) {
            __auto_type _mv_787 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_787.has_value) {
                __auto_type branch = _mv_787.value;
                __auto_type _mv_788 = (*branch);
                switch (_mv_788.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_788.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if (((int64_t)((branch_items).len)) >= 2) {
                                __auto_type _mv_789 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_789.has_value) {
                                    __auto_type pattern = _mv_789.value;
                                    {
                                        __auto_type tag = match_get_pattern_tag(pattern);
                                        if (string_eq(tag, SLOP_STR("else")) || string_eq(tag, SLOP_STR("_"))) {
                                            has_else = 1;
                                        }
                                    }
                                    match_emit_enum_case(ctx, scrut_c_type, pattern, branch_items, is_return);
                                } else if (!_mv_789.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_787.has_value) {
            }
            i = (i + 1);
        }
        context_ctx_exit_switch(ctx);
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
        match_emit_match_fallthrough_trap(ctx, is_return, has_else);
    }
}

void match_emit_enum_case(context_TranspileContext* ctx, slop_string scrut_c_type, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((pattern != NULL)), "(!= pattern nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type tag = match_get_pattern_tag(pattern);
        if (string_eq(tag, SLOP_STR("else")) || string_eq(tag, SLOP_STR("_"))) {
            context_ctx_emit(ctx, SLOP_STR("default: {"));
            context_ctx_indent(ctx);
            match_emit_branch_body(ctx, branch_items, is_return);
            context_ctx_emit(ctx, SLOP_STR("break;"));
            context_ctx_dedent(ctx);
            context_ctx_emit(ctx, SLOP_STR("}"));
        } else {
            __auto_type _mv_790 = context_ctx_resolve_enum_variant_for(ctx, tag, scrut_c_type, pattern);
            if (_mv_790.has_value) {
                __auto_type type_name = _mv_790.value;
                {
                    __auto_type c_case = context_ctx_str3(ctx, type_name, SLOP_STR("_"), ctype_to_c_name(arena, tag));
                    context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("case "), context_ctx_str(ctx, c_case, SLOP_STR(": {"))));
                    context_ctx_indent(ctx);
                    match_emit_branch_body(ctx, branch_items, is_return);
                    context_ctx_emit(ctx, SLOP_STR("break;"));
                    context_ctx_dedent(ctx);
                    context_ctx_emit(ctx, SLOP_STR("}"));
                }
            } else if (!_mv_790.has_value) {
                context_ctx_add_error_at(ctx, context_ctx_str3(ctx, SLOP_STR("unknown enum variant '"), tag, SLOP_STR("' in match")), context_ctx_sexpr_line(pattern), context_ctx_sexpr_col(pattern));
                context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("/* unknown enum variant: "), context_ctx_str(ctx, tag, SLOP_STR(" */"))));
            }
        }
    }
}

void match_transpile_literal_match(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 2;
        uint8_t first = 1;
        uint8_t has_else = 0;
        while (i < len) {
            __auto_type _mv_791 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_791.has_value) {
                __auto_type branch = _mv_791.value;
                __auto_type _mv_792 = (*branch);
                switch (_mv_792.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_792.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if (((int64_t)((branch_items).len)) >= 2) {
                                __auto_type _mv_793 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_793.has_value) {
                                    __auto_type pattern = _mv_793.value;
                                    {
                                        __auto_type pattern_tag = match_get_pattern_tag(pattern);
                                        if (string_eq(pattern_tag, SLOP_STR("else")) || string_eq(pattern_tag, SLOP_STR("_"))) {
                                            has_else = 1;
                                        }
                                    }
                                    match_emit_literal_case(ctx, scrutinee_c, pattern, branch_items, is_return, first);
                                    first = 0;
                                } else if (!_mv_793.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_791.has_value) {
            }
            i = (i + 1);
        }
        if (!(first)) {
            context_ctx_emit(ctx, SLOP_STR("}"));
        }
        match_emit_match_fallthrough_trap(ctx, is_return, has_else);
    }
}

void match_emit_literal_case(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, uint8_t is_return, uint8_t first) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((pattern != NULL)), "(!= pattern nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type tag = match_get_pattern_tag(pattern);
        if (string_eq(tag, SLOP_STR("else")) || string_eq(tag, SLOP_STR("_"))) {
            if (first) {
                context_ctx_emit(ctx, SLOP_STR("{"));
            } else {
                context_ctx_emit(ctx, SLOP_STR("} else {"));
            }
            context_ctx_indent(ctx);
            match_emit_branch_body(ctx, branch_items, is_return);
            context_ctx_dedent(ctx);
        } else {
            {
                __auto_type literal_c = expr_transpile_expr(ctx, pattern);
                __auto_type cond_c = expr_literal_pattern_cond(ctx, scrutinee_c, pattern, literal_c);
                if (first) {
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), cond_c, SLOP_STR(") {")));
                } else {
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("} else if ("), cond_c, SLOP_STR(") {")));
                }
                context_ctx_indent(ctx);
                match_emit_branch_body(ctx, branch_items, is_return);
                context_ctx_dedent(ctx);
            }
        }
    }
}

void match_transpile_union_match(context_TranspileContext* ctx, slop_string scrutinee_c, slop_string scrut_c_type, slop_list_types_SExpr_ptr patterns, slop_list_types_SExpr_ptr items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (match_has_literal_in_patterns(patterns)) {
        match_transpile_union_match_with_literals(ctx, scrutinee_c, scrut_c_type, patterns, items, is_return);
    } else {
        {
            __auto_type arena = (*ctx).arena;
            __auto_type len = ((int64_t)((items).len));
            int64_t i = 2;
            uint8_t first = 1;
            uint8_t has_else = 0;
            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("switch ("), scrutinee_c, SLOP_STR(".tag) {")));
            context_ctx_indent(ctx);
            context_ctx_enter_switch(ctx);
            while (i < len) {
                __auto_type _mv_794 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_794.has_value) {
                    __auto_type branch = _mv_794.value;
                    __auto_type _mv_795 = (*branch);
                    switch (_mv_795.tag) {
                        case types_SExpr_lst:
                        {
                            __auto_type branch_lst = _mv_795.data.lst;
                            {
                                __auto_type branch_items = branch_lst.items;
                                if (((int64_t)((branch_items).len)) >= 2) {
                                    __auto_type _mv_796 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_796.has_value) {
                                        __auto_type pattern = _mv_796.value;
                                        {
                                            __auto_type tag = match_get_pattern_tag(pattern);
                                            if (string_eq(tag, SLOP_STR("else")) || string_eq(tag, SLOP_STR("_"))) {
                                                has_else = 1;
                                                context_ctx_emit(ctx, SLOP_STR("default: {"));
                                                context_ctx_indent(ctx);
                                                match_emit_branch_body(ctx, branch_items, is_return);
                                                if (!(is_return)) {
                                                    context_ctx_emit(ctx, SLOP_STR("break;"));
                                                }
                                                context_ctx_dedent(ctx);
                                                context_ctx_emit(ctx, SLOP_STR("}"));
                                            } else {
                                                __auto_type _mv_797 = context_ctx_resolve_enum_variant_for(ctx, tag, scrut_c_type, pattern);
                                                if (_mv_797.has_value) {
                                                    __auto_type union_type_name = _mv_797.value;
                                                    match_emit_union_case(ctx, scrutinee_c, pattern, tag, union_type_name, branch_items, is_return);
                                                } else if (!_mv_797.has_value) {
                                                    context_ctx_add_error(ctx, context_ctx_str3(ctx, SLOP_STR("unknown union variant in match: "), tag, SLOP_STR(" (not registered as enum variant)")));
                                                }
                                            }
                                        }
                                    } else if (!_mv_796.has_value) {
                                    }
                                }
                            }
                            break;
                        }
                        default: {
                            break;
                        }
                    }
                } else if (!_mv_794.has_value) {
                }
                i = (i + 1);
            }
            context_ctx_exit_switch(ctx);
            context_ctx_dedent(ctx);
            context_ctx_emit(ctx, SLOP_STR("}"));
            match_emit_match_fallthrough_trap(ctx, is_return, has_else);
        }
    }
}

void match_emit_union_case(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* pattern, slop_string tag, slop_string union_type_name, slop_list_types_SExpr_ptr branch_items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((pattern != NULL)), "(!= pattern nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type c_tag = ctype_to_c_name(arena, tag);
        __auto_type case_label = context_ctx_str4(ctx, union_type_name, SLOP_STR("_"), c_tag, SLOP_STR(":"));
        __auto_type num_bindings = match_count_pattern_bindings(pattern);
        context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("case "), case_label));
        context_ctx_emit(ctx, SLOP_STR("{"));
        context_ctx_indent(ctx);
        context_ctx_push_scope(ctx);
        {
            __auto_type count_key = context_ctx_str3(ctx, tag, SLOP_STR("__count"), SLOP_STR(""));
            __auto_type multi_field_count = ({ __auto_type _mv = context_ctx_lookup_field_type(ctx, union_type_name, count_key); _mv.has_value ? ({ __auto_type ct = _mv.value; ct; }) : (SLOP_STR("")); });
            if (!(string_eq(multi_field_count, SLOP_STR("")))) {
                __auto_type _mv_798 = (*pattern);
                switch (_mv_798.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type pat_lst = _mv_798.data.lst;
                        {
                            __auto_type pat_items = pat_lst.items;
                            __auto_type pat_len = ((int64_t)((pat_items).len));
                            for (int64_t bi = 1; bi < pat_len; bi++) {
                                __auto_type _mv_799 = ({ __auto_type _lst = pat_items; size_t _idx = (size_t)bi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_799.has_value) {
                                    __auto_type binding_expr = _mv_799.value;
                                    {
                                        __auto_type binding_name = parser_sexpr_get_symbol_name(binding_expr);
                                        if (!(string_eq(binding_name, SLOP_STR(""))) && !(string_eq(binding_name, SLOP_STR("_")))) {
                                            {
                                                __auto_type c_binding = ctype_to_c_name(arena, binding_name);
                                                __auto_type field_idx = (bi - 1);
                                                __auto_type field_key = context_ctx_str3(ctx, tag, SLOP_STR("__"), int_to_string(arena, field_idx));
                                                __auto_type payload_c_type = ({ __auto_type _mv = context_ctx_lookup_field_type(ctx, union_type_name, field_key); _mv.has_value ? ({ __auto_type ct = _mv.value; ct; }) : (SLOP_STR("auto")); });
                                                __auto_type payload_slop_type = ({ __auto_type _mv = context_ctx_lookup_field_slop_type(ctx, union_type_name, field_key); _mv.has_value ? ({ __auto_type st = _mv.value; st; }) : (SLOP_STR("")); });
                                                __auto_type field_name = context_ctx_str(ctx, SLOP_STR("f"), int_to_string(arena, field_idx));
                                                context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("__auto_type "), c_binding, SLOP_STR(" = "), scrutinee_c, context_ctx_str5(ctx, SLOP_STR(".data."), c_tag, SLOP_STR("."), field_name, SLOP_STR(";"))));
                                                context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_binding, payload_c_type, payload_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_bound});
                                            }
                                        }
                                    }
                                } else if (!_mv_799.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else {
                __auto_type _mv_800 = match_extract_binding_name(pattern);
                if (_mv_800.has_value) {
                    __auto_type binding_name = _mv_800.value;
                    {
                        __auto_type c_binding = ctype_to_c_name(arena, binding_name);
                        __auto_type payload_c_type = ({ __auto_type _mv = context_ctx_lookup_field_type(ctx, union_type_name, tag); _mv.has_value ? ({ __auto_type ct = _mv.value; ct; }) : (SLOP_STR("auto")); });
                        __auto_type payload_slop_type = ({ __auto_type _mv = context_ctx_lookup_field_slop_type(ctx, union_type_name, tag); _mv.has_value ? ({ __auto_type st = _mv.value; st; }) : (SLOP_STR("")); });
                        context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("__auto_type "), c_binding, SLOP_STR(" = "), scrutinee_c, context_ctx_str3(ctx, SLOP_STR(".data."), c_tag, SLOP_STR(";"))));
                        context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_binding, payload_c_type, payload_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_bound});
                    }
                } else if (!_mv_800.has_value) {
                }
            }
        }
        match_emit_branch_body(ctx, branch_items, is_return);
        context_ctx_pop_scope(ctx);
        if (!(is_return)) {
            context_ctx_emit(ctx, SLOP_STR("break;"));
        }
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
    }
}

void match_transpile_generic_match(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    match_transpile_literal_match(ctx, scrutinee_c, items, is_return);
}

void match_emit_match_fallthrough_trap(context_TranspileContext* ctx, uint8_t is_return, uint8_t has_else) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (is_return && !(has_else)) {
        context_ctx_emit(ctx, SLOP_STR("SLOP_UNREACHABLE();"));
    }
}

void match_emit_else_branch(context_TranspileContext* ctx, slop_list_types_SExpr_ptr branch_items, uint8_t is_return, uint8_t first) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (first) {
        context_ctx_emit(ctx, SLOP_STR("{"));
    } else {
        context_ctx_emit(ctx, SLOP_STR("} else {"));
    }
    context_ctx_indent(ctx);
    match_emit_branch_body(ctx, branch_items, is_return);
    context_ctx_dedent(ctx);
}

void match_emit_branch_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr branch_items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((branch_items).len));
        int64_t i = 1;
        while (i < len) {
            __auto_type _mv_801 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_801.has_value) {
                __auto_type body_expr = _mv_801.value;
                {
                    __auto_type is_last = (i == (len - 1));
                    match_emit_branch_body_item(ctx, body_expr, is_return, is_last);
                }
            } else if (!_mv_801.has_value) {
            }
            i = (i + 1);
        }
    }
}

void match_emit_branch_body_item(context_TranspileContext* ctx, types_SExpr* body_expr, uint8_t is_return, uint8_t is_last) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((body_expr != NULL)), "(!= body-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_802 = (*body_expr);
        switch (_mv_802.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_802.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) < 1) {
                        context_ctx_emit(ctx, SLOP_STR("/* empty list */;"));
                    } else {
                        __auto_type _mv_803 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_803.has_value) {
                            __auto_type head_expr = _mv_803.value;
                            __auto_type _mv_804 = (*head_expr);
                            switch (_mv_804.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_804.data.sym;
                                    {
                                        __auto_type op = sym.name;
                                        if (string_eq(op, SLOP_STR("let"))) {
                                            match_emit_inline_let(ctx, items, is_return, is_last);
                                        } else if (string_eq(op, SLOP_STR("do"))) {
                                            match_emit_inline_do(ctx, items, is_return, is_last);
                                        } else if (string_eq(op, SLOP_STR("if"))) {
                                            match_emit_inline_if(ctx, items, (is_return && is_last));
                                        } else if (string_eq(op, SLOP_STR("while"))) {
                                            match_emit_inline_while(ctx, items);
                                        } else if (string_eq(op, SLOP_STR("set!"))) {
                                            match_emit_inline_set(ctx, items);
                                        } else if (string_eq(op, SLOP_STR("when"))) {
                                            match_emit_inline_when(ctx, items);
                                        } else if (string_eq(op, SLOP_STR("cond"))) {
                                            match_emit_inline_cond(ctx, items, is_return, is_last);
                                        } else if (string_eq(op, SLOP_STR("match"))) {
                                            match_transpile_match(ctx, body_expr, (is_return && is_last));
                                        } else if (string_eq(op, SLOP_STR("with-arena"))) {
                                            match_emit_inline_with_arena(ctx, items, (is_return && is_last));
                                        } else if (string_eq(op, SLOP_STR("for"))) {
                                            match_emit_inline_for(ctx, items);
                                        } else if (string_eq(op, SLOP_STR("for-each"))) {
                                            match_emit_inline_for_each(ctx, items);
                                        } else if (string_eq(op, SLOP_STR("return"))) {
                                            match_emit_inline_return(ctx, items);
                                        } else if (strlib_starts_with(op, SLOP_STR("@")) && !(string_eq(op, SLOP_STR("@")))) {
                                        } else {
                                            if (is_return && is_last) {
                                                match_emit_typed_return_expr(ctx, body_expr);
                                            } else {
                                                if (!(string_eq(parser_sexpr_get_symbol_name(body_expr), SLOP_STR("unit")))) {
                                                    context_ctx_emit(ctx, context_ctx_str(ctx, expr_transpile_expr(ctx, body_expr), SLOP_STR(";")));
                                                }
                                            }
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    if (!(string_eq(parser_sexpr_get_symbol_name(body_expr), SLOP_STR("unit")))) {
                                        context_ctx_emit(ctx, context_ctx_str(ctx, expr_transpile_expr(ctx, body_expr), SLOP_STR(";")));
                                    }
                                    break;
                                }
                            }
                        } else if (!_mv_803.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("empty"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                        }
                    }
                }
                break;
            }
            default: {
                if (is_return && is_last) {
                    match_emit_typed_return_expr(ctx, body_expr);
                } else {
                    if (!(string_eq(parser_sexpr_get_symbol_name(body_expr), SLOP_STR("unit")))) {
                        context_ctx_emit(ctx, context_ctx_str(ctx, expr_transpile_expr(ctx, body_expr), SLOP_STR(";")));
                    }
                }
                break;
            }
        }
    }
}

void match_emit_inline_let(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, uint8_t is_return, uint8_t is_last) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 2) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid let"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        } else {
            context_ctx_emit(ctx, SLOP_STR("{"));
            context_ctx_indent(ctx);
            context_ctx_push_scope(ctx);
            __auto_type _mv_805 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_805.has_value) {
                __auto_type bindings_expr = _mv_805.value;
                match_emit_inline_bindings(ctx, bindings_expr);
            } else if (!_mv_805.has_value) {
            }
            {
                int64_t i = 2;
                while (i < len) {
                    __auto_type _mv_806 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_806.has_value) {
                        __auto_type body_item = _mv_806.value;
                        {
                            __auto_type body_last = (i == (len - 1));
                            match_emit_branch_body_item(ctx, body_item, is_return, (is_last && body_last));
                        }
                    } else if (!_mv_806.has_value) {
                    }
                    i = (i + 1);
                }
            }
            context_ctx_pop_scope(ctx);
            context_ctx_dedent(ctx);
            context_ctx_emit(ctx, SLOP_STR("}"));
        }
    }
}

void match_emit_inline_bindings(context_TranspileContext* ctx, types_SExpr* bindings_expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((bindings_expr != NULL)), "(!= bindings-expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_807 = (*bindings_expr);
        switch (_mv_807.tag) {
            case types_SExpr_lst:
            {
                __auto_type bindings_lst = _mv_807.data.lst;
                {
                    __auto_type bindings = bindings_lst.items;
                    __auto_type len = ((int64_t)((bindings).len));
                    int64_t i = 0;
                    while (i < len) {
                        __auto_type _mv_808 = ({ __auto_type _lst = bindings; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_808.has_value) {
                            __auto_type binding = _mv_808.value;
                            match_emit_single_inline_binding(ctx, binding);
                        } else if (!_mv_808.has_value) {
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
}

void match_emit_single_inline_binding(context_TranspileContext* ctx, types_SExpr* binding) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((binding != NULL)), "(!= binding nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_809 = (*binding);
        switch (_mv_809.tag) {
            case types_SExpr_lst:
            {
                __auto_type binding_lst = _mv_809.data.lst;
                {
                    __auto_type items = binding_lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    {
                        __auto_type has_mut = match_binding_starts_with_mut(items);
                        __auto_type start_idx = ((match_binding_starts_with_mut(items)) ? 1 : 0);
                        if ((len - start_idx) < 2) {
                            context_ctx_add_error_at(ctx, SLOP_STR("invalid binding"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                        } else {
                            __auto_type _mv_810 = ({ __auto_type _lst = items; size_t _idx = (size_t)start_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_810.has_value) {
                                __auto_type name_expr = _mv_810.value;
                                __auto_type _mv_811 = (*name_expr);
                                switch (_mv_811.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type name_sym = _mv_811.data.sym;
                                        {
                                            __auto_type raw_name = name_sym.name;
                                            __auto_type c_name = ctype_to_c_name(arena, raw_name);
                                            if ((len - start_idx) >= 3) {
                                                {
                                                    __auto_type type_idx = (start_idx + 1);
                                                    __auto_type val_idx = (start_idx + 2);
                                                    __auto_type _mv_812 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_812.has_value) {
                                                        __auto_type type_expr = _mv_812.value;
                                                        if (match_is_type_expr(type_expr)) {
                                                            __auto_type _mv_813 = ({ __auto_type _lst = items; size_t _idx = (size_t)val_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_813.has_value) {
                                                                __auto_type val_expr = _mv_813.value;
                                                                {
                                                                    __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                                    __auto_type is_ptr = strlib_ends_with(c_type, SLOP_STR("*"));
                                                                    {
                                                                        __auto_type final_init = ((context_ctx_is_option_c_type(ctx, c_type)) ? ({ __auto_type some_val = match_get_some_value_inline(val_expr); ({ __auto_type _mv = some_val; _mv.has_value ? ({ __auto_type inner_expr = _mv.value; ({ __auto_type inner_c = expr_transpile_expr(ctx, inner_expr); context_ctx_str5(ctx, SLOP_STR("("), c_type, SLOP_STR("){.has_value = 1, .value = "), inner_c, SLOP_STR("}")); }); }) : (((match_is_none_form_inline(val_expr)) ? context_ctx_str3(ctx, SLOP_STR("("), c_type, SLOP_STR("){.has_value = false}")) : expr_transpile_expr(ctx, val_expr))); }); }) : expr_transpile_expr(ctx, val_expr));
                                                                        __auto_type slop_type_str = ctype_sexpr_to_type_string(arena, type_expr);
                                                                        context_ctx_emit(ctx, context_ctx_str5(ctx, c_type, SLOP_STR(" "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, final_init, SLOP_STR(";"))));
                                                                        context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, c_type, slop_type_str, is_ptr, has_mut, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_local});
                                                                    }
                                                                }
                                                            } else if (!_mv_813.has_value) {
                                                                context_ctx_add_error_at(ctx, SLOP_STR("missing value"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                                                            }
                                                        } else {
                                                            __auto_type _mv_814 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_814.has_value) {
                                                                __auto_type val_expr = _mv_814.value;
                                                                {
                                                                    __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                                    __auto_type inferred_slop_type = expr_infer_expr_slop_type(ctx, val_expr);
                                                                    __auto_type ptr_type_opt = match_get_arena_alloc_ptr_type_inline(ctx, val_expr);
                                                                    __auto_type _mv_815 = ptr_type_opt;
                                                                    if (_mv_815.has_value) {
                                                                        __auto_type ptr_type = _mv_815.value;
                                                                        context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, val_c, SLOP_STR(";"))));
                                                                        context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, ptr_type, inferred_slop_type, 1, has_mut, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_local});
                                                                    } else if (!_mv_815.has_value) {
                                                                        {
                                                                            __auto_type inferred_type = expr_infer_expr_c_type(ctx, val_expr);
                                                                            __auto_type is_ptr = strlib_ends_with(inferred_type, SLOP_STR("*"));
                                                                            context_ctx_emit(ctx, context_ctx_str4(ctx, match_let_decl_type(ctx, has_mut, inferred_type), c_name, SLOP_STR(" = "), context_ctx_str(ctx, val_c, SLOP_STR(";"))));
                                                                            context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, inferred_type, inferred_slop_type, is_ptr, has_mut, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_local});
                                                                        }
                                                                    }
                                                                }
                                                            } else if (!_mv_814.has_value) {
                                                                context_ctx_add_error_at(ctx, SLOP_STR("missing value"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                                                            }
                                                        }
                                                    } else if (!_mv_812.has_value) {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("missing type/value"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                                                    }
                                                }
                                            } else {
                                                {
                                                    __auto_type val_idx = (start_idx + 1);
                                                    __auto_type _mv_816 = ({ __auto_type _lst = items; size_t _idx = (size_t)val_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_816.has_value) {
                                                        __auto_type val_expr = _mv_816.value;
                                                        {
                                                            __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                            __auto_type inferred_slop_type = expr_infer_expr_slop_type(ctx, val_expr);
                                                            __auto_type ptr_type_opt = match_get_arena_alloc_ptr_type_inline(ctx, val_expr);
                                                            __auto_type _mv_817 = ptr_type_opt;
                                                            if (_mv_817.has_value) {
                                                                __auto_type ptr_type = _mv_817.value;
                                                                context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, val_c, SLOP_STR(";"))));
                                                                context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, ptr_type, inferred_slop_type, 1, has_mut, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_local});
                                                            } else if (!_mv_817.has_value) {
                                                                {
                                                                    __auto_type inferred_type = expr_infer_expr_c_type(ctx, val_expr);
                                                                    __auto_type is_ptr = strlib_ends_with(inferred_type, SLOP_STR("*"));
                                                                    context_ctx_emit(ctx, context_ctx_str4(ctx, match_let_decl_type(ctx, has_mut, inferred_type), c_name, SLOP_STR(" = "), context_ctx_str(ctx, val_c, SLOP_STR(";"))));
                                                                    context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, inferred_type, inferred_slop_type, is_ptr, has_mut, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_local});
                                                                }
                                                            }
                                                        }
                                                    } else if (!_mv_816.has_value) {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("missing value"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                                                    }
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
                            } else if (!_mv_810.has_value) {
                                context_ctx_add_error_at(ctx, SLOP_STR("missing binding name"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                            }
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("binding must be list"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                break;
            }
        }
    }
}

slop_string match_let_decl_type(context_TranspileContext* ctx, uint8_t has_mut, slop_string inferred_type) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (has_mut && expr_is_simple_primitive_c_type(inferred_type)) {
        return context_ctx_str(ctx, inferred_type, SLOP_STR(" "));
    } else {
        return SLOP_STR("__auto_type ");
    }
}

uint8_t match_binding_starts_with_mut(slop_list_types_SExpr_ptr items) {
    if (((int64_t)((items).len)) < 1) {
        return 0;
    } else {
        __auto_type _mv_818 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_818.has_value) {
            __auto_type first = _mv_818.value;
            __auto_type _mv_819 = (*first);
            switch (_mv_819.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_819.data.sym;
                    return string_eq(sym.name, SLOP_STR("mut"));
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_818.has_value) {
            return 0;
        }
        SLOP_UNREACHABLE();
    }
}

uint8_t match_is_type_expr(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_820 = (*expr);
    switch (_mv_820.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_820.data.sym;
            {
                __auto_type name = sym.name;
                if (string_len(name) == 0) {
                    return 0;
                } else {
                    {
                        __auto_type first_char = strlib_char_at(name, 0);
                        return ((first_char >= 65) && (first_char <= 90));
                    }
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type _ = _mv_820.data.lst;
            return 1;
        }
        default: {
            return 0;
        }
    }
}

uint8_t match_is_none_form_inline(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_821 = (*expr);
    switch (_mv_821.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_821.data.sym;
            return string_eq(sym.name, SLOP_STR("none"));
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_821.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) == 1) {
                    __auto_type _mv_822 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_822.has_value) {
                        __auto_type head = _mv_822.value;
                        __auto_type _mv_823 = (*head);
                        switch (_mv_823.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_823.data.sym;
                                return string_eq(sym.name, SLOP_STR("none"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_822.has_value) {
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

slop_string match_to_c_type_simple(slop_arena* arena, types_SExpr* type_expr) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    return ctype_to_c_type(arena, type_expr);
}

slop_option_string match_get_arena_alloc_ptr_type_inline(context_TranspileContext* ctx, types_SExpr* expr) {
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
                    if (((int64_t)((items).len)) >= 3) {
                        __auto_type _mv_825 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_825.has_value) {
                            __auto_type head_ptr = _mv_825.value;
                            __auto_type _mv_826 = (*head_ptr);
                            switch (_mv_826.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_826.data.sym;
                                    if (string_eq(head_sym.name, SLOP_STR("arena-alloc"))) {
                                        __auto_type _mv_827 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_827.has_value) {
                                            __auto_type size_expr = _mv_827.value;
                                            return match_extract_sizeof_type_inline(ctx, size_expr);
                                        } else if (!_mv_827.has_value) {
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
                        } else if (!_mv_825.has_value) {
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

slop_option_string match_extract_sizeof_type_inline(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_828 = (*expr);
        switch (_mv_828.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_828.data.sym;
                {
                    __auto_type type_name = sym.name;
                    __auto_type _mv_829 = context_ctx_lookup_type(ctx, type_name);
                    if (_mv_829.has_value) {
                        __auto_type entry = _mv_829.value;
                        return (slop_option_string){.has_value = 1, .value = context_ctx_str(ctx, entry.c_name, SLOP_STR("*"))};
                    } else if (!_mv_829.has_value) {
                        return (slop_option_string){.has_value = false};
                    }
                    SLOP_UNREACHABLE();
                }
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_828.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) >= 2) {
                        __auto_type _mv_830 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_830.has_value) {
                            __auto_type head_ptr = _mv_830.value;
                            __auto_type _mv_831 = (*head_ptr);
                            switch (_mv_831.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_831.data.sym;
                                    if (string_eq(head_sym.name, SLOP_STR("sizeof"))) {
                                        __auto_type _mv_832 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_832.has_value) {
                                            __auto_type type_expr = _mv_832.value;
                                            {
                                                __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                return (slop_option_string){.has_value = 1, .value = context_ctx_str(ctx, c_type, SLOP_STR("*"))};
                                            }
                                        } else if (!_mv_832.has_value) {
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
                        } else if (!_mv_830.has_value) {
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

void match_emit_inline_do(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, uint8_t is_return, uint8_t is_last) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 1;
        while (i < len) {
            __auto_type _mv_833 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_833.has_value) {
                __auto_type item = _mv_833.value;
                {
                    __auto_type item_last = (i == (len - 1));
                    match_emit_branch_body_item(ctx, item, is_return, (is_last && item_last));
                }
            } else if (!_mv_833.has_value) {
            }
            i = (i + 1);
        }
    }
}

void match_emit_inline_if(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 3) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid if"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        } else {
            expr_check_if_operands(ctx, items);
            __auto_type _mv_834 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_834.has_value) {
                __auto_type cond_expr = _mv_834.value;
                {
                    __auto_type cond_c = context_ctx_strip_cond_parens(ctx, expr_transpile_expr(ctx, cond_expr));
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), cond_c, SLOP_STR(") {")));
                }
            } else if (!_mv_834.has_value) {
                context_ctx_emit(ctx, SLOP_STR("if (/* missing */) {"));
            }
            context_ctx_indent(ctx);
            __auto_type _mv_835 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_835.has_value) {
                __auto_type then_expr = _mv_835.value;
                match_emit_branch_body_item(ctx, then_expr, is_return, 1);
            } else if (!_mv_835.has_value) {
            }
            context_ctx_dedent(ctx);
            if (len >= 4) {
                context_ctx_emit(ctx, SLOP_STR("} else {"));
                context_ctx_indent(ctx);
                __auto_type _mv_836 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_836.has_value) {
                    __auto_type else_expr = _mv_836.value;
                    match_emit_branch_body_item(ctx, else_expr, is_return, 1);
                } else if (!_mv_836.has_value) {
                }
                context_ctx_dedent(ctx);
                context_ctx_emit(ctx, SLOP_STR("}"));
            } else {
                context_ctx_emit(ctx, SLOP_STR("}"));
            }
        }
    }
}

void match_emit_inline_while(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 3) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid while"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        } else {
            __auto_type _mv_837 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_837.has_value) {
                __auto_type cond_expr = _mv_837.value;
                {
                    __auto_type cond_c = context_ctx_strip_cond_parens(ctx, expr_transpile_expr(ctx, cond_expr));
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("while ("), cond_c, SLOP_STR(") {")));
                }
            } else if (!_mv_837.has_value) {
                context_ctx_emit(ctx, SLOP_STR("while (/* missing */) {"));
            }
            context_ctx_indent(ctx);
            {
                __auto_type after_loop = match_emit_inline_loop_body(ctx, items, 2);
                context_ctx_dedent(ctx);
                context_ctx_emit(ctx, SLOP_STR("}"));
                context_ctx_emit_loop_end(ctx, after_loop);
            }
        }
    }
}

slop_option_string match_get_var_c_type_inline(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    __auto_type _mv_838 = (*expr);
    switch (_mv_838.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_838.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_839 = context_ctx_lookup_var(ctx, name);
                if (_mv_839.has_value) {
                    __auto_type var_entry = _mv_839.value;
                    return (slop_option_string){.has_value = 1, .value = var_entry.c_type};
                } else if (!_mv_839.has_value) {
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

slop_option_types_SExpr_ptr match_get_some_value_inline(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        slop_option_types_SExpr_ptr result = (slop_option_types_SExpr_ptr){.has_value = false};
        __auto_type _mv_840 = (*expr);
        switch (_mv_840.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_840.data.lst;
                {
                    __auto_type items = lst.items;
                    if (((int64_t)((items).len)) >= 2) {
                        __auto_type _mv_841 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_841.has_value) {
                            __auto_type head = _mv_841.value;
                            __auto_type _mv_842 = (*head);
                            switch (_mv_842.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_842.data.sym;
                                    if (string_eq(sym.name, SLOP_STR("some"))) {
                                        __auto_type _mv_843 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_843.has_value) {
                                            __auto_type val = _mv_843.value;
                                            result = (slop_option_types_SExpr_ptr){.has_value = 1, .value = val};
                                        } else if (!_mv_843.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_841.has_value) {
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

void match_emit_inline_set(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (expr_set_is_self_assign(items)) {
        } else if (len == 5) {
            __auto_type _mv_844 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_844.has_value) {
                __auto_type target_expr = _mv_844.value;
                __auto_type _mv_845 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_845.has_value) {
                    __auto_type field_expr = _mv_845.value;
                    __auto_type _mv_846 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_846.has_value) {
                        __auto_type type_expr = _mv_846.value;
                        __auto_type _mv_847 = ({ __auto_type _lst = items; size_t _idx = (size_t)4; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_847.has_value) {
                            __auto_type value_expr = _mv_847.value;
                            {
                                __auto_type field_name = match_get_field_name_inline(ctx, field_expr);
                                __auto_type c_type = ctype_to_c_type(arena, type_expr);
                                {
                                    __auto_type target_access = ((match_is_deref_inline(target_expr)) ? ({ __auto_type inner_c = match_get_deref_inner_inline(ctx, target_expr); context_ctx_str(ctx, SLOP_STR("(*"), context_ctx_str(ctx, inner_c, SLOP_STR(")."))); }) : ({ __auto_type target_c = expr_transpile_expr(ctx, target_expr); context_ctx_str(ctx, target_c, SLOP_STR(".")); }));
                                    if (context_ctx_is_option_c_type(ctx, c_type)) {
                                        if (match_is_none_form_inline(value_expr)) {
                                            context_ctx_emit(ctx, context_ctx_str(ctx, target_access, context_ctx_str(ctx, field_name, context_ctx_str3(ctx, SLOP_STR(" = ("), c_type, SLOP_STR("){.has_value = false};")))));
                                        } else {
                                            __auto_type _mv_848 = match_get_some_value_inline(value_expr);
                                            if (_mv_848.has_value) {
                                                __auto_type inner_val = _mv_848.value;
                                                {
                                                    __auto_type val_c = expr_transpile_expr(ctx, inner_val);
                                                    context_ctx_emit(ctx, context_ctx_str(ctx, target_access, context_ctx_str(ctx, field_name, context_ctx_str5(ctx, SLOP_STR(" = ("), c_type, SLOP_STR("){.has_value = 1, .value = "), val_c, SLOP_STR("};")))));
                                                }
                                            } else if (!_mv_848.has_value) {
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
                        } else if (!_mv_847.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                        }
                    } else if (!_mv_846.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing set! type"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    }
                } else if (!_mv_845.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("missing set! field"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                }
            } else if (!_mv_844.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            }
        } else if (len == 4) {
            __auto_type _mv_849 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_849.has_value) {
                __auto_type target_expr = _mv_849.value;
                __auto_type _mv_850 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_850.has_value) {
                    __auto_type field_expr = _mv_850.value;
                    __auto_type _mv_851 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_851.has_value) {
                        __auto_type value_expr = _mv_851.value;
                        {
                            __auto_type field_name = match_get_field_name_inline(ctx, field_expr);
                            __auto_type value_c = expr_transpile_expr(ctx, value_expr);
                            if (match_is_deref_inline(target_expr)) {
                                {
                                    __auto_type inner_c = match_get_deref_inner_inline(ctx, target_expr);
                                    context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("(*"), context_ctx_str(ctx, inner_c, context_ctx_str(ctx, SLOP_STR(")."), context_ctx_str(ctx, field_name, context_ctx_str(ctx, SLOP_STR(" = "), context_ctx_str(ctx, value_c, SLOP_STR(";"))))))));
                                }
                            } else {
                                {
                                    __auto_type target_c = expr_transpile_expr(ctx, target_expr);
                                    context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str(ctx, SLOP_STR("."), context_ctx_str(ctx, field_name, context_ctx_str(ctx, SLOP_STR(" = "), context_ctx_str(ctx, value_c, SLOP_STR(";")))))));
                                }
                            }
                        }
                    } else if (!_mv_851.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    }
                } else if (!_mv_850.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("missing set! field"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                }
            } else if (!_mv_849.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            }
        } else if (len >= 3) {
            __auto_type _mv_852 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_852.has_value) {
                __auto_type target_expr = _mv_852.value;
                __auto_type _mv_853 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_853.has_value) {
                    __auto_type val_expr = _mv_853.value;
                    {
                        __auto_type target_c = expr_transpile_expr(ctx, target_expr);
                        __auto_type target_type_opt = match_get_var_c_type_inline(ctx, target_expr);
                        __auto_type _mv_854 = target_type_opt;
                        if (_mv_854.has_value) {
                            __auto_type target_type = _mv_854.value;
                            if (context_ctx_is_option_c_type(ctx, target_type)) {
                                {
                                    __auto_type some_val_opt = match_get_some_value_inline(val_expr);
                                    __auto_type _mv_855 = some_val_opt;
                                    if (_mv_855.has_value) {
                                        __auto_type inner_expr = _mv_855.value;
                                        {
                                            __auto_type inner_c = expr_transpile_expr(ctx, inner_expr);
                                            context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str5(ctx, SLOP_STR(" = ("), target_type, SLOP_STR("){.has_value = 1, .value = "), inner_c, SLOP_STR("};"))));
                                        }
                                    } else if (!_mv_855.has_value) {
                                        {
                                            __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                            if (string_eq(val_c, SLOP_STR("none"))) {
                                                context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str3(ctx, SLOP_STR(" = ("), target_type, SLOP_STR("){.has_value = false};"))));
                                            } else {
                                                context_ctx_emit(ctx, context_ctx_str4(ctx, target_c, SLOP_STR(" = "), val_c, SLOP_STR(";")));
                                            }
                                        }
                                    }
                                }
                            } else {
                                {
                                    __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                    context_ctx_emit(ctx, context_ctx_str4(ctx, target_c, SLOP_STR(" = "), val_c, SLOP_STR(";")));
                                }
                            }
                        } else if (!_mv_854.has_value) {
                            {
                                __auto_type some_val_opt = match_get_some_value_inline(val_expr);
                                __auto_type _mv_856 = some_val_opt;
                                if (_mv_856.has_value) {
                                    __auto_type inner_expr = _mv_856.value;
                                    {
                                        __auto_type inner_c = expr_transpile_expr(ctx, inner_expr);
                                        __auto_type inner_type = expr_infer_expr_c_type(ctx, inner_expr);
                                        __auto_type option_type = expr_c_type_to_option_type_name(ctx, inner_type);
                                        context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str5(ctx, SLOP_STR(" = ("), option_type, SLOP_STR("){.has_value = 1, .value = "), inner_c, SLOP_STR("};"))));
                                    }
                                } else if (!_mv_856.has_value) {
                                    if (match_is_none_form_inline(val_expr)) {
                                        __auto_type _mv_857 = context_ctx_get_current_return_type(ctx);
                                        if (_mv_857.has_value) {
                                            __auto_type ret_type = _mv_857.value;
                                            if (context_ctx_is_option_c_type(ctx, ret_type)) {
                                                context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str3(ctx, SLOP_STR(" = ("), ret_type, SLOP_STR("){.has_value = false};"))));
                                            } else {
                                                {
                                                    __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                    context_ctx_emit(ctx, context_ctx_str4(ctx, target_c, SLOP_STR(" = "), val_c, SLOP_STR(";")));
                                                }
                                            }
                                        } else if (!_mv_857.has_value) {
                                            {
                                                __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                context_ctx_emit(ctx, context_ctx_str4(ctx, target_c, SLOP_STR(" = "), val_c, SLOP_STR(";")));
                                            }
                                        }
                                    } else {
                                        {
                                            __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                            context_ctx_emit(ctx, context_ctx_str4(ctx, target_c, SLOP_STR(" = "), val_c, SLOP_STR(";")));
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else if (!_mv_853.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                }
            } else if (!_mv_852.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            }
        } else {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid set!"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        }
    }
}

uint8_t match_is_deref_inline(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_858 = (*expr);
    switch (_mv_858.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_858.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 2) {
                    return 0;
                } else {
                    __auto_type _mv_859 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_859.has_value) {
                        __auto_type head = _mv_859.value;
                        __auto_type _mv_860 = (*head);
                        switch (_mv_860.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_860.data.sym;
                                return string_eq(sym.name, SLOP_STR("deref"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_859.has_value) {
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

slop_string match_get_deref_inner_inline(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_861 = (*expr);
    switch (_mv_861.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_861.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type _mv_862 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_862.has_value) {
                    __auto_type inner = _mv_862.value;
                    return expr_transpile_expr(ctx, inner);
                } else if (!_mv_862.has_value) {
                    return SLOP_STR("/* missing deref arg */");
                }
                SLOP_UNREACHABLE();
            }
        }
        default: {
            return SLOP_STR("/* not a deref */");
        }
    }
}

slop_string match_get_field_name_inline(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_863 = (*expr);
        switch (_mv_863.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_863.data.sym;
                return ctype_to_c_name(arena, sym.name);
            }
            default: {
                return SLOP_STR("/* unknown field */");
            }
        }
    }
}

void match_emit_inline_when(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 2) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid when"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        } else {
            __auto_type _mv_864 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_864.has_value) {
                __auto_type cond_expr = _mv_864.value;
                {
                    __auto_type cond_c = context_ctx_strip_cond_parens(ctx, expr_transpile_expr(ctx, cond_expr));
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), cond_c, SLOP_STR(") {")));
                }
            } else if (!_mv_864.has_value) {
                context_ctx_emit(ctx, SLOP_STR("if (/* missing */) {"));
            }
            context_ctx_indent(ctx);
            match_emit_inline_body_items(ctx, items, 2);
            context_ctx_dedent(ctx);
            context_ctx_emit(ctx, SLOP_STR("}"));
        }
    }
}

void match_emit_inline_cond(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, uint8_t is_return, uint8_t is_last) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 1;
        uint8_t first = 1;
        uint8_t has_else = 0;
        while (i < len) {
            __auto_type _mv_865 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_865.has_value) {
                __auto_type clause_expr = _mv_865.value;
                __auto_type _mv_866 = (*clause_expr);
                switch (_mv_866.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type clause_lst = _mv_866.data.lst;
                        {
                            __auto_type clause_items = clause_lst.items;
                            __auto_type clause_len = ((int64_t)((clause_items).len));
                            if (clause_len < 1) {
                                context_ctx_add_error_at(ctx, SLOP_STR("invalid cond clause"), context_ctx_sexpr_line(clause_expr), context_ctx_sexpr_col(clause_expr));
                            } else {
                                __auto_type _mv_867 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_867.has_value) {
                                    __auto_type test_expr = _mv_867.value;
                                    __auto_type _mv_868 = (*test_expr);
                                    switch (_mv_868.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_868.data.sym;
                                            if (string_eq(sym.name, SLOP_STR("else"))) {
                                                has_else = 1;
                                                context_ctx_emit(ctx, SLOP_STR("} else {"));
                                                context_ctx_indent(ctx);
                                                match_emit_inline_cond_body(ctx, clause_items, 1, is_return, is_last);
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
                                                    match_emit_inline_cond_body(ctx, clause_items, 1, is_return, is_last);
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
                                                match_emit_inline_cond_body(ctx, clause_items, 1, is_return, is_last);
                                                context_ctx_dedent(ctx);
                                            }
                                            break;
                                        }
                                    }
                                } else if (!_mv_867.has_value) {
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
            } else if (!_mv_865.has_value) {
            }
            i = (i + 1);
        }
        if (!(first)) {
            context_ctx_emit(ctx, SLOP_STR("}"));
        }
        match_emit_match_fallthrough_trap(ctx, is_return, has_else);
    }
}

void match_emit_inline_cond_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start, uint8_t is_return, uint8_t is_last) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = start;
        while (i < len) {
            __auto_type _mv_869 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_869.has_value) {
                __auto_type body_expr = _mv_869.value;
                {
                    __auto_type body_is_last = (i == (len - 1));
                    match_emit_branch_body_item(ctx, body_expr, is_return, (is_last && body_is_last));
                }
            } else if (!_mv_869.has_value) {
            }
            i = (i + 1);
        }
    }
}

void match_emit_inline_with_arena(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type ctx_arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 2) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid with-arena: need size"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        } else {
            {
                __auto_type is_named = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type item1 = _mv.value; string_eq(parser_sexpr_get_symbol_name(item1), SLOP_STR(":as")); }) : (0); });
                __auto_type arena_name = ((is_named) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type name_expr = _mv.value; parser_sexpr_get_symbol_name(name_expr); }) : (SLOP_STR("arena")); }) : SLOP_STR("arena"));
                __auto_type size_idx = ((is_named) ? 3 : 1);
                __auto_type body_start = ((is_named) ? 4 : 2);
                __auto_type c_arena_name = ctype_to_c_name(ctx_arena, arena_name);
                __auto_type c_local = context_ctx_unique_arena_local(ctx, ((is_named) ? string_concat(ctx_arena, SLOP_STR("_arena_"), c_arena_name) : SLOP_STR("_arena")));
                if (is_named && (len < 4)) {
                    context_ctx_add_error_at(ctx, SLOP_STR("with-arena :as requires name and size"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                } else {
                    context_ctx_emit(ctx, SLOP_STR("{"));
                    context_ctx_indent(ctx);
                    context_ctx_push_scope(ctx);
                    __auto_type _mv_870 = ({ __auto_type _lst = items; size_t _idx = (size_t)size_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_870.has_value) {
                        __auto_type size_expr = _mv_870.value;
                        {
                            __auto_type size_c = expr_transpile_expr(ctx, size_expr);
                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("slop_arena "), c_local, SLOP_STR(" = slop_arena_new("), size_c, SLOP_STR(");")));
                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("slop_arena* "), c_arena_name, SLOP_STR(" = &"), c_local, SLOP_STR(";")));
                        }
                    } else if (!_mv_870.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing size"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    }
                    context_ctx_bind_var(ctx, (context_VarEntry){arena_name, c_arena_name, SLOP_STR("slop_arena*"), SLOP_STR(""), 1, 0, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_bound});
                    context_ctx_push_open_arena(ctx, context_ctx_str(ctx, SLOP_STR("&"), c_local));
                    {
                        int64_t i = body_start;
                        while (i < len) {
                            __auto_type _mv_871 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_871.has_value) {
                                __auto_type body_expr = _mv_871.value;
                                {
                                    __auto_type is_last = (i == (len - 1));
                                    match_emit_branch_body_item(ctx, body_expr, (is_return && is_last), is_last);
                                }
                            } else if (!_mv_871.has_value) {
                            }
                            i = (i + 1);
                        }
                    }
                    context_ctx_pop_open_arena(ctx);
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("slop_arena_free("), c_arena_name, SLOP_STR(");")));
                    context_ctx_pop_scope(ctx);
                    context_ctx_dedent(ctx);
                    context_ctx_emit(ctx, SLOP_STR("}"));
                }
            }
        }
    }
}

void match_emit_inline_body_items(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = start;
        while (i < len) {
            __auto_type _mv_872 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_872.has_value) {
                __auto_type body_expr = _mv_872.value;
                match_emit_branch_body_item(ctx, body_expr, 0, 0);
            } else if (!_mv_872.has_value) {
            }
            i = (i + 1);
        }
    }
}

slop_string match_emit_inline_loop_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_enter_loop(ctx);
    match_emit_inline_body_items(ctx, items, start);
    return context_ctx_exit_loop(ctx);
}

void match_emit_inline_for(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 2) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid for: need binding"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        } else {
            __auto_type _mv_873 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_873.has_value) {
                __auto_type binding_expr = _mv_873.value;
                __auto_type _mv_874 = (*binding_expr);
                switch (_mv_874.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type binding_lst = _mv_874.data.lst;
                        {
                            __auto_type binding_items = binding_lst.items;
                            __auto_type binding_len = ((int64_t)((binding_items).len));
                            if (binding_len < 3) {
                                context_ctx_add_error_at(ctx, SLOP_STR("for binding needs (var start end)"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                            } else {
                                __auto_type _mv_875 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_875.has_value) {
                                    __auto_type var_expr = _mv_875.value;
                                    __auto_type _mv_876 = (*var_expr);
                                    switch (_mv_876.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type var_sym = _mv_876.data.sym;
                                            {
                                                __auto_type var_name = ctype_to_c_name(arena, var_sym.name);
                                                __auto_type _mv_877 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_877.has_value) {
                                                    __auto_type start_expr = _mv_877.value;
                                                    __auto_type _mv_878 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_878.has_value) {
                                                        __auto_type end_expr = _mv_878.value;
                                                        {
                                                            __auto_type start_c = expr_transpile_expr(ctx, start_expr);
                                                            __auto_type end_c = expr_transpile_expr(ctx, end_expr);
                                                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("for (int64_t "), var_name, SLOP_STR(" = "), start_c, context_ctx_str5(ctx, SLOP_STR("; "), var_name, SLOP_STR(" < "), end_c, context_ctx_str3(ctx, SLOP_STR("; "), var_name, SLOP_STR("++) {")))));
                                                            context_ctx_indent(ctx);
                                                            context_ctx_push_scope(ctx);
                                                            context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, SLOP_STR("int64_t"), SLOP_STR("Int"), 0, 0, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_bound});
                                                            {
                                                                __auto_type after_loop = match_emit_inline_loop_body(ctx, items, 2);
                                                                context_ctx_pop_scope(ctx);
                                                                context_ctx_dedent(ctx);
                                                                context_ctx_emit(ctx, SLOP_STR("}"));
                                                                context_ctx_emit_loop_end(ctx, after_loop);
                                                            }
                                                        }
                                                    } else if (!_mv_878.has_value) {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("missing end"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                                                    }
                                                } else if (!_mv_877.has_value) {
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
                                } else if (!_mv_875.has_value) {
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
            } else if (!_mv_873.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing binding"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            }
        }
    }
}

void match_emit_inline_for_each_set(context_TranspileContext* ctx, slop_string var_name, types_SExprSymbol var_sym, slop_string coll_c, slop_string resolved_type, slop_list_types_SExpr_ptr items, int64_t len) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type elem_slop_type = expr_extract_set_elem_from_slop_type(arena, resolved_type);
        __auto_type elem_c_type = expr_slop_value_type_to_c_type(ctx, elem_slop_type);
        context_ctx_emit(ctx, SLOP_STR("{"));
        context_ctx_indent(ctx);
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("slop_map* _coll = (slop_map*)"), expr_deref_container_c(ctx, coll_c, resolved_type), SLOP_STR(";")));
        context_ctx_emit(ctx, SLOP_STR("for (size_t _i = 0; _i < _coll->len; _i++) {"));
        context_ctx_indent(ctx);
        context_ctx_emit(ctx, SLOP_STR("{"));
        context_ctx_indent(ctx);
        {
            __auto_type cast_part = context_ctx_str(ctx, elem_c_type, SLOP_STR("*)slop_map_key_at(_coll, _i)"));
            __auto_type assign_prefix = context_ctx_str4(ctx, elem_c_type, SLOP_STR(" "), var_name, SLOP_STR(" = *("));
            __auto_type assign_part = context_ctx_str3(ctx, assign_prefix, cast_part, SLOP_STR(";"));
            context_ctx_emit(ctx, assign_part);
        }
        context_ctx_push_scope(ctx);
        context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, elem_c_type, elem_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_bound});
        {
            __auto_type after_loop = match_emit_inline_loop_body(ctx, items, 2);
            context_ctx_pop_scope(ctx);
            context_ctx_dedent(ctx);
            context_ctx_emit(ctx, SLOP_STR("}"));
            context_ctx_dedent(ctx);
            context_ctx_emit(ctx, SLOP_STR("}"));
            context_ctx_dedent(ctx);
            context_ctx_emit(ctx, SLOP_STR("}"));
            context_ctx_emit_loop_end(ctx, after_loop);
        }
    }
}

void match_emit_inline_for_each_map_keys(context_TranspileContext* ctx, slop_string var_name, types_SExprSymbol var_sym, slop_string coll_c, slop_string resolved_type, slop_list_types_SExpr_ptr items, int64_t len) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type key_slop_type = expr_extract_map_key_from_slop_type(arena, resolved_type);
        __auto_type key_c_type = expr_slop_value_type_to_c_type(ctx, key_slop_type);
        context_ctx_emit(ctx, SLOP_STR("{"));
        context_ctx_indent(ctx);
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("slop_map* _coll = (slop_map*)"), expr_deref_container_c(ctx, coll_c, resolved_type), SLOP_STR(";")));
        context_ctx_emit(ctx, SLOP_STR("for (size_t _i = 0; _i < _coll->len; _i++) {"));
        context_ctx_indent(ctx);
        context_ctx_emit(ctx, SLOP_STR("{"));
        context_ctx_indent(ctx);
        {
            __auto_type cast_part = context_ctx_str(ctx, key_c_type, SLOP_STR("*)slop_map_key_at(_coll, _i)"));
            __auto_type assign_prefix = context_ctx_str4(ctx, key_c_type, SLOP_STR(" "), var_name, SLOP_STR(" = *("));
            __auto_type assign_part = context_ctx_str3(ctx, assign_prefix, cast_part, SLOP_STR(";"));
            context_ctx_emit(ctx, assign_part);
        }
        context_ctx_push_scope(ctx);
        context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, key_c_type, key_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_bound});
        {
            __auto_type after_loop = match_emit_inline_loop_body(ctx, items, 2);
            context_ctx_pop_scope(ctx);
            context_ctx_dedent(ctx);
            context_ctx_emit(ctx, SLOP_STR("}"));
            context_ctx_dedent(ctx);
            context_ctx_emit(ctx, SLOP_STR("}"));
            context_ctx_dedent(ctx);
            context_ctx_emit(ctx, SLOP_STR("}"));
            context_ctx_emit_loop_end(ctx, after_loop);
        }
    }
}

void match_emit_inline_for_each_map_kv(context_TranspileContext* ctx, slop_list_types_SExpr_ptr binding_items, slop_list_types_SExpr_ptr items, int64_t len) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_879 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_879.has_value) {
            __auto_type kv_list_expr = _mv_879.value;
            __auto_type _mv_880 = (*kv_list_expr);
            switch (_mv_880.tag) {
                case types_SExpr_lst:
                {
                    __auto_type kv_lst = _mv_880.data.lst;
                    {
                        __auto_type kv_items = kv_lst.items;
                        if (((int64_t)((kv_items).len)) < 2) {
                            context_ctx_add_error(ctx, SLOP_STR("Map for-each needs ((k v) map)"));
                        } else {
                            __auto_type _mv_881 = ({ __auto_type _lst = kv_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_881.has_value) {
                                __auto_type k_expr = _mv_881.value;
                                __auto_type _mv_882 = ({ __auto_type _lst = kv_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_882.has_value) {
                                    __auto_type v_expr = _mv_882.value;
                                    __auto_type _mv_883 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_883.has_value) {
                                        __auto_type map_expr = _mv_883.value;
                                        __auto_type _mv_884 = (*k_expr);
                                        switch (_mv_884.tag) {
                                            case types_SExpr_sym:
                                            {
                                                __auto_type k_sym = _mv_884.data.sym;
                                                __auto_type _mv_885 = (*v_expr);
                                                switch (_mv_885.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type v_sym = _mv_885.data.sym;
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
                                                            context_ctx_emit(ctx, SLOP_STR("for (size_t _i = 0; _i < _coll->len; _i++) {"));
                                                            context_ctx_indent(ctx);
                                                            context_ctx_emit(ctx, SLOP_STR("{"));
                                                            context_ctx_indent(ctx);
                                                            {
                                                                __auto_type k_cast = context_ctx_str(ctx, key_c_type, SLOP_STR("*)slop_map_key_at(_coll, _i)"));
                                                                __auto_type k_prefix = context_ctx_str4(ctx, key_c_type, SLOP_STR(" "), k_name, SLOP_STR(" = *("));
                                                                __auto_type k_assign = context_ctx_str3(ctx, k_prefix, k_cast, SLOP_STR(";"));
                                                                context_ctx_emit(ctx, k_assign);
                                                            }
                                                            {
                                                                __auto_type v_cast = context_ctx_str(ctx, val_c_type, SLOP_STR("*)slop_map_value_at(_coll, _i)"));
                                                                __auto_type v_prefix = context_ctx_str4(ctx, val_c_type, SLOP_STR(" "), v_name, SLOP_STR(" = *("));
                                                                __auto_type v_assign = context_ctx_str3(ctx, v_prefix, v_cast, SLOP_STR(";"));
                                                                context_ctx_emit(ctx, v_assign);
                                                            }
                                                            context_ctx_push_scope(ctx);
                                                            context_ctx_bind_var(ctx, (context_VarEntry){k_sym.name, k_name, key_c_type, key_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_bound});
                                                            context_ctx_bind_var(ctx, (context_VarEntry){v_sym.name, v_name, val_c_type, val_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_bound});
                                                            {
                                                                __auto_type after_loop = match_emit_inline_loop_body(ctx, items, 2);
                                                                context_ctx_pop_scope(ctx);
                                                                context_ctx_dedent(ctx);
                                                                context_ctx_emit(ctx, SLOP_STR("}"));
                                                                context_ctx_dedent(ctx);
                                                                context_ctx_emit(ctx, SLOP_STR("}"));
                                                                context_ctx_dedent(ctx);
                                                                context_ctx_emit(ctx, SLOP_STR("}"));
                                                                context_ctx_emit_loop_end(ctx, after_loop);
                                                            }
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
                                    } else if (!_mv_883.has_value) {
                                        context_ctx_add_error(ctx, SLOP_STR("Missing map expression"));
                                    }
                                } else if (!_mv_882.has_value) {
                                    context_ctx_add_error(ctx, SLOP_STR("Missing value binding"));
                                }
                            } else if (!_mv_881.has_value) {
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
        } else if (!_mv_879.has_value) {
            context_ctx_add_error(ctx, SLOP_STR("Missing binding"));
        }
    }
}

void match_emit_inline_for_each(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if (len < 2) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid for-each: need binding"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        } else {
            __auto_type _mv_886 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_886.has_value) {
                __auto_type binding_expr = _mv_886.value;
                __auto_type _mv_887 = (*binding_expr);
                switch (_mv_887.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type binding_lst = _mv_887.data.lst;
                        {
                            __auto_type binding_items = binding_lst.items;
                            __auto_type binding_len = ((int64_t)((binding_items).len));
                            if (binding_len < 2) {
                                context_ctx_add_error_at(ctx, SLOP_STR("for-each binding needs (var coll)"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                            } else {
                                __auto_type _mv_888 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_888.has_value) {
                                    __auto_type first_elem = _mv_888.value;
                                    __auto_type _mv_889 = (*first_elem);
                                    switch (_mv_889.tag) {
                                        case types_SExpr_lst:
                                        {
                                            __auto_type _ = _mv_889.data.lst;
                                            match_emit_inline_for_each_map_kv(ctx, binding_items, items, len);
                                            break;
                                        }
                                        case types_SExpr_sym:
                                        {
                                            __auto_type var_sym = _mv_889.data.sym;
                                            {
                                                __auto_type var_name = ctype_to_c_name(arena, var_sym.name);
                                                __auto_type _mv_890 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_890.has_value) {
                                                    __auto_type coll_expr = _mv_890.value;
                                                    {
                                                        __auto_type coll_slop_type = expr_infer_expr_slop_type(ctx, coll_expr);
                                                        __auto_type resolved_type = expr_resolve_type_alias(ctx, coll_slop_type);
                                                        if (expr_is_set_type(resolved_type)) {
                                                            {
                                                                __auto_type coll_c = expr_transpile_expr(ctx, coll_expr);
                                                                match_emit_inline_for_each_set(ctx, var_name, var_sym, coll_c, resolved_type, items, len);
                                                            }
                                                        } else if (expr_is_map_type(resolved_type)) {
                                                            {
                                                                __auto_type coll_c = expr_transpile_expr(ctx, coll_expr);
                                                                match_emit_inline_for_each_map_keys(ctx, var_name, var_sym, coll_c, resolved_type, items, len);
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
                                                                    context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, elem_c_type, elem_slop_type, is_ptr_elem, 0, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_bound});
                                                                }
                                                                {
                                                                    __auto_type after_loop = match_emit_inline_loop_body(ctx, items, 2);
                                                                    context_ctx_pop_scope(ctx);
                                                                    context_ctx_dedent(ctx);
                                                                    context_ctx_emit(ctx, SLOP_STR("}"));
                                                                    context_ctx_dedent(ctx);
                                                                    context_ctx_emit(ctx, SLOP_STR("}"));
                                                                    context_ctx_emit_loop_end(ctx, after_loop);
                                                                }
                                                            }
                                                        }
                                                    }
                                                } else if (!_mv_890.has_value) {
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
                                } else if (!_mv_888.has_value) {
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
            } else if (!_mv_886.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing binding"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            }
        }
    }
}

void match_emit_inline_return(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if (len < 2) {
            context_ctx_emit_return(ctx, SLOP_STR(""));
        } else {
            __auto_type _mv_891 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_891.has_value) {
                __auto_type val_expr = _mv_891.value;
                match_emit_typed_return_expr(ctx, val_expr);
            } else if (!_mv_891.has_value) {
                context_ctx_emit_return(ctx, SLOP_STR(""));
            }
        }
    }
}

void match_emit_return_typed(context_TranspileContext* ctx, slop_string code) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type final_code = ((string_eq(code, SLOP_STR("none"))) ? ({ __auto_type _mv = context_ctx_get_current_return_type(ctx); _mv.has_value ? ({ __auto_type ret_type = _mv.value; ((context_ctx_is_option_c_type(ctx, ret_type)) ? context_ctx_str3(ctx, SLOP_STR("("), ret_type, SLOP_STR("){.has_value = false}")) : code); }) : (code); }) : code);
        context_ctx_emit_return(ctx, final_code);
    }
}

void match_emit_typed_return_expr(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_892 = (*expr);
    switch (_mv_892.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_892.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 1) {
                    match_emit_return_typed(ctx, context_ctx_range_wrap(ctx, expr_transpile_expr(ctx, expr), ({ __auto_type _mv = context_ctx_get_current_return_type(ctx); _mv.has_value ? ({ __auto_type rt = _mv.value; rt; }) : (SLOP_STR("")); }), context_ctx_get_current_return_slop_type(ctx), SLOP_STR("return value"), expr));
                } else {
                    __auto_type _mv_893 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_893.has_value) {
                        __auto_type head = _mv_893.value;
                        __auto_type _mv_894 = (*head);
                        switch (_mv_894.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_894.data.sym;
                                {
                                    __auto_type op = sym.name;
                                    if (string_eq(op, SLOP_STR("some"))) {
                                        __auto_type _mv_895 = context_ctx_get_current_return_type(ctx);
                                        if (_mv_895.has_value) {
                                            __auto_type ret_type = _mv_895.value;
                                            if (context_ctx_is_option_c_type(ctx, ret_type)) {
                                                if (((int64_t)((items).len)) < 2) {
                                                    match_emit_return_typed(ctx, context_ctx_range_wrap(ctx, expr_transpile_expr(ctx, expr), ({ __auto_type _mv = context_ctx_get_current_return_type(ctx); _mv.has_value ? ({ __auto_type rt = _mv.value; rt; }) : (SLOP_STR("")); }), context_ctx_get_current_return_slop_type(ctx), SLOP_STR("return value"), expr));
                                                } else {
                                                    __auto_type _mv_896 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_896.has_value) {
                                                        __auto_type inner_expr = _mv_896.value;
                                                        {
                                                            __auto_type inner_c = expr_transpile_expr(ctx, inner_expr);
                                                            context_ctx_emit_return(ctx, context_ctx_str5(ctx, SLOP_STR("("), ret_type, SLOP_STR("){.has_value = 1, .value = "), inner_c, SLOP_STR("}")));
                                                        }
                                                    } else if (!_mv_896.has_value) {
                                                        match_emit_return_typed(ctx, context_ctx_range_wrap(ctx, expr_transpile_expr(ctx, expr), ({ __auto_type _mv = context_ctx_get_current_return_type(ctx); _mv.has_value ? ({ __auto_type rt = _mv.value; rt; }) : (SLOP_STR("")); }), context_ctx_get_current_return_slop_type(ctx), SLOP_STR("return value"), expr));
                                                    }
                                                }
                                            } else {
                                                match_emit_return_typed(ctx, context_ctx_range_wrap(ctx, expr_transpile_expr(ctx, expr), ({ __auto_type _mv = context_ctx_get_current_return_type(ctx); _mv.has_value ? ({ __auto_type rt = _mv.value; rt; }) : (SLOP_STR("")); }), context_ctx_get_current_return_slop_type(ctx), SLOP_STR("return value"), expr));
                                            }
                                        } else if (!_mv_895.has_value) {
                                            match_emit_return_typed(ctx, context_ctx_range_wrap(ctx, expr_transpile_expr(ctx, expr), ({ __auto_type _mv = context_ctx_get_current_return_type(ctx); _mv.has_value ? ({ __auto_type rt = _mv.value; rt; }) : (SLOP_STR("")); }), context_ctx_get_current_return_slop_type(ctx), SLOP_STR("return value"), expr));
                                        }
                                    } else if (string_eq(op, SLOP_STR("none"))) {
                                        __auto_type _mv_897 = context_ctx_get_current_return_type(ctx);
                                        if (_mv_897.has_value) {
                                            __auto_type ret_type = _mv_897.value;
                                            if (context_ctx_is_option_c_type(ctx, ret_type)) {
                                                context_ctx_emit_return(ctx, context_ctx_str3(ctx, SLOP_STR("("), ret_type, SLOP_STR("){.has_value = false}")));
                                            } else {
                                                match_emit_return_typed(ctx, context_ctx_range_wrap(ctx, expr_transpile_expr(ctx, expr), ({ __auto_type _mv = context_ctx_get_current_return_type(ctx); _mv.has_value ? ({ __auto_type rt = _mv.value; rt; }) : (SLOP_STR("")); }), context_ctx_get_current_return_slop_type(ctx), SLOP_STR("return value"), expr));
                                            }
                                        } else if (!_mv_897.has_value) {
                                            match_emit_return_typed(ctx, context_ctx_range_wrap(ctx, expr_transpile_expr(ctx, expr), ({ __auto_type _mv = context_ctx_get_current_return_type(ctx); _mv.has_value ? ({ __auto_type rt = _mv.value; rt; }) : (SLOP_STR("")); }), context_ctx_get_current_return_slop_type(ctx), SLOP_STR("return value"), expr));
                                        }
                                    } else {
                                        match_emit_return_typed(ctx, context_ctx_range_wrap(ctx, expr_transpile_expr(ctx, expr), ({ __auto_type _mv = context_ctx_get_current_return_type(ctx); _mv.has_value ? ({ __auto_type rt = _mv.value; rt; }) : (SLOP_STR("")); }), context_ctx_get_current_return_slop_type(ctx), SLOP_STR("return value"), expr));
                                    }
                                }
                                break;
                            }
                            default: {
                                match_emit_return_typed(ctx, context_ctx_range_wrap(ctx, expr_transpile_expr(ctx, expr), ({ __auto_type _mv = context_ctx_get_current_return_type(ctx); _mv.has_value ? ({ __auto_type rt = _mv.value; rt; }) : (SLOP_STR("")); }), context_ctx_get_current_return_slop_type(ctx), SLOP_STR("return value"), expr));
                                break;
                            }
                        }
                    } else if (!_mv_893.has_value) {
                        match_emit_return_typed(ctx, context_ctx_range_wrap(ctx, expr_transpile_expr(ctx, expr), ({ __auto_type _mv = context_ctx_get_current_return_type(ctx); _mv.has_value ? ({ __auto_type rt = _mv.value; rt; }) : (SLOP_STR("")); }), context_ctx_get_current_return_slop_type(ctx), SLOP_STR("return value"), expr));
                    }
                }
            }
            break;
        }
        default: {
            match_emit_return_typed(ctx, context_ctx_range_wrap(ctx, expr_transpile_expr(ctx, expr), ({ __auto_type _mv = context_ctx_get_current_return_type(ctx); _mv.has_value ? ({ __auto_type rt = _mv.value; rt; }) : (SLOP_STR("")); }), context_ctx_get_current_return_slop_type(ctx), SLOP_STR("return value"), expr));
            break;
        }
    }
}

uint8_t match_is_pattern_literal(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_898 = (*expr);
    switch (_mv_898.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_898.data.sym;
            {
                __auto_type name = sym.name;
                return (string_eq(name, SLOP_STR("true")) || string_eq(name, SLOP_STR("false")));
            }
        }
        case types_SExpr_num:
        {
            __auto_type _ = _mv_898.data.num;
            return 1;
        }
        case types_SExpr_str:
        {
            __auto_type _ = _mv_898.data.str;
            return 1;
        }
        default: {
            return 0;
        }
    }
}

slop_string match_pattern_literal_to_c(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_899 = (*expr);
    switch (_mv_899.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_899.data.sym;
            {
                __auto_type name = sym.name;
                if (string_eq(name, SLOP_STR("true"))) {
                    return SLOP_STR("1");
                } else if (string_eq(name, SLOP_STR("false"))) {
                    return SLOP_STR("0");
                } else {
                    return SLOP_STR("");
                }
            }
        }
        case types_SExpr_num:
        {
            __auto_type n = _mv_899.data.num;
            return n.raw;
        }
        default: {
            return SLOP_STR("");
        }
    }
}

uint8_t match_has_literal_in_union_arm(types_SExpr* pat_expr) {
    SLOP_PRE(((pat_expr != NULL)), "(!= pat-expr nil)");
    __auto_type _mv_900 = (*pat_expr);
    switch (_mv_900.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_900.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                uint8_t found = 0;
                for (int64_t i = 1; i < len; i++) {
                    if (!(found)) {
                        __auto_type _mv_901 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_901.has_value) {
                            __auto_type item = _mv_901.value;
                            if (match_is_pattern_literal(item)) {
                                found = 1;
                            }
                        } else if (!_mv_901.has_value) {
                        }
                    }
                }
                return found;
            }
        }
        default: {
            return 0;
        }
    }
}

uint8_t match_has_literal_in_patterns(slop_list_types_SExpr_ptr patterns) {
    {
        __auto_type len = ((int64_t)((patterns).len));
        uint8_t found = 0;
        int64_t i = 0;
        while ((i < len) && !(found)) {
            __auto_type _mv_902 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_902.has_value) {
                __auto_type pat_expr = _mv_902.value;
                if (match_has_literal_in_union_arm(pat_expr)) {
                    found = 1;
                }
            } else if (!_mv_902.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

slop_string match_build_literal_guard_cond(context_TranspileContext* ctx, slop_string scrutinee_c, slop_string c_tag, slop_string tag_cond, types_SExpr* pattern, uint8_t is_multi) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((pattern != NULL)), "(!= pattern nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_903 = (*pattern);
        switch (_mv_903.tag) {
            case types_SExpr_lst:
            {
                __auto_type pat_lst = _mv_903.data.lst;
                {
                    __auto_type pat_items = pat_lst.items;
                    __auto_type pat_len = ((int64_t)((pat_items).len));
                    __auto_type cond = tag_cond;
                    for (int64_t bi = 1; bi < pat_len; bi++) {
                        __auto_type _mv_904 = ({ __auto_type _lst = pat_items; size_t _idx = (size_t)bi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_904.has_value) {
                            __auto_type item = _mv_904.value;
                            if (match_is_pattern_literal(item)) {
                                {
                                    __auto_type lit_c = ((expr_pattern_is_string_literal(item)) ? expr_transpile_literal(ctx, item) : match_pattern_literal_to_c(item));
                                    __auto_type field_idx = (bi - 1);
                                    __auto_type lhs = ((is_multi) ? context_ctx_str5(ctx, scrutinee_c, SLOP_STR(".data."), c_tag, SLOP_STR("."), context_ctx_str(ctx, SLOP_STR("f"), int_to_string(arena, field_idx))) : context_ctx_str4(ctx, scrutinee_c, SLOP_STR(".data."), c_tag, SLOP_STR("")));
                                    cond = context_ctx_str3(ctx, cond, SLOP_STR(" && "), expr_literal_pattern_cond(ctx, lhs, item, lit_c));
                                }
                            }
                        } else if (!_mv_904.has_value) {
                        }
                    }
                    return cond;
                }
            }
            default: {
                return tag_cond;
            }
        }
    }
}

void match_emit_union_literal_bindings(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* pattern, slop_string tag, slop_string union_type_name, slop_string c_tag, uint8_t is_multi) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((pattern != NULL)), "(!= pattern nil)");
    {
        __auto_type arena = (*ctx).arena;
        if (is_multi) {
            __auto_type _mv_905 = (*pattern);
            switch (_mv_905.tag) {
                case types_SExpr_lst:
                {
                    __auto_type pat_lst = _mv_905.data.lst;
                    {
                        __auto_type pat_items = pat_lst.items;
                        __auto_type pat_len = ((int64_t)((pat_items).len));
                        for (int64_t bi = 1; bi < pat_len; bi++) {
                            __auto_type _mv_906 = ({ __auto_type _lst = pat_items; size_t _idx = (size_t)bi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_906.has_value) {
                                __auto_type binding_expr = _mv_906.value;
                                if (!(match_is_pattern_literal(binding_expr))) {
                                    {
                                        __auto_type binding_name = parser_sexpr_get_symbol_name(binding_expr);
                                        if (!(string_eq(binding_name, SLOP_STR(""))) && !(string_eq(binding_name, SLOP_STR("_")))) {
                                            {
                                                __auto_type c_binding = ctype_to_c_name(arena, binding_name);
                                                __auto_type field_idx = (bi - 1);
                                                __auto_type field_key = context_ctx_str3(ctx, tag, SLOP_STR("__"), int_to_string(arena, field_idx));
                                                __auto_type payload_c_type = ({ __auto_type _mv = context_ctx_lookup_field_type(ctx, union_type_name, field_key); _mv.has_value ? ({ __auto_type ct = _mv.value; ct; }) : (SLOP_STR("auto")); });
                                                __auto_type payload_slop_type = ({ __auto_type _mv = context_ctx_lookup_field_slop_type(ctx, union_type_name, field_key); _mv.has_value ? ({ __auto_type st = _mv.value; st; }) : (SLOP_STR("")); });
                                                __auto_type field_name = context_ctx_str(ctx, SLOP_STR("f"), int_to_string(arena, field_idx));
                                                context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("__auto_type "), c_binding, SLOP_STR(" = "), scrutinee_c, context_ctx_str5(ctx, SLOP_STR(".data."), c_tag, SLOP_STR("."), field_name, SLOP_STR(";"))));
                                                context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_binding, payload_c_type, payload_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_bound});
                                            }
                                        }
                                    }
                                }
                            } else if (!_mv_906.has_value) {
                            }
                        }
                    }
                    break;
                }
                default: {
                    break;
                }
            }
        } else {
            __auto_type _mv_907 = match_extract_binding_name(pattern);
            if (_mv_907.has_value) {
                __auto_type binding_name = _mv_907.value;
                if ((!(string_eq(binding_name, SLOP_STR("true")))) && (!(string_eq(binding_name, SLOP_STR("false")))) && (!(string_eq(binding_name, SLOP_STR("_"))))) {
                    {
                        __auto_type c_binding = ctype_to_c_name(arena, binding_name);
                        __auto_type payload_c_type = ({ __auto_type _mv = context_ctx_lookup_field_type(ctx, union_type_name, tag); _mv.has_value ? ({ __auto_type ct = _mv.value; ct; }) : (SLOP_STR("auto")); });
                        __auto_type payload_slop_type = ({ __auto_type _mv = context_ctx_lookup_field_slop_type(ctx, union_type_name, tag); _mv.has_value ? ({ __auto_type st = _mv.value; st; }) : (SLOP_STR("")); });
                        context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("__auto_type "), c_binding, SLOP_STR(" = "), scrutinee_c, context_ctx_str3(ctx, SLOP_STR(".data."), c_tag, SLOP_STR(";"))));
                        context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_binding, payload_c_type, payload_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR(""), types_BindingOrigin_origin_bound});
                    }
                }
            } else if (!_mv_907.has_value) {
            }
        }
    }
}

void match_transpile_union_match_with_literals(context_TranspileContext* ctx, slop_string scrutinee_c, slop_string scrut_c_type, slop_list_types_SExpr_ptr patterns, slop_list_types_SExpr_ptr items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 2;
        uint8_t first = 1;
        uint8_t has_else = 0;
        while (i < len) {
            __auto_type _mv_908 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_908.has_value) {
                __auto_type branch = _mv_908.value;
                __auto_type _mv_909 = (*branch);
                switch (_mv_909.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_909.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if (((int64_t)((branch_items).len)) >= 2) {
                                __auto_type _mv_910 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_910.has_value) {
                                    __auto_type pattern = _mv_910.value;
                                    {
                                        __auto_type tag = match_get_pattern_tag(pattern);
                                        if (string_eq(tag, SLOP_STR("else")) || string_eq(tag, SLOP_STR("_"))) {
                                            has_else = 1;
                                            if (first) {
                                                context_ctx_emit(ctx, SLOP_STR("{"));
                                            } else {
                                                context_ctx_emit(ctx, SLOP_STR("} else {"));
                                            }
                                            context_ctx_indent(ctx);
                                            match_emit_branch_body(ctx, branch_items, is_return);
                                            context_ctx_dedent(ctx);
                                            first = 0;
                                        } else {
                                            __auto_type _mv_911 = context_ctx_resolve_enum_variant_for(ctx, tag, scrut_c_type, pattern);
                                            if (_mv_911.has_value) {
                                                __auto_type union_type_name = _mv_911.value;
                                                {
                                                    __auto_type c_tag = ctype_to_c_name(arena, tag);
                                                    __auto_type tag_cond = context_ctx_str5(ctx, scrutinee_c, SLOP_STR(".tag == "), union_type_name, SLOP_STR("_"), c_tag);
                                                    __auto_type count_key = context_ctx_str3(ctx, tag, SLOP_STR("__count"), SLOP_STR(""));
                                                    __auto_type multi_field_count = ({ __auto_type _mv = context_ctx_lookup_field_type(ctx, union_type_name, count_key); _mv.has_value ? ({ __auto_type ct = _mv.value; ct; }) : (SLOP_STR("")); });
                                                    __auto_type is_multi = !(string_eq(multi_field_count, SLOP_STR("")));
                                                    __auto_type full_cond = match_build_literal_guard_cond(ctx, scrutinee_c, c_tag, tag_cond, pattern, is_multi);
                                                    if (first) {
                                                        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), full_cond, SLOP_STR(") {")));
                                                    } else {
                                                        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("} else if ("), full_cond, SLOP_STR(") {")));
                                                    }
                                                    context_ctx_indent(ctx);
                                                    context_ctx_push_scope(ctx);
                                                    match_emit_union_literal_bindings(ctx, scrutinee_c, pattern, tag, union_type_name, c_tag, is_multi);
                                                    match_emit_branch_body(ctx, branch_items, is_return);
                                                    context_ctx_pop_scope(ctx);
                                                    context_ctx_dedent(ctx);
                                                    first = 0;
                                                }
                                            } else if (!_mv_911.has_value) {
                                                context_ctx_add_error(ctx, context_ctx_str3(ctx, SLOP_STR("unknown union variant in match: "), tag, SLOP_STR(" (not registered as enum variant)")));
                                            }
                                        }
                                    }
                                } else if (!_mv_910.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_908.has_value) {
            }
            i = (i + 1);
        }
        if (!(first)) {
            context_ctx_emit(ctx, SLOP_STR("}"));
        }
        match_emit_match_fallthrough_trap(ctx, is_return, has_else);
    }
}

