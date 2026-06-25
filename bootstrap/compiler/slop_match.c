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
void match_transpile_enum_match(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr items, uint8_t is_return);
void match_emit_enum_case(context_TranspileContext* ctx, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, uint8_t is_return);
void match_transpile_literal_match(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr items, uint8_t is_return);
void match_emit_literal_case(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, uint8_t is_return, uint8_t first);
void match_transpile_union_match(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr patterns, slop_list_types_SExpr_ptr items, uint8_t is_return);
void match_emit_union_case(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* pattern, slop_string tag, slop_string union_type_name, slop_list_types_SExpr_ptr branch_items, uint8_t is_return);
void match_transpile_generic_match(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr items, uint8_t is_return);
void match_emit_else_branch(context_TranspileContext* ctx, slop_list_types_SExpr_ptr branch_items, uint8_t is_return, uint8_t first);
void match_emit_branch_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr branch_items, uint8_t is_return);
void match_emit_branch_body_item(context_TranspileContext* ctx, types_SExpr* body_expr, uint8_t is_return, uint8_t is_last);
void match_emit_inline_let(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, uint8_t is_return, uint8_t is_last);
void match_emit_inline_bindings(context_TranspileContext* ctx, types_SExpr* bindings_expr);
void match_emit_single_inline_binding(context_TranspileContext* ctx, types_SExpr* binding);
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
void match_transpile_union_match_with_literals(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr patterns, slop_list_types_SExpr_ptr items, uint8_t is_return);

uint8_t match_is_option_match(slop_list_types_SExpr_ptr patterns) {
    {
        __auto_type len = ((int64_t)((patterns).len));
        uint8_t has_some = 0;
        uint8_t has_none = 0;
        int64_t i = 0;
        while ((i < len)) {
            __auto_type _mv_632 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_632.has_value) {
                __auto_type pat_expr = _mv_632.value;
                {
                    __auto_type tag = match_get_pattern_tag(pat_expr);
                    if (string_eq(tag, SLOP_STR("some"))) {
                        has_some = 1;
                    } else if (string_eq(tag, SLOP_STR("none"))) {
                        has_none = 1;
                    } else {
                    }
                }
            } else if (!_mv_632.has_value) {
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
        while ((i < len)) {
            __auto_type _mv_633 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_633.has_value) {
                __auto_type pat_expr = _mv_633.value;
                {
                    __auto_type tag = match_get_pattern_tag(pat_expr);
                    if (string_eq(tag, SLOP_STR("ok"))) {
                        has_ok = 1;
                    } else if (string_eq(tag, SLOP_STR("error"))) {
                        has_error = 1;
                    } else {
                    }
                }
            } else if (!_mv_633.has_value) {
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
        while (((i < len) && all_symbols)) {
            __auto_type _mv_634 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_634.has_value) {
                __auto_type pat_expr = _mv_634.value;
                __auto_type _mv_635 = (*pat_expr);
                switch (_mv_635.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type _ = _mv_635.data.sym;
                        break;
                    }
                    default: {
                        all_symbols = 0;
                        break;
                    }
                }
            } else if (!_mv_634.has_value) {
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
        while (((i < len) && !(has_literal))) {
            __auto_type _mv_636 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_636.has_value) {
                __auto_type pat_expr = _mv_636.value;
                __auto_type _mv_637 = (*pat_expr);
                switch (_mv_637.tag) {
                    case types_SExpr_num:
                    {
                        __auto_type _ = _mv_637.data.num;
                        has_literal = 1;
                        break;
                    }
                    case types_SExpr_str:
                    {
                        __auto_type _ = _mv_637.data.str;
                        has_literal = 1;
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_636.has_value) {
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
        while (((i < len) && !(has_union_variant))) {
            __auto_type _mv_638 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_638.has_value) {
                __auto_type pat_expr = _mv_638.value;
                {
                    __auto_type tag = match_get_pattern_tag(pat_expr);
                    if (((!(string_eq(tag, SLOP_STR("")))) && (!(string_eq(tag, SLOP_STR("some")))) && (!(string_eq(tag, SLOP_STR("none")))) && (!(string_eq(tag, SLOP_STR("ok")))) && (!(string_eq(tag, SLOP_STR("error")))) && (!(string_eq(tag, SLOP_STR("else")))) && (!(string_eq(tag, SLOP_STR("_")))))) {
                        __auto_type _mv_639 = context_ctx_lookup_enum_variant(ctx, tag);
                        if (_mv_639.has_value) {
                            __auto_type _ = _mv_639.value;
                            has_union_variant = 1;
                        } else if (!_mv_639.has_value) {
                        }
                    }
                }
            } else if (!_mv_638.has_value) {
            }
            i = (i + 1);
        }
        return has_union_variant;
    }
}

slop_string match_get_pattern_tag(types_SExpr* pat_expr) {
    SLOP_PRE(((pat_expr != NULL)), "(!= pat-expr nil)");
    __auto_type _mv_640 = (*pat_expr);
    switch (_mv_640.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_640.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_641 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_641.has_value) {
                        __auto_type head = _mv_641.value;
                        __auto_type _mv_642 = (*head);
                        switch (_mv_642.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_642.data.sym;
                                return sym.name;
                            }
                            default: {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_641.has_value) {
                        return SLOP_STR("");
                    }
                }
            }
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_640.data.sym;
            return sym.name;
        }
        default: {
            return SLOP_STR("");
        }
    }
}

slop_option_string match_extract_binding_name(types_SExpr* pat_expr) {
    SLOP_PRE(((pat_expr != NULL)), "(!= pat-expr nil)");
    __auto_type _mv_643 = (*pat_expr);
    switch (_mv_643.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_643.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 2)) {
                    return (slop_option_string){.has_value = false};
                } else {
                    __auto_type _mv_644 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_644.has_value) {
                        __auto_type binding = _mv_644.value;
                        __auto_type _mv_645 = (*binding);
                        switch (_mv_645.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_645.data.sym;
                                return (slop_option_string){.has_value = 1, .value = sym.name};
                            }
                            default: {
                                return (slop_option_string){.has_value = false};
                            }
                        }
                    } else if (!_mv_644.has_value) {
                        return (slop_option_string){.has_value = false};
                    }
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
    __auto_type _mv_646 = (*pat_expr);
    switch (_mv_646.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_646.data.lst;
            {
                __auto_type len = ((int64_t)((lst.items).len));
                if ((len > 1)) {
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
        __auto_type _mv_647 = (*expr);
        switch (_mv_647.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_647.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 3)) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid match: need value and at least one branch"), context_ctx_sexpr_line(expr), context_ctx_sexpr_col(expr));
                    } else {
                        __auto_type _mv_648 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_648.has_value) {
                            __auto_type scrutinee = _mv_648.value;
                            {
                                __auto_type scrutinee_c = expr_transpile_expr(ctx, scrutinee);
                                __auto_type patterns = match_collect_patterns(ctx, items);
                                __auto_type scrutinee_var = context_ctx_gensym(ctx, SLOP_STR("_mv"));
                                {
                                    __auto_type scrut_c_type = expr_infer_expr_c_type(ctx, scrutinee);
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
                                    match_transpile_enum_match(ctx, scrutinee_var, items, is_return);
                                } else if (match_is_literal_match(patterns)) {
                                    match_transpile_literal_match(ctx, scrutinee_var, items, is_return);
                                } else if (match_is_union_match(ctx, patterns)) {
                                    match_transpile_union_match(ctx, scrutinee_var, patterns, items, is_return);
                                } else {
                                    match_transpile_generic_match(ctx, scrutinee_var, items, is_return);
                                }
                            }
                        } else if (!_mv_648.has_value) {
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
        __auto_type result = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
        int64_t i = 2;
        while ((i < len)) {
            __auto_type _mv_649 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_649.has_value) {
                __auto_type branch = _mv_649.value;
                __auto_type _mv_650 = (*branch);
                switch (_mv_650.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_650.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if ((((int64_t)((branch_items).len)) >= 1)) {
                                __auto_type _mv_651 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_651.has_value) {
                                    __auto_type pattern = _mv_651.value;
                                    ({ __auto_type _lst_p = &(result); __auto_type _item = (pattern); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                } else if (!_mv_651.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_649.has_value) {
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
        while ((i < len)) {
            __auto_type _mv_652 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_652.has_value) {
                __auto_type branch = _mv_652.value;
                __auto_type _mv_653 = (*branch);
                switch (_mv_653.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_653.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if ((((int64_t)((branch_items).len)) >= 2)) {
                                __auto_type _mv_654 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_654.has_value) {
                                    __auto_type pattern = _mv_654.value;
                                    {
                                        __auto_type tag = match_get_pattern_tag(pattern);
                                        if (string_eq(tag, SLOP_STR("some"))) {
                                            match_emit_option_some_branch(ctx, scrutinee_c, scrutinee_expr, pattern, branch_items, is_return, first);
                                            first = 0;
                                        } else if (string_eq(tag, SLOP_STR("none"))) {
                                            match_emit_option_none_branch(ctx, scrutinee_c, branch_items, is_return, first);
                                            first = 0;
                                        } else if (string_eq(tag, SLOP_STR("else"))) {
                                            match_emit_else_branch(ctx, branch_items, is_return, first);
                                            first = 0;
                                        } else {
                                        }
                                    }
                                } else if (!_mv_654.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
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
        __auto_type _mv_655 = match_extract_binding_name(pattern);
        if (_mv_655.has_value) {
            __auto_type binding_name = _mv_655.value;
            {
                __auto_type c_name = ctype_to_c_name(arena, binding_name);
                __auto_type inner_slop_type = expr_infer_option_inner_slop_type(ctx, scrutinee_expr);
                __auto_type is_ptr = strlib_starts_with(inner_slop_type, SLOP_STR("(Ptr "));
                __auto_type inner_c_type = ((is_ptr) ? expr_slop_value_type_to_c_type(ctx, inner_slop_type) : SLOP_STR("auto"));
                context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, scrutinee_c, SLOP_STR(".value;"))));
                context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_name, inner_c_type, inner_slop_type, is_ptr, 0, 0, SLOP_STR(""), SLOP_STR("")});
            }
        } else if (!_mv_655.has_value) {
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
        while ((i < len)) {
            __auto_type _mv_656 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_656.has_value) {
                __auto_type branch = _mv_656.value;
                __auto_type _mv_657 = (*branch);
                switch (_mv_657.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_657.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if ((((int64_t)((branch_items).len)) >= 2)) {
                                __auto_type _mv_658 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_658.has_value) {
                                    __auto_type pattern = _mv_658.value;
                                    {
                                        __auto_type tag = match_get_pattern_tag(pattern);
                                        if (string_eq(tag, SLOP_STR("ok"))) {
                                            match_emit_result_ok_branch(ctx, scrutinee_c, scrutinee_expr, pattern, branch_items, is_return, first);
                                            first = 0;
                                        } else if (string_eq(tag, SLOP_STR("error"))) {
                                            match_emit_result_error_branch(ctx, scrutinee_c, scrutinee_expr, pattern, branch_items, is_return, first);
                                            first = 0;
                                        } else if (string_eq(tag, SLOP_STR("else"))) {
                                            match_emit_else_branch(ctx, branch_items, is_return, first);
                                            first = 0;
                                        } else {
                                        }
                                    }
                                } else if (!_mv_658.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_656.has_value) {
            }
            i = (i + 1);
        }
        if (!(first)) {
            context_ctx_emit(ctx, SLOP_STR("}"));
        }
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
        __auto_type _mv_659 = match_extract_binding_name(pattern);
        if (_mv_659.has_value) {
            __auto_type binding_name = _mv_659.value;
            {
                __auto_type c_name = ctype_to_c_name(arena, binding_name);
                __auto_type ok_slop_type = expr_infer_result_ok_slop_type(ctx, scrutinee_expr);
                __auto_type is_ptr = strlib_starts_with(ok_slop_type, SLOP_STR("(Ptr "));
                __auto_type ok_c_type = ((is_ptr) ? expr_slop_value_type_to_c_type(ctx, ok_slop_type) : SLOP_STR("auto"));
                context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, scrutinee_c, SLOP_STR(".data.ok;"))));
                context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_name, ok_c_type, ok_slop_type, is_ptr, 0, 0, SLOP_STR(""), SLOP_STR("")});
            }
        } else if (!_mv_659.has_value) {
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
        __auto_type _mv_660 = match_extract_binding_name(pattern);
        if (_mv_660.has_value) {
            __auto_type binding_name = _mv_660.value;
            {
                __auto_type c_name = ctype_to_c_name(arena, binding_name);
                __auto_type err_slop_type = expr_infer_result_err_slop_type(ctx, scrutinee_expr);
                __auto_type is_ptr = strlib_starts_with(err_slop_type, SLOP_STR("(Ptr "));
                __auto_type err_c_type = ((is_ptr) ? expr_slop_value_type_to_c_type(ctx, err_slop_type) : SLOP_STR("auto"));
                context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, scrutinee_c, SLOP_STR(".data.err;"))));
                context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_name, err_c_type, err_slop_type, is_ptr, 0, 0, SLOP_STR(""), SLOP_STR("")});
            }
        } else if (!_mv_660.has_value) {
        }
        match_emit_branch_body(ctx, branch_items, is_return);
        context_ctx_pop_scope(ctx);
        context_ctx_dedent(ctx);
    }
}

void match_transpile_enum_match(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 2;
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("switch ("), scrutinee_c, SLOP_STR(") {")));
        context_ctx_indent(ctx);
        while ((i < len)) {
            __auto_type _mv_661 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_661.has_value) {
                __auto_type branch = _mv_661.value;
                __auto_type _mv_662 = (*branch);
                switch (_mv_662.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_662.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if ((((int64_t)((branch_items).len)) >= 2)) {
                                __auto_type _mv_663 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_663.has_value) {
                                    __auto_type pattern = _mv_663.value;
                                    match_emit_enum_case(ctx, pattern, branch_items, is_return);
                                } else if (!_mv_663.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_661.has_value) {
            }
            i = (i + 1);
        }
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
    }
}

void match_emit_enum_case(context_TranspileContext* ctx, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((pattern != NULL)), "(!= pattern nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type tag = match_get_pattern_tag(pattern);
        if ((string_eq(tag, SLOP_STR("else")) || string_eq(tag, SLOP_STR("_")))) {
            context_ctx_emit(ctx, SLOP_STR("default: {"));
            context_ctx_indent(ctx);
            match_emit_branch_body(ctx, branch_items, is_return);
            context_ctx_emit(ctx, SLOP_STR("break;"));
            context_ctx_dedent(ctx);
            context_ctx_emit(ctx, SLOP_STR("}"));
        } else {
            __auto_type _mv_664 = context_ctx_lookup_enum_variant(ctx, tag);
            if (_mv_664.has_value) {
                __auto_type type_name = _mv_664.value;
                {
                    __auto_type c_case = context_ctx_str3(ctx, type_name, SLOP_STR("_"), ctype_to_c_name(arena, tag));
                    context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("case "), context_ctx_str(ctx, c_case, SLOP_STR(": {"))));
                    context_ctx_indent(ctx);
                    match_emit_branch_body(ctx, branch_items, is_return);
                    context_ctx_emit(ctx, SLOP_STR("break;"));
                    context_ctx_dedent(ctx);
                    context_ctx_emit(ctx, SLOP_STR("}"));
                }
            } else if (!_mv_664.has_value) {
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
        while ((i < len)) {
            __auto_type _mv_665 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_665.has_value) {
                __auto_type branch = _mv_665.value;
                __auto_type _mv_666 = (*branch);
                switch (_mv_666.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_666.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if ((((int64_t)((branch_items).len)) >= 2)) {
                                __auto_type _mv_667 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_667.has_value) {
                                    __auto_type pattern = _mv_667.value;
                                    match_emit_literal_case(ctx, scrutinee_c, pattern, branch_items, is_return, first);
                                    first = 0;
                                } else if (!_mv_667.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_665.has_value) {
            }
            i = (i + 1);
        }
        if (!(first)) {
            context_ctx_emit(ctx, SLOP_STR("}"));
        }
    }
}

void match_emit_literal_case(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* pattern, slop_list_types_SExpr_ptr branch_items, uint8_t is_return, uint8_t first) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((pattern != NULL)), "(!= pattern nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type tag = match_get_pattern_tag(pattern);
        if (string_eq(tag, SLOP_STR("else"))) {
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
                if (first) {
                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("if ("), scrutinee_c, SLOP_STR(" == "), literal_c, SLOP_STR(") {")));
                } else {
                    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("} else if ("), scrutinee_c, SLOP_STR(" == "), literal_c, SLOP_STR(") {")));
                }
                context_ctx_indent(ctx);
                match_emit_branch_body(ctx, branch_items, is_return);
                context_ctx_dedent(ctx);
            }
        }
    }
}

void match_transpile_union_match(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr patterns, slop_list_types_SExpr_ptr items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (match_has_literal_in_patterns(patterns)) {
        match_transpile_union_match_with_literals(ctx, scrutinee_c, patterns, items, is_return);
    } else {
        {
            __auto_type arena = (*ctx).arena;
            __auto_type len = ((int64_t)((items).len));
            int64_t i = 2;
            uint8_t first = 1;
            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("switch ("), scrutinee_c, SLOP_STR(".tag) {")));
            context_ctx_indent(ctx);
            while ((i < len)) {
                __auto_type _mv_668 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_668.has_value) {
                    __auto_type branch = _mv_668.value;
                    __auto_type _mv_669 = (*branch);
                    switch (_mv_669.tag) {
                        case types_SExpr_lst:
                        {
                            __auto_type branch_lst = _mv_669.data.lst;
                            {
                                __auto_type branch_items = branch_lst.items;
                                if ((((int64_t)((branch_items).len)) >= 2)) {
                                    __auto_type _mv_670 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_670.has_value) {
                                        __auto_type pattern = _mv_670.value;
                                        {
                                            __auto_type tag = match_get_pattern_tag(pattern);
                                            if ((string_eq(tag, SLOP_STR("else")) || string_eq(tag, SLOP_STR("_")))) {
                                                context_ctx_emit(ctx, SLOP_STR("default: {"));
                                                context_ctx_indent(ctx);
                                                match_emit_branch_body(ctx, branch_items, is_return);
                                                if (!(is_return)) {
                                                    context_ctx_emit(ctx, SLOP_STR("break;"));
                                                }
                                                context_ctx_dedent(ctx);
                                                context_ctx_emit(ctx, SLOP_STR("}"));
                                            } else {
                                                __auto_type _mv_671 = context_ctx_lookup_enum_variant(ctx, tag);
                                                if (_mv_671.has_value) {
                                                    __auto_type union_type_name = _mv_671.value;
                                                    match_emit_union_case(ctx, scrutinee_c, pattern, tag, union_type_name, branch_items, is_return);
                                                } else if (!_mv_671.has_value) {
                                                    context_ctx_add_error(ctx, context_ctx_str3(ctx, SLOP_STR("unknown union variant in match: "), tag, SLOP_STR(" (not registered as enum variant)")));
                                                }
                                            }
                                        }
                                    } else if (!_mv_670.has_value) {
                                    }
                                }
                            }
                            break;
                        }
                        default: {
                            break;
                        }
                    }
                } else if (!_mv_668.has_value) {
                }
                i = (i + 1);
            }
            context_ctx_dedent(ctx);
            context_ctx_emit(ctx, SLOP_STR("}"));
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
                __auto_type _mv_672 = (*pattern);
                switch (_mv_672.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type pat_lst = _mv_672.data.lst;
                        {
                            __auto_type pat_items = pat_lst.items;
                            __auto_type pat_len = ((int64_t)((pat_items).len));
                            for (int64_t bi = 1; bi < pat_len; bi++) {
                                __auto_type _mv_673 = ({ __auto_type _lst = pat_items; size_t _idx = (size_t)bi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_673.has_value) {
                                    __auto_type binding_expr = _mv_673.value;
                                    {
                                        __auto_type binding_name = parser_sexpr_get_symbol_name(binding_expr);
                                        if ((!(string_eq(binding_name, SLOP_STR(""))) && !(string_eq(binding_name, SLOP_STR("_"))))) {
                                            {
                                                __auto_type c_binding = ctype_to_c_name(arena, binding_name);
                                                __auto_type field_idx = (bi - 1);
                                                __auto_type field_key = context_ctx_str3(ctx, tag, SLOP_STR("__"), int_to_string(arena, field_idx));
                                                __auto_type payload_c_type = ({ __auto_type _mv = context_ctx_lookup_field_type(ctx, union_type_name, field_key); _mv.has_value ? ({ __auto_type ct = _mv.value; ct; }) : (SLOP_STR("auto")); });
                                                __auto_type payload_slop_type = ({ __auto_type _mv = context_ctx_lookup_field_slop_type(ctx, union_type_name, field_key); _mv.has_value ? ({ __auto_type st = _mv.value; st; }) : (SLOP_STR("")); });
                                                __auto_type field_name = context_ctx_str(ctx, SLOP_STR("f"), int_to_string(arena, field_idx));
                                                context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("__auto_type "), c_binding, SLOP_STR(" = "), scrutinee_c, context_ctx_str5(ctx, SLOP_STR(".data."), c_tag, SLOP_STR("."), field_name, SLOP_STR(";"))));
                                                context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_binding, payload_c_type, payload_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                            }
                                        }
                                    }
                                } else if (!_mv_673.has_value) {
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
                __auto_type _mv_674 = match_extract_binding_name(pattern);
                if (_mv_674.has_value) {
                    __auto_type binding_name = _mv_674.value;
                    {
                        __auto_type c_binding = ctype_to_c_name(arena, binding_name);
                        __auto_type payload_c_type = ({ __auto_type _mv = context_ctx_lookup_field_type(ctx, union_type_name, tag); _mv.has_value ? ({ __auto_type ct = _mv.value; ct; }) : (SLOP_STR("auto")); });
                        __auto_type payload_slop_type = ({ __auto_type _mv = context_ctx_lookup_field_slop_type(ctx, union_type_name, tag); _mv.has_value ? ({ __auto_type st = _mv.value; st; }) : (SLOP_STR("")); });
                        context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("__auto_type "), c_binding, SLOP_STR(" = "), scrutinee_c, context_ctx_str3(ctx, SLOP_STR(".data."), c_tag, SLOP_STR(";"))));
                        context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_binding, payload_c_type, payload_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                    }
                } else if (!_mv_674.has_value) {
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
        while ((i < len)) {
            __auto_type _mv_675 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_675.has_value) {
                __auto_type body_expr = _mv_675.value;
                {
                    __auto_type is_last = (i == (len - 1));
                    match_emit_branch_body_item(ctx, body_expr, is_return, is_last);
                }
            } else if (!_mv_675.has_value) {
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
        __auto_type _mv_676 = (*body_expr);
        switch (_mv_676.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_676.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) < 1)) {
                        context_ctx_emit(ctx, SLOP_STR("/* empty list */;"));
                    } else {
                        __auto_type _mv_677 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_677.has_value) {
                            __auto_type head_expr = _mv_677.value;
                            __auto_type _mv_678 = (*head_expr);
                            switch (_mv_678.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_678.data.sym;
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
                                        } else if ((strlib_starts_with(op, SLOP_STR("@")) && !(string_eq(op, SLOP_STR("@"))))) {
                                        } else {
                                            if ((is_return && is_last)) {
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
                        } else if (!_mv_677.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("empty"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                        }
                    }
                }
                break;
            }
            default: {
                if ((is_return && is_last)) {
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
        if ((len < 2)) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid let"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        } else {
            context_ctx_emit(ctx, SLOP_STR("{"));
            context_ctx_indent(ctx);
            context_ctx_push_scope(ctx);
            __auto_type _mv_679 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_679.has_value) {
                __auto_type bindings_expr = _mv_679.value;
                match_emit_inline_bindings(ctx, bindings_expr);
            } else if (!_mv_679.has_value) {
            }
            {
                int64_t i = 2;
                while ((i < len)) {
                    __auto_type _mv_680 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_680.has_value) {
                        __auto_type body_item = _mv_680.value;
                        {
                            __auto_type body_last = (i == (len - 1));
                            match_emit_branch_body_item(ctx, body_item, is_return, (is_last && body_last));
                        }
                    } else if (!_mv_680.has_value) {
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
        __auto_type _mv_681 = (*bindings_expr);
        switch (_mv_681.tag) {
            case types_SExpr_lst:
            {
                __auto_type bindings_lst = _mv_681.data.lst;
                {
                    __auto_type bindings = bindings_lst.items;
                    __auto_type len = ((int64_t)((bindings).len));
                    __auto_type i = 0;
                    while ((i < len)) {
                        __auto_type _mv_682 = ({ __auto_type _lst = bindings; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_682.has_value) {
                            __auto_type binding = _mv_682.value;
                            match_emit_single_inline_binding(ctx, binding);
                        } else if (!_mv_682.has_value) {
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
        __auto_type _mv_683 = (*binding);
        switch (_mv_683.tag) {
            case types_SExpr_lst:
            {
                __auto_type binding_lst = _mv_683.data.lst;
                {
                    __auto_type items = binding_lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    {
                        __auto_type has_mut = match_binding_starts_with_mut(items);
                        __auto_type start_idx = ((match_binding_starts_with_mut(items)) ? 1 : 0);
                        if (((len - start_idx) < 2)) {
                            context_ctx_add_error_at(ctx, SLOP_STR("invalid binding"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                        } else {
                            __auto_type _mv_684 = ({ __auto_type _lst = items; size_t _idx = (size_t)start_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_684.has_value) {
                                __auto_type name_expr = _mv_684.value;
                                __auto_type _mv_685 = (*name_expr);
                                switch (_mv_685.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type name_sym = _mv_685.data.sym;
                                        {
                                            __auto_type raw_name = name_sym.name;
                                            __auto_type c_name = ctype_to_c_name(arena, raw_name);
                                            if (((len - start_idx) >= 3)) {
                                                {
                                                    __auto_type type_idx = (start_idx + 1);
                                                    __auto_type val_idx = (start_idx + 2);
                                                    __auto_type _mv_686 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_686.has_value) {
                                                        __auto_type type_expr = _mv_686.value;
                                                        if (match_is_type_expr(type_expr)) {
                                                            __auto_type _mv_687 = ({ __auto_type _lst = items; size_t _idx = (size_t)val_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_687.has_value) {
                                                                __auto_type val_expr = _mv_687.value;
                                                                {
                                                                    __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                                    __auto_type is_ptr = strlib_ends_with(c_type, SLOP_STR("*"));
                                                                    {
                                                                        __auto_type final_init = ((strlib_starts_with(c_type, SLOP_STR("slop_option_"))) ? ({ __auto_type some_val = match_get_some_value_inline(val_expr); ({ __auto_type _mv = some_val; _mv.has_value ? ({ __auto_type inner_expr = _mv.value; ({ __auto_type inner_c = expr_transpile_expr(ctx, inner_expr); context_ctx_str5(ctx, SLOP_STR("("), c_type, SLOP_STR("){.has_value = 1, .value = "), inner_c, SLOP_STR("}")); }); }) : (((match_is_none_form_inline(val_expr)) ? context_ctx_str3(ctx, SLOP_STR("("), c_type, SLOP_STR("){.has_value = false}")) : expr_transpile_expr(ctx, val_expr))); }); }) : expr_transpile_expr(ctx, val_expr));
                                                                        __auto_type slop_type_str = ctype_sexpr_to_type_string(arena, type_expr);
                                                                        context_ctx_emit(ctx, context_ctx_str5(ctx, c_type, SLOP_STR(" "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, final_init, SLOP_STR(";"))));
                                                                        context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, c_type, slop_type_str, is_ptr, has_mut, 0, SLOP_STR(""), SLOP_STR("")});
                                                                    }
                                                                }
                                                            } else if (!_mv_687.has_value) {
                                                                context_ctx_add_error_at(ctx, SLOP_STR("missing value"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                                                            }
                                                        } else {
                                                            __auto_type _mv_688 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_688.has_value) {
                                                                __auto_type val_expr = _mv_688.value;
                                                                {
                                                                    __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                                    __auto_type inferred_slop_type = expr_infer_expr_slop_type(ctx, val_expr);
                                                                    __auto_type ptr_type_opt = match_get_arena_alloc_ptr_type_inline(ctx, val_expr);
                                                                    __auto_type _mv_689 = ptr_type_opt;
                                                                    if (_mv_689.has_value) {
                                                                        __auto_type ptr_type = _mv_689.value;
                                                                        context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, val_c, SLOP_STR(";"))));
                                                                        context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, ptr_type, inferred_slop_type, 1, has_mut, 0, SLOP_STR(""), SLOP_STR("")});
                                                                    } else if (!_mv_689.has_value) {
                                                                        {
                                                                            __auto_type inferred_type = expr_infer_expr_c_type(ctx, val_expr);
                                                                            __auto_type is_ptr = strlib_ends_with(inferred_type, SLOP_STR("*"));
                                                                            context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, val_c, SLOP_STR(";"))));
                                                                            context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, inferred_type, inferred_slop_type, is_ptr, has_mut, 0, SLOP_STR(""), SLOP_STR("")});
                                                                        }
                                                                    }
                                                                }
                                                            } else if (!_mv_688.has_value) {
                                                                context_ctx_add_error_at(ctx, SLOP_STR("missing value"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                                                            }
                                                        }
                                                    } else if (!_mv_686.has_value) {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("missing type/value"), context_ctx_sexpr_line(binding), context_ctx_sexpr_col(binding));
                                                    }
                                                }
                                            } else {
                                                {
                                                    __auto_type val_idx = (start_idx + 1);
                                                    __auto_type _mv_690 = ({ __auto_type _lst = items; size_t _idx = (size_t)val_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_690.has_value) {
                                                        __auto_type val_expr = _mv_690.value;
                                                        {
                                                            __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                            __auto_type inferred_slop_type = expr_infer_expr_slop_type(ctx, val_expr);
                                                            __auto_type ptr_type_opt = match_get_arena_alloc_ptr_type_inline(ctx, val_expr);
                                                            __auto_type _mv_691 = ptr_type_opt;
                                                            if (_mv_691.has_value) {
                                                                __auto_type ptr_type = _mv_691.value;
                                                                context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, val_c, SLOP_STR(";"))));
                                                                context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, ptr_type, inferred_slop_type, 1, has_mut, 0, SLOP_STR(""), SLOP_STR("")});
                                                            } else if (!_mv_691.has_value) {
                                                                {
                                                                    __auto_type inferred_type = expr_infer_expr_c_type(ctx, val_expr);
                                                                    __auto_type is_ptr = strlib_ends_with(inferred_type, SLOP_STR("*"));
                                                                    context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, val_c, SLOP_STR(";"))));
                                                                    context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, inferred_type, inferred_slop_type, is_ptr, has_mut, 0, SLOP_STR(""), SLOP_STR("")});
                                                                }
                                                            }
                                                        }
                                                    } else if (!_mv_690.has_value) {
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
                            } else if (!_mv_684.has_value) {
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

uint8_t match_binding_starts_with_mut(slop_list_types_SExpr_ptr items) {
    if ((((int64_t)((items).len)) < 1)) {
        return 0;
    } else {
        __auto_type _mv_692 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_692.has_value) {
            __auto_type first = _mv_692.value;
            __auto_type _mv_693 = (*first);
            switch (_mv_693.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_693.data.sym;
                    return string_eq(sym.name, SLOP_STR("mut"));
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_692.has_value) {
            return 0;
        }
    }
}

uint8_t match_is_type_expr(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_694 = (*expr);
    switch (_mv_694.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_694.data.sym;
            {
                __auto_type name = sym.name;
                if ((string_len(name) == 0)) {
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
            __auto_type _ = _mv_694.data.lst;
            return 1;
        }
        default: {
            return 0;
        }
    }
}

uint8_t match_is_none_form_inline(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_695 = (*expr);
    switch (_mv_695.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_695.data.sym;
            return string_eq(sym.name, SLOP_STR("none"));
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_695.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 1)) {
                    __auto_type _mv_696 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_696.has_value) {
                        __auto_type head = _mv_696.value;
                        __auto_type _mv_697 = (*head);
                        switch (_mv_697.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_697.data.sym;
                                return string_eq(sym.name, SLOP_STR("none"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_696.has_value) {
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

slop_string match_to_c_type_simple(slop_arena* arena, types_SExpr* type_expr) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    return ctype_to_c_type(arena, type_expr);
}

slop_option_string match_get_arena_alloc_ptr_type_inline(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_698 = (*expr);
        switch (_mv_698.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_698.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 3)) {
                        __auto_type _mv_699 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_699.has_value) {
                            __auto_type head_ptr = _mv_699.value;
                            __auto_type _mv_700 = (*head_ptr);
                            switch (_mv_700.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_700.data.sym;
                                    if (string_eq(head_sym.name, SLOP_STR("arena-alloc"))) {
                                        __auto_type _mv_701 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_701.has_value) {
                                            __auto_type size_expr = _mv_701.value;
                                            return match_extract_sizeof_type_inline(ctx, size_expr);
                                        } else if (!_mv_701.has_value) {
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
                        } else if (!_mv_699.has_value) {
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

slop_option_string match_extract_sizeof_type_inline(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_702 = (*expr);
        switch (_mv_702.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_702.data.sym;
                {
                    __auto_type type_name = sym.name;
                    __auto_type _mv_703 = context_ctx_lookup_type(ctx, type_name);
                    if (_mv_703.has_value) {
                        __auto_type entry = _mv_703.value;
                        return (slop_option_string){.has_value = 1, .value = context_ctx_str(ctx, entry.c_name, SLOP_STR("*"))};
                    } else if (!_mv_703.has_value) {
                        return (slop_option_string){.has_value = false};
                    }
                }
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_702.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 2)) {
                        __auto_type _mv_704 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_704.has_value) {
                            __auto_type head_ptr = _mv_704.value;
                            __auto_type _mv_705 = (*head_ptr);
                            switch (_mv_705.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_705.data.sym;
                                    if (string_eq(head_sym.name, SLOP_STR("sizeof"))) {
                                        __auto_type _mv_706 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_706.has_value) {
                                            __auto_type type_expr = _mv_706.value;
                                            {
                                                __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                return (slop_option_string){.has_value = 1, .value = context_ctx_str(ctx, c_type, SLOP_STR("*"))};
                                            }
                                        } else if (!_mv_706.has_value) {
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
                        } else if (!_mv_704.has_value) {
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

void match_emit_inline_do(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, uint8_t is_return, uint8_t is_last) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 1;
        while ((i < len)) {
            __auto_type _mv_707 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_707.has_value) {
                __auto_type item = _mv_707.value;
                {
                    __auto_type item_last = (i == (len - 1));
                    match_emit_branch_body_item(ctx, item, is_return, (is_last && item_last));
                }
            } else if (!_mv_707.has_value) {
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
        if ((len < 3)) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid if"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        } else {
            __auto_type _mv_708 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_708.has_value) {
                __auto_type cond_expr = _mv_708.value;
                {
                    __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), cond_c, SLOP_STR(") {")));
                }
            } else if (!_mv_708.has_value) {
                context_ctx_emit(ctx, SLOP_STR("if (/* missing */) {"));
            }
            context_ctx_indent(ctx);
            __auto_type _mv_709 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_709.has_value) {
                __auto_type then_expr = _mv_709.value;
                match_emit_branch_body_item(ctx, then_expr, is_return, 1);
            } else if (!_mv_709.has_value) {
            }
            context_ctx_dedent(ctx);
            if ((len >= 4)) {
                context_ctx_emit(ctx, SLOP_STR("} else {"));
                context_ctx_indent(ctx);
                __auto_type _mv_710 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_710.has_value) {
                    __auto_type else_expr = _mv_710.value;
                    match_emit_branch_body_item(ctx, else_expr, is_return, 1);
                } else if (!_mv_710.has_value) {
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
        if ((len < 3)) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid while"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        } else {
            __auto_type _mv_711 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_711.has_value) {
                __auto_type cond_expr = _mv_711.value;
                {
                    __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("while ("), cond_c, SLOP_STR(") {")));
                }
            } else if (!_mv_711.has_value) {
                context_ctx_emit(ctx, SLOP_STR("while (/* missing */) {"));
            }
            context_ctx_indent(ctx);
            match_emit_inline_body_items(ctx, items, 2);
            context_ctx_dedent(ctx);
            context_ctx_emit(ctx, SLOP_STR("}"));
        }
    }
}

slop_option_string match_get_var_c_type_inline(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    __auto_type _mv_712 = (*expr);
    switch (_mv_712.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_712.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_713 = context_ctx_lookup_var(ctx, name);
                if (_mv_713.has_value) {
                    __auto_type var_entry = _mv_713.value;
                    return (slop_option_string){.has_value = 1, .value = var_entry.c_type};
                } else if (!_mv_713.has_value) {
                    return (slop_option_string){.has_value = false};
                }
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
        __auto_type _mv_714 = (*expr);
        switch (_mv_714.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_714.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 2)) {
                        __auto_type _mv_715 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_715.has_value) {
                            __auto_type head = _mv_715.value;
                            __auto_type _mv_716 = (*head);
                            switch (_mv_716.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_716.data.sym;
                                    if (string_eq(sym.name, SLOP_STR("some"))) {
                                        __auto_type _mv_717 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_717.has_value) {
                                            __auto_type val = _mv_717.value;
                                            result = (slop_option_types_SExpr_ptr){.has_value = 1, .value = val};
                                        } else if (!_mv_717.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_715.has_value) {
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
        if ((len == 5)) {
            __auto_type _mv_718 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_718.has_value) {
                __auto_type target_expr = _mv_718.value;
                __auto_type _mv_719 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_719.has_value) {
                    __auto_type field_expr = _mv_719.value;
                    __auto_type _mv_720 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_720.has_value) {
                        __auto_type type_expr = _mv_720.value;
                        __auto_type _mv_721 = ({ __auto_type _lst = items; size_t _idx = (size_t)4; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_721.has_value) {
                            __auto_type value_expr = _mv_721.value;
                            {
                                __auto_type field_name = match_get_field_name_inline(ctx, field_expr);
                                __auto_type c_type = ctype_to_c_type(arena, type_expr);
                                {
                                    __auto_type target_access = ((match_is_deref_inline(target_expr)) ? ({ __auto_type inner_c = match_get_deref_inner_inline(ctx, target_expr); context_ctx_str(ctx, SLOP_STR("(*"), context_ctx_str(ctx, inner_c, SLOP_STR(")."))); }) : ({ __auto_type target_c = expr_transpile_expr(ctx, target_expr); context_ctx_str(ctx, target_c, SLOP_STR(".")); }));
                                    if (strlib_starts_with(c_type, SLOP_STR("slop_option_"))) {
                                        if (match_is_none_form_inline(value_expr)) {
                                            context_ctx_emit(ctx, context_ctx_str(ctx, target_access, context_ctx_str(ctx, field_name, context_ctx_str3(ctx, SLOP_STR(" = ("), c_type, SLOP_STR("){.has_value = false};")))));
                                        } else {
                                            __auto_type _mv_722 = match_get_some_value_inline(value_expr);
                                            if (_mv_722.has_value) {
                                                __auto_type inner_val = _mv_722.value;
                                                {
                                                    __auto_type val_c = expr_transpile_expr(ctx, inner_val);
                                                    context_ctx_emit(ctx, context_ctx_str(ctx, target_access, context_ctx_str(ctx, field_name, context_ctx_str5(ctx, SLOP_STR(" = ("), c_type, SLOP_STR("){.has_value = 1, .value = "), val_c, SLOP_STR("};")))));
                                                }
                                            } else if (!_mv_722.has_value) {
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
                        } else if (!_mv_721.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                        }
                    } else if (!_mv_720.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing set! type"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    }
                } else if (!_mv_719.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("missing set! field"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                }
            } else if (!_mv_718.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            }
        } else if ((len == 4)) {
            __auto_type _mv_723 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_723.has_value) {
                __auto_type target_expr = _mv_723.value;
                __auto_type _mv_724 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_724.has_value) {
                    __auto_type field_expr = _mv_724.value;
                    __auto_type _mv_725 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_725.has_value) {
                        __auto_type value_expr = _mv_725.value;
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
                    } else if (!_mv_725.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    }
                } else if (!_mv_724.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("missing set! field"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                }
            } else if (!_mv_723.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            }
        } else if ((len >= 3)) {
            __auto_type _mv_726 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_726.has_value) {
                __auto_type target_expr = _mv_726.value;
                __auto_type _mv_727 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_727.has_value) {
                    __auto_type val_expr = _mv_727.value;
                    {
                        __auto_type target_c = expr_transpile_expr(ctx, target_expr);
                        __auto_type target_type_opt = match_get_var_c_type_inline(ctx, target_expr);
                        __auto_type _mv_728 = target_type_opt;
                        if (_mv_728.has_value) {
                            __auto_type target_type = _mv_728.value;
                            if (strlib_starts_with(target_type, SLOP_STR("slop_option_"))) {
                                {
                                    __auto_type some_val_opt = match_get_some_value_inline(val_expr);
                                    __auto_type _mv_729 = some_val_opt;
                                    if (_mv_729.has_value) {
                                        __auto_type inner_expr = _mv_729.value;
                                        {
                                            __auto_type inner_c = expr_transpile_expr(ctx, inner_expr);
                                            context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str5(ctx, SLOP_STR(" = ("), target_type, SLOP_STR("){.has_value = 1, .value = "), inner_c, SLOP_STR("};"))));
                                        }
                                    } else if (!_mv_729.has_value) {
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
                        } else if (!_mv_728.has_value) {
                            {
                                __auto_type some_val_opt = match_get_some_value_inline(val_expr);
                                __auto_type _mv_730 = some_val_opt;
                                if (_mv_730.has_value) {
                                    __auto_type inner_expr = _mv_730.value;
                                    {
                                        __auto_type inner_c = expr_transpile_expr(ctx, inner_expr);
                                        __auto_type inner_type = expr_infer_expr_c_type(ctx, inner_expr);
                                        __auto_type option_type = expr_c_type_to_option_type_name(ctx, inner_type);
                                        context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str5(ctx, SLOP_STR(" = ("), option_type, SLOP_STR("){.has_value = 1, .value = "), inner_c, SLOP_STR("};"))));
                                    }
                                } else if (!_mv_730.has_value) {
                                    if (match_is_none_form_inline(val_expr)) {
                                        __auto_type _mv_731 = context_ctx_get_current_return_type(ctx);
                                        if (_mv_731.has_value) {
                                            __auto_type ret_type = _mv_731.value;
                                            if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                                                context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str3(ctx, SLOP_STR(" = ("), ret_type, SLOP_STR("){.has_value = false};"))));
                                            } else {
                                                {
                                                    __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                    context_ctx_emit(ctx, context_ctx_str4(ctx, target_c, SLOP_STR(" = "), val_c, SLOP_STR(";")));
                                                }
                                            }
                                        } else if (!_mv_731.has_value) {
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
                } else if (!_mv_727.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                }
            } else if (!_mv_726.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            }
        } else {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid set!"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        }
    }
}

uint8_t match_is_deref_inline(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_732 = (*expr);
    switch (_mv_732.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_732.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 2)) {
                    return 0;
                } else {
                    __auto_type _mv_733 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_733.has_value) {
                        __auto_type head = _mv_733.value;
                        __auto_type _mv_734 = (*head);
                        switch (_mv_734.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_734.data.sym;
                                return string_eq(sym.name, SLOP_STR("deref"));
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
        }
        default: {
            return 0;
        }
    }
}

slop_string match_get_deref_inner_inline(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_735 = (*expr);
    switch (_mv_735.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_735.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type _mv_736 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_736.has_value) {
                    __auto_type inner = _mv_736.value;
                    return expr_transpile_expr(ctx, inner);
                } else if (!_mv_736.has_value) {
                    return SLOP_STR("/* missing deref arg */");
                }
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
        __auto_type _mv_737 = (*expr);
        switch (_mv_737.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_737.data.sym;
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
        if ((len < 2)) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid when"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        } else {
            __auto_type _mv_738 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_738.has_value) {
                __auto_type cond_expr = _mv_738.value;
                {
                    __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), cond_c, SLOP_STR(") {")));
                }
            } else if (!_mv_738.has_value) {
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
        while ((i < len)) {
            __auto_type _mv_739 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_739.has_value) {
                __auto_type clause_expr = _mv_739.value;
                __auto_type _mv_740 = (*clause_expr);
                switch (_mv_740.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type clause_lst = _mv_740.data.lst;
                        {
                            __auto_type clause_items = clause_lst.items;
                            __auto_type clause_len = ((int64_t)((clause_items).len));
                            if ((clause_len < 1)) {
                                context_ctx_add_error_at(ctx, SLOP_STR("invalid cond clause"), context_ctx_sexpr_line(clause_expr), context_ctx_sexpr_col(clause_expr));
                            } else {
                                __auto_type _mv_741 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_741.has_value) {
                                    __auto_type test_expr = _mv_741.value;
                                    __auto_type _mv_742 = (*test_expr);
                                    switch (_mv_742.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_742.data.sym;
                                            if (string_eq(sym.name, SLOP_STR("else"))) {
                                                context_ctx_emit(ctx, SLOP_STR("} else {"));
                                                context_ctx_indent(ctx);
                                                match_emit_inline_cond_body(ctx, clause_items, 1, is_return, is_last);
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
                                                    match_emit_inline_cond_body(ctx, clause_items, 1, is_return, is_last);
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
                                                match_emit_inline_cond_body(ctx, clause_items, 1, is_return, is_last);
                                                context_ctx_dedent(ctx);
                                            }
                                            break;
                                        }
                                    }
                                } else if (!_mv_741.has_value) {
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
            } else if (!_mv_739.has_value) {
            }
            i = (i + 1);
        }
        if (!(first)) {
            context_ctx_emit(ctx, SLOP_STR("}"));
        }
    }
}

void match_emit_inline_cond_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start, uint8_t is_return, uint8_t is_last) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = start;
        while ((i < len)) {
            __auto_type _mv_743 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_743.has_value) {
                __auto_type body_expr = _mv_743.value;
                {
                    __auto_type body_is_last = (i == (len - 1));
                    match_emit_branch_body_item(ctx, body_expr, is_return, (is_last && body_is_last));
                }
            } else if (!_mv_743.has_value) {
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
        if ((len < 2)) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid with-arena: need size"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        } else {
            {
                __auto_type is_named = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type item1 = _mv.value; string_eq(parser_sexpr_get_symbol_name(item1), SLOP_STR(":as")); }) : (0); });
                __auto_type arena_name = ((is_named) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type name_expr = _mv.value; parser_sexpr_get_symbol_name(name_expr); }) : (SLOP_STR("arena")); }) : SLOP_STR("arena"));
                __auto_type size_idx = ((is_named) ? 3 : 1);
                __auto_type body_start = ((is_named) ? 4 : 2);
                __auto_type c_local = ((is_named) ? string_concat(ctx_arena, SLOP_STR("_arena_"), arena_name) : SLOP_STR("_arena"));
                if ((is_named && (len < 4))) {
                    context_ctx_add_error_at(ctx, SLOP_STR("with-arena :as requires name and size"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                } else {
                    context_ctx_emit(ctx, SLOP_STR("{"));
                    context_ctx_indent(ctx);
                    context_ctx_push_scope(ctx);
                    __auto_type _mv_744 = ({ __auto_type _lst = items; size_t _idx = (size_t)size_idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_744.has_value) {
                        __auto_type size_expr = _mv_744.value;
                        {
                            __auto_type size_c = expr_transpile_expr(ctx, size_expr);
                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("slop_arena "), c_local, SLOP_STR(" = slop_arena_new("), size_c, SLOP_STR(");")));
                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("slop_arena* "), arena_name, SLOP_STR(" = &"), c_local, SLOP_STR(";")));
                        }
                    } else if (!_mv_744.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing size"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
                    }
                    context_ctx_bind_var(ctx, (context_VarEntry){arena_name, arena_name, SLOP_STR("slop_arena*"), SLOP_STR(""), 1, 0, 0, SLOP_STR(""), SLOP_STR("")});
                    {
                        int64_t i = body_start;
                        while ((i < len)) {
                            __auto_type _mv_745 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_745.has_value) {
                                __auto_type body_expr = _mv_745.value;
                                {
                                    __auto_type is_last = (i == (len - 1));
                                    match_emit_branch_body_item(ctx, body_expr, (is_return && is_last), is_last);
                                }
                            } else if (!_mv_745.has_value) {
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
}

void match_emit_inline_body_items(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = start;
        while ((i < len)) {
            __auto_type _mv_746 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_746.has_value) {
                __auto_type body_expr = _mv_746.value;
                match_emit_branch_body_item(ctx, body_expr, 0, 0);
            } else if (!_mv_746.has_value) {
            }
            i = (i + 1);
        }
    }
}

void match_emit_inline_for(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if ((len < 2)) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid for: need binding"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        } else {
            __auto_type _mv_747 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_747.has_value) {
                __auto_type binding_expr = _mv_747.value;
                __auto_type _mv_748 = (*binding_expr);
                switch (_mv_748.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type binding_lst = _mv_748.data.lst;
                        {
                            __auto_type binding_items = binding_lst.items;
                            __auto_type binding_len = ((int64_t)((binding_items).len));
                            if ((binding_len < 3)) {
                                context_ctx_add_error_at(ctx, SLOP_STR("for binding needs (var start end)"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                            } else {
                                __auto_type _mv_749 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_749.has_value) {
                                    __auto_type var_expr = _mv_749.value;
                                    __auto_type _mv_750 = (*var_expr);
                                    switch (_mv_750.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type var_sym = _mv_750.data.sym;
                                            {
                                                __auto_type var_name = ctype_to_c_name(arena, var_sym.name);
                                                __auto_type _mv_751 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_751.has_value) {
                                                    __auto_type start_expr = _mv_751.value;
                                                    __auto_type _mv_752 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_752.has_value) {
                                                        __auto_type end_expr = _mv_752.value;
                                                        {
                                                            __auto_type start_c = expr_transpile_expr(ctx, start_expr);
                                                            __auto_type end_c = expr_transpile_expr(ctx, end_expr);
                                                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("for (int64_t "), var_name, SLOP_STR(" = "), start_c, context_ctx_str5(ctx, SLOP_STR("; "), var_name, SLOP_STR(" < "), end_c, context_ctx_str3(ctx, SLOP_STR("; "), var_name, SLOP_STR("++) {")))));
                                                            context_ctx_indent(ctx);
                                                            context_ctx_push_scope(ctx);
                                                            context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, SLOP_STR("int64_t"), SLOP_STR("Int"), 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                                            match_emit_inline_body_items(ctx, items, 2);
                                                            context_ctx_pop_scope(ctx);
                                                            context_ctx_dedent(ctx);
                                                            context_ctx_emit(ctx, SLOP_STR("}"));
                                                        }
                                                    } else if (!_mv_752.has_value) {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("missing end"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                                                    }
                                                } else if (!_mv_751.has_value) {
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
                                } else if (!_mv_749.has_value) {
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
            } else if (!_mv_747.has_value) {
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
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("slop_map* _coll = (slop_map*)"), coll_c, SLOP_STR(";")));
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
        match_emit_inline_body_items(ctx, items, 2);
        context_ctx_pop_scope(ctx);
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
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
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("slop_map* _coll = (slop_map*)"), coll_c, SLOP_STR(";")));
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
        match_emit_inline_body_items(ctx, items, 2);
        context_ctx_pop_scope(ctx);
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
    }
}

void match_emit_inline_for_each_map_kv(context_TranspileContext* ctx, slop_list_types_SExpr_ptr binding_items, slop_list_types_SExpr_ptr items, int64_t len) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_753 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_753.has_value) {
            __auto_type kv_list_expr = _mv_753.value;
            __auto_type _mv_754 = (*kv_list_expr);
            switch (_mv_754.tag) {
                case types_SExpr_lst:
                {
                    __auto_type kv_lst = _mv_754.data.lst;
                    {
                        __auto_type kv_items = kv_lst.items;
                        if ((((int64_t)((kv_items).len)) < 2)) {
                            context_ctx_add_error(ctx, SLOP_STR("Map for-each needs ((k v) map)"));
                        } else {
                            __auto_type _mv_755 = ({ __auto_type _lst = kv_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_755.has_value) {
                                __auto_type k_expr = _mv_755.value;
                                __auto_type _mv_756 = ({ __auto_type _lst = kv_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_756.has_value) {
                                    __auto_type v_expr = _mv_756.value;
                                    __auto_type _mv_757 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_757.has_value) {
                                        __auto_type map_expr = _mv_757.value;
                                        __auto_type _mv_758 = (*k_expr);
                                        switch (_mv_758.tag) {
                                            case types_SExpr_sym:
                                            {
                                                __auto_type k_sym = _mv_758.data.sym;
                                                __auto_type _mv_759 = (*v_expr);
                                                switch (_mv_759.tag) {
                                                    case types_SExpr_sym:
                                                    {
                                                        __auto_type v_sym = _mv_759.data.sym;
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
                                                            context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("slop_map* _coll = (slop_map*)"), map_c, SLOP_STR(";")));
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
                                                            match_emit_inline_body_items(ctx, items, 2);
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
                                    } else if (!_mv_757.has_value) {
                                        context_ctx_add_error(ctx, SLOP_STR("Missing map expression"));
                                    }
                                } else if (!_mv_756.has_value) {
                                    context_ctx_add_error(ctx, SLOP_STR("Missing value binding"));
                                }
                            } else if (!_mv_755.has_value) {
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
        } else if (!_mv_753.has_value) {
            context_ctx_add_error(ctx, SLOP_STR("Missing binding"));
        }
    }
}

void match_emit_inline_for_each(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if ((len < 2)) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid for-each: need binding"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
        } else {
            __auto_type _mv_760 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_760.has_value) {
                __auto_type binding_expr = _mv_760.value;
                __auto_type _mv_761 = (*binding_expr);
                switch (_mv_761.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type binding_lst = _mv_761.data.lst;
                        {
                            __auto_type binding_items = binding_lst.items;
                            __auto_type binding_len = ((int64_t)((binding_items).len));
                            if ((binding_len < 2)) {
                                context_ctx_add_error_at(ctx, SLOP_STR("for-each binding needs (var coll)"), context_ctx_sexpr_line(binding_expr), context_ctx_sexpr_col(binding_expr));
                            } else {
                                __auto_type _mv_762 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_762.has_value) {
                                    __auto_type first_elem = _mv_762.value;
                                    __auto_type _mv_763 = (*first_elem);
                                    switch (_mv_763.tag) {
                                        case types_SExpr_lst:
                                        {
                                            __auto_type _ = _mv_763.data.lst;
                                            match_emit_inline_for_each_map_kv(ctx, binding_items, items, len);
                                            break;
                                        }
                                        case types_SExpr_sym:
                                        {
                                            __auto_type var_sym = _mv_763.data.sym;
                                            {
                                                __auto_type var_name = ctype_to_c_name(arena, var_sym.name);
                                                __auto_type _mv_764 = ({ __auto_type _lst = binding_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_764.has_value) {
                                                    __auto_type coll_expr = _mv_764.value;
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
                                                                    context_ctx_bind_var(ctx, (context_VarEntry){var_sym.name, var_name, elem_c_type, elem_slop_type, is_ptr_elem, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                                                }
                                                                match_emit_inline_body_items(ctx, items, 2);
                                                                context_ctx_pop_scope(ctx);
                                                                context_ctx_dedent(ctx);
                                                                context_ctx_emit(ctx, SLOP_STR("}"));
                                                                context_ctx_dedent(ctx);
                                                                context_ctx_emit(ctx, SLOP_STR("}"));
                                                            }
                                                        }
                                                    }
                                                } else if (!_mv_764.has_value) {
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
                                } else if (!_mv_762.has_value) {
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
            } else if (!_mv_760.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing binding"), context_ctx_list_first_line(items), context_ctx_list_first_col(items));
            }
        }
    }
}

void match_emit_inline_return(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 2)) {
            context_ctx_emit(ctx, SLOP_STR("return;"));
        } else {
            __auto_type _mv_765 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_765.has_value) {
                __auto_type val_expr = _mv_765.value;
                match_emit_typed_return_expr(ctx, val_expr);
            } else if (!_mv_765.has_value) {
                context_ctx_emit(ctx, SLOP_STR("return;"));
            }
        }
    }
}

void match_emit_return_typed(context_TranspileContext* ctx, slop_string code) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type final_code = ((string_eq(code, SLOP_STR("none"))) ? ({ __auto_type _mv = context_ctx_get_current_return_type(ctx); _mv.has_value ? ({ __auto_type ret_type = _mv.value; ((strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) ? context_ctx_str3(ctx, SLOP_STR("("), ret_type, SLOP_STR("){.has_value = false}")) : code); }) : (code); }) : code);
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("return "), final_code, SLOP_STR(";")));
    }
}

void match_emit_typed_return_expr(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_766 = (*expr);
    switch (_mv_766.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_766.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
                } else {
                    __auto_type _mv_767 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_767.has_value) {
                        __auto_type head = _mv_767.value;
                        __auto_type _mv_768 = (*head);
                        switch (_mv_768.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_768.data.sym;
                                {
                                    __auto_type op = sym.name;
                                    if (string_eq(op, SLOP_STR("some"))) {
                                        __auto_type _mv_769 = context_ctx_get_current_return_type(ctx);
                                        if (_mv_769.has_value) {
                                            __auto_type ret_type = _mv_769.value;
                                            if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                                                if ((((int64_t)((items).len)) < 2)) {
                                                    match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
                                                } else {
                                                    __auto_type _mv_770 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_770.has_value) {
                                                        __auto_type inner_expr = _mv_770.value;
                                                        {
                                                            __auto_type inner_c = expr_transpile_expr(ctx, inner_expr);
                                                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("return ("), ret_type, SLOP_STR("){.has_value = 1, .value = "), inner_c, SLOP_STR("};")));
                                                        }
                                                    } else if (!_mv_770.has_value) {
                                                        match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
                                                    }
                                                }
                                            } else {
                                                match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
                                            }
                                        } else if (!_mv_769.has_value) {
                                            match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
                                        }
                                    } else if (string_eq(op, SLOP_STR("none"))) {
                                        __auto_type _mv_771 = context_ctx_get_current_return_type(ctx);
                                        if (_mv_771.has_value) {
                                            __auto_type ret_type = _mv_771.value;
                                            if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                                                context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("return ("), ret_type, SLOP_STR("){.has_value = false};")));
                                            } else {
                                                match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
                                            }
                                        } else if (!_mv_771.has_value) {
                                            match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
                                        }
                                    } else {
                                        match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
                                    }
                                }
                                break;
                            }
                            default: {
                                match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
                                break;
                            }
                        }
                    } else if (!_mv_767.has_value) {
                        match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
                    }
                }
            }
            break;
        }
        default: {
            match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
            break;
        }
    }
}

uint8_t match_is_pattern_literal(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_772 = (*expr);
    switch (_mv_772.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_772.data.sym;
            {
                __auto_type name = sym.name;
                return (string_eq(name, SLOP_STR("true")) || string_eq(name, SLOP_STR("false")));
            }
        }
        case types_SExpr_num:
        {
            __auto_type _ = _mv_772.data.num;
            return 1;
        }
        default: {
            return 0;
        }
    }
}

slop_string match_pattern_literal_to_c(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_773 = (*expr);
    switch (_mv_773.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_773.data.sym;
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
            __auto_type n = _mv_773.data.num;
            return n.raw;
        }
        default: {
            return SLOP_STR("");
        }
    }
}

uint8_t match_has_literal_in_union_arm(types_SExpr* pat_expr) {
    SLOP_PRE(((pat_expr != NULL)), "(!= pat-expr nil)");
    __auto_type _mv_774 = (*pat_expr);
    switch (_mv_774.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_774.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type found = 0;
                for (int64_t i = 1; i < len; i++) {
                    if (!(found)) {
                        __auto_type _mv_775 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_775.has_value) {
                            __auto_type item = _mv_775.value;
                            if (match_is_pattern_literal(item)) {
                                found = 1;
                            }
                        } else if (!_mv_775.has_value) {
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
        while (((i < len) && !(found))) {
            __auto_type _mv_776 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_776.has_value) {
                __auto_type pat_expr = _mv_776.value;
                if (match_has_literal_in_union_arm(pat_expr)) {
                    found = 1;
                }
            } else if (!_mv_776.has_value) {
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
        __auto_type _mv_777 = (*pattern);
        switch (_mv_777.tag) {
            case types_SExpr_lst:
            {
                __auto_type pat_lst = _mv_777.data.lst;
                {
                    __auto_type pat_items = pat_lst.items;
                    __auto_type pat_len = ((int64_t)((pat_items).len));
                    __auto_type cond = tag_cond;
                    for (int64_t bi = 1; bi < pat_len; bi++) {
                        __auto_type _mv_778 = ({ __auto_type _lst = pat_items; size_t _idx = (size_t)bi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_778.has_value) {
                            __auto_type item = _mv_778.value;
                            if (match_is_pattern_literal(item)) {
                                {
                                    __auto_type lit_c = match_pattern_literal_to_c(item);
                                    __auto_type field_idx = (bi - 1);
                                    if (is_multi) {
                                        {
                                            __auto_type field_name = context_ctx_str(ctx, SLOP_STR("f"), int_to_string(arena, field_idx));
                                            __auto_type guard_str = context_ctx_str4(ctx, SLOP_STR(".data."), c_tag, SLOP_STR("."), context_ctx_str3(ctx, field_name, SLOP_STR(" == "), lit_c));
                                            cond = context_ctx_str(ctx, cond, context_ctx_str3(ctx, SLOP_STR(" && "), scrutinee_c, guard_str));
                                        }
                                    } else {
                                        {
                                            __auto_type guard_str = context_ctx_str3(ctx, SLOP_STR(".data."), c_tag, context_ctx_str(ctx, SLOP_STR(" == "), lit_c));
                                            cond = context_ctx_str(ctx, cond, context_ctx_str3(ctx, SLOP_STR(" && "), scrutinee_c, guard_str));
                                        }
                                    }
                                }
                            }
                        } else if (!_mv_778.has_value) {
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
            __auto_type _mv_779 = (*pattern);
            switch (_mv_779.tag) {
                case types_SExpr_lst:
                {
                    __auto_type pat_lst = _mv_779.data.lst;
                    {
                        __auto_type pat_items = pat_lst.items;
                        __auto_type pat_len = ((int64_t)((pat_items).len));
                        for (int64_t bi = 1; bi < pat_len; bi++) {
                            __auto_type _mv_780 = ({ __auto_type _lst = pat_items; size_t _idx = (size_t)bi; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_780.has_value) {
                                __auto_type binding_expr = _mv_780.value;
                                if (!(match_is_pattern_literal(binding_expr))) {
                                    {
                                        __auto_type binding_name = parser_sexpr_get_symbol_name(binding_expr);
                                        if ((!(string_eq(binding_name, SLOP_STR(""))) && !(string_eq(binding_name, SLOP_STR("_"))))) {
                                            {
                                                __auto_type c_binding = ctype_to_c_name(arena, binding_name);
                                                __auto_type field_idx = (bi - 1);
                                                __auto_type field_key = context_ctx_str3(ctx, tag, SLOP_STR("__"), int_to_string(arena, field_idx));
                                                __auto_type payload_c_type = ({ __auto_type _mv = context_ctx_lookup_field_type(ctx, union_type_name, field_key); _mv.has_value ? ({ __auto_type ct = _mv.value; ct; }) : (SLOP_STR("auto")); });
                                                __auto_type payload_slop_type = ({ __auto_type _mv = context_ctx_lookup_field_slop_type(ctx, union_type_name, field_key); _mv.has_value ? ({ __auto_type st = _mv.value; st; }) : (SLOP_STR("")); });
                                                __auto_type field_name = context_ctx_str(ctx, SLOP_STR("f"), int_to_string(arena, field_idx));
                                                context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("__auto_type "), c_binding, SLOP_STR(" = "), scrutinee_c, context_ctx_str5(ctx, SLOP_STR(".data."), c_tag, SLOP_STR("."), field_name, SLOP_STR(";"))));
                                                context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_binding, payload_c_type, payload_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                                            }
                                        }
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
        } else {
            __auto_type _mv_781 = match_extract_binding_name(pattern);
            if (_mv_781.has_value) {
                __auto_type binding_name = _mv_781.value;
                if (((!(string_eq(binding_name, SLOP_STR("true")))) && (!(string_eq(binding_name, SLOP_STR("false")))) && (!(string_eq(binding_name, SLOP_STR("_")))))) {
                    {
                        __auto_type c_binding = ctype_to_c_name(arena, binding_name);
                        __auto_type payload_c_type = ({ __auto_type _mv = context_ctx_lookup_field_type(ctx, union_type_name, tag); _mv.has_value ? ({ __auto_type ct = _mv.value; ct; }) : (SLOP_STR("auto")); });
                        __auto_type payload_slop_type = ({ __auto_type _mv = context_ctx_lookup_field_slop_type(ctx, union_type_name, tag); _mv.has_value ? ({ __auto_type st = _mv.value; st; }) : (SLOP_STR("")); });
                        context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("__auto_type "), c_binding, SLOP_STR(" = "), scrutinee_c, context_ctx_str3(ctx, SLOP_STR(".data."), c_tag, SLOP_STR(";"))));
                        context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_binding, payload_c_type, payload_slop_type, 0, 0, 0, SLOP_STR(""), SLOP_STR("")});
                    }
                }
            } else if (!_mv_781.has_value) {
            }
        }
    }
}

void match_transpile_union_match_with_literals(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr patterns, slop_list_types_SExpr_ptr items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 2;
        uint8_t first = 1;
        while ((i < len)) {
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
                            if ((((int64_t)((branch_items).len)) >= 2)) {
                                __auto_type _mv_784 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_784.has_value) {
                                    __auto_type pattern = _mv_784.value;
                                    {
                                        __auto_type tag = match_get_pattern_tag(pattern);
                                        if ((string_eq(tag, SLOP_STR("else")) || string_eq(tag, SLOP_STR("_")))) {
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
                                            __auto_type _mv_785 = context_ctx_lookup_enum_variant(ctx, tag);
                                            if (_mv_785.has_value) {
                                                __auto_type union_type_name = _mv_785.value;
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
                                            } else if (!_mv_785.has_value) {
                                                context_ctx_add_error(ctx, context_ctx_str3(ctx, SLOP_STR("unknown union variant in match: "), tag, SLOP_STR(" (not registered as enum variant)")));
                                            }
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
    }
}

