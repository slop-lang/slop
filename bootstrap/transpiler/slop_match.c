#include "../runtime/slop_runtime.h"
#include "slop_match.h"

uint8_t match_is_option_match(slop_list_types_SExpr_ptr patterns);
uint8_t match_is_result_match(slop_list_types_SExpr_ptr patterns);
uint8_t match_is_enum_match(slop_list_types_SExpr_ptr patterns);
uint8_t match_is_literal_match(slop_list_types_SExpr_ptr patterns);
uint8_t match_is_union_match(context_TranspileContext* ctx, slop_list_types_SExpr_ptr patterns);
slop_string match_get_pattern_tag(types_SExpr* pat_expr);
slop_option_string match_extract_binding_name(types_SExpr* pat_expr);
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
void match_emit_inline_return(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void match_emit_return_typed(context_TranspileContext* ctx, slop_string code);
void match_emit_typed_return_expr(context_TranspileContext* ctx, types_SExpr* expr);

uint8_t match_is_option_match(slop_list_types_SExpr_ptr patterns) {
    {
        __auto_type len = ((int64_t)((patterns).len));
        __auto_type has_some = 0;
        __auto_type has_none = 0;
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_427 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_427.has_value) {
                __auto_type pat_expr = _mv_427.value;
                {
                    __auto_type tag = match_get_pattern_tag(pat_expr);
                    if (string_eq(tag, SLOP_STR("some"))) {
                        has_some = 1;
                    } else if (string_eq(tag, SLOP_STR("none"))) {
                        has_none = 1;
                    } else {
                    }
                }
            } else if (!_mv_427.has_value) {
            }
            i = (i + 1);
        }
        return (has_some || has_none);
    }
}

uint8_t match_is_result_match(slop_list_types_SExpr_ptr patterns) {
    {
        __auto_type len = ((int64_t)((patterns).len));
        __auto_type has_ok = 0;
        __auto_type has_error = 0;
        __auto_type i = 0;
        while ((i < len)) {
            __auto_type _mv_428 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_428.has_value) {
                __auto_type pat_expr = _mv_428.value;
                {
                    __auto_type tag = match_get_pattern_tag(pat_expr);
                    if (string_eq(tag, SLOP_STR("ok"))) {
                        has_ok = 1;
                    } else if (string_eq(tag, SLOP_STR("error"))) {
                        has_error = 1;
                    } else {
                    }
                }
            } else if (!_mv_428.has_value) {
            }
            i = (i + 1);
        }
        return (has_ok || has_error);
    }
}

uint8_t match_is_enum_match(slop_list_types_SExpr_ptr patterns) {
    {
        __auto_type len = ((int64_t)((patterns).len));
        __auto_type all_symbols = 1;
        __auto_type i = 0;
        while (((i < len) && all_symbols)) {
            __auto_type _mv_429 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_429.has_value) {
                __auto_type pat_expr = _mv_429.value;
                __auto_type _mv_430 = (*pat_expr);
                switch (_mv_430.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type _ = _mv_430.data.sym;
                        break;
                    }
                    default: {
                        all_symbols = 0;
                        break;
                    }
                }
            } else if (!_mv_429.has_value) {
            }
            i = (i + 1);
        }
        return all_symbols;
    }
}

uint8_t match_is_literal_match(slop_list_types_SExpr_ptr patterns) {
    {
        __auto_type len = ((int64_t)((patterns).len));
        __auto_type has_literal = 0;
        __auto_type i = 0;
        while (((i < len) && !(has_literal))) {
            __auto_type _mv_431 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_431.has_value) {
                __auto_type pat_expr = _mv_431.value;
                __auto_type _mv_432 = (*pat_expr);
                switch (_mv_432.tag) {
                    case types_SExpr_num:
                    {
                        __auto_type _ = _mv_432.data.num;
                        has_literal = 1;
                        break;
                    }
                    case types_SExpr_str:
                    {
                        __auto_type _ = _mv_432.data.str;
                        has_literal = 1;
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_431.has_value) {
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
        __auto_type has_union_variant = 0;
        __auto_type i = 0;
        while (((i < len) && !(has_union_variant))) {
            __auto_type _mv_433 = ({ __auto_type _lst = patterns; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_433.has_value) {
                __auto_type pat_expr = _mv_433.value;
                {
                    __auto_type tag = match_get_pattern_tag(pat_expr);
                    if (((!(string_eq(tag, SLOP_STR("")))) && (!(string_eq(tag, SLOP_STR("some")))) && (!(string_eq(tag, SLOP_STR("none")))) && (!(string_eq(tag, SLOP_STR("ok")))) && (!(string_eq(tag, SLOP_STR("error")))) && (!(string_eq(tag, SLOP_STR("else")))) && (!(string_eq(tag, SLOP_STR("_")))))) {
                        __auto_type _mv_434 = context_ctx_lookup_enum_variant(ctx, tag);
                        if (_mv_434.has_value) {
                            __auto_type _ = _mv_434.value;
                            has_union_variant = 1;
                        } else if (!_mv_434.has_value) {
                        }
                    }
                }
            } else if (!_mv_433.has_value) {
            }
            i = (i + 1);
        }
        return has_union_variant;
    }
}

slop_string match_get_pattern_tag(types_SExpr* pat_expr) {
    SLOP_PRE(((pat_expr != NULL)), "(!= pat-expr nil)");
    __auto_type _mv_435 = (*pat_expr);
    switch (_mv_435.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_435.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    return SLOP_STR("");
                } else {
                    __auto_type _mv_436 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_436.has_value) {
                        __auto_type head = _mv_436.value;
                        __auto_type _mv_437 = (*head);
                        switch (_mv_437.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_437.data.sym;
                                return sym.name;
                            }
                            default: {
                                return SLOP_STR("");
                            }
                        }
                    } else if (!_mv_436.has_value) {
                        return SLOP_STR("");
                    }
                }
            }
        }
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_435.data.sym;
            return sym.name;
        }
        default: {
            return SLOP_STR("");
        }
    }
}

slop_option_string match_extract_binding_name(types_SExpr* pat_expr) {
    SLOP_PRE(((pat_expr != NULL)), "(!= pat-expr nil)");
    __auto_type _mv_438 = (*pat_expr);
    switch (_mv_438.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_438.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 2)) {
                    return (slop_option_string){.has_value = false};
                } else {
                    __auto_type _mv_439 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_439.has_value) {
                        __auto_type binding = _mv_439.value;
                        __auto_type _mv_440 = (*binding);
                        switch (_mv_440.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_440.data.sym;
                                return (slop_option_string){.has_value = 1, .value = sym.name};
                            }
                            default: {
                                return (slop_option_string){.has_value = false};
                            }
                        }
                    } else if (!_mv_439.has_value) {
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

void match_transpile_match(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type _mv_441 = (*expr);
        switch (_mv_441.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_441.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    if ((len < 3)) {
                        context_ctx_add_error_at(ctx, SLOP_STR("invalid match: need value and at least one branch"), context_sexpr_line(expr), context_sexpr_col(expr));
                    } else {
                        __auto_type _mv_442 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_442.has_value) {
                            __auto_type scrutinee = _mv_442.value;
                            {
                                __auto_type scrutinee_c = expr_transpile_expr(ctx, scrutinee);
                                __auto_type patterns = match_collect_patterns(ctx, items);
                                __auto_type scrutinee_var = context_ctx_gensym(ctx, SLOP_STR("_mv"));
                                context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), scrutinee_var, SLOP_STR(" = "), context_ctx_str(ctx, scrutinee_c, SLOP_STR(";"))));
                                if (match_is_option_match(patterns)) {
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
                        } else if (!_mv_442.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing match scrutinee"), context_sexpr_line(expr), context_sexpr_col(expr));
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("invalid match"), context_sexpr_line(expr), context_sexpr_col(expr));
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
        __auto_type i = 2;
        while ((i < len)) {
            __auto_type _mv_443 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_443.has_value) {
                __auto_type branch = _mv_443.value;
                __auto_type _mv_444 = (*branch);
                switch (_mv_444.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_444.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if ((((int64_t)((branch_items).len)) >= 1)) {
                                __auto_type _mv_445 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_445.has_value) {
                                    __auto_type pattern = _mv_445.value;
                                    ({ __auto_type _lst_p = &(result); __auto_type _item = (pattern); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                } else if (!_mv_445.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_443.has_value) {
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
        __auto_type i = 2;
        __auto_type first = 1;
        while ((i < len)) {
            __auto_type _mv_446 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_446.has_value) {
                __auto_type branch = _mv_446.value;
                __auto_type _mv_447 = (*branch);
                switch (_mv_447.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_447.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if ((((int64_t)((branch_items).len)) >= 2)) {
                                __auto_type _mv_448 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_448.has_value) {
                                    __auto_type pattern = _mv_448.value;
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
                                } else if (!_mv_448.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_446.has_value) {
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
        __auto_type _mv_449 = match_extract_binding_name(pattern);
        if (_mv_449.has_value) {
            __auto_type binding_name = _mv_449.value;
            {
                __auto_type c_name = ctype_to_c_name(arena, binding_name);
                __auto_type inner_slop_type = expr_infer_option_inner_slop_type(ctx, scrutinee_expr);
                context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, scrutinee_c, SLOP_STR(".value;"))));
                context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_name, SLOP_STR("auto"), inner_slop_type, 0, 0});
            }
        } else if (!_mv_449.has_value) {
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
        __auto_type i = 2;
        __auto_type first = 1;
        while ((i < len)) {
            __auto_type _mv_450 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_450.has_value) {
                __auto_type branch = _mv_450.value;
                __auto_type _mv_451 = (*branch);
                switch (_mv_451.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_451.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if ((((int64_t)((branch_items).len)) >= 2)) {
                                __auto_type _mv_452 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_452.has_value) {
                                    __auto_type pattern = _mv_452.value;
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
                                } else if (!_mv_452.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_450.has_value) {
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
        __auto_type _mv_453 = match_extract_binding_name(pattern);
        if (_mv_453.has_value) {
            __auto_type binding_name = _mv_453.value;
            {
                __auto_type c_name = ctype_to_c_name(arena, binding_name);
                __auto_type ok_slop_type = expr_infer_result_ok_slop_type(ctx, scrutinee_expr);
                context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, scrutinee_c, SLOP_STR(".data.ok;"))));
                context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_name, SLOP_STR("auto"), ok_slop_type, 0, 0});
            }
        } else if (!_mv_453.has_value) {
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
        __auto_type _mv_454 = match_extract_binding_name(pattern);
        if (_mv_454.has_value) {
            __auto_type binding_name = _mv_454.value;
            {
                __auto_type c_name = ctype_to_c_name(arena, binding_name);
                __auto_type err_slop_type = expr_infer_result_err_slop_type(ctx, scrutinee_expr);
                context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, scrutinee_c, SLOP_STR(".data.err;"))));
                context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_name, SLOP_STR("auto"), err_slop_type, 0, 0});
            }
        } else if (!_mv_454.has_value) {
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
        __auto_type i = 2;
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("switch ("), scrutinee_c, SLOP_STR(") {")));
        context_ctx_indent(ctx);
        while ((i < len)) {
            __auto_type _mv_455 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_455.has_value) {
                __auto_type branch = _mv_455.value;
                __auto_type _mv_456 = (*branch);
                switch (_mv_456.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_456.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if ((((int64_t)((branch_items).len)) >= 2)) {
                                __auto_type _mv_457 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_457.has_value) {
                                    __auto_type pattern = _mv_457.value;
                                    match_emit_enum_case(ctx, pattern, branch_items, is_return);
                                } else if (!_mv_457.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_455.has_value) {
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
        if (string_eq(tag, SLOP_STR("else"))) {
            context_ctx_emit(ctx, SLOP_STR("default: {"));
            context_ctx_indent(ctx);
            match_emit_branch_body(ctx, branch_items, is_return);
            context_ctx_emit(ctx, SLOP_STR("break;"));
            context_ctx_dedent(ctx);
            context_ctx_emit(ctx, SLOP_STR("}"));
        } else {
            __auto_type _mv_458 = context_ctx_lookup_enum_variant(ctx, tag);
            if (_mv_458.has_value) {
                __auto_type type_name = _mv_458.value;
                {
                    __auto_type c_case = context_ctx_str3(ctx, type_name, SLOP_STR("_"), ctype_to_c_name(arena, tag));
                    context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("case "), context_ctx_str(ctx, c_case, SLOP_STR(": {"))));
                    context_ctx_indent(ctx);
                    match_emit_branch_body(ctx, branch_items, is_return);
                    context_ctx_emit(ctx, SLOP_STR("break;"));
                    context_ctx_dedent(ctx);
                    context_ctx_emit(ctx, SLOP_STR("}"));
                }
            } else if (!_mv_458.has_value) {
                {
                    __auto_type c_case = ctype_to_c_name(arena, tag);
                    context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("case "), context_ctx_str(ctx, c_case, SLOP_STR(": {"))));
                    context_ctx_indent(ctx);
                    match_emit_branch_body(ctx, branch_items, is_return);
                    context_ctx_emit(ctx, SLOP_STR("break;"));
                    context_ctx_dedent(ctx);
                    context_ctx_emit(ctx, SLOP_STR("}"));
                }
            }
        }
    }
}

void match_transpile_literal_match(context_TranspileContext* ctx, slop_string scrutinee_c, slop_list_types_SExpr_ptr items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 2;
        __auto_type first = 1;
        while ((i < len)) {
            __auto_type _mv_459 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_459.has_value) {
                __auto_type branch = _mv_459.value;
                __auto_type _mv_460 = (*branch);
                switch (_mv_460.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_460.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if ((((int64_t)((branch_items).len)) >= 2)) {
                                __auto_type _mv_461 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_461.has_value) {
                                    __auto_type pattern = _mv_461.value;
                                    match_emit_literal_case(ctx, scrutinee_c, pattern, branch_items, is_return, first);
                                    first = 0;
                                } else if (!_mv_461.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_459.has_value) {
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
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        __auto_type i = 2;
        __auto_type first = 1;
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("switch ("), scrutinee_c, SLOP_STR(".tag) {")));
        context_ctx_indent(ctx);
        while ((i < len)) {
            __auto_type _mv_462 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_462.has_value) {
                __auto_type branch = _mv_462.value;
                __auto_type _mv_463 = (*branch);
                switch (_mv_463.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type branch_lst = _mv_463.data.lst;
                        {
                            __auto_type branch_items = branch_lst.items;
                            if ((((int64_t)((branch_items).len)) >= 2)) {
                                __auto_type _mv_464 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_464.has_value) {
                                    __auto_type pattern = _mv_464.value;
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
                                            __auto_type _mv_465 = context_ctx_lookup_enum_variant(ctx, tag);
                                            if (_mv_465.has_value) {
                                                __auto_type union_type_name = _mv_465.value;
                                                match_emit_union_case(ctx, scrutinee_c, pattern, tag, union_type_name, branch_items, is_return);
                                            } else if (!_mv_465.has_value) {
                                                context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("/* unknown union variant: "), tag, SLOP_STR(" */")));
                                            }
                                        }
                                    }
                                } else if (!_mv_464.has_value) {
                                }
                            }
                        }
                        break;
                    }
                    default: {
                        break;
                    }
                }
            } else if (!_mv_462.has_value) {
            }
            i = (i + 1);
        }
        context_ctx_dedent(ctx);
        context_ctx_emit(ctx, SLOP_STR("}"));
    }
}

void match_emit_union_case(context_TranspileContext* ctx, slop_string scrutinee_c, types_SExpr* pattern, slop_string tag, slop_string union_type_name, slop_list_types_SExpr_ptr branch_items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    SLOP_PRE(((pattern != NULL)), "(!= pattern nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type c_tag = ctype_to_c_name(arena, tag);
        __auto_type case_label = context_ctx_str4(ctx, union_type_name, SLOP_STR("_"), c_tag, SLOP_STR(":"));
        context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("case "), case_label));
        context_ctx_emit(ctx, SLOP_STR("{"));
        context_ctx_indent(ctx);
        context_ctx_push_scope(ctx);
        __auto_type _mv_466 = match_extract_binding_name(pattern);
        if (_mv_466.has_value) {
            __auto_type binding_name = _mv_466.value;
            {
                __auto_type c_binding = ctype_to_c_name(arena, binding_name);
                context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("__auto_type "), c_binding, SLOP_STR(" = "), scrutinee_c, context_ctx_str3(ctx, SLOP_STR(".data."), c_tag, SLOP_STR(";"))));
                context_ctx_bind_var(ctx, (context_VarEntry){binding_name, c_binding, SLOP_STR("auto"), SLOP_STR(""), 0, 0});
            }
        } else if (!_mv_466.has_value) {
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
        __auto_type i = 1;
        while ((i < len)) {
            __auto_type _mv_467 = ({ __auto_type _lst = branch_items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_467.has_value) {
                __auto_type body_expr = _mv_467.value;
                {
                    __auto_type is_last = (i == (len - 1));
                    match_emit_branch_body_item(ctx, body_expr, is_return, is_last);
                }
            } else if (!_mv_467.has_value) {
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
        __auto_type _mv_468 = (*body_expr);
        switch (_mv_468.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_468.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) < 1)) {
                        context_ctx_emit(ctx, SLOP_STR("/* empty list */;"));
                    } else {
                        __auto_type _mv_469 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_469.has_value) {
                            __auto_type head_expr = _mv_469.value;
                            __auto_type _mv_470 = (*head_expr);
                            switch (_mv_470.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_470.data.sym;
                                    {
                                        __auto_type op = sym.name;
                                        if (string_eq(op, SLOP_STR("let"))) {
                                            match_emit_inline_let(ctx, items, is_return, is_last);
                                        } else if (string_eq(op, SLOP_STR("do"))) {
                                            match_emit_inline_do(ctx, items, is_return, is_last);
                                        } else if (string_eq(op, SLOP_STR("if"))) {
                                            match_emit_inline_if(ctx, items, is_return);
                                        } else if (string_eq(op, SLOP_STR("while"))) {
                                            match_emit_inline_while(ctx, items);
                                        } else if (string_eq(op, SLOP_STR("set!"))) {
                                            match_emit_inline_set(ctx, items);
                                        } else if (string_eq(op, SLOP_STR("when"))) {
                                            match_emit_inline_when(ctx, items);
                                        } else if (string_eq(op, SLOP_STR("cond"))) {
                                            match_emit_inline_cond(ctx, items, is_return, is_last);
                                        } else if (string_eq(op, SLOP_STR("match"))) {
                                            match_transpile_match(ctx, body_expr, is_return);
                                        } else if (string_eq(op, SLOP_STR("with-arena"))) {
                                            match_emit_inline_with_arena(ctx, items, is_return);
                                        } else if (string_eq(op, SLOP_STR("return"))) {
                                            match_emit_inline_return(ctx, items);
                                        } else {
                                            if ((is_return && is_last)) {
                                                match_emit_typed_return_expr(ctx, body_expr);
                                            } else {
                                                context_ctx_emit(ctx, context_ctx_str(ctx, expr_transpile_expr(ctx, body_expr), SLOP_STR(";")));
                                            }
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    context_ctx_emit(ctx, context_ctx_str(ctx, expr_transpile_expr(ctx, body_expr), SLOP_STR(";")));
                                    break;
                                }
                            }
                        } else if (!_mv_469.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("empty"), context_list_first_line(items), context_list_first_col(items));
                        }
                    }
                }
                break;
            }
            default: {
                if ((is_return && is_last)) {
                    match_emit_typed_return_expr(ctx, body_expr);
                } else {
                    context_ctx_emit(ctx, context_ctx_str(ctx, expr_transpile_expr(ctx, body_expr), SLOP_STR(";")));
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
            context_ctx_add_error_at(ctx, SLOP_STR("invalid let"), context_list_first_line(items), context_list_first_col(items));
        } else {
            context_ctx_emit(ctx, SLOP_STR("{"));
            context_ctx_indent(ctx);
            context_ctx_push_scope(ctx);
            __auto_type _mv_471 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_471.has_value) {
                __auto_type bindings_expr = _mv_471.value;
                match_emit_inline_bindings(ctx, bindings_expr);
            } else if (!_mv_471.has_value) {
            }
            {
                __auto_type i = 2;
                while ((i < len)) {
                    __auto_type _mv_472 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_472.has_value) {
                        __auto_type body_item = _mv_472.value;
                        {
                            __auto_type body_last = (i == (len - 1));
                            match_emit_branch_body_item(ctx, body_item, is_return, (is_last && body_last));
                        }
                    } else if (!_mv_472.has_value) {
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
        __auto_type _mv_473 = (*bindings_expr);
        switch (_mv_473.tag) {
            case types_SExpr_lst:
            {
                __auto_type bindings_lst = _mv_473.data.lst;
                {
                    __auto_type bindings = bindings_lst.items;
                    __auto_type len = ((int64_t)((bindings).len));
                    __auto_type i = 0;
                    while ((i < len)) {
                        __auto_type _mv_474 = ({ __auto_type _lst = bindings; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_474.has_value) {
                            __auto_type binding = _mv_474.value;
                            match_emit_single_inline_binding(ctx, binding);
                        } else if (!_mv_474.has_value) {
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
        __auto_type _mv_475 = (*binding);
        switch (_mv_475.tag) {
            case types_SExpr_lst:
            {
                __auto_type binding_lst = _mv_475.data.lst;
                {
                    __auto_type items = binding_lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    {
                        __auto_type has_mut = match_binding_starts_with_mut(items);
                        __auto_type start_idx = ((match_binding_starts_with_mut(items)) ? 1 : 0);
                        if (((len - start_idx) < 2)) {
                            context_ctx_add_error_at(ctx, SLOP_STR("invalid binding"), context_sexpr_line(binding), context_sexpr_col(binding));
                        } else {
                            __auto_type _mv_476 = ({ __auto_type _lst = items; size_t _idx = (size_t)start_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_476.has_value) {
                                __auto_type name_expr = _mv_476.value;
                                __auto_type _mv_477 = (*name_expr);
                                switch (_mv_477.tag) {
                                    case types_SExpr_sym:
                                    {
                                        __auto_type name_sym = _mv_477.data.sym;
                                        {
                                            __auto_type raw_name = name_sym.name;
                                            __auto_type c_name = ctype_to_c_name(arena, raw_name);
                                            if (((len - start_idx) >= 3)) {
                                                {
                                                    __auto_type type_idx = (start_idx + 1);
                                                    __auto_type val_idx = (start_idx + 2);
                                                    __auto_type _mv_478 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_478.has_value) {
                                                        __auto_type type_expr = _mv_478.value;
                                                        if (match_is_type_expr(type_expr)) {
                                                            __auto_type _mv_479 = ({ __auto_type _lst = items; size_t _idx = (size_t)val_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_479.has_value) {
                                                                __auto_type val_expr = _mv_479.value;
                                                                {
                                                                    __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                                    __auto_type is_ptr = strlib_ends_with(c_type, SLOP_STR("*"));
                                                                    {
                                                                        __auto_type final_init = ((strlib_starts_with(c_type, SLOP_STR("slop_option_"))) ? ({ __auto_type some_val = match_get_some_value_inline(val_expr); ({ __auto_type _mv = some_val; _mv.has_value ? ({ __auto_type inner_expr = _mv.value; ({ __auto_type inner_c = expr_transpile_expr(ctx, inner_expr); context_ctx_str5(ctx, SLOP_STR("("), c_type, SLOP_STR("){.has_value = 1, .value = "), inner_c, SLOP_STR("}")); }); }) : (((match_is_none_form_inline(val_expr)) ? context_ctx_str3(ctx, SLOP_STR("("), c_type, SLOP_STR("){.has_value = false}")) : expr_transpile_expr(ctx, val_expr))); }); }) : expr_transpile_expr(ctx, val_expr));
                                                                        __auto_type slop_type_str = ctype_sexpr_to_type_string(arena, type_expr);
                                                                        context_ctx_emit(ctx, context_ctx_str5(ctx, c_type, SLOP_STR(" "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, final_init, SLOP_STR(";"))));
                                                                        context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, c_type, slop_type_str, is_ptr, has_mut});
                                                                    }
                                                                }
                                                            } else if (!_mv_479.has_value) {
                                                                context_ctx_add_error_at(ctx, SLOP_STR("missing value"), context_sexpr_line(binding), context_sexpr_col(binding));
                                                            }
                                                        } else {
                                                            __auto_type _mv_480 = ({ __auto_type _lst = items; size_t _idx = (size_t)type_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                            if (_mv_480.has_value) {
                                                                __auto_type val_expr = _mv_480.value;
                                                                {
                                                                    __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                                    __auto_type inferred_slop_type = expr_infer_expr_slop_type(ctx, val_expr);
                                                                    __auto_type ptr_type_opt = match_get_arena_alloc_ptr_type_inline(ctx, val_expr);
                                                                    __auto_type _mv_481 = ptr_type_opt;
                                                                    if (_mv_481.has_value) {
                                                                        __auto_type ptr_type = _mv_481.value;
                                                                        context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, val_c, SLOP_STR(";"))));
                                                                        context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, ptr_type, inferred_slop_type, 1, has_mut});
                                                                    } else if (!_mv_481.has_value) {
                                                                        {
                                                                            __auto_type inferred_type = expr_infer_expr_c_type(ctx, val_expr);
                                                                            __auto_type is_ptr = strlib_ends_with(inferred_type, SLOP_STR("*"));
                                                                            context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, val_c, SLOP_STR(";"))));
                                                                            context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, inferred_type, inferred_slop_type, is_ptr, has_mut});
                                                                        }
                                                                    }
                                                                }
                                                            } else if (!_mv_480.has_value) {
                                                                context_ctx_add_error_at(ctx, SLOP_STR("missing value"), context_sexpr_line(binding), context_sexpr_col(binding));
                                                            }
                                                        }
                                                    } else if (!_mv_478.has_value) {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("missing type/value"), context_sexpr_line(binding), context_sexpr_col(binding));
                                                    }
                                                }
                                            } else {
                                                {
                                                    __auto_type val_idx = (start_idx + 1);
                                                    __auto_type _mv_482 = ({ __auto_type _lst = items; size_t _idx = (size_t)val_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_482.has_value) {
                                                        __auto_type val_expr = _mv_482.value;
                                                        {
                                                            __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                                            __auto_type inferred_slop_type = expr_infer_expr_slop_type(ctx, val_expr);
                                                            __auto_type ptr_type_opt = match_get_arena_alloc_ptr_type_inline(ctx, val_expr);
                                                            __auto_type _mv_483 = ptr_type_opt;
                                                            if (_mv_483.has_value) {
                                                                __auto_type ptr_type = _mv_483.value;
                                                                context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, val_c, SLOP_STR(";"))));
                                                                context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, ptr_type, inferred_slop_type, 1, has_mut});
                                                            } else if (!_mv_483.has_value) {
                                                                {
                                                                    __auto_type inferred_type = expr_infer_expr_c_type(ctx, val_expr);
                                                                    __auto_type is_ptr = strlib_ends_with(inferred_type, SLOP_STR("*"));
                                                                    context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("__auto_type "), c_name, SLOP_STR(" = "), context_ctx_str(ctx, val_c, SLOP_STR(";"))));
                                                                    context_ctx_bind_var(ctx, (context_VarEntry){raw_name, c_name, inferred_type, inferred_slop_type, is_ptr, has_mut});
                                                                }
                                                            }
                                                        }
                                                    } else if (!_mv_482.has_value) {
                                                        context_ctx_add_error_at(ctx, SLOP_STR("missing value"), context_sexpr_line(binding), context_sexpr_col(binding));
                                                    }
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
                            } else if (!_mv_476.has_value) {
                                context_ctx_add_error_at(ctx, SLOP_STR("missing binding name"), context_sexpr_line(binding), context_sexpr_col(binding));
                            }
                        }
                    }
                }
                break;
            }
            default: {
                context_ctx_add_error_at(ctx, SLOP_STR("binding must be list"), context_sexpr_line(binding), context_sexpr_col(binding));
                break;
            }
        }
    }
}

uint8_t match_binding_starts_with_mut(slop_list_types_SExpr_ptr items) {
    if ((((int64_t)((items).len)) < 1)) {
        return 0;
    } else {
        __auto_type _mv_484 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_484.has_value) {
            __auto_type first = _mv_484.value;
            __auto_type _mv_485 = (*first);
            switch (_mv_485.tag) {
                case types_SExpr_sym:
                {
                    __auto_type sym = _mv_485.data.sym;
                    return string_eq(sym.name, SLOP_STR("mut"));
                }
                default: {
                    return 0;
                }
            }
        } else if (!_mv_484.has_value) {
            return 0;
        }
    }
}

uint8_t match_is_type_expr(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_486 = (*expr);
    switch (_mv_486.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_486.data.sym;
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
            __auto_type _ = _mv_486.data.lst;
            return 1;
        }
        default: {
            return 0;
        }
    }
}

uint8_t match_is_none_form_inline(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_487 = (*expr);
    switch (_mv_487.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_487.data.sym;
            return string_eq(sym.name, SLOP_STR("none"));
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_487.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) == 1)) {
                    __auto_type _mv_488 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_488.has_value) {
                        __auto_type head = _mv_488.value;
                        __auto_type _mv_489 = (*head);
                        switch (_mv_489.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_489.data.sym;
                                return string_eq(sym.name, SLOP_STR("none"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_488.has_value) {
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
        __auto_type _mv_490 = (*expr);
        switch (_mv_490.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_490.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 3)) {
                        __auto_type _mv_491 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_491.has_value) {
                            __auto_type head_ptr = _mv_491.value;
                            __auto_type _mv_492 = (*head_ptr);
                            switch (_mv_492.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_492.data.sym;
                                    if (string_eq(head_sym.name, SLOP_STR("arena-alloc"))) {
                                        __auto_type _mv_493 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_493.has_value) {
                                            __auto_type size_expr = _mv_493.value;
                                            return match_extract_sizeof_type_inline(ctx, size_expr);
                                        } else if (!_mv_493.has_value) {
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
                        } else if (!_mv_491.has_value) {
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
        __auto_type _mv_494 = (*expr);
        switch (_mv_494.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_494.data.sym;
                {
                    __auto_type type_name = sym.name;
                    __auto_type _mv_495 = context_ctx_lookup_type(ctx, type_name);
                    if (_mv_495.has_value) {
                        __auto_type entry = _mv_495.value;
                        return (slop_option_string){.has_value = 1, .value = context_ctx_str(ctx, entry.c_name, SLOP_STR("*"))};
                    } else if (!_mv_495.has_value) {
                        return (slop_option_string){.has_value = false};
                    }
                }
            }
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_494.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 2)) {
                        __auto_type _mv_496 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_496.has_value) {
                            __auto_type head_ptr = _mv_496.value;
                            __auto_type _mv_497 = (*head_ptr);
                            switch (_mv_497.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type head_sym = _mv_497.data.sym;
                                    if (string_eq(head_sym.name, SLOP_STR("sizeof"))) {
                                        __auto_type _mv_498 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_498.has_value) {
                                            __auto_type type_expr = _mv_498.value;
                                            {
                                                __auto_type c_type = context_to_c_type_prefixed(ctx, type_expr);
                                                return (slop_option_string){.has_value = 1, .value = context_ctx_str(ctx, c_type, SLOP_STR("*"))};
                                            }
                                        } else if (!_mv_498.has_value) {
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
                        } else if (!_mv_496.has_value) {
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
        __auto_type i = 1;
        while ((i < len)) {
            __auto_type _mv_499 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_499.has_value) {
                __auto_type item = _mv_499.value;
                {
                    __auto_type item_last = (i == (len - 1));
                    match_emit_branch_body_item(ctx, item, is_return, (is_last && item_last));
                }
            } else if (!_mv_499.has_value) {
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
            context_ctx_add_error_at(ctx, SLOP_STR("invalid if"), context_list_first_line(items), context_list_first_col(items));
        } else {
            __auto_type _mv_500 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_500.has_value) {
                __auto_type cond_expr = _mv_500.value;
                {
                    __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), cond_c, SLOP_STR(") {")));
                }
            } else if (!_mv_500.has_value) {
                context_ctx_emit(ctx, SLOP_STR("if (/* missing */) {"));
            }
            context_ctx_indent(ctx);
            __auto_type _mv_501 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_501.has_value) {
                __auto_type then_expr = _mv_501.value;
                match_emit_branch_body_item(ctx, then_expr, is_return, 1);
            } else if (!_mv_501.has_value) {
            }
            context_ctx_dedent(ctx);
            if ((len >= 4)) {
                context_ctx_emit(ctx, SLOP_STR("} else {"));
                context_ctx_indent(ctx);
                __auto_type _mv_502 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_502.has_value) {
                    __auto_type else_expr = _mv_502.value;
                    match_emit_branch_body_item(ctx, else_expr, is_return, 1);
                } else if (!_mv_502.has_value) {
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
            context_ctx_add_error_at(ctx, SLOP_STR("invalid while"), context_list_first_line(items), context_list_first_col(items));
        } else {
            __auto_type _mv_503 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_503.has_value) {
                __auto_type cond_expr = _mv_503.value;
                {
                    __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("while ("), cond_c, SLOP_STR(") {")));
                }
            } else if (!_mv_503.has_value) {
                context_ctx_emit(ctx, SLOP_STR("while (/* missing */) {"));
            }
            context_ctx_indent(ctx);
            {
                __auto_type i = 2;
                while ((i < len)) {
                    __auto_type _mv_504 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_504.has_value) {
                        __auto_type body_expr = _mv_504.value;
                        match_emit_branch_body_item(ctx, body_expr, 0, 0);
                    } else if (!_mv_504.has_value) {
                    }
                    i = (i + 1);
                }
            }
            context_ctx_dedent(ctx);
            context_ctx_emit(ctx, SLOP_STR("}"));
        }
    }
}

slop_option_string match_get_var_c_type_inline(context_TranspileContext* ctx, types_SExpr* expr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    __auto_type _mv_505 = (*expr);
    switch (_mv_505.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_505.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_506 = context_ctx_lookup_var(ctx, name);
                if (_mv_506.has_value) {
                    __auto_type var_entry = _mv_506.value;
                    return (slop_option_string){.has_value = 1, .value = var_entry.c_type};
                } else if (!_mv_506.has_value) {
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
        __auto_type _mv_507 = (*expr);
        switch (_mv_507.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_507.data.lst;
                {
                    __auto_type items = lst.items;
                    if ((((int64_t)((items).len)) >= 2)) {
                        __auto_type _mv_508 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_508.has_value) {
                            __auto_type head = _mv_508.value;
                            __auto_type _mv_509 = (*head);
                            switch (_mv_509.tag) {
                                case types_SExpr_sym:
                                {
                                    __auto_type sym = _mv_509.data.sym;
                                    if (string_eq(sym.name, SLOP_STR("some"))) {
                                        __auto_type _mv_510 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_510.has_value) {
                                            __auto_type val = _mv_510.value;
                                            result = (slop_option_types_SExpr_ptr){.has_value = 1, .value = val};
                                        } else if (!_mv_510.has_value) {
                                        }
                                    }
                                    break;
                                }
                                default: {
                                    break;
                                }
                            }
                        } else if (!_mv_508.has_value) {
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
            __auto_type _mv_511 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_511.has_value) {
                __auto_type target_expr = _mv_511.value;
                __auto_type _mv_512 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_512.has_value) {
                    __auto_type field_expr = _mv_512.value;
                    __auto_type _mv_513 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_513.has_value) {
                        __auto_type type_expr = _mv_513.value;
                        __auto_type _mv_514 = ({ __auto_type _lst = items; size_t _idx = (size_t)4; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_514.has_value) {
                            __auto_type value_expr = _mv_514.value;
                            {
                                __auto_type field_name = match_get_field_name_inline(ctx, field_expr);
                                __auto_type c_type = ctype_to_c_type(arena, type_expr);
                                {
                                    __auto_type target_access = ((match_is_deref_inline(target_expr)) ? ({ __auto_type inner_c = match_get_deref_inner_inline(ctx, target_expr); context_ctx_str(ctx, SLOP_STR("(*"), context_ctx_str(ctx, inner_c, SLOP_STR(")."))); }) : ({ __auto_type target_c = expr_transpile_expr(ctx, target_expr); context_ctx_str(ctx, target_c, SLOP_STR(".")); }));
                                    if (strlib_starts_with(c_type, SLOP_STR("slop_option_"))) {
                                        if (match_is_none_form_inline(value_expr)) {
                                            context_ctx_emit(ctx, context_ctx_str(ctx, target_access, context_ctx_str(ctx, field_name, context_ctx_str3(ctx, SLOP_STR(" = ("), c_type, SLOP_STR("){.has_value = false};")))));
                                        } else {
                                            __auto_type _mv_515 = match_get_some_value_inline(value_expr);
                                            if (_mv_515.has_value) {
                                                __auto_type inner_val = _mv_515.value;
                                                {
                                                    __auto_type val_c = expr_transpile_expr(ctx, inner_val);
                                                    context_ctx_emit(ctx, context_ctx_str(ctx, target_access, context_ctx_str(ctx, field_name, context_ctx_str5(ctx, SLOP_STR(" = ("), c_type, SLOP_STR("){.has_value = 1, .value = "), val_c, SLOP_STR("};")))));
                                                }
                                            } else if (!_mv_515.has_value) {
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
                        } else if (!_mv_514.has_value) {
                            context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_list_first_line(items), context_list_first_col(items));
                        }
                    } else if (!_mv_513.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing set! type"), context_list_first_line(items), context_list_first_col(items));
                    }
                } else if (!_mv_512.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("missing set! field"), context_list_first_line(items), context_list_first_col(items));
                }
            } else if (!_mv_511.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_list_first_line(items), context_list_first_col(items));
            }
        } else if ((len == 4)) {
            __auto_type _mv_516 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_516.has_value) {
                __auto_type target_expr = _mv_516.value;
                __auto_type _mv_517 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_517.has_value) {
                    __auto_type field_expr = _mv_517.value;
                    __auto_type _mv_518 = ({ __auto_type _lst = items; size_t _idx = (size_t)3; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_518.has_value) {
                        __auto_type value_expr = _mv_518.value;
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
                    } else if (!_mv_518.has_value) {
                        context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_list_first_line(items), context_list_first_col(items));
                    }
                } else if (!_mv_517.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("missing set! field"), context_list_first_line(items), context_list_first_col(items));
                }
            } else if (!_mv_516.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_list_first_line(items), context_list_first_col(items));
            }
        } else if ((len >= 3)) {
            __auto_type _mv_519 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_519.has_value) {
                __auto_type target_expr = _mv_519.value;
                __auto_type _mv_520 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_520.has_value) {
                    __auto_type val_expr = _mv_520.value;
                    {
                        __auto_type target_c = expr_transpile_expr(ctx, target_expr);
                        __auto_type target_type_opt = match_get_var_c_type_inline(ctx, target_expr);
                        __auto_type _mv_521 = target_type_opt;
                        if (_mv_521.has_value) {
                            __auto_type target_type = _mv_521.value;
                            if (strlib_starts_with(target_type, SLOP_STR("slop_option_"))) {
                                {
                                    __auto_type some_val_opt = match_get_some_value_inline(val_expr);
                                    __auto_type _mv_522 = some_val_opt;
                                    if (_mv_522.has_value) {
                                        __auto_type inner_expr = _mv_522.value;
                                        {
                                            __auto_type inner_c = expr_transpile_expr(ctx, inner_expr);
                                            context_ctx_emit(ctx, context_ctx_str(ctx, target_c, context_ctx_str5(ctx, SLOP_STR(" = ("), target_type, SLOP_STR("){.has_value = 1, .value = "), inner_c, SLOP_STR("};"))));
                                        }
                                    } else if (!_mv_522.has_value) {
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
                        } else if (!_mv_521.has_value) {
                            {
                                __auto_type val_c = expr_transpile_expr(ctx, val_expr);
                                context_ctx_emit(ctx, context_ctx_str4(ctx, target_c, SLOP_STR(" = "), val_c, SLOP_STR(";")));
                            }
                        }
                    }
                } else if (!_mv_520.has_value) {
                    context_ctx_add_error_at(ctx, SLOP_STR("missing set! value"), context_list_first_line(items), context_list_first_col(items));
                }
            } else if (!_mv_519.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing set! target"), context_list_first_line(items), context_list_first_col(items));
            }
        } else {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid set!"), context_list_first_line(items), context_list_first_col(items));
        }
    }
}

uint8_t match_is_deref_inline(types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_523 = (*expr);
    switch (_mv_523.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_523.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 2)) {
                    return 0;
                } else {
                    __auto_type _mv_524 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_524.has_value) {
                        __auto_type head = _mv_524.value;
                        __auto_type _mv_525 = (*head);
                        switch (_mv_525.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_525.data.sym;
                                return string_eq(sym.name, SLOP_STR("deref"));
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_524.has_value) {
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
    __auto_type _mv_526 = (*expr);
    switch (_mv_526.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_526.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type _mv_527 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_527.has_value) {
                    __auto_type inner = _mv_527.value;
                    return expr_transpile_expr(ctx, inner);
                } else if (!_mv_527.has_value) {
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
        __auto_type _mv_528 = (*expr);
        switch (_mv_528.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_528.data.sym;
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
            context_ctx_add_error_at(ctx, SLOP_STR("invalid when"), context_list_first_line(items), context_list_first_col(items));
        } else {
            __auto_type _mv_529 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_529.has_value) {
                __auto_type cond_expr = _mv_529.value;
                {
                    __auto_type cond_c = expr_transpile_expr(ctx, cond_expr);
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), cond_c, SLOP_STR(") {")));
                }
            } else if (!_mv_529.has_value) {
                context_ctx_emit(ctx, SLOP_STR("if (/* missing */) {"));
            }
            context_ctx_indent(ctx);
            {
                __auto_type i = 2;
                while ((i < len)) {
                    __auto_type _mv_530 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_530.has_value) {
                        __auto_type body_expr = _mv_530.value;
                        match_emit_branch_body_item(ctx, body_expr, 0, 0);
                    } else if (!_mv_530.has_value) {
                    }
                    i = (i + 1);
                }
            }
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
        __auto_type i = 1;
        __auto_type first = 1;
        while ((i < len)) {
            __auto_type _mv_531 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_531.has_value) {
                __auto_type clause_expr = _mv_531.value;
                __auto_type _mv_532 = (*clause_expr);
                switch (_mv_532.tag) {
                    case types_SExpr_lst:
                    {
                        __auto_type clause_lst = _mv_532.data.lst;
                        {
                            __auto_type clause_items = clause_lst.items;
                            __auto_type clause_len = ((int64_t)((clause_items).len));
                            if ((clause_len < 1)) {
                                context_ctx_add_error_at(ctx, SLOP_STR("invalid cond clause"), context_sexpr_line(clause_expr), context_sexpr_col(clause_expr));
                            } else {
                                __auto_type _mv_533 = ({ __auto_type _lst = clause_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_533.has_value) {
                                    __auto_type test_expr = _mv_533.value;
                                    __auto_type _mv_534 = (*test_expr);
                                    switch (_mv_534.tag) {
                                        case types_SExpr_sym:
                                        {
                                            __auto_type sym = _mv_534.data.sym;
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
                                } else if (!_mv_533.has_value) {
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
            } else if (!_mv_531.has_value) {
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
        __auto_type i = start;
        while ((i < len)) {
            __auto_type _mv_535 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_535.has_value) {
                __auto_type body_expr = _mv_535.value;
                {
                    __auto_type body_is_last = (i == (len - 1));
                    match_emit_branch_body_item(ctx, body_expr, is_return, (is_last && body_is_last));
                }
            } else if (!_mv_535.has_value) {
            }
            i = (i + 1);
        }
    }
}

void match_emit_inline_with_arena(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, uint8_t is_return) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type arena = (*ctx).arena;
        __auto_type len = ((int64_t)((items).len));
        if ((len < 2)) {
            context_ctx_add_error_at(ctx, SLOP_STR("invalid with-arena: need size"), context_list_first_line(items), context_list_first_col(items));
        } else {
            context_ctx_emit(ctx, SLOP_STR("{"));
            context_ctx_indent(ctx);
            context_ctx_push_scope(ctx);
            __auto_type _mv_536 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_536.has_value) {
                __auto_type size_expr = _mv_536.value;
                {
                    __auto_type size_c = expr_transpile_expr(ctx, size_expr);
                    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("slop_arena _arena = slop_arena_new("), size_c, SLOP_STR(");")));
                    context_ctx_emit(ctx, SLOP_STR("slop_arena* arena = &_arena;"));
                }
            } else if (!_mv_536.has_value) {
                context_ctx_add_error_at(ctx, SLOP_STR("missing size"), context_list_first_line(items), context_list_first_col(items));
            }
            context_ctx_bind_var(ctx, (context_VarEntry){SLOP_STR("arena"), SLOP_STR("arena"), SLOP_STR("slop_arena*"), SLOP_STR(""), 1, 0});
            {
                __auto_type i = 2;
                while ((i < len)) {
                    __auto_type _mv_537 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_537.has_value) {
                        __auto_type body_expr = _mv_537.value;
                        {
                            __auto_type is_last = (i == (len - 1));
                            match_emit_branch_body_item(ctx, body_expr, (is_return && is_last), is_last);
                        }
                    } else if (!_mv_537.has_value) {
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
}

void match_emit_inline_return(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 2)) {
            context_ctx_emit(ctx, SLOP_STR("return;"));
        } else {
            __auto_type _mv_538 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_538.has_value) {
                __auto_type val_expr = _mv_538.value;
                match_emit_typed_return_expr(ctx, val_expr);
            } else if (!_mv_538.has_value) {
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
    __auto_type _mv_539 = (*expr);
    switch (_mv_539.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_539.data.lst;
            {
                __auto_type items = lst.items;
                if ((((int64_t)((items).len)) < 1)) {
                    match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
                } else {
                    __auto_type _mv_540 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_540.has_value) {
                        __auto_type head = _mv_540.value;
                        __auto_type _mv_541 = (*head);
                        switch (_mv_541.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_541.data.sym;
                                {
                                    __auto_type op = sym.name;
                                    if (string_eq(op, SLOP_STR("some"))) {
                                        __auto_type _mv_542 = context_ctx_get_current_return_type(ctx);
                                        if (_mv_542.has_value) {
                                            __auto_type ret_type = _mv_542.value;
                                            if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                                                if ((((int64_t)((items).len)) < 2)) {
                                                    match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
                                                } else {
                                                    __auto_type _mv_543 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                    if (_mv_543.has_value) {
                                                        __auto_type inner_expr = _mv_543.value;
                                                        {
                                                            __auto_type inner_c = expr_transpile_expr(ctx, inner_expr);
                                                            context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("return ("), ret_type, SLOP_STR("){.has_value = 1, .value = "), inner_c, SLOP_STR("};")));
                                                        }
                                                    } else if (!_mv_543.has_value) {
                                                        match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
                                                    }
                                                }
                                            } else {
                                                match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
                                            }
                                        } else if (!_mv_542.has_value) {
                                            match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
                                        }
                                    } else if (string_eq(op, SLOP_STR("none"))) {
                                        __auto_type _mv_544 = context_ctx_get_current_return_type(ctx);
                                        if (_mv_544.has_value) {
                                            __auto_type ret_type = _mv_544.value;
                                            if (strlib_starts_with(ret_type, SLOP_STR("slop_option_"))) {
                                                context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("return ("), ret_type, SLOP_STR("){.has_value = false};")));
                                            } else {
                                                match_emit_return_typed(ctx, expr_transpile_expr(ctx, expr));
                                            }
                                        } else if (!_mv_544.has_value) {
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
                    } else if (!_mv_540.has_value) {
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

