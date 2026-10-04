#include "../runtime/slop_runtime.h"
#include "slop_extract.h"

extract_TestCase* extract_test_case_new(slop_arena* arena, slop_string fn_name, slop_option_string module_name, slop_list_types_SExpr_ptr args, types_SExpr* expected, slop_option_string return_type, uint8_t needs_arena, int64_t arena_position, slop_option_string eq_fn, types_SExpr* params, slop_list_types_SExpr_ptr preconditions);
int64_t extract_find_arrow_separator(slop_list_types_SExpr_ptr items);
int64_t extract_find_arrow_separator_from(slop_list_types_SExpr_ptr items, int64_t start);
int64_t extract_detect_arena_param(types_SExpr* params);
slop_option_string extract_extract_return_type(slop_arena* arena, types_SExpr* spec_form);
slop_list_types_SExpr_ptr extract_collect_preconditions(slop_arena* arena, types_SExpr* fn_form);
slop_list_extract_TestCase_ptr extract_extract_fn_examples(slop_arena* arena, types_SExpr* fn_form, slop_option_string module_name);
slop_option_extract_TestCase_ptr extract_parse_example(slop_arena* arena, types_SExpr* example_form, slop_string fn_name, slop_option_string module_name, slop_option_string return_type, uint8_t needs_arena, int64_t arena_pos, types_SExpr* params, slop_list_types_SExpr_ptr preconditions);
slop_list_types_SExpr_ptr extract_unpack_grouped_args(slop_arena* arena, slop_list_types_SExpr_ptr args);
slop_list_extract_TestCase_ptr extract_extract_examples_from_module(slop_arena* arena, types_SExpr* module_form);
slop_list_extract_TestCase_ptr extract_extract_examples_from_ast(slop_arena* arena, slop_list_types_SExpr_ptr ast);

extract_TestCase* extract_test_case_new(slop_arena* arena, slop_string fn_name, slop_option_string module_name, slop_list_types_SExpr_ptr args, types_SExpr* expected, slop_option_string return_type, uint8_t needs_arena, int64_t arena_position, slop_option_string eq_fn, types_SExpr* params, slop_list_types_SExpr_ptr preconditions) {
    {
        __auto_type tc = ((extract_TestCase*)(({ __auto_type _alloc = (extract_TestCase*)slop_arena_alloc(arena, sizeof(extract_TestCase)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        (*tc) = (extract_TestCase){fn_name, module_name, args, expected, return_type, needs_arena, arena_position, eq_fn, params, preconditions};
        return tc;
    }
}

int64_t extract_find_arrow_separator(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 0;
        int64_t found = -1;
        while ((i < len) && (found == -1)) {
            __auto_type _mv_1616 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1616.has_value) {
                __auto_type item = _mv_1616.value;
                if (parser_sexpr_is_symbol(item)) {
                    if (string_eq(parser_sexpr_get_symbol_name(item), SLOP_STR("->"))) {
                        found = i;
                    }
                }
            } else if (!_mv_1616.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

int64_t extract_find_arrow_separator_from(slop_list_types_SExpr_ptr items, int64_t start) {
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = start;
        int64_t found = -1;
        while ((i < len) && (found == -1)) {
            __auto_type _mv_1617 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1617.has_value) {
                __auto_type item = _mv_1617.value;
                if (parser_sexpr_is_symbol(item)) {
                    if (string_eq(parser_sexpr_get_symbol_name(item), SLOP_STR("->"))) {
                        found = i;
                    }
                }
            } else if (!_mv_1617.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

int64_t extract_detect_arena_param(types_SExpr* params) {
    if (!(parser_sexpr_is_symbol(params))) {
        {
            __auto_type len = parser_sexpr_list_len(params);
            int64_t i = 0;
            int64_t found = -1;
            while ((i < len) && (found == -1)) {
                __auto_type _mv_1618 = parser_sexpr_list_get(params, i);
                if (_mv_1618.has_value) {
                    __auto_type param = _mv_1618.value;
                    {
                        __auto_type plen = parser_sexpr_list_len(param);
                        if (plen >= 2) {
                            {
                                __auto_type type_pos = (((plen == 2)) ? 1 : 2);
                                __auto_type name_pos = (((plen == 2)) ? 0 : 1);
                                __auto_type _mv_1619 = parser_sexpr_list_get(param, name_pos);
                                if (_mv_1619.has_value) {
                                    __auto_type name_expr = _mv_1619.value;
                                    if (parser_sexpr_is_symbol(name_expr)) {
                                        if (string_eq(parser_sexpr_get_symbol_name(name_expr), SLOP_STR("arena"))) {
                                            __auto_type _mv_1620 = parser_sexpr_list_get(param, type_pos);
                                            if (_mv_1620.has_value) {
                                                __auto_type type_expr = _mv_1620.value;
                                                if (parser_sexpr_is_symbol(type_expr)) {
                                                    if (string_eq(parser_sexpr_get_symbol_name(type_expr), SLOP_STR("Arena"))) {
                                                        found = i;
                                                    }
                                                }
                                            } else if (!_mv_1620.has_value) {
                                            }
                                        }
                                    }
                                } else if (!_mv_1619.has_value) {
                                }
                            }
                        }
                    }
                } else if (!_mv_1618.has_value) {
                }
                i = (i + 1);
            }
            return found;
        }
    } else {
        return -1;
    }
}

slop_option_string extract_extract_return_type(slop_arena* arena, types_SExpr* spec_form) {
    if (parser_sexpr_list_len(spec_form) < 2) {
        return (slop_option_string){.has_value = false};
    } else {
        __auto_type _mv_1621 = parser_sexpr_list_get(spec_form, 1);
        if (_mv_1621.has_value) {
            __auto_type sig = _mv_1621.value;
            {
                __auto_type sig_len = parser_sexpr_list_len(sig);
                if (sig_len < 3) {
                    return (slop_option_string){.has_value = false};
                } else {
                    __auto_type _mv_1622 = parser_sexpr_list_get(sig, (sig_len - 1));
                    if (_mv_1622.has_value) {
                        __auto_type ret_type = _mv_1622.value;
                        return (slop_option_string){.has_value = 1, .value = parser_pretty_print(arena, ret_type)};
                    } else if (!_mv_1622.has_value) {
                        return (slop_option_string){.has_value = false};
                    }
                    SLOP_UNREACHABLE();
                }
            }
        } else if (!_mv_1621.has_value) {
            return (slop_option_string){.has_value = false};
        }
        SLOP_UNREACHABLE();
    }
}

slop_list_types_SExpr_ptr extract_collect_preconditions(slop_arena* arena, types_SExpr* fn_form) {
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    {
        __auto_type result = ((slop_list_types_SExpr_ptr){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
        __auto_type form_len = parser_sexpr_list_len(fn_form);
        int64_t i = 3;
        while (i < form_len) {
            __auto_type _mv_1623 = parser_sexpr_list_get(fn_form, i);
            if (_mv_1623.has_value) {
                __auto_type item = _mv_1623.value;
                if (parser_is_form(item, SLOP_STR("@pre"))) {
                    if (parser_sexpr_list_len(item) >= 2) {
                        __auto_type _mv_1624 = parser_sexpr_list_get(item, 1);
                        if (_mv_1624.has_value) {
                            __auto_type cond_expr = _mv_1624.value;
                            ({ __auto_type _lst_p = &(result); __auto_type _item = (cond_expr); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        } else if (!_mv_1624.has_value) {
                        }
                    }
                }
            } else if (!_mv_1623.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_list_extract_TestCase_ptr extract_extract_fn_examples(slop_arena* arena, types_SExpr* fn_form, slop_option_string module_name) {
    {
        __auto_type result = ((slop_list_extract_TestCase_ptr){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
        if (parser_sexpr_list_len(fn_form) < 3) {
            return result;
        } else {
            {
                __auto_type fn_name_opt = parser_sexpr_list_get(fn_form, 1);
                __auto_type _mv_1625 = fn_name_opt;
                if (!_mv_1625.has_value) {
                    return result;
                } else if (_mv_1625.has_value) {
                    __auto_type fn_name_expr = _mv_1625.value;
                    if (!(parser_sexpr_is_symbol(fn_name_expr))) {
                        return result;
                    } else {
                        {
                            __auto_type fn_name = parser_sexpr_get_symbol_name(fn_name_expr);
                            {
                                __auto_type params_opt = parser_sexpr_list_get(fn_form, 2);
                                __auto_type _mv_1626 = params_opt;
                                if (!_mv_1626.has_value) {
                                    return result;
                                } else if (_mv_1626.has_value) {
                                    __auto_type params = _mv_1626.value;
                                    {
                                        __auto_type arena_pos = extract_detect_arena_param(params);
                                        __auto_type needs_arena = (arena_pos >= 0);
                                        __auto_type preconditions = extract_collect_preconditions(arena, fn_form);
                                        slop_option_string return_type = (slop_option_string){.has_value = false};
                                        {
                                            __auto_type form_len = parser_sexpr_list_len(fn_form);
                                            __auto_type i = 3;
                                            while (i < form_len) {
                                                __auto_type _mv_1627 = parser_sexpr_list_get(fn_form, i);
                                                if (_mv_1627.has_value) {
                                                    __auto_type item = _mv_1627.value;
                                                    if (parser_is_form(item, SLOP_STR("@spec"))) {
                                                        return_type = extract_extract_return_type(arena, item);
                                                    }
                                                    if (parser_is_form(item, SLOP_STR("@example"))) {
                                                        {
                                                            __auto_type example_tc = extract_parse_example(arena, item, fn_name, module_name, return_type, needs_arena, arena_pos, params, preconditions);
                                                            __auto_type _mv_1628 = example_tc;
                                                            if (_mv_1628.has_value) {
                                                                __auto_type tc = _mv_1628.value;
                                                                ({ __auto_type _lst_p = &(result); __auto_type _item = (tc); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                            } else if (!_mv_1628.has_value) {
                                                            }
                                                        }
                                                    }
                                                } else if (!_mv_1627.has_value) {
                                                }
                                                i = (i + 1);
                                            }
                                        }
                                        return result;
                                    }
                                }
                                SLOP_UNREACHABLE();
                            }
                        }
                    }
                }
                SLOP_UNREACHABLE();
            }
        }
    }
}

slop_option_extract_TestCase_ptr extract_parse_example(slop_arena* arena, types_SExpr* example_form, slop_string fn_name, slop_option_string module_name, slop_option_string return_type, uint8_t needs_arena, int64_t arena_pos, types_SExpr* params, slop_list_types_SExpr_ptr preconditions) {
    {
        __auto_type example_len = parser_sexpr_list_len(example_form);
        if (example_len < 2) {
            return (slop_option_extract_TestCase_ptr){.has_value = false};
        } else {
            {
                __auto_type items = ((slop_list_types_SExpr_ptr){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
                int64_t i = 1;
                while (i < example_len) {
                    __auto_type _mv_1629 = parser_sexpr_list_get(example_form, i);
                    if (_mv_1629.has_value) {
                        __auto_type item = _mv_1629.value;
                        ({ __auto_type _lst_p = &(items); __auto_type _item = (item); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    } else if (!_mv_1629.has_value) {
                    }
                    i = (i + 1);
                }
                {
                    slop_option_string eq_fn = (slop_option_string){.has_value = false};
                    int64_t args_start = 0;
                    if (((int64_t)((items).len)) >= 2) {
                        __auto_type _mv_1630 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1630.has_value) {
                            __auto_type first_item = _mv_1630.value;
                            if (parser_sexpr_is_symbol(first_item)) {
                                if (string_eq(parser_sexpr_get_symbol_name(first_item), SLOP_STR(":eq"))) {
                                    __auto_type _mv_1631 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_1631.has_value) {
                                        __auto_type eq_name_expr = _mv_1631.value;
                                        if (parser_sexpr_is_symbol(eq_name_expr)) {
                                            eq_fn = (slop_option_string){.has_value = 1, .value = parser_sexpr_get_symbol_name(eq_name_expr)};
                                            args_start = 2;
                                        }
                                    } else if (!_mv_1631.has_value) {
                                    }
                                }
                            }
                        } else if (!_mv_1630.has_value) {
                        }
                    }
                    {
                        __auto_type arrow_idx = extract_find_arrow_separator_from(items, args_start);
                        if (arrow_idx < 0) {
                            return (slop_option_extract_TestCase_ptr){.has_value = false};
                        } else {
                            if (arrow_idx >= (((int64_t)((items).len)) - 1)) {
                                return (slop_option_extract_TestCase_ptr){.has_value = false};
                            } else {
                                {
                                    __auto_type args = ((slop_list_types_SExpr_ptr){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
                                    int64_t j = args_start;
                                    while (j < arrow_idx) {
                                        __auto_type _mv_1632 = ({ __auto_type _lst = items; size_t _idx = (size_t)j; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1632.has_value) {
                                            __auto_type arg = _mv_1632.value;
                                            ({ __auto_type _lst_p = &(args); __auto_type _item = (arg); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                        } else if (!_mv_1632.has_value) {
                                        }
                                        j = (j + 1);
                                    }
                                    {
                                        __auto_type final_args = extract_unpack_grouped_args(arena, args);
                                        __auto_type _mv_1633 = ({ __auto_type _lst = items; size_t _idx = (size_t)(arrow_idx + 1); slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1633.has_value) {
                                            __auto_type expected = _mv_1633.value;
                                            return (slop_option_extract_TestCase_ptr){.has_value = 1, .value = extract_test_case_new(arena, fn_name, module_name, final_args, expected, return_type, needs_arena, arena_pos, eq_fn, params, preconditions)};
                                        } else if (!_mv_1633.has_value) {
                                            return (slop_option_extract_TestCase_ptr){.has_value = false};
                                        }
                                        SLOP_UNREACHABLE();
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

slop_list_types_SExpr_ptr extract_unpack_grouped_args(slop_arena* arena, slop_list_types_SExpr_ptr args) {
    {
        slop_list_types_SExpr_ptr result = args;
        if (((int64_t)((args).len)) == 1) {
            __auto_type _mv_1634 = ({ __auto_type _lst = args; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1634.has_value) {
                __auto_type first_arg = _mv_1634.value;
                if (!(parser_sexpr_is_symbol(first_arg))) {
                    {
                        __auto_type inner_len = parser_sexpr_list_len(first_arg);
                        if (inner_len == 0) {
                            result = ((slop_list_types_SExpr_ptr){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
                        } else {
                            __auto_type _mv_1635 = parser_sexpr_list_get(first_arg, 0);
                            if (_mv_1635.has_value) {
                                __auto_type first_inner = _mv_1635.value;
                                if (parser_sexpr_is_symbol(first_inner) && string_eq(parser_sexpr_get_symbol_name(first_inner), SLOP_STR("arena"))) {
                                    {
                                        __auto_type unpacked = ((slop_list_types_SExpr_ptr){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
                                        __auto_type i = 1;
                                        while (i < inner_len) {
                                            __auto_type _mv_1636 = parser_sexpr_list_get(first_arg, i);
                                            if (_mv_1636.has_value) {
                                                __auto_type item = _mv_1636.value;
                                                ({ __auto_type _lst_p = &(unpacked); __auto_type _item = (item); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                            } else if (!_mv_1636.has_value) {
                                            }
                                            i = (i + 1);
                                        }
                                        result = unpacked;
                                    }
                                } else {
                                    if ((parser_sexpr_is_number(first_inner)) || (parser_sexpr_is_string(first_inner)) || (!(parser_sexpr_is_symbol(first_inner)))) {
                                        {
                                            __auto_type unpacked = ((slop_list_types_SExpr_ptr){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
                                            __auto_type i = 0;
                                            while (i < inner_len) {
                                                __auto_type _mv_1637 = parser_sexpr_list_get(first_arg, i);
                                                if (_mv_1637.has_value) {
                                                    __auto_type item = _mv_1637.value;
                                                    ({ __auto_type _lst_p = &(unpacked); __auto_type _item = (item); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                } else if (!_mv_1637.has_value) {
                                                }
                                                i = (i + 1);
                                            }
                                            result = unpacked;
                                        }
                                    }
                                }
                            } else if (!_mv_1635.has_value) {
                            }
                        }
                    }
                }
            } else if (!_mv_1634.has_value) {
            }
        }
        return result;
    }
}

slop_list_extract_TestCase_ptr extract_extract_examples_from_module(slop_arena* arena, types_SExpr* module_form) {
    {
        __auto_type result = ((slop_list_extract_TestCase_ptr){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
        if (parser_sexpr_list_len(module_form) < 2) {
            return result;
        } else {
            {
                __auto_type mod_name_opt = parser_sexpr_list_get(module_form, 1);
                __auto_type _mv_1638 = mod_name_opt;
                if (!_mv_1638.has_value) {
                    return result;
                } else if (_mv_1638.has_value) {
                    __auto_type mod_name_expr = _mv_1638.value;
                    {
                        slop_option_string mod_name = (slop_option_string){.has_value = false};
                        if (parser_sexpr_is_symbol(mod_name_expr)) {
                            mod_name = (slop_option_string){.has_value = 1, .value = parser_sexpr_get_symbol_name(mod_name_expr)};
                        }
                        {
                            __auto_type form_len = parser_sexpr_list_len(module_form);
                            __auto_type i = 2;
                            while (i < form_len) {
                                __auto_type _mv_1639 = parser_sexpr_list_get(module_form, i);
                                if (_mv_1639.has_value) {
                                    __auto_type item = _mv_1639.value;
                                    if (parser_is_form(item, SLOP_STR("fn"))) {
                                        {
                                            __auto_type fn_tests = extract_extract_fn_examples(arena, item, mod_name);
                                            __auto_type fn_tests_len = ((int64_t)((fn_tests).len));
                                            __auto_type j = 0;
                                            while (j < fn_tests_len) {
                                                __auto_type _mv_1640 = ({ __auto_type _lst = fn_tests; size_t _idx = (size_t)j; slop_option_extract_TestCase_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1640.has_value) {
                                                    __auto_type tc = _mv_1640.value;
                                                    ({ __auto_type _lst_p = &(result); __auto_type _item = (tc); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                } else if (!_mv_1640.has_value) {
                                                }
                                                j = (j + 1);
                                            }
                                        }
                                    }
                                } else if (!_mv_1639.has_value) {
                                }
                                i = (i + 1);
                            }
                        }
                        return result;
                    }
                }
                SLOP_UNREACHABLE();
            }
        }
    }
}

slop_list_extract_TestCase_ptr extract_extract_examples_from_ast(slop_arena* arena, slop_list_types_SExpr_ptr ast) {
    {
        __auto_type result = ((slop_list_extract_TestCase_ptr){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
        __auto_type len = ((int64_t)((ast).len));
        int64_t i = 0;
        while (i < len) {
            __auto_type _mv_1641 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1641.has_value) {
                __auto_type form = _mv_1641.value;
                if (parser_is_form(form, SLOP_STR("fn"))) {
                    {
                        __auto_type fn_tests = extract_extract_fn_examples(arena, form, ((slop_option_string){.has_value = false}));
                        __auto_type fn_tests_len = ((int64_t)((fn_tests).len));
                        __auto_type j = 0;
                        while (j < fn_tests_len) {
                            __auto_type _mv_1642 = ({ __auto_type _lst = fn_tests; size_t _idx = (size_t)j; slop_option_extract_TestCase_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1642.has_value) {
                                __auto_type tc = _mv_1642.value;
                                ({ __auto_type _lst_p = &(result); __auto_type _item = (tc); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            } else if (!_mv_1642.has_value) {
                            }
                            j = (j + 1);
                        }
                    }
                }
                if (parser_is_form(form, SLOP_STR("module"))) {
                    {
                        __auto_type mod_tests = extract_extract_examples_from_module(arena, form);
                        __auto_type mod_tests_len = ((int64_t)((mod_tests).len));
                        __auto_type k = 0;
                        while (k < mod_tests_len) {
                            __auto_type _mv_1643 = ({ __auto_type _lst = mod_tests; size_t _idx = (size_t)k; slop_option_extract_TestCase_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1643.has_value) {
                                __auto_type tc = _mv_1643.value;
                                ({ __auto_type _lst_p = &(result); __auto_type _item = (tc); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            } else if (!_mv_1643.has_value) {
                            }
                            k = (k + 1);
                        }
                    }
                }
            } else if (!_mv_1641.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

