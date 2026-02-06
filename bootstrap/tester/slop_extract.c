#include "../runtime/slop_runtime.h"
#include "slop_extract.h"

extract_TestCase* extract_test_case_new(slop_arena* arena, slop_string fn_name, slop_option_string module_name, slop_list_types_SExpr_ptr args, types_SExpr* expected, slop_option_string return_type, uint8_t needs_arena, int64_t arena_position, slop_option_string eq_fn);
int64_t extract_find_arrow_separator(slop_list_types_SExpr_ptr items);
int64_t extract_find_arrow_separator_from(slop_list_types_SExpr_ptr items, int64_t start);
int64_t extract_detect_arena_param(types_SExpr* params);
slop_option_string extract_extract_return_type(slop_arena* arena, types_SExpr* spec_form);
slop_list_extract_TestCase_ptr extract_extract_fn_examples(slop_arena* arena, types_SExpr* fn_form, slop_option_string module_name);
slop_option_extract_TestCase_ptr extract_parse_example(slop_arena* arena, types_SExpr* example_form, slop_string fn_name, slop_option_string module_name, slop_option_string return_type, uint8_t needs_arena, int64_t arena_pos);
slop_list_types_SExpr_ptr extract_unpack_grouped_args(slop_arena* arena, slop_list_types_SExpr_ptr args);
slop_list_extract_TestCase_ptr extract_extract_examples_from_module(slop_arena* arena, types_SExpr* module_form);
slop_list_extract_TestCase_ptr extract_extract_examples_from_ast(slop_arena* arena, slop_list_types_SExpr_ptr ast);

extract_TestCase* extract_test_case_new(slop_arena* arena, slop_string fn_name, slop_option_string module_name, slop_list_types_SExpr_ptr args, types_SExpr* expected, slop_option_string return_type, uint8_t needs_arena, int64_t arena_position, slop_option_string eq_fn) {
    {
        __auto_type tc = ((extract_TestCase*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 160); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        (*tc) = (extract_TestCase){fn_name, module_name, args, expected, return_type, needs_arena, arena_position, eq_fn};
        return tc;
    }
}

int64_t extract_find_arrow_separator(slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        int64_t i = 0;
        int64_t found = -1;
        while (((i < len) && (found == -1))) {
            __auto_type _mv_1416 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1416.has_value) {
                __auto_type item = _mv_1416.value;
                if (parser_sexpr_is_symbol(item)) {
                    if (string_eq(parser_sexpr_get_symbol_name(item), SLOP_STR("->"))) {
                        found = i;
                    }
                }
            } else if (!_mv_1416.has_value) {
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
        while (((i < len) && (found == -1))) {
            __auto_type _mv_1417 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1417.has_value) {
                __auto_type item = _mv_1417.value;
                if (parser_sexpr_is_symbol(item)) {
                    if (string_eq(parser_sexpr_get_symbol_name(item), SLOP_STR("->"))) {
                        found = i;
                    }
                }
            } else if (!_mv_1417.has_value) {
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
            while (((i < len) && (found == -1))) {
                __auto_type _mv_1418 = parser_sexpr_list_get(params, i);
                if (_mv_1418.has_value) {
                    __auto_type param = _mv_1418.value;
                    {
                        __auto_type plen = parser_sexpr_list_len(param);
                        if ((plen >= 2)) {
                            {
                                __auto_type type_pos = (((plen == 2)) ? 1 : 2);
                                __auto_type name_pos = (((plen == 2)) ? 0 : 1);
                                __auto_type _mv_1419 = parser_sexpr_list_get(param, name_pos);
                                if (_mv_1419.has_value) {
                                    __auto_type name_expr = _mv_1419.value;
                                    if (parser_sexpr_is_symbol(name_expr)) {
                                        if (string_eq(parser_sexpr_get_symbol_name(name_expr), SLOP_STR("arena"))) {
                                            __auto_type _mv_1420 = parser_sexpr_list_get(param, type_pos);
                                            if (_mv_1420.has_value) {
                                                __auto_type type_expr = _mv_1420.value;
                                                if (parser_sexpr_is_symbol(type_expr)) {
                                                    if (string_eq(parser_sexpr_get_symbol_name(type_expr), SLOP_STR("Arena"))) {
                                                        found = i;
                                                    }
                                                }
                                            } else if (!_mv_1420.has_value) {
                                            }
                                        }
                                    }
                                } else if (!_mv_1419.has_value) {
                                }
                            }
                        }
                    }
                } else if (!_mv_1418.has_value) {
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
    if ((parser_sexpr_list_len(spec_form) < 2)) {
        return (slop_option_string){.has_value = false};
    } else {
        __auto_type _mv_1421 = parser_sexpr_list_get(spec_form, 1);
        if (_mv_1421.has_value) {
            __auto_type sig = _mv_1421.value;
            {
                __auto_type sig_len = parser_sexpr_list_len(sig);
                if ((sig_len < 3)) {
                    return (slop_option_string){.has_value = false};
                } else {
                    __auto_type _mv_1422 = parser_sexpr_list_get(sig, (sig_len - 1));
                    if (_mv_1422.has_value) {
                        __auto_type ret_type = _mv_1422.value;
                        return (slop_option_string){.has_value = 1, .value = parser_pretty_print(arena, ret_type)};
                    } else if (!_mv_1422.has_value) {
                        return (slop_option_string){.has_value = false};
                    }
                }
            }
        } else if (!_mv_1421.has_value) {
            return (slop_option_string){.has_value = false};
        }
    }
}

slop_list_extract_TestCase_ptr extract_extract_fn_examples(slop_arena* arena, types_SExpr* fn_form, slop_option_string module_name) {
    {
        __auto_type result = ((slop_list_extract_TestCase_ptr){ .data = (extract_TestCase**)slop_arena_alloc(arena, 16 * sizeof(extract_TestCase*)), .len = 0, .cap = 16 });
        if ((parser_sexpr_list_len(fn_form) < 3)) {
            return result;
        } else {
            {
                __auto_type fn_name_opt = parser_sexpr_list_get(fn_form, 1);
                __auto_type _mv_1423 = fn_name_opt;
                if (!_mv_1423.has_value) {
                    return result;
                } else if (_mv_1423.has_value) {
                    __auto_type fn_name_expr = _mv_1423.value;
                    if (!(parser_sexpr_is_symbol(fn_name_expr))) {
                        return result;
                    } else {
                        {
                            __auto_type fn_name = parser_sexpr_get_symbol_name(fn_name_expr);
                            {
                                __auto_type params_opt = parser_sexpr_list_get(fn_form, 2);
                                __auto_type _mv_1424 = params_opt;
                                if (!_mv_1424.has_value) {
                                    return result;
                                } else if (_mv_1424.has_value) {
                                    __auto_type params = _mv_1424.value;
                                    {
                                        __auto_type arena_pos = extract_detect_arena_param(params);
                                        __auto_type needs_arena = (arena_pos >= 0);
                                        slop_option_string return_type = (slop_option_string){.has_value = false};
                                        {
                                            __auto_type form_len = parser_sexpr_list_len(fn_form);
                                            __auto_type i = 3;
                                            while ((i < form_len)) {
                                                __auto_type _mv_1425 = parser_sexpr_list_get(fn_form, i);
                                                if (_mv_1425.has_value) {
                                                    __auto_type item = _mv_1425.value;
                                                    if (parser_is_form(item, SLOP_STR("@spec"))) {
                                                        return_type = extract_extract_return_type(arena, item);
                                                    }
                                                    if (parser_is_form(item, SLOP_STR("@example"))) {
                                                        {
                                                            __auto_type example_tc = extract_parse_example(arena, item, fn_name, module_name, return_type, needs_arena, arena_pos);
                                                            __auto_type _mv_1426 = example_tc;
                                                            if (_mv_1426.has_value) {
                                                                __auto_type tc = _mv_1426.value;
                                                                ({ __auto_type _lst_p = &(result); __auto_type _item = (tc); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                            } else if (!_mv_1426.has_value) {
                                                            }
                                                        }
                                                    }
                                                } else if (!_mv_1425.has_value) {
                                                }
                                                i = (i + 1);
                                            }
                                        }
                                        return result;
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

slop_option_extract_TestCase_ptr extract_parse_example(slop_arena* arena, types_SExpr* example_form, slop_string fn_name, slop_option_string module_name, slop_option_string return_type, uint8_t needs_arena, int64_t arena_pos) {
    {
        __auto_type example_len = parser_sexpr_list_len(example_form);
        if ((example_len < 2)) {
            return (slop_option_extract_TestCase_ptr){.has_value = false};
        } else {
            {
                __auto_type items = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
                int64_t i = 1;
                while ((i < example_len)) {
                    __auto_type _mv_1427 = parser_sexpr_list_get(example_form, i);
                    if (_mv_1427.has_value) {
                        __auto_type item = _mv_1427.value;
                        ({ __auto_type _lst_p = &(items); __auto_type _item = (item); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    } else if (!_mv_1427.has_value) {
                    }
                    i = (i + 1);
                }
                {
                    slop_option_string eq_fn = (slop_option_string){.has_value = false};
                    int64_t args_start = 0;
                    if ((((int64_t)((items).len)) >= 2)) {
                        __auto_type _mv_1428 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1428.has_value) {
                            __auto_type first_item = _mv_1428.value;
                            if (parser_sexpr_is_symbol(first_item)) {
                                if (string_eq(parser_sexpr_get_symbol_name(first_item), SLOP_STR(":eq"))) {
                                    __auto_type _mv_1429 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_1429.has_value) {
                                        __auto_type eq_name_expr = _mv_1429.value;
                                        if (parser_sexpr_is_symbol(eq_name_expr)) {
                                            eq_fn = (slop_option_string){.has_value = 1, .value = parser_sexpr_get_symbol_name(eq_name_expr)};
                                            args_start = 2;
                                        }
                                    } else if (!_mv_1429.has_value) {
                                    }
                                }
                            }
                        } else if (!_mv_1428.has_value) {
                        }
                    }
                    {
                        __auto_type arrow_idx = extract_find_arrow_separator_from(items, args_start);
                        if ((arrow_idx < 0)) {
                            return (slop_option_extract_TestCase_ptr){.has_value = false};
                        } else {
                            if ((arrow_idx >= (((int64_t)((items).len)) - 1))) {
                                return (slop_option_extract_TestCase_ptr){.has_value = false};
                            } else {
                                {
                                    __auto_type args = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
                                    int64_t j = args_start;
                                    while ((j < arrow_idx)) {
                                        __auto_type _mv_1430 = ({ __auto_type _lst = items; size_t _idx = (size_t)j; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1430.has_value) {
                                            __auto_type arg = _mv_1430.value;
                                            ({ __auto_type _lst_p = &(args); __auto_type _item = (arg); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                        } else if (!_mv_1430.has_value) {
                                        }
                                        j = (j + 1);
                                    }
                                    {
                                        __auto_type final_args = extract_unpack_grouped_args(arena, args);
                                        __auto_type _mv_1431 = ({ __auto_type _lst = items; size_t _idx = (size_t)(arrow_idx + 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1431.has_value) {
                                            __auto_type expected = _mv_1431.value;
                                            return (slop_option_extract_TestCase_ptr){.has_value = 1, .value = extract_test_case_new(arena, fn_name, module_name, final_args, expected, return_type, needs_arena, arena_pos, eq_fn)};
                                        } else if (!_mv_1431.has_value) {
                                            return (slop_option_extract_TestCase_ptr){.has_value = false};
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

slop_list_types_SExpr_ptr extract_unpack_grouped_args(slop_arena* arena, slop_list_types_SExpr_ptr args) {
    {
        slop_list_types_SExpr_ptr result = args;
        if ((((int64_t)((args).len)) == 1)) {
            __auto_type _mv_1432 = ({ __auto_type _lst = args; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1432.has_value) {
                __auto_type first_arg = _mv_1432.value;
                if (!(parser_sexpr_is_symbol(first_arg))) {
                    {
                        __auto_type inner_len = parser_sexpr_list_len(first_arg);
                        if ((inner_len == 0)) {
                            result = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
                        } else {
                            __auto_type _mv_1433 = parser_sexpr_list_get(first_arg, 0);
                            if (_mv_1433.has_value) {
                                __auto_type first_inner = _mv_1433.value;
                                if ((parser_sexpr_is_symbol(first_inner) && string_eq(parser_sexpr_get_symbol_name(first_inner), SLOP_STR("arena")))) {
                                    {
                                        __auto_type unpacked = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
                                        __auto_type i = 1;
                                        while ((i < inner_len)) {
                                            __auto_type _mv_1434 = parser_sexpr_list_get(first_arg, i);
                                            if (_mv_1434.has_value) {
                                                __auto_type item = _mv_1434.value;
                                                ({ __auto_type _lst_p = &(unpacked); __auto_type _item = (item); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                            } else if (!_mv_1434.has_value) {
                                            }
                                            i = (i + 1);
                                        }
                                        result = unpacked;
                                    }
                                } else {
                                    if (((parser_sexpr_is_number(first_inner)) || (parser_sexpr_is_string(first_inner)) || (!(parser_sexpr_is_symbol(first_inner))))) {
                                        {
                                            __auto_type unpacked = ((slop_list_types_SExpr_ptr){ .data = (types_SExpr**)slop_arena_alloc(arena, 16 * sizeof(types_SExpr*)), .len = 0, .cap = 16 });
                                            __auto_type i = 0;
                                            while ((i < inner_len)) {
                                                __auto_type _mv_1435 = parser_sexpr_list_get(first_arg, i);
                                                if (_mv_1435.has_value) {
                                                    __auto_type item = _mv_1435.value;
                                                    ({ __auto_type _lst_p = &(unpacked); __auto_type _item = (item); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                } else if (!_mv_1435.has_value) {
                                                }
                                                i = (i + 1);
                                            }
                                            result = unpacked;
                                        }
                                    }
                                }
                            } else if (!_mv_1433.has_value) {
                            }
                        }
                    }
                }
            } else if (!_mv_1432.has_value) {
            }
        }
        return result;
    }
}

slop_list_extract_TestCase_ptr extract_extract_examples_from_module(slop_arena* arena, types_SExpr* module_form) {
    {
        __auto_type result = ((slop_list_extract_TestCase_ptr){ .data = (extract_TestCase**)slop_arena_alloc(arena, 16 * sizeof(extract_TestCase*)), .len = 0, .cap = 16 });
        if ((parser_sexpr_list_len(module_form) < 2)) {
            return result;
        } else {
            {
                __auto_type mod_name_opt = parser_sexpr_list_get(module_form, 1);
                __auto_type _mv_1436 = mod_name_opt;
                if (!_mv_1436.has_value) {
                    return result;
                } else if (_mv_1436.has_value) {
                    __auto_type mod_name_expr = _mv_1436.value;
                    {
                        slop_option_string mod_name = (slop_option_string){.has_value = false};
                        if (parser_sexpr_is_symbol(mod_name_expr)) {
                            mod_name = (slop_option_string){.has_value = 1, .value = parser_sexpr_get_symbol_name(mod_name_expr)};
                        }
                        {
                            __auto_type form_len = parser_sexpr_list_len(module_form);
                            __auto_type i = 2;
                            while ((i < form_len)) {
                                __auto_type _mv_1437 = parser_sexpr_list_get(module_form, i);
                                if (_mv_1437.has_value) {
                                    __auto_type item = _mv_1437.value;
                                    if (parser_is_form(item, SLOP_STR("fn"))) {
                                        {
                                            __auto_type fn_tests = extract_extract_fn_examples(arena, item, mod_name);
                                            __auto_type fn_tests_len = ((int64_t)((fn_tests).len));
                                            __auto_type j = 0;
                                            while ((j < fn_tests_len)) {
                                                __auto_type _mv_1438 = ({ __auto_type _lst = fn_tests; size_t _idx = (size_t)j; slop_option_extract_TestCase_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1438.has_value) {
                                                    __auto_type tc = _mv_1438.value;
                                                    ({ __auto_type _lst_p = &(result); __auto_type _item = (tc); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                } else if (!_mv_1438.has_value) {
                                                }
                                                j = (j + 1);
                                            }
                                        }
                                    }
                                } else if (!_mv_1437.has_value) {
                                }
                                i = (i + 1);
                            }
                        }
                        return result;
                    }
                }
            }
        }
    }
}

slop_list_extract_TestCase_ptr extract_extract_examples_from_ast(slop_arena* arena, slop_list_types_SExpr_ptr ast) {
    {
        __auto_type result = ((slop_list_extract_TestCase_ptr){ .data = (extract_TestCase**)slop_arena_alloc(arena, 16 * sizeof(extract_TestCase*)), .len = 0, .cap = 16 });
        __auto_type len = ((int64_t)((ast).len));
        int64_t i = 0;
        while ((i < len)) {
            __auto_type _mv_1439 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1439.has_value) {
                __auto_type form = _mv_1439.value;
                if (parser_is_form(form, SLOP_STR("fn"))) {
                    {
                        __auto_type fn_tests = extract_extract_fn_examples(arena, form, ((slop_option_string){.has_value = false}));
                        __auto_type fn_tests_len = ((int64_t)((fn_tests).len));
                        __auto_type j = 0;
                        while ((j < fn_tests_len)) {
                            __auto_type _mv_1440 = ({ __auto_type _lst = fn_tests; size_t _idx = (size_t)j; slop_option_extract_TestCase_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1440.has_value) {
                                __auto_type tc = _mv_1440.value;
                                ({ __auto_type _lst_p = &(result); __auto_type _item = (tc); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            } else if (!_mv_1440.has_value) {
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
                        while ((k < mod_tests_len)) {
                            __auto_type _mv_1441 = ({ __auto_type _lst = mod_tests; size_t _idx = (size_t)k; slop_option_extract_TestCase_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1441.has_value) {
                                __auto_type tc = _mv_1441.value;
                                ({ __auto_type _lst_p = &(result); __auto_type _item = (tc); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            } else if (!_mv_1441.has_value) {
                            }
                            k = (k + 1);
                        }
                    }
                }
            } else if (!_mv_1439.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

