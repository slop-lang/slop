#include "../runtime/slop_runtime.h"
#include "slop_ctype.h"

uint8_t ctype_is_c_keyword(slop_string name);
uint8_t ctype_is_builtin_type(slop_string name);
uint8_t ctype_is_builtin_c_type(slop_string c_name);
slop_option_string ctype_builtin_type_c(slop_arena* arena, slop_string name);
slop_string ctype_to_c_name(slop_arena* arena, slop_string name);
slop_string ctype_type_to_identifier(slop_arena* arena, slop_string c_type);
slop_string ctype_to_c_type(slop_arena* arena, types_SExpr* expr);
slop_string ctype_to_c_type_compound(slop_arena* arena, slop_list_types_SExpr_ptr items);
slop_string ctype_build_fn_args_str(slop_arena* arena, types_SExpr* args_expr);
slop_string ctype_sexpr_to_type_string(slop_arena* arena, types_SExpr* expr);

uint8_t ctype_is_c_keyword(slop_string name) {
    return ((string_eq(name, SLOP_STR("auto"))) || (string_eq(name, SLOP_STR("break"))) || (string_eq(name, SLOP_STR("case"))) || (string_eq(name, SLOP_STR("char"))) || (string_eq(name, SLOP_STR("const"))) || (string_eq(name, SLOP_STR("continue"))) || (string_eq(name, SLOP_STR("default"))) || (string_eq(name, SLOP_STR("do"))) || (string_eq(name, SLOP_STR("double"))) || (string_eq(name, SLOP_STR("else"))) || (string_eq(name, SLOP_STR("enum"))) || (string_eq(name, SLOP_STR("extern"))) || (string_eq(name, SLOP_STR("float"))) || (string_eq(name, SLOP_STR("for"))) || (string_eq(name, SLOP_STR("goto"))) || (string_eq(name, SLOP_STR("if"))) || (string_eq(name, SLOP_STR("int"))) || (string_eq(name, SLOP_STR("long"))) || (string_eq(name, SLOP_STR("register"))) || (string_eq(name, SLOP_STR("return"))) || (string_eq(name, SLOP_STR("short"))) || (string_eq(name, SLOP_STR("signed"))) || (string_eq(name, SLOP_STR("sizeof"))) || (string_eq(name, SLOP_STR("static"))) || (string_eq(name, SLOP_STR("struct"))) || (string_eq(name, SLOP_STR("switch"))) || (string_eq(name, SLOP_STR("typedef"))) || (string_eq(name, SLOP_STR("union"))) || (string_eq(name, SLOP_STR("unsigned"))) || (string_eq(name, SLOP_STR("void"))) || (string_eq(name, SLOP_STR("volatile"))) || (string_eq(name, SLOP_STR("while"))) || (string_eq(name, SLOP_STR("inline"))) || (string_eq(name, SLOP_STR("restrict"))));
}

uint8_t ctype_is_builtin_type(slop_string name) {
    return ((string_eq(name, SLOP_STR("Int"))) || (string_eq(name, SLOP_STR("I8"))) || (string_eq(name, SLOP_STR("I16"))) || (string_eq(name, SLOP_STR("I32"))) || (string_eq(name, SLOP_STR("I64"))) || (string_eq(name, SLOP_STR("U8"))) || (string_eq(name, SLOP_STR("U16"))) || (string_eq(name, SLOP_STR("U32"))) || (string_eq(name, SLOP_STR("U64"))) || (string_eq(name, SLOP_STR("Char"))) || (string_eq(name, SLOP_STR("Float"))) || (string_eq(name, SLOP_STR("F32"))) || (string_eq(name, SLOP_STR("Bool"))) || (string_eq(name, SLOP_STR("String"))) || (string_eq(name, SLOP_STR("Bytes"))) || (string_eq(name, SLOP_STR("Unit"))) || (string_eq(name, SLOP_STR("Void"))) || (string_eq(name, SLOP_STR("Arena"))) || (string_eq(name, SLOP_STR("Milliseconds"))));
}

uint8_t ctype_is_builtin_c_type(slop_string c_name) {
    return ((string_eq(c_name, SLOP_STR("int64_t"))) || (string_eq(c_name, SLOP_STR("int32_t"))) || (string_eq(c_name, SLOP_STR("int16_t"))) || (string_eq(c_name, SLOP_STR("int8_t"))) || (string_eq(c_name, SLOP_STR("uint64_t"))) || (string_eq(c_name, SLOP_STR("uint32_t"))) || (string_eq(c_name, SLOP_STR("uint16_t"))) || (string_eq(c_name, SLOP_STR("uint8_t"))) || (string_eq(c_name, SLOP_STR("double"))) || (string_eq(c_name, SLOP_STR("float"))) || (string_eq(c_name, SLOP_STR("bool"))) || (string_eq(c_name, SLOP_STR("char"))) || (string_eq(c_name, SLOP_STR("void"))) || (string_eq(c_name, SLOP_STR("slop_string"))) || (string_eq(c_name, SLOP_STR("slop_bytes"))) || (string_eq(c_name, SLOP_STR("slop_arena"))) || (string_eq(c_name, SLOP_STR("slop_arena*"))));
}

slop_option_string ctype_builtin_type_c(slop_arena* arena, slop_string name) {
    if (string_eq(name, SLOP_STR("Int"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("int64_t")};
    } else if (string_eq(name, SLOP_STR("I8"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("int8_t")};
    } else if (string_eq(name, SLOP_STR("I16"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("int16_t")};
    } else if (string_eq(name, SLOP_STR("I32"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("int32_t")};
    } else if (string_eq(name, SLOP_STR("I64"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("int64_t")};
    } else if (string_eq(name, SLOP_STR("U8"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("uint8_t")};
    } else if (string_eq(name, SLOP_STR("U16"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("uint16_t")};
    } else if (string_eq(name, SLOP_STR("U32"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("uint32_t")};
    } else if (string_eq(name, SLOP_STR("U64"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("uint64_t")};
    } else if (string_eq(name, SLOP_STR("Char"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("char")};
    } else if (string_eq(name, SLOP_STR("Float"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("double")};
    } else if (string_eq(name, SLOP_STR("F32"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("float")};
    } else if (string_eq(name, SLOP_STR("Bool"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("uint8_t")};
    } else if (string_eq(name, SLOP_STR("String"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("slop_string")};
    } else if (string_eq(name, SLOP_STR("Bytes"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("slop_bytes")};
    } else if (string_eq(name, SLOP_STR("Unit"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("void")};
    } else if (string_eq(name, SLOP_STR("Void"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("void")};
    } else if (string_eq(name, SLOP_STR("Arena"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("slop_arena*")};
    } else if (string_eq(name, SLOP_STR("Milliseconds"))) {
        return (slop_option_string){.has_value = 1, .value = SLOP_STR("int64_t")};
    } else {
        return (slop_option_string){.has_value = false};
    }
}

slop_string ctype_to_c_name(slop_arena* arena, slop_string name) {
    {
        __auto_type result = strlib_replace_all(arena, name, SLOP_STR("-"), SLOP_STR("_"));
        result = strlib_replace_all(arena, result, SLOP_STR("/"), SLOP_STR("_"));
        result = strlib_replace_all(arena, result, SLOP_STR("?"), SLOP_STR("_p"));
        result = strlib_replace_all(arena, result, SLOP_STR("!"), SLOP_STR("_x"));
        result = strlib_replace_all(arena, result, SLOP_STR("$"), SLOP_STR("_"));
        if (ctype_is_c_keyword(result)) {
            return string_concat(arena, SLOP_STR("slop_"), result);
        } else {
            return result;
        }
    }
}

slop_string ctype_type_to_identifier(slop_arena* arena, slop_string c_type) {
    {
        __auto_type result = strlib_replace(arena, c_type, SLOP_STR("*"), SLOP_STR("_ptr"));
        result = strlib_replace(arena, result, SLOP_STR(" "), SLOP_STR("_"));
        if (strlib_starts_with(result, SLOP_STR("slop_"))) {
            {
                __auto_type len_minus_5 = ((int64_t)((string_len(result) - 5)));
                result = strlib_substring(arena, result, 5, len_minus_5);
            }
        }
        if (string_eq(result, SLOP_STR("int64_t"))) {
            result = SLOP_STR("int");
        }
        return result;
    }
}

slop_string ctype_to_c_type(slop_arena* arena, types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_18 = (*expr);
    switch (_mv_18.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_18.data.sym;
            {
                __auto_type name = sym.name;
                __auto_type _mv_19 = ctype_builtin_type_c(arena, name);
                if (_mv_19.has_value) {
                    __auto_type c_type = _mv_19.value;
                    return c_type;
                } else if (!_mv_19.has_value) {
                    return ctype_to_c_name(arena, name);
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_18.data.lst;
            return ctype_to_c_type_compound(arena, lst.items);
        }
        case types_SExpr_str:
        {
            __auto_type _ = _mv_18.data.str;
            return SLOP_STR("void*");
        }
        case types_SExpr_num:
        {
            __auto_type _ = _mv_18.data.num;
            return SLOP_STR("void*");
        }
    }
}

slop_string ctype_to_c_type_compound(slop_arena* arena, slop_list_types_SExpr_ptr items) {
    {
        __auto_type len = ((int64_t)((items).len));
        if ((len < 1)) {
            return SLOP_STR("void*");
        } else {
            __auto_type _mv_20 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_20.has_value) {
                __auto_type first_expr = _mv_20.value;
                __auto_type _mv_21 = (*first_expr);
                switch (_mv_21.tag) {
                    case types_SExpr_sym:
                    {
                        __auto_type head_sym = _mv_21.data.sym;
                        {
                            __auto_type head = head_sym.name;
                            if (string_eq(head, SLOP_STR("Ptr"))) {
                                if ((len < 2)) {
                                    return SLOP_STR("void*");
                                } else {
                                    __auto_type _mv_22 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_22.has_value) {
                                        __auto_type inner = _mv_22.value;
                                        return string_concat(arena, ctype_to_c_type(arena, inner), SLOP_STR("*"));
                                    } else if (!_mv_22.has_value) {
                                        return SLOP_STR("void*");
                                    }
                                }
                            } else if (string_eq(head, SLOP_STR("ScopedPtr"))) {
                                if ((len < 2)) {
                                    return SLOP_STR("void*");
                                } else {
                                    __auto_type _mv_23 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_23.has_value) {
                                        __auto_type inner = _mv_23.value;
                                        return string_concat(arena, ctype_to_c_type(arena, inner), SLOP_STR("*"));
                                    } else if (!_mv_23.has_value) {
                                        return SLOP_STR("void*");
                                    }
                                }
                            } else if (string_eq(head, SLOP_STR("Option"))) {
                                if ((len < 2)) {
                                    return SLOP_STR("slop_option_void");
                                } else {
                                    __auto_type _mv_24 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_24.has_value) {
                                        __auto_type inner = _mv_24.value;
                                        {
                                            __auto_type inner_c = ctype_to_c_type(arena, inner);
                                            __auto_type inner_id = ctype_type_to_identifier(arena, inner_c);
                                            return string_concat(arena, SLOP_STR("slop_option_"), inner_id);
                                        }
                                    } else if (!_mv_24.has_value) {
                                        return SLOP_STR("slop_option_void");
                                    }
                                }
                            } else if (string_eq(head, SLOP_STR("Result"))) {
                                {
                                    __auto_type ok_id = (((len < 2)) ? SLOP_STR("void") : ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type ok_expr = _mv.value; ctype_type_to_identifier(arena, ctype_to_c_type(arena, ok_expr)); }) : (SLOP_STR("void")); }));
                                    __auto_type err_id = (((len < 3)) ? SLOP_STR("slop_error") : ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type err_expr = _mv.value; ctype_type_to_identifier(arena, ctype_to_c_type(arena, err_expr)); }) : (SLOP_STR("slop_error")); }));
                                    return string_concat(arena, string_concat(arena, SLOP_STR("slop_result_"), ok_id), string_concat(arena, SLOP_STR("_"), err_id));
                                }
                            } else if (string_eq(head, SLOP_STR("List"))) {
                                if ((len < 2)) {
                                    return SLOP_STR("slop_list_void");
                                } else {
                                    __auto_type _mv_25 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_25.has_value) {
                                        __auto_type inner = _mv_25.value;
                                        {
                                            __auto_type inner_c = ctype_to_c_type(arena, inner);
                                            __auto_type inner_id = ctype_type_to_identifier(arena, inner_c);
                                            return string_concat(arena, SLOP_STR("slop_list_"), inner_id);
                                        }
                                    } else if (!_mv_25.has_value) {
                                        return SLOP_STR("slop_list_void");
                                    }
                                }
                            } else if (string_eq(head, SLOP_STR("Map"))) {
                                return SLOP_STR("slop_map*");
                            } else if (string_eq(head, SLOP_STR("Array"))) {
                                if ((len < 2)) {
                                    return SLOP_STR("void*");
                                } else {
                                    __auto_type _mv_26 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_26.has_value) {
                                        __auto_type inner = _mv_26.value;
                                        return string_concat(arena, ctype_to_c_type(arena, inner), SLOP_STR("*"));
                                    } else if (!_mv_26.has_value) {
                                        return SLOP_STR("void*");
                                    }
                                }
                            } else if (string_eq(head, SLOP_STR("Chan"))) {
                                if ((len < 2)) {
                                    return SLOP_STR("slop_chan_void");
                                } else {
                                    __auto_type _mv_27 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_27.has_value) {
                                        __auto_type inner = _mv_27.value;
                                        {
                                            __auto_type inner_c = ctype_to_c_type(arena, inner);
                                            __auto_type inner_id = ctype_type_to_identifier(arena, inner_c);
                                            return string_concat(arena, SLOP_STR("slop_chan_"), inner_id);
                                        }
                                    } else if (!_mv_27.has_value) {
                                        return SLOP_STR("slop_chan_void");
                                    }
                                }
                            } else if (string_eq(head, SLOP_STR("Thread"))) {
                                if ((len < 2)) {
                                    return SLOP_STR("slop_thread_void");
                                } else {
                                    __auto_type _mv_28 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_28.has_value) {
                                        __auto_type inner = _mv_28.value;
                                        {
                                            __auto_type inner_c = ctype_to_c_type(arena, inner);
                                            __auto_type inner_id = ctype_type_to_identifier(arena, inner_c);
                                            return string_concat(arena, SLOP_STR("slop_thread_"), inner_id);
                                        }
                                    } else if (!_mv_28.has_value) {
                                        return SLOP_STR("slop_thread_void");
                                    }
                                }
                            } else if (string_eq(head, SLOP_STR("Fn"))) {
                                if ((len < 2)) {
                                    return SLOP_STR("void*");
                                } else {
                                    {
                                        __auto_type ret_type = ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)(len - 1); slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type ret = _mv.value; ctype_to_c_type(arena, ret); }) : (SLOP_STR("void")); });
                                        if ((len == 2)) {
                                            return string_concat(arena, ret_type, SLOP_STR("(*)(void)"));
                                        } else {
                                            __auto_type _mv_29 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                            if (_mv_29.has_value) {
                                                __auto_type args_expr = _mv_29.value;
                                                {
                                                    __auto_type args_str = ctype_build_fn_args_str(arena, args_expr);
                                                    return string_concat(arena, string_concat(arena, ret_type, SLOP_STR("(*)")), args_str);
                                                }
                                            } else if (!_mv_29.has_value) {
                                                return string_concat(arena, ret_type, SLOP_STR("(*)(void)"));
                                            }
                                        }
                                    }
                                }
                            } else {
                                __auto_type _mv_30 = ctype_builtin_type_c(arena, head);
                                if (_mv_30.has_value) {
                                    __auto_type c_type = _mv_30.value;
                                    return c_type;
                                } else if (!_mv_30.has_value) {
                                    return ctype_to_c_name(arena, head);
                                }
                            }
                        }
                    }
                    default: {
                        return SLOP_STR("void*");
                    }
                }
            } else if (!_mv_20.has_value) {
                return SLOP_STR("void*");
            }
        }
    }
}

slop_string ctype_build_fn_args_str(slop_arena* arena, types_SExpr* args_expr) {
    __auto_type _mv_31 = (*args_expr);
    switch (_mv_31.tag) {
        case types_SExpr_lst:
        {
            __auto_type args_list = _mv_31.data.lst;
            {
                __auto_type arg_items = args_list.items;
                __auto_type arg_count = ((int64_t)((arg_items).len));
                if ((arg_count == 0)) {
                    return SLOP_STR("(void)");
                } else {
                    {
                        __auto_type result = SLOP_STR("(");
                        __auto_type i = 0;
                        while ((i < arg_count)) {
                            __auto_type _mv_32 = ({ __auto_type _lst = arg_items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_32.has_value) {
                                __auto_type arg_expr = _mv_32.value;
                                {
                                    __auto_type arg_type = ctype_to_c_type(arena, arg_expr);
                                    if ((i > 0)) {
                                        result = string_concat(arena, result, string_concat(arena, SLOP_STR(", "), arg_type));
                                    } else {
                                        result = string_concat(arena, result, arg_type);
                                    }
                                }
                            } else if (!_mv_32.has_value) {
                                /* empty list */;
                            }
                            i = (i + 1);
                        }
                        return string_concat(arena, result, SLOP_STR(")"));
                    }
                }
            }
        }
        default: {
            return SLOP_STR("(void)");
        }
    }
}

slop_string ctype_sexpr_to_type_string(slop_arena* arena, types_SExpr* expr) {
    SLOP_PRE(((expr != NULL)), "(!= expr nil)");
    __auto_type _mv_33 = (*expr);
    switch (_mv_33.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_33.data.sym;
            return sym.name;
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_33.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                __auto_type result = SLOP_STR("(");
                __auto_type i = 0;
                while ((i < len)) {
                    __auto_type _mv_34 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_34.has_value) {
                        __auto_type item_expr = _mv_34.value;
                        {
                            __auto_type item_str = ctype_sexpr_to_type_string(arena, item_expr);
                            if ((i > 0)) {
                                result = string_concat(arena, result, string_concat(arena, SLOP_STR(" "), item_str));
                            } else {
                                result = string_concat(arena, result, item_str);
                            }
                        }
                    } else if (!_mv_34.has_value) {
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

