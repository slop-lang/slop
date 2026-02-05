#include "../runtime/slop_runtime.h"
#include "slop_collect.h"

void collect_collect_module(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void collect_collect_types(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void collect_register_type_name(env_TypeEnv* env, slop_arena* arena, types_SExpr* expr);
void collect_resolve_type_body(env_TypeEnv* env, slop_arena* arena, types_SExpr* expr);
void collect_collect_record_fields(env_TypeEnv* env, slop_arena* arena, types_ResolvedType* resolved, types_SExpr* record_expr);
types_SExpr* collect_get_type_arg(types_SExpr* type_expr, int64_t idx);
types_ResolvedType* collect_get_field_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr);
uint8_t collect_is_type_param(slop_string name, slop_list_string type_params);
types_ResolvedType* collect_get_field_type_generic(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr, slop_list_string type_params);
slop_list_string collect_find_fn_type_params(slop_arena* arena, types_SExpr* fn_form);
types_ResolvedType* collect_find_fn_return_type_generic(env_TypeEnv* env, types_SExpr* fn_form, slop_list_string type_params);
types_ResolvedType* collect_extract_spec_return_type_generic(env_TypeEnv* env, types_SExpr* spec_form, slop_list_string type_params);
slop_list_types_ResolvedType_ptr collect_collect_fn_spec_params(env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form, slop_list_string type_params);
void collect_set_module_name_from_form(env_TypeEnv* env, types_SExpr* module_form);
void collect_register_module_type_names(env_TypeEnv* env, types_SExpr* module_form);
void collect_resolve_module_type_bodies(env_TypeEnv* env, types_SExpr* module_form);
slop_option_types_ResolvedType_ptr collect_lookup_payload_type(env_TypeEnv* env, slop_string type_name);
uint8_t collect_is_range_type_expr(types_SExpr* type_expr);
types_ResolvedType* collect_get_range_base_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr);
slop_string collect_get_type_name_from_expr(types_SExpr* expr);
uint8_t collect_is_reserved_variant_name(slop_string name);
void collect_collect_union_variants(env_TypeEnv* env, slop_arena* arena, types_ResolvedType* resolved, types_SExpr* union_expr);
slop_option_types_ResolvedType_ptr collect_get_variant_payload_type(env_TypeEnv* env, types_SExpr* variant_form);
slop_string collect_checker_get_variant_name(types_SExpr* variant_form);
void collect_collect_single_union_variant(env_TypeEnv* env, slop_arena* arena, types_ResolvedType* resolved, types_SExpr* variant_form, int64_t variant_idx);
void collect_collect_enum_variants(env_TypeEnv* env, slop_string enum_name, types_SExpr* enum_expr);
void collect_collect_constants(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void collect_collect_module_constants(env_TypeEnv* env, types_SExpr* module_form);
void collect_collect_single_constant(env_TypeEnv* env, slop_arena* arena, types_SExpr* const_form);
types_ResolvedType* collect_get_const_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr);
void collect_collect_functions(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void collect_collect_module_functions(env_TypeEnv* env, types_SExpr* module_form);
void collect_collect_ffi_functions(env_TypeEnv* env, slop_arena* arena, types_SExpr* ffi_form);
void collect_collect_ffi_function(env_TypeEnv* env, slop_arena* arena, types_SExpr* func_decl);
slop_list_types_ParamInfo collect_collect_ffi_params(env_TypeEnv* env, slop_arena* arena, types_SExpr* func_decl);
types_ResolvedType* collect_get_ffi_return_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* func_decl);
void collect_collect_single_function(env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form);
uint8_t collect_is_integer_type_name(slop_string name);
void collect_validate_main_params(env_TypeEnv* env, types_SExpr* fn_form, slop_list_types_ParamInfo params);
slop_list_types_ParamInfo collect_collect_fn_params(env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form);
slop_list_types_ParamInfo collect_collect_fn_params_generic(env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form, slop_list_string type_params);
types_ResolvedType* collect_find_fn_return_type(env_TypeEnv* env, types_SExpr* fn_form);
types_ResolvedType* collect_checker_extract_spec_return_type(env_TypeEnv* env, types_SExpr* spec_form);

void collect_collect_module(env_TypeEnv* env, slop_list_types_SExpr_ptr ast) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    collect_collect_types(env, ast);
    env_env_check_variant_collisions(env);
    collect_collect_constants(env, ast);
    collect_collect_functions(env, ast);
}

void collect_collect_types(env_TypeEnv* env, slop_list_types_SExpr_ptr ast) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type arena = env_env_arena(env);
        __auto_type len = ((int64_t)((ast).len));
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_1040 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1040.has_value) {
                __auto_type expr = _mv_1040.value;
                if (parser_is_form(expr, SLOP_STR("type"))) {
                    collect_register_type_name(env, arena, expr);
                } else if (parser_is_form(expr, SLOP_STR("module"))) {
                    collect_register_module_type_names(env, expr);
                } else {
                }
            } else if (!_mv_1040.has_value) {
            }
        }
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_1041 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1041.has_value) {
                __auto_type expr = _mv_1041.value;
                if (parser_is_form(expr, SLOP_STR("type"))) {
                    collect_resolve_type_body(env, arena, expr);
                } else if (parser_is_form(expr, SLOP_STR("module"))) {
                    collect_resolve_module_type_bodies(env, expr);
                } else {
                }
            } else if (!_mv_1041.has_value) {
            }
        }
    }
}

void collect_register_type_name(env_TypeEnv* env, slop_arena* arena, types_SExpr* expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type mod_name = env_env_get_module(env);
        __auto_type _mv_1042 = (*expr);
        switch (_mv_1042.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1042.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type _mv_1043 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1043.has_value) {
                        __auto_type name_expr = _mv_1043.value;
                        __auto_type _mv_1044 = (*name_expr);
                        switch (_mv_1044.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1044.data.sym;
                                {
                                    __auto_type type_name = sym.name;
                                    __auto_type _mv_1045 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_1045.has_value) {
                                        __auto_type type_expr = _mv_1045.value;
                                        if (parser_is_form(type_expr, SLOP_STR("enum"))) {
                                            {
                                                __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_enum, type_name, mod_name, type_name);
                                                env_env_register_type(env, resolved);
                                            }
                                        } else if (parser_is_form(type_expr, SLOP_STR("record"))) {
                                            {
                                                __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_record, type_name, mod_name, type_name);
                                                env_env_register_type(env, resolved);
                                            }
                                        } else if (parser_is_form(type_expr, SLOP_STR("union"))) {
                                            {
                                                __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_union, type_name, mod_name, type_name);
                                                env_env_register_type(env, resolved);
                                            }
                                        } else if (collect_is_range_type_expr(type_expr)) {
                                            {
                                                __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_range, type_name, mod_name, type_name);
                                                env_env_register_type(env, resolved);
                                            }
                                        } else if (parser_is_form(type_expr, SLOP_STR("Map"))) {
                                            {
                                                __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_map, type_name, mod_name, SLOP_STR("slop_map*"));
                                                env_env_register_type(env, resolved);
                                            }
                                        } else if (parser_is_form(type_expr, SLOP_STR("Set"))) {
                                            {
                                                __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, type_name, mod_name, SLOP_STR("slop_map*"));
                                                env_env_register_type(env, resolved);
                                            }
                                        } else if (parser_is_form(type_expr, SLOP_STR("List"))) {
                                            {
                                                __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_list, type_name, mod_name, SLOP_STR("slop_list_t*"));
                                                env_env_register_type(env, resolved);
                                            }
                                        } else {
                                            {
                                                __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, type_name, mod_name, type_name);
                                                env_env_register_type(env, resolved);
                                            }
                                        }
                                    } else if (!_mv_1045.has_value) {
                                        {
                                            __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, type_name, mod_name, type_name);
                                            env_env_register_type(env, resolved);
                                        }
                                    }
                                }
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_1043.has_value) {
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

void collect_resolve_type_body(env_TypeEnv* env, slop_arena* arena, types_SExpr* expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1046 = (*expr);
    switch (_mv_1046.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1046.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type _mv_1047 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1047.has_value) {
                    __auto_type name_expr = _mv_1047.value;
                    __auto_type _mv_1048 = (*name_expr);
                    switch (_mv_1048.tag) {
                        case types_SExpr_sym:
                        {
                            __auto_type sym = _mv_1048.data.sym;
                            {
                                __auto_type type_name = sym.name;
                                __auto_type _mv_1049 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1049.has_value) {
                                    __auto_type type_expr = _mv_1049.value;
                                    if (parser_is_form(type_expr, SLOP_STR("enum"))) {
                                        collect_collect_enum_variants(env, type_name, type_expr);
                                    } else if (parser_is_form(type_expr, SLOP_STR("record"))) {
                                        __auto_type _mv_1050 = env_env_lookup_type_direct(env, type_name);
                                        if (_mv_1050.has_value) {
                                            __auto_type resolved = _mv_1050.value;
                                            collect_collect_record_fields(env, arena, resolved, type_expr);
                                        } else if (!_mv_1050.has_value) {
                                        }
                                    } else if (parser_is_form(type_expr, SLOP_STR("union"))) {
                                        __auto_type _mv_1051 = env_env_lookup_type_direct(env, type_name);
                                        if (_mv_1051.has_value) {
                                            __auto_type resolved = _mv_1051.value;
                                            collect_collect_union_variants(env, arena, resolved, type_expr);
                                        } else if (!_mv_1051.has_value) {
                                        }
                                    } else if (collect_is_range_type_expr(type_expr)) {
                                        __auto_type _mv_1052 = env_env_lookup_type_direct(env, type_name);
                                        if (_mv_1052.has_value) {
                                            __auto_type resolved = _mv_1052.value;
                                            {
                                                __auto_type base_type = collect_get_range_base_type(env, arena, type_expr);
                                                types_resolved_type_set_inner(resolved, base_type);
                                            }
                                        } else if (!_mv_1052.has_value) {
                                        }
                                    } else if (parser_is_form(type_expr, SLOP_STR("Map"))) {
                                        __auto_type _mv_1053 = env_env_lookup_type_direct(env, type_name);
                                        if (_mv_1053.has_value) {
                                            __auto_type resolved = _mv_1053.value;
                                            {
                                                __auto_type key_type = collect_get_field_type(env, arena, collect_get_type_arg(type_expr, 1));
                                                __auto_type val_type = collect_get_field_type(env, arena, collect_get_type_arg(type_expr, 2));
                                                types_resolved_type_set_inner(resolved, key_type);
                                                types_resolved_type_set_inner2(resolved, val_type);
                                            }
                                        } else if (!_mv_1053.has_value) {
                                        }
                                    } else if (parser_is_form(type_expr, SLOP_STR("Set"))) {
                                        __auto_type _mv_1054 = env_env_lookup_type_direct(env, type_name);
                                        if (_mv_1054.has_value) {
                                            __auto_type resolved = _mv_1054.value;
                                            {
                                                __auto_type elem_type = collect_get_field_type(env, arena, collect_get_type_arg(type_expr, 1));
                                                types_resolved_type_set_inner(resolved, elem_type);
                                            }
                                        } else if (!_mv_1054.has_value) {
                                        }
                                    } else if (parser_is_form(type_expr, SLOP_STR("List"))) {
                                        __auto_type _mv_1055 = env_env_lookup_type_direct(env, type_name);
                                        if (_mv_1055.has_value) {
                                            __auto_type resolved = _mv_1055.value;
                                            {
                                                __auto_type elem_type = collect_get_field_type(env, arena, collect_get_type_arg(type_expr, 1));
                                                types_resolved_type_set_inner(resolved, elem_type);
                                            }
                                        } else if (!_mv_1055.has_value) {
                                        }
                                    } else {
                                        {
                                            __auto_type alias_name = parser_sexpr_get_symbol_name(type_expr);
                                            if (!(string_eq(alias_name, SLOP_STR("")))) {
                                                __auto_type _mv_1056 = env_env_lookup_type_direct(env, type_name);
                                                if (_mv_1056.has_value) {
                                                    __auto_type resolved = _mv_1056.value;
                                                    {
                                                        __auto_type base_type = collect_get_field_type(env, arena, type_expr);
                                                        types_resolved_type_set_inner(resolved, base_type);
                                                    }
                                                } else if (!_mv_1056.has_value) {
                                                }
                                            }
                                        }
                                    }
                                } else if (!_mv_1049.has_value) {
                                }
                            }
                            break;
                        }
                        default: {
                            break;
                        }
                    }
                } else if (!_mv_1047.has_value) {
                }
            }
            break;
        }
        default: {
            break;
        }
    }
}

void collect_collect_record_fields(env_TypeEnv* env, slop_arena* arena, types_ResolvedType* resolved, types_SExpr* record_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((resolved != NULL)), "(!= resolved nil)");
    SLOP_PRE(((record_expr != NULL)), "(!= record-expr nil)");
    __auto_type _mv_1057 = (*record_expr);
    switch (_mv_1057.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1057.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                ({ for (int64_t i = 1; i < len; i++) { ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type field_form = _mv.value; ({ __auto_type _mv = (*field_form); switch (_mv.tag) { case types_SExpr_lst: { __auto_type field_lst = _mv.data.lst; ({ __auto_type field_items = field_lst.items; ({ __auto_type _mv = ({ __auto_type _lst = field_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type name_expr = _mv.value; ({ __auto_type _mv = (*name_expr); switch (_mv.tag) { case types_SExpr_sym: { __auto_type name_sym = _mv.data.sym; ({ __auto_type _mv = ({ __auto_type _lst = field_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type type_expr = _mv.value; ({ __auto_type field_name = name_sym.name; __auto_type field_type = collect_get_field_type(env, arena, type_expr); __auto_type field = types_resolved_field_new(arena, field_name, field_type, (i - 1)); ({ ({ __auto_type _lst_p = &((*resolved).fields); __auto_type _item = ((*field)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); }); }); } else { ({ (void)0; }); } (void)0; }); break; } default: { ({ (void)0; }); break; }  } (void)0; }); } else { ({ (void)0; }); } (void)0; }); }); break; } default: { ({ (void)0; }); break; }  } (void)0; }); } else { ({ (void)0; }); } (void)0; }); } 0; });
            }
            break;
        }
        default: {
            break;
        }
    }
}

types_SExpr* collect_get_type_arg(types_SExpr* type_expr, int64_t idx) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_1058 = (*type_expr);
    switch (_mv_1058.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1058.data.lst;
            __auto_type _mv_1059 = ({ __auto_type _lst = lst.items; size_t _idx = (size_t)idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1059.has_value) {
                __auto_type arg = _mv_1059.value;
                return arg;
            } else if (!_mv_1059.has_value) {
                return type_expr;
            }
        }
        default: {
            return type_expr;
        }
    }
}

types_ResolvedType* collect_get_field_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1060 = (*type_expr);
    switch (_mv_1060.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1060.data.sym;
            {
                __auto_type type_name = sym.name;
                __auto_type _mv_1061 = env_env_lookup_type_direct(env, type_name);
                if (_mv_1061.has_value) {
                    __auto_type t = _mv_1061.value;
                    return t;
                } else if (!_mv_1061.has_value) {
                    if (string_eq(type_name, SLOP_STR("Int"))) {
                        return env_env_get_int_type(env);
                    } else if (string_eq(type_name, SLOP_STR("Bool"))) {
                        return env_env_get_bool_type(env);
                    } else if (string_eq(type_name, SLOP_STR("String"))) {
                        return env_env_get_string_type(env);
                    } else if (string_eq(type_name, SLOP_STR("Unit"))) {
                        return env_env_get_unit_type(env);
                    } else {
                        return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, type_name, ((slop_option_string){.has_value = false}), type_name);
                    }
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1060.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type _mv_1062 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1062.has_value) {
                    __auto_type head_expr = _mv_1062.value;
                    {
                        __auto_type head_name = parser_sexpr_get_symbol_name(head_expr);
                        if (string_eq(head_name, SLOP_STR("Option"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                return env_env_make_option_type(env, inner_type);
                            }
                        } else if (string_eq(head_name, SLOP_STR("Ptr"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type inner_name = (*inner_type).name;
                                    __auto_type ptr_name = string_concat(arena, SLOP_STR("Ptr_"), inner_name);
                                    __auto_type ptr_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_ptr, ptr_name, ((slop_option_string){.has_value = false}), SLOP_STR("void*"));
                                    types_resolved_type_set_inner(ptr_type, inner_type);
                                    return ptr_type;
                                }
                            }
                        } else if (string_eq(head_name, SLOP_STR("List"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type list_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_list, SLOP_STR("List"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_list_t*"));
                                    types_resolved_type_set_inner(list_type, inner_type);
                                    return list_type;
                                }
                            }
                        } else if (string_eq(head_name, SLOP_STR("Set"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type set_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Set"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_map*"));
                                    types_resolved_type_set_inner(set_type, inner_type);
                                    return set_type;
                                }
                            }
                        } else if (string_eq(head_name, SLOP_STR("Map"))) {
                            {
                                __auto_type key_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                __auto_type val_type = (((((int64_t)((items).len)) >= 3)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type map_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_map, SLOP_STR("Map"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_map*"));
                                    types_resolved_type_set_inner(map_type, key_type);
                                    types_resolved_type_set_inner2(map_type, val_type);
                                    return map_type;
                                }
                            }
                        } else if (string_eq(head_name, SLOP_STR("Result"))) {
                            {
                                __auto_type ok_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_unit_type(env)); }) : env_env_get_unit_type(env));
                                __auto_type err_type = (((((int64_t)((items).len)) >= 3)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_unit_type(env)); }) : env_env_get_unit_type(env));
                                __auto_type ok_name = (*ok_type).name;
                                __auto_type err_name = (*err_type).name;
                                __auto_type result_name = string_concat(arena, SLOP_STR("Result_"), string_concat(arena, ok_name, string_concat(arena, SLOP_STR("_"), err_name)));
                                __auto_type result_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_result, result_name, ((slop_option_string){.has_value = false}), SLOP_STR("Result"));
                                types_resolved_type_set_inner(result_type, ok_type);
                                types_resolved_type_set_inner2(result_type, err_type);
                                return result_type;
                            }
                        } else {
                            return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, head_name, ((slop_option_string){.has_value = false}), head_name);
                        }
                    }
                } else if (!_mv_1062.has_value) {
                    return env_env_get_unit_type(env);
                }
            }
        }
        default: {
            return env_env_get_unit_type(env);
        }
    }
}

uint8_t collect_is_type_param(slop_string name, slop_list_string type_params) {
    {
        __auto_type len = ((int64_t)((type_params).len));
        uint8_t found = 0;
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_1063 = ({ __auto_type _lst = type_params; size_t _idx = (size_t)i; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1063.has_value) {
                __auto_type tp = _mv_1063.value;
                if (string_eq(name, tp)) {
                    found = 1;
                }
            } else if (!_mv_1063.has_value) {
            }
        }
        return found;
    }
}

types_ResolvedType* collect_get_field_type_generic(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr, slop_list_string type_params) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1064 = (*type_expr);
    switch (_mv_1064.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1064.data.sym;
            {
                __auto_type type_name = sym.name;
                if (collect_is_type_param(type_name, type_params)) {
                    return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_typevar, type_name, ((slop_option_string){.has_value = false}), type_name);
                } else {
                    __auto_type _mv_1065 = env_env_lookup_type_direct(env, type_name);
                    if (_mv_1065.has_value) {
                        __auto_type t = _mv_1065.value;
                        return t;
                    } else if (!_mv_1065.has_value) {
                        if (string_eq(type_name, SLOP_STR("Int"))) {
                            return env_env_get_int_type(env);
                        } else if (string_eq(type_name, SLOP_STR("Bool"))) {
                            return env_env_get_bool_type(env);
                        } else if (string_eq(type_name, SLOP_STR("String"))) {
                            return env_env_get_string_type(env);
                        } else if (string_eq(type_name, SLOP_STR("Unit"))) {
                            return env_env_get_unit_type(env);
                        } else {
                            return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, type_name, ((slop_option_string){.has_value = false}), type_name);
                        }
                    }
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1064.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type _mv_1066 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1066.has_value) {
                    __auto_type head_expr = _mv_1066.value;
                    {
                        __auto_type head_name = parser_sexpr_get_symbol_name(head_expr);
                        if (string_eq(head_name, SLOP_STR("Option"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type_generic(env, arena, inner_expr, type_params); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                return env_env_make_option_type(env, inner_type);
                            }
                        } else if (string_eq(head_name, SLOP_STR("Ptr"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type_generic(env, arena, inner_expr, type_params); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type inner_name = (*inner_type).name;
                                    __auto_type ptr_name = string_concat(arena, SLOP_STR("Ptr_"), inner_name);
                                    __auto_type ptr_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_ptr, ptr_name, ((slop_option_string){.has_value = false}), SLOP_STR("void*"));
                                    types_resolved_type_set_inner(ptr_type, inner_type);
                                    return ptr_type;
                                }
                            }
                        } else if (string_eq(head_name, SLOP_STR("List"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type_generic(env, arena, inner_expr, type_params); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type list_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_list, SLOP_STR("List"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_list_t*"));
                                    types_resolved_type_set_inner(list_type, inner_type);
                                    return list_type;
                                }
                            }
                        } else if (string_eq(head_name, SLOP_STR("Chan"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type_generic(env, arena, inner_expr, type_params); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type chan_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_chan, SLOP_STR("Chan"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_chan_int*"));
                                    types_resolved_type_set_inner(chan_type, inner_type);
                                    return chan_type;
                                }
                            }
                        } else if (string_eq(head_name, SLOP_STR("Thread"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type_generic(env, arena, inner_expr, type_params); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type thread_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_thread, SLOP_STR("Thread"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_thread_int*"));
                                    types_resolved_type_set_inner(thread_type, inner_type);
                                    return thread_type;
                                }
                            }
                        } else if (string_eq(head_name, SLOP_STR("Result"))) {
                            {
                                __auto_type ok_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type_generic(env, arena, inner_expr, type_params); }) : (env_env_get_unit_type(env)); }) : env_env_get_unit_type(env));
                                __auto_type err_type = (((((int64_t)((items).len)) >= 3)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type_generic(env, arena, inner_expr, type_params); }) : (env_env_get_unit_type(env)); }) : env_env_get_unit_type(env));
                                __auto_type ok_name = (*ok_type).name;
                                __auto_type err_name = (*err_type).name;
                                __auto_type result_name = string_concat(arena, SLOP_STR("Result_"), string_concat(arena, ok_name, string_concat(arena, SLOP_STR("_"), err_name)));
                                __auto_type result_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_result, result_name, ((slop_option_string){.has_value = false}), SLOP_STR("Result"));
                                types_resolved_type_set_inner(result_type, ok_type);
                                types_resolved_type_set_inner2(result_type, err_type);
                                return result_type;
                            }
                        } else if (string_eq(head_name, SLOP_STR("Fn"))) {
                            return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_function, SLOP_STR("Fn"), ((slop_option_string){.has_value = false}), SLOP_STR("void*"));
                        } else {
                            return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, head_name, ((slop_option_string){.has_value = false}), head_name);
                        }
                    }
                } else if (!_mv_1066.has_value) {
                    return env_env_get_unit_type(env);
                }
            }
        }
        default: {
            return env_env_get_unit_type(env);
        }
    }
}

slop_list_string collect_find_fn_type_params(slop_arena* arena, types_SExpr* fn_form) {
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    {
        __auto_type type_params = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
        __auto_type len = parser_sexpr_list_len(fn_form);
        for (int64_t i = 3; i < len; i++) {
            __auto_type _mv_1067 = parser_sexpr_list_get(fn_form, i);
            if (_mv_1067.has_value) {
                __auto_type item = _mv_1067.value;
                if (parser_is_form(item, SLOP_STR("@generic"))) {
                    __auto_type _mv_1068 = parser_sexpr_list_get(item, 1);
                    if (_mv_1068.has_value) {
                        __auto_type params_expr = _mv_1068.value;
                        if (parser_sexpr_is_list(params_expr)) {
                            {
                                __auto_type num_params = parser_sexpr_list_len(params_expr);
                                ({ for (int64_t j = 0; j < num_params; j++) { ({ __auto_type _mv = parser_sexpr_list_get(params_expr, j); if (_mv.has_value) { __auto_type param_expr = _mv.value; ({ __auto_type param_name = parser_sexpr_get_symbol_name(param_expr); ((!(string_eq(param_name, SLOP_STR("")))) ? ({ ({ __auto_type _lst_p = &(type_params); __auto_type _item = (param_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); 0; }) : ({ (void)0; })); }); } else { ({ (void)0; }); } (void)0; }); } 0; });
                            }
                        }
                    } else if (!_mv_1068.has_value) {
                    }
                }
            } else if (!_mv_1067.has_value) {
            }
        }
        return type_params;
    }
}

types_ResolvedType* collect_find_fn_return_type_generic(env_TypeEnv* env, types_SExpr* fn_form, slop_list_string type_params) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    {
        __auto_type len = parser_sexpr_list_len(fn_form);
        uint8_t found = 0;
        types_ResolvedType* found_type = env_env_get_unit_type(env);
        for (int64_t i = 3; i < len; i++) {
            __auto_type _mv_1069 = parser_sexpr_list_get(fn_form, i);
            if (_mv_1069.has_value) {
                __auto_type item = _mv_1069.value;
                if (parser_is_form(item, SLOP_STR("@spec"))) {
                    if (!(found)) {
                        found_type = collect_extract_spec_return_type_generic(env, item, type_params);
                        found = 1;
                    }
                }
            } else if (!_mv_1069.has_value) {
            }
        }
        return found_type;
    }
}

types_ResolvedType* collect_extract_spec_return_type_generic(env_TypeEnv* env, types_SExpr* spec_form, slop_list_string type_params) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type arena = env_env_arena(env);
        __auto_type _mv_1070 = parser_sexpr_list_get(spec_form, 1);
        if (_mv_1070.has_value) {
            __auto_type spec_body = _mv_1070.value;
            if (parser_sexpr_is_list(spec_body)) {
                {
                    __auto_type len = parser_sexpr_list_len(spec_body);
                    __auto_type _mv_1071 = parser_sexpr_list_get(spec_body, (len - 1));
                    if (_mv_1071.has_value) {
                        __auto_type ret_expr = _mv_1071.value;
                        return collect_get_field_type_generic(env, arena, ret_expr, type_params);
                    } else if (!_mv_1071.has_value) {
                        return env_env_get_unit_type(env);
                    }
                }
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (!_mv_1070.has_value) {
            return env_env_get_unit_type(env);
        }
    }
}

slop_list_types_ResolvedType_ptr collect_collect_fn_spec_params(env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form, slop_list_string type_params) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    {
        __auto_type spec_params = ((slop_list_types_ResolvedType_ptr){ .data = (types_ResolvedType**)slop_arena_alloc(arena, 16 * sizeof(types_ResolvedType*)), .len = 0, .cap = 16 });
        __auto_type len = parser_sexpr_list_len(fn_form);
        for (int64_t i = 3; i < len; i++) {
            __auto_type _mv_1072 = parser_sexpr_list_get(fn_form, i);
            if (_mv_1072.has_value) {
                __auto_type item = _mv_1072.value;
                if (parser_is_form(item, SLOP_STR("@spec"))) {
                    __auto_type _mv_1073 = parser_sexpr_list_get(item, 1);
                    if (_mv_1073.has_value) {
                        __auto_type spec_body = _mv_1073.value;
                        if (parser_sexpr_is_list(spec_body)) {
                            __auto_type _mv_1074 = parser_sexpr_list_get(spec_body, 0);
                            if (_mv_1074.has_value) {
                                __auto_type param_types_expr = _mv_1074.value;
                                if (parser_sexpr_is_list(param_types_expr)) {
                                    {
                                        __auto_type num_ptypes = parser_sexpr_list_len(param_types_expr);
                                        ({ for (int64_t j = 0; j < num_ptypes; j++) { ({ __auto_type _mv = parser_sexpr_list_get(param_types_expr, j); if (_mv.has_value) { __auto_type ptype_expr = _mv.value; ({ __auto_type pt = collect_get_field_type_generic(env, arena, ptype_expr, type_params); ({ __auto_type _lst_p = &(spec_params); __auto_type _item = (pt); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); }); } else { ({ (void)0; }); } (void)0; }); } 0; });
                                    }
                                }
                            } else if (!_mv_1074.has_value) {
                            }
                        }
                    } else if (!_mv_1073.has_value) {
                    }
                }
            } else if (!_mv_1072.has_value) {
            }
        }
        return spec_params;
    }
}

void collect_set_module_name_from_form(env_TypeEnv* env, types_SExpr* module_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1075 = parser_sexpr_list_get(module_form, 1);
    if (_mv_1075.has_value) {
        __auto_type name_expr = _mv_1075.value;
        {
            __auto_type mod_name = parser_sexpr_get_symbol_name(name_expr);
            if (!(string_eq(mod_name, SLOP_STR("")))) {
                env_env_set_module(env, (slop_option_string){.has_value = 1, .value = mod_name});
            }
        }
    } else if (!_mv_1075.has_value) {
    }
}

void collect_register_module_type_names(env_TypeEnv* env, types_SExpr* module_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((module_form != NULL)), "(!= module-form nil)");
    {
        __auto_type arena = env_env_arena(env);
        if (parser_sexpr_is_list(module_form)) {
            collect_set_module_name_from_form(env, module_form);
            {
                __auto_type len = parser_sexpr_list_len(module_form);
                for (int64_t i = 2; i < len; i++) {
                    __auto_type _mv_1076 = parser_sexpr_list_get(module_form, i);
                    if (_mv_1076.has_value) {
                        __auto_type item = _mv_1076.value;
                        if (parser_is_form(item, SLOP_STR("type"))) {
                            collect_register_type_name(env, arena, item);
                        }
                    } else if (!_mv_1076.has_value) {
                    }
                }
            }
        }
    }
}

void collect_resolve_module_type_bodies(env_TypeEnv* env, types_SExpr* module_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((module_form != NULL)), "(!= module-form nil)");
    {
        __auto_type arena = env_env_arena(env);
        if (parser_sexpr_is_list(module_form)) {
            collect_set_module_name_from_form(env, module_form);
            {
                __auto_type len = parser_sexpr_list_len(module_form);
                for (int64_t i = 2; i < len; i++) {
                    __auto_type _mv_1077 = parser_sexpr_list_get(module_form, i);
                    if (_mv_1077.has_value) {
                        __auto_type item = _mv_1077.value;
                        if (parser_is_form(item, SLOP_STR("type"))) {
                            collect_resolve_type_body(env, arena, item);
                        }
                    } else if (!_mv_1077.has_value) {
                    }
                }
            }
        }
    }
}

slop_option_types_ResolvedType_ptr collect_lookup_payload_type(env_TypeEnv* env, slop_string type_name) {
    if (string_eq(type_name, SLOP_STR(""))) {
        return (slop_option_types_ResolvedType_ptr){.has_value = false};
    } else {
        __auto_type _mv_1078 = env_env_lookup_type_direct(env, type_name);
        if (_mv_1078.has_value) {
            __auto_type t = _mv_1078.value;
            return (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = t};
        } else if (!_mv_1078.has_value) {
            if (string_eq(type_name, SLOP_STR("Int"))) {
                return (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = env_env_get_int_type(env)};
            } else if (string_eq(type_name, SLOP_STR("Bool"))) {
                return (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = env_env_get_bool_type(env)};
            } else if (string_eq(type_name, SLOP_STR("String"))) {
                return (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = env_env_get_string_type(env)};
            } else {
                return (slop_option_types_ResolvedType_ptr){.has_value = false};
            }
        }
    }
}

uint8_t collect_is_range_type_expr(types_SExpr* type_expr) {
    if (!(parser_sexpr_is_list(type_expr))) {
        return 0;
    } else {
        if ((parser_sexpr_list_len(type_expr) < 2)) {
            return 0;
        } else {
            __auto_type _mv_1079 = parser_sexpr_list_get(type_expr, 0);
            if (_mv_1079.has_value) {
                __auto_type first_elem = _mv_1079.value;
                {
                    __auto_type base_name = parser_sexpr_get_symbol_name(first_elem);
                    return (string_eq(base_name, SLOP_STR("Int")) || string_eq(base_name, SLOP_STR("Float")));
                }
            } else if (!_mv_1079.has_value) {
                return 0;
            }
        }
    }
}

types_ResolvedType* collect_get_range_base_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1080 = parser_sexpr_list_get(type_expr, 0);
    if (_mv_1080.has_value) {
        __auto_type first_elem = _mv_1080.value;
        {
            __auto_type base_name = parser_sexpr_get_symbol_name(first_elem);
            if (string_eq(base_name, SLOP_STR("Int"))) {
                return env_env_get_int_type(env);
            } else if (string_eq(base_name, SLOP_STR("Float"))) {
                __auto_type _mv_1081 = env_env_lookup_type_direct(env, SLOP_STR("Float"));
                if (_mv_1081.has_value) {
                    __auto_type t = _mv_1081.value;
                    return t;
                } else if (!_mv_1081.has_value) {
                    return env_env_get_int_type(env);
                }
            } else {
                return env_env_get_int_type(env);
            }
        }
    } else if (!_mv_1080.has_value) {
        return env_env_get_int_type(env);
    }
}

slop_string collect_get_type_name_from_expr(types_SExpr* expr) {
    __auto_type _mv_1082 = (*expr);
    switch (_mv_1082.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1082.data.sym;
            return sym.name;
        }
        default: {
            return SLOP_STR("");
        }
    }
}

uint8_t collect_is_reserved_variant_name(slop_string name) {
    return ((string_eq(name, SLOP_STR("list"))) || (string_eq(name, SLOP_STR("ok"))) || (string_eq(name, SLOP_STR("error"))) || (string_eq(name, SLOP_STR("some"))) || (string_eq(name, SLOP_STR("none"))));
}

void collect_collect_union_variants(env_TypeEnv* env, slop_arena* arena, types_ResolvedType* resolved, types_SExpr* union_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((resolved != NULL)), "(!= resolved nil)");
    SLOP_PRE(((union_expr != NULL)), "(!= union-expr nil)");
    if (parser_sexpr_is_list(union_expr)) {
        {
            __auto_type len = parser_sexpr_list_len(union_expr);
            int64_t variant_idx = 0;
            for (int64_t i = 1; i < len; i++) {
                __auto_type _mv_1083 = parser_sexpr_list_get(union_expr, i);
                if (_mv_1083.has_value) {
                    __auto_type variant_form = _mv_1083.value;
                    collect_collect_single_union_variant(env, arena, resolved, variant_form, variant_idx);
                    variant_idx = (variant_idx + 1);
                } else if (!_mv_1083.has_value) {
                }
            }
        }
    }
}

slop_option_types_ResolvedType_ptr collect_get_variant_payload_type(env_TypeEnv* env, types_SExpr* variant_form) {
    if ((parser_sexpr_list_len(variant_form) <= 1)) {
        return (slop_option_types_ResolvedType_ptr){.has_value = false};
    } else {
        __auto_type _mv_1084 = parser_sexpr_list_get(variant_form, 1);
        if (_mv_1084.has_value) {
            __auto_type type_expr = _mv_1084.value;
            return collect_lookup_payload_type(env, parser_sexpr_get_symbol_name(type_expr));
        } else if (!_mv_1084.has_value) {
            return (slop_option_types_ResolvedType_ptr){.has_value = false};
        }
    }
}

slop_string collect_checker_get_variant_name(types_SExpr* variant_form) {
    if (parser_sexpr_is_list(variant_form)) {
        if ((parser_sexpr_list_len(variant_form) == 0)) {
            return SLOP_STR("");
        } else {
            __auto_type _mv_1085 = parser_sexpr_list_get(variant_form, 0);
            if (_mv_1085.has_value) {
                __auto_type name_expr = _mv_1085.value;
                return parser_sexpr_get_symbol_name(name_expr);
            } else if (!_mv_1085.has_value) {
                return SLOP_STR("");
            }
        }
    } else {
        __auto_type _mv_1086 = (*variant_form);
        switch (_mv_1086.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_1086.data.sym;
                return sym.name;
            }
            default: {
                return SLOP_STR("");
            }
        }
    }
}

void collect_collect_single_union_variant(env_TypeEnv* env, slop_arena* arena, types_ResolvedType* resolved, types_SExpr* variant_form, int64_t variant_idx) {
    {
        __auto_type vname = collect_checker_get_variant_name(variant_form);
        __auto_type type_name = (*resolved).name;
        __auto_type arena = env_env_arena(env);
        if (!(string_eq(vname, SLOP_STR("")))) {
            if (collect_is_reserved_variant_name(vname)) {
                {
                    __auto_type msg = string_concat(arena, SLOP_STR("union variant '"), string_concat(arena, vname, string_concat(arena, SLOP_STR("' in type '"), string_concat(arena, type_name, SLOP_STR("' shadows built-in form")))));
                    env_env_add_warning(env, msg, parser_sexpr_line(variant_form), parser_sexpr_col(variant_form));
                }
            }
            {
                __auto_type payload_type = collect_get_variant_payload_type(env, variant_form);
                __auto_type v = types_resolved_variant_new(arena, vname, variant_idx, vname, payload_type);
                ({ __auto_type _lst_p = &((*resolved).variants); __auto_type _item = ((*v)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                env_env_register_variant(env, vname, type_name);
            }
        }
    }
}

void collect_collect_enum_variants(env_TypeEnv* env, slop_string enum_name, types_SExpr* enum_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((enum_expr != NULL)), "(!= enum-expr nil)");
    __auto_type _mv_1087 = (*enum_expr);
    switch (_mv_1087.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1087.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                ({ for (int64_t i = 1; i < len; i++) { ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type variant_expr = _mv.value; ({ __auto_type _mv = (*variant_expr); switch (_mv.tag) { case types_SExpr_sym: { __auto_type sym = _mv.data.sym; ({ env_env_register_variant(env, sym.name, enum_name); }); break; } default: { ({ (void)0; }); break; }  } (void)0; }); } else { ({ (void)0; }); } (void)0; }); } 0; });
            }
            break;
        }
        default: {
            break;
        }
    }
}

void collect_collect_constants(env_TypeEnv* env, slop_list_types_SExpr_ptr ast) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type arena = env_env_arena(env);
        __auto_type len = ((int64_t)((ast).len));
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_1088 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1088.has_value) {
                __auto_type expr = _mv_1088.value;
                if (parser_is_form(expr, SLOP_STR("const"))) {
                    collect_collect_single_constant(env, arena, expr);
                } else if (parser_is_form(expr, SLOP_STR("module"))) {
                    collect_collect_module_constants(env, expr);
                } else {
                }
            } else if (!_mv_1088.has_value) {
            }
        }
    }
}

void collect_collect_module_constants(env_TypeEnv* env, types_SExpr* module_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((module_form != NULL)), "(!= module-form nil)");
    {
        __auto_type arena = env_env_arena(env);
        if (parser_sexpr_is_list(module_form)) {
            {
                __auto_type len = parser_sexpr_list_len(module_form);
                for (int64_t i = 2; i < len; i++) {
                    __auto_type _mv_1089 = parser_sexpr_list_get(module_form, i);
                    if (_mv_1089.has_value) {
                        __auto_type item = _mv_1089.value;
                        if (parser_is_form(item, SLOP_STR("const"))) {
                            collect_collect_single_constant(env, arena, item);
                        }
                    } else if (!_mv_1089.has_value) {
                    }
                }
            }
        }
    }
}

void collect_collect_single_constant(env_TypeEnv* env, slop_arena* arena, types_SExpr* const_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((const_form != NULL)), "(!= const-form nil)");
    if (parser_sexpr_is_list(const_form)) {
        if ((parser_sexpr_list_len(const_form) >= 3)) {
            __auto_type _mv_1090 = parser_sexpr_list_get(const_form, 1);
            if (_mv_1090.has_value) {
                __auto_type name_expr = _mv_1090.value;
                {
                    __auto_type const_name = parser_sexpr_get_symbol_name(name_expr);
                    if (!(string_eq(const_name, SLOP_STR("")))) {
                        __auto_type _mv_1091 = parser_sexpr_list_get(const_form, 2);
                        if (_mv_1091.has_value) {
                            __auto_type type_expr = _mv_1091.value;
                            {
                                __auto_type const_type = collect_get_const_type(env, arena, type_expr);
                                env_env_register_constant(env, const_name, const_type);
                            }
                        } else if (!_mv_1091.has_value) {
                        }
                    }
                }
            } else if (!_mv_1090.has_value) {
            }
        }
    }
}

types_ResolvedType* collect_get_const_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1092 = (*type_expr);
    switch (_mv_1092.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1092.data.sym;
            {
                __auto_type type_name = sym.name;
                __auto_type _mv_1093 = env_env_lookup_type_direct(env, type_name);
                if (_mv_1093.has_value) {
                    __auto_type t = _mv_1093.value;
                    return t;
                } else if (!_mv_1093.has_value) {
                    if (string_eq(type_name, SLOP_STR("Int"))) {
                        return env_env_get_int_type(env);
                    } else if (string_eq(type_name, SLOP_STR("Bool"))) {
                        return env_env_get_bool_type(env);
                    } else if (string_eq(type_name, SLOP_STR("String"))) {
                        return env_env_get_string_type(env);
                    } else if (string_eq(type_name, SLOP_STR("Unit"))) {
                        return env_env_get_unit_type(env);
                    } else {
                        return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, type_name, ((slop_option_string){.has_value = false}), type_name);
                    }
                }
            }
        }
        default: {
            return env_env_get_int_type(env);
        }
    }
}

void collect_collect_functions(env_TypeEnv* env, slop_list_types_SExpr_ptr ast) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type arena = env_env_arena(env);
        __auto_type len = ((int64_t)((ast).len));
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_1094 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1094.has_value) {
                __auto_type expr = _mv_1094.value;
                if (parser_is_form(expr, SLOP_STR("fn"))) {
                    collect_collect_single_function(env, arena, expr);
                } else if (parser_is_form(expr, SLOP_STR("module"))) {
                    collect_collect_module_functions(env, expr);
                } else {
                }
            } else if (!_mv_1094.has_value) {
            }
        }
    }
}

void collect_collect_module_functions(env_TypeEnv* env, types_SExpr* module_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((module_form != NULL)), "(!= module-form nil)");
    {
        __auto_type arena = env_env_arena(env);
        if (parser_sexpr_is_list(module_form)) {
            __auto_type _mv_1095 = parser_sexpr_list_get(module_form, 1);
            if (_mv_1095.has_value) {
                __auto_type name_expr = _mv_1095.value;
                {
                    __auto_type mod_name = parser_sexpr_get_symbol_name(name_expr);
                    if (!(string_eq(mod_name, SLOP_STR("")))) {
                        env_env_set_module(env, (slop_option_string){.has_value = 1, .value = mod_name});
                    }
                }
            } else if (!_mv_1095.has_value) {
            }
            {
                __auto_type len = parser_sexpr_list_len(module_form);
                for (int64_t i = 2; i < len; i++) {
                    __auto_type _mv_1096 = parser_sexpr_list_get(module_form, i);
                    if (_mv_1096.has_value) {
                        __auto_type item = _mv_1096.value;
                        if (parser_is_form(item, SLOP_STR("fn"))) {
                            collect_collect_single_function(env, arena, item);
                        } else if (parser_is_form(item, SLOP_STR("ffi"))) {
                            collect_collect_ffi_functions(env, arena, item);
                        } else {
                        }
                    } else if (!_mv_1096.has_value) {
                    }
                }
            }
        }
    }
}

void collect_collect_ffi_functions(env_TypeEnv* env, slop_arena* arena, types_SExpr* ffi_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((ffi_form != NULL)), "(!= ffi-form nil)");
    if (parser_sexpr_is_list(ffi_form)) {
        {
            __auto_type len = parser_sexpr_list_len(ffi_form);
            for (int64_t i = 2; i < len; i++) {
                __auto_type _mv_1097 = parser_sexpr_list_get(ffi_form, i);
                if (_mv_1097.has_value) {
                    __auto_type func_decl = _mv_1097.value;
                    collect_collect_ffi_function(env, arena, func_decl);
                } else if (!_mv_1097.has_value) {
                }
            }
        }
    }
}

void collect_collect_ffi_function(env_TypeEnv* env, slop_arena* arena, types_SExpr* func_decl) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((func_decl != NULL)), "(!= func-decl nil)");
    if (parser_sexpr_is_list(func_decl)) {
        {
            __auto_type decl_len = parser_sexpr_list_len(func_decl);
            if ((decl_len >= 3)) {
                __auto_type _mv_1098 = parser_sexpr_list_get(func_decl, 0);
                if (_mv_1098.has_value) {
                    __auto_type name_expr = _mv_1098.value;
                    {
                        __auto_type fn_name = parser_sexpr_get_symbol_name(name_expr);
                        if (!(string_eq(fn_name, SLOP_STR("")))) {
                            {
                                __auto_type mod_opt = env_env_get_module(env);
                                __auto_type qualified_name = ((mod_opt.has_value) ? string_concat(arena, mod_opt.value, string_concat(arena, SLOP_STR(":"), fn_name)) : fn_name);
                                __auto_type params = collect_collect_ffi_params(env, arena, func_decl);
                                __auto_type ret_type = collect_get_ffi_return_type(env, arena, func_decl);
                                __auto_type sig = types_fn_signature_new(arena, qualified_name, fn_name, params, ret_type);
                                (*sig).module_name = mod_opt;
                                env_env_register_function(env, sig);
                            }
                        }
                    }
                } else if (!_mv_1098.has_value) {
                }
            } else if ((decl_len == 2)) {
                __auto_type _mv_1099 = parser_sexpr_list_get(func_decl, 0);
                if (_mv_1099.has_value) {
                    __auto_type name_expr = _mv_1099.value;
                    {
                        __auto_type const_name = parser_sexpr_get_symbol_name(name_expr);
                        if (!(string_eq(const_name, SLOP_STR("")))) {
                            __auto_type _mv_1100 = parser_sexpr_list_get(func_decl, 1);
                            if (_mv_1100.has_value) {
                                __auto_type type_expr = _mv_1100.value;
                                {
                                    __auto_type const_type = collect_get_field_type(env, arena, type_expr);
                                    env_env_register_constant(env, const_name, const_type);
                                }
                            } else if (!_mv_1100.has_value) {
                            }
                        }
                    }
                } else if (!_mv_1099.has_value) {
                }
            } else {
            }
        }
    }
}

slop_list_types_ParamInfo collect_collect_ffi_params(env_TypeEnv* env, slop_arena* arena, types_SExpr* func_decl) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type params = ((slop_list_types_ParamInfo){ .data = (types_ParamInfo*)slop_arena_alloc(arena, 16 * sizeof(types_ParamInfo)), .len = 0, .cap = 16 });
        __auto_type _mv_1101 = parser_sexpr_list_get(func_decl, 1);
        if (_mv_1101.has_value) {
            __auto_type params_expr = _mv_1101.value;
            if (parser_sexpr_is_list(params_expr)) {
                {
                    __auto_type num_params = parser_sexpr_list_len(params_expr);
                    ({ for (int64_t j = 0; j < num_params; j++) { ({ __auto_type _mv = parser_sexpr_list_get(params_expr, j); if (_mv.has_value) { __auto_type param_form = _mv.value; ((parser_sexpr_is_list(param_form)) ? ({ (((parser_sexpr_list_len(param_form) >= 2)) ? ({ ({ __auto_type _mv = parser_sexpr_list_get(param_form, 0); if (_mv.has_value) { __auto_type pname_expr = _mv.value; ({ __auto_type param_name = parser_sexpr_get_symbol_name(pname_expr); ((!(string_eq(param_name, SLOP_STR("")))) ? ({ ({ __auto_type _mv = parser_sexpr_list_get(param_form, 1); if (_mv.has_value) { __auto_type ptype_expr = _mv.value; ({ __auto_type param_type = collect_get_field_type(env, arena, ptype_expr); __auto_type info = types_param_info_new(arena, param_name, param_type); ({ __auto_type _lst_p = &(params); __auto_type _item = ((*info)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); }); } else { ({ (void)0; }); } (void)0; }); 0; }) : ({ (void)0; })); }); } else { ({ (void)0; }); } (void)0; }); 0; }) : ({ (void)0; })); 0; }) : ({ (void)0; })); } else { ({ (void)0; }); } (void)0; }); } 0; });
                }
            }
        } else if (!_mv_1101.has_value) {
        }
        return params;
    }
}

types_ResolvedType* collect_get_ffi_return_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* func_decl) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1102 = parser_sexpr_list_get(func_decl, 2);
    if (_mv_1102.has_value) {
        __auto_type ret_expr = _mv_1102.value;
        return collect_get_field_type(env, arena, ret_expr);
    } else if (!_mv_1102.has_value) {
        return env_env_get_unit_type(env);
    }
}

void collect_collect_single_function(env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    if (parser_sexpr_is_list(fn_form)) {
        if ((parser_sexpr_list_len(fn_form) >= 3)) {
            __auto_type _mv_1103 = parser_sexpr_list_get(fn_form, 1);
            if (_mv_1103.has_value) {
                __auto_type name_expr = _mv_1103.value;
                {
                    __auto_type fn_name = parser_sexpr_get_symbol_name(name_expr);
                    if (!(string_eq(fn_name, SLOP_STR("")))) {
                        {
                            __auto_type mod_opt = env_env_get_module(env);
                            __auto_type qualified_name = ((mod_opt.has_value) ? string_concat(arena, mod_opt.value, string_concat(arena, SLOP_STR(":"), fn_name)) : fn_name);
                            __auto_type type_params = collect_find_fn_type_params(arena, fn_form);
                            __auto_type has_generics = (((int64_t)((type_params).len)) > 0);
                            __auto_type concrete_params = collect_collect_fn_params(env, arena, fn_form);
                            __auto_type params = ((has_generics) ? collect_collect_fn_params_generic(env, arena, fn_form, type_params) : concrete_params);
                            __auto_type ret_type = ((has_generics) ? collect_find_fn_return_type_generic(env, fn_form, type_params) : collect_find_fn_return_type(env, fn_form));
                            __auto_type sig = types_fn_signature_new(arena, qualified_name, fn_name, params, ret_type);
                            (*sig).module_name = mod_opt;
                            if (has_generics) {
                                (*sig).type_params = type_params;
                            }
                            if (string_eq(fn_name, SLOP_STR("main"))) {
                                collect_validate_main_params(env, fn_form, concrete_params);
                            }
                            env_env_register_function(env, sig);
                        }
                    }
                }
            } else if (!_mv_1103.has_value) {
            }
        }
    }
}

uint8_t collect_is_integer_type_name(slop_string name) {
    return ((string_eq(name, SLOP_STR("Int"))) || (string_eq(name, SLOP_STR("I8"))) || (string_eq(name, SLOP_STR("I16"))) || (string_eq(name, SLOP_STR("I32"))) || (string_eq(name, SLOP_STR("I64"))) || (string_eq(name, SLOP_STR("U8"))) || (string_eq(name, SLOP_STR("U16"))) || (string_eq(name, SLOP_STR("U32"))) || (string_eq(name, SLOP_STR("U64"))));
}

void collect_validate_main_params(env_TypeEnv* env, types_SExpr* fn_form, slop_list_types_ParamInfo params) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    {
        __auto_type num_params = ((int64_t)((params).len));
        __auto_type line = parser_sexpr_line(fn_form);
        __auto_type col = parser_sexpr_col(fn_form);
        if ((num_params == 0)) {
        } else if ((num_params == 2)) {
            __auto_type _mv_1104 = ({ __auto_type _lst = params; size_t _idx = (size_t)0; slop_option_types_ParamInfo _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1104.has_value) {
                __auto_type p0 = _mv_1104.value;
                {
                    __auto_type t0 = p0.param_type;
                    if ((t0 != NULL)) {
                        {
                            __auto_type name0 = (*t0).name;
                            if (!(collect_is_integer_type_name(name0))) {
                                env_env_add_error(env, SLOP_STR("main's first parameter must be an integer type (e.g., Int for argc)"), line, col);
                            }
                        }
                    }
                }
            } else if (!_mv_1104.has_value) {
            }
            __auto_type _mv_1105 = ({ __auto_type _lst = params; size_t _idx = (size_t)1; slop_option_types_ParamInfo _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1105.has_value) {
                __auto_type p1 = _mv_1105.value;
                {
                    __auto_type t1 = p1.param_type;
                    if ((t1 != NULL)) {
                        if (!(types_resolved_type_is_pointer(t1))) {
                            env_env_add_error(env, SLOP_STR("main's second parameter must be a pointer type (e.g., (Ptr (Ptr U8)) for argv)"), line, col);
                        }
                    }
                }
            } else if (!_mv_1105.has_value) {
            }
        } else {
            env_env_add_error(env, SLOP_STR("main function must have either no parameters or exactly two parameters (argc: Int, argv: (Ptr (Ptr U8)))"), line, col);
        }
    }
}

slop_list_types_ParamInfo collect_collect_fn_params(env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    {
        __auto_type params = ((slop_list_types_ParamInfo){ .data = (types_ParamInfo*)slop_arena_alloc(arena, 16 * sizeof(types_ParamInfo)), .len = 0, .cap = 16 });
        __auto_type _mv_1106 = parser_sexpr_list_get(fn_form, 2);
        if (_mv_1106.has_value) {
            __auto_type params_expr = _mv_1106.value;
            if (parser_sexpr_is_list(params_expr)) {
                {
                    __auto_type num_params = parser_sexpr_list_len(params_expr);
                    ({ for (int64_t i = 0; i < num_params; i++) { ({ __auto_type _mv = parser_sexpr_list_get(params_expr, i); if (_mv.has_value) { __auto_type param_form = _mv.value; (((parser_sexpr_is_list(param_form) && (parser_sexpr_list_len(param_form) >= 2))) ? ({ ({ __auto_type _mv = parser_sexpr_list_get(param_form, 0); if (_mv.has_value) { __auto_type first_expr = _mv.value; ({ __auto_type first_name = parser_sexpr_get_symbol_name(first_expr); ((((string_eq(first_name, SLOP_STR("in"))) || (string_eq(first_name, SLOP_STR("out"))) || (string_eq(first_name, SLOP_STR("mut"))))) ? (((parser_sexpr_list_len(param_form) >= 3)) ? ({ ({ __auto_type _mv = parser_sexpr_list_get(param_form, 1); if (_mv.has_value) { __auto_type name_expr = _mv.value; ({ __auto_type param_name = parser_sexpr_get_symbol_name(name_expr); ((!(string_eq(param_name, SLOP_STR("")))) ? ({ ({ __auto_type _mv = parser_sexpr_list_get(param_form, 2); if (_mv.has_value) { __auto_type type_expr = _mv.value; ({ __auto_type param_type = collect_get_field_type(env, arena, type_expr); __auto_type info = types_param_info_new(arena, param_name, param_type); ({ ({ __auto_type _lst_p = &(params); __auto_type _item = ((*info)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); }); }); } else { ({ (void)0; }); } (void)0; }); 0; }) : ({ (void)0; })); }); } else { ({ (void)0; }); } (void)0; }); 0; }) : ({ (void)0; })) : ((!(string_eq(first_name, SLOP_STR("")))) ? ({ ({ __auto_type _mv = parser_sexpr_list_get(param_form, 1); if (_mv.has_value) { __auto_type type_expr = _mv.value; ({ __auto_type param_type = collect_get_field_type(env, arena, type_expr); __auto_type info = types_param_info_new(arena, first_name, param_type); ({ ({ __auto_type _lst_p = &(params); __auto_type _item = ((*info)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); }); }); } else { ({ (void)0; }); } (void)0; }); 0; }) : ({ (void)0; }))); }); } else { ({ (void)0; }); } (void)0; }); 0; }) : ({ (void)0; })); } else { ({ (void)0; }); } (void)0; }); } 0; });
                }
            }
        } else if (!_mv_1106.has_value) {
        }
        return params;
    }
}

slop_list_types_ParamInfo collect_collect_fn_params_generic(env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form, slop_list_string type_params) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    {
        __auto_type params = ((slop_list_types_ParamInfo){ .data = (types_ParamInfo*)slop_arena_alloc(arena, 16 * sizeof(types_ParamInfo)), .len = 0, .cap = 16 });
        __auto_type _mv_1107 = parser_sexpr_list_get(fn_form, 2);
        if (_mv_1107.has_value) {
            __auto_type params_expr = _mv_1107.value;
            if (parser_sexpr_is_list(params_expr)) {
                {
                    __auto_type num_params = parser_sexpr_list_len(params_expr);
                    ({ for (int64_t i = 0; i < num_params; i++) { ({ __auto_type _mv = parser_sexpr_list_get(params_expr, i); if (_mv.has_value) { __auto_type param_form = _mv.value; (((parser_sexpr_is_list(param_form) && (parser_sexpr_list_len(param_form) >= 2))) ? ({ ({ __auto_type _mv = parser_sexpr_list_get(param_form, 0); if (_mv.has_value) { __auto_type first_expr = _mv.value; ({ __auto_type first_name = parser_sexpr_get_symbol_name(first_expr); ((((string_eq(first_name, SLOP_STR("in"))) || (string_eq(first_name, SLOP_STR("out"))) || (string_eq(first_name, SLOP_STR("mut"))))) ? (((parser_sexpr_list_len(param_form) >= 3)) ? ({ ({ __auto_type _mv = parser_sexpr_list_get(param_form, 1); if (_mv.has_value) { __auto_type name_expr = _mv.value; ({ __auto_type param_name = parser_sexpr_get_symbol_name(name_expr); ((!(string_eq(param_name, SLOP_STR("")))) ? ({ ({ __auto_type _mv = parser_sexpr_list_get(param_form, 2); if (_mv.has_value) { __auto_type type_expr = _mv.value; ({ __auto_type param_type = collect_get_field_type_generic(env, arena, type_expr, type_params); __auto_type info = types_param_info_new(arena, param_name, param_type); ({ ({ __auto_type _lst_p = &(params); __auto_type _item = ((*info)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); }); }); } else { ({ (void)0; }); } (void)0; }); 0; }) : ({ (void)0; })); }); } else { ({ (void)0; }); } (void)0; }); 0; }) : ({ (void)0; })) : ((!(string_eq(first_name, SLOP_STR("")))) ? ({ ({ __auto_type _mv = parser_sexpr_list_get(param_form, 1); if (_mv.has_value) { __auto_type type_expr = _mv.value; ({ __auto_type param_type = collect_get_field_type_generic(env, arena, type_expr, type_params); __auto_type info = types_param_info_new(arena, first_name, param_type); ({ ({ __auto_type _lst_p = &(params); __auto_type _item = ((*info)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); }); }); } else { ({ (void)0; }); } (void)0; }); 0; }) : ({ (void)0; }))); }); } else { ({ (void)0; }); } (void)0; }); 0; }) : ({ (void)0; })); } else { ({ (void)0; }); } (void)0; }); } 0; });
                }
            }
        } else if (!_mv_1107.has_value) {
        }
        return params;
    }
}

types_ResolvedType* collect_find_fn_return_type(env_TypeEnv* env, types_SExpr* fn_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    {
        __auto_type len = parser_sexpr_list_len(fn_form);
        uint8_t found = 0;
        types_ResolvedType* found_type = env_env_get_unit_type(env);
        for (int64_t i = 3; i < len; i++) {
            __auto_type _mv_1108 = parser_sexpr_list_get(fn_form, i);
            if (_mv_1108.has_value) {
                __auto_type item = _mv_1108.value;
                if (parser_is_form(item, SLOP_STR("@spec"))) {
                    if (!(found)) {
                        found_type = collect_checker_extract_spec_return_type(env, item);
                        found = 1;
                    }
                }
            } else if (!_mv_1108.has_value) {
            }
        }
        return found_type;
    }
}

types_ResolvedType* collect_checker_extract_spec_return_type(env_TypeEnv* env, types_SExpr* spec_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type arena = env_env_arena(env);
        __auto_type _mv_1109 = parser_sexpr_list_get(spec_form, 1);
        if (_mv_1109.has_value) {
            __auto_type spec_body = _mv_1109.value;
            if (parser_sexpr_is_list(spec_body)) {
                {
                    __auto_type len = parser_sexpr_list_len(spec_body);
                    __auto_type _mv_1110 = parser_sexpr_list_get(spec_body, (len - 1));
                    if (_mv_1110.has_value) {
                        __auto_type ret_expr = _mv_1110.value;
                        return collect_get_field_type(env, arena, ret_expr);
                    } else if (!_mv_1110.has_value) {
                        return env_env_get_unit_type(env);
                    }
                }
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (!_mv_1109.has_value) {
            return env_env_get_unit_type(env);
        }
    }
}

