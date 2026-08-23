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
slop_list_types_ResolvedType_ptr collect_get_variant_payload_types(env_TypeEnv* env, types_SExpr* variant_form);
slop_option_types_ResolvedType_ptr collect_get_variant_payload_type(env_TypeEnv* env, types_SExpr* variant_form);
slop_string collect_checker_get_variant_name(types_SExpr* variant_form);
uint8_t collect_check_type_expr_recursive(types_SExpr* type_expr, slop_string union_name);
uint8_t collect_has_recursive_value_payload(types_SExpr* variant_form, slop_string union_name);
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
uint8_t collect_ffi_has_variadic(types_SExpr* func_decl);
slop_list_types_ParamInfo collect_collect_ffi_params(env_TypeEnv* env, slop_arena* arena, types_SExpr* func_decl);
types_ResolvedType* collect_get_ffi_return_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* func_decl);
void collect_collect_single_function(env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form);
uint8_t collect_is_reserved_builtin_name(slop_string name);
void collect_report_reserved_name(env_TypeEnv* env, slop_string name, slop_string what, int64_t line, int64_t col);
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
            __auto_type _mv_1159 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1159.has_value) {
                __auto_type expr = _mv_1159.value;
                if (parser_is_form(expr, SLOP_STR("type"))) {
                    collect_register_type_name(env, arena, expr);
                } else if (parser_is_form(expr, SLOP_STR("module"))) {
                    collect_register_module_type_names(env, expr);
                } else {
                }
            } else if (!_mv_1159.has_value) {
            }
        }
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_1160 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1160.has_value) {
                __auto_type expr = _mv_1160.value;
                if (parser_is_form(expr, SLOP_STR("type"))) {
                    collect_resolve_type_body(env, arena, expr);
                } else if (parser_is_form(expr, SLOP_STR("module"))) {
                    collect_resolve_module_type_bodies(env, expr);
                } else {
                }
            } else if (!_mv_1160.has_value) {
            }
        }
    }
}

void collect_register_type_name(env_TypeEnv* env, slop_arena* arena, types_SExpr* expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type mod_name = env_env_get_module(env);
        __auto_type _mv_1161 = (*expr);
        switch (_mv_1161.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_1161.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type _mv_1162 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1162.has_value) {
                        __auto_type name_expr = _mv_1162.value;
                        __auto_type _mv_1163 = (*name_expr);
                        switch (_mv_1163.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1163.data.sym;
                                {
                                    __auto_type type_name = sym.name;
                                    if (collect_is_reserved_builtin_name(type_name)) {
                                        collect_report_reserved_name(env, type_name, SLOP_STR("type"), parser_sexpr_line(name_expr), parser_sexpr_col(name_expr));
                                    }
                                    __auto_type _mv_1164 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_1164.has_value) {
                                        __auto_type type_expr = _mv_1164.value;
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
                                        } else if (parser_is_form(type_expr, SLOP_STR("Option"))) {
                                            {
                                                __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_option, type_name, mod_name, type_name);
                                                env_env_register_type(env, resolved);
                                            }
                                        } else {
                                            {
                                                __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, type_name, mod_name, type_name);
                                                env_env_register_type(env, resolved);
                                            }
                                        }
                                    } else if (!_mv_1164.has_value) {
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
                    } else if (!_mv_1162.has_value) {
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
    __auto_type _mv_1165 = (*expr);
    switch (_mv_1165.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1165.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type _mv_1166 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1166.has_value) {
                    __auto_type name_expr = _mv_1166.value;
                    __auto_type _mv_1167 = (*name_expr);
                    switch (_mv_1167.tag) {
                        case types_SExpr_sym:
                        {
                            __auto_type sym = _mv_1167.data.sym;
                            {
                                __auto_type type_name = sym.name;
                                __auto_type _mv_1168 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_1168.has_value) {
                                    __auto_type type_expr = _mv_1168.value;
                                    if (parser_is_form(type_expr, SLOP_STR("enum"))) {
                                        collect_collect_enum_variants(env, type_name, type_expr);
                                    } else if (parser_is_form(type_expr, SLOP_STR("record"))) {
                                        __auto_type _mv_1169 = env_env_lookup_type_direct(env, type_name);
                                        if (_mv_1169.has_value) {
                                            __auto_type resolved = _mv_1169.value;
                                            collect_collect_record_fields(env, arena, resolved, type_expr);
                                        } else if (!_mv_1169.has_value) {
                                        }
                                    } else if (parser_is_form(type_expr, SLOP_STR("union"))) {
                                        __auto_type _mv_1170 = env_env_lookup_type_direct(env, type_name);
                                        if (_mv_1170.has_value) {
                                            __auto_type resolved = _mv_1170.value;
                                            collect_collect_union_variants(env, arena, resolved, type_expr);
                                        } else if (!_mv_1170.has_value) {
                                        }
                                    } else if (collect_is_range_type_expr(type_expr)) {
                                        __auto_type _mv_1171 = env_env_lookup_type_direct(env, type_name);
                                        if (_mv_1171.has_value) {
                                            __auto_type resolved = _mv_1171.value;
                                            {
                                                __auto_type base_type = collect_get_range_base_type(env, arena, type_expr);
                                                types_resolved_type_set_inner(resolved, base_type);
                                            }
                                        } else if (!_mv_1171.has_value) {
                                        }
                                    } else if (parser_is_form(type_expr, SLOP_STR("Map"))) {
                                        __auto_type _mv_1172 = env_env_lookup_type_direct(env, type_name);
                                        if (_mv_1172.has_value) {
                                            __auto_type resolved = _mv_1172.value;
                                            {
                                                __auto_type key_type = collect_get_field_type(env, arena, collect_get_type_arg(type_expr, 1));
                                                __auto_type val_type = collect_get_field_type(env, arena, collect_get_type_arg(type_expr, 2));
                                                types_resolved_type_set_inner(resolved, key_type);
                                                types_resolved_type_set_inner2(resolved, val_type);
                                            }
                                        } else if (!_mv_1172.has_value) {
                                        }
                                    } else if (parser_is_form(type_expr, SLOP_STR("Set"))) {
                                        __auto_type _mv_1173 = env_env_lookup_type_direct(env, type_name);
                                        if (_mv_1173.has_value) {
                                            __auto_type resolved = _mv_1173.value;
                                            {
                                                __auto_type elem_type = collect_get_field_type(env, arena, collect_get_type_arg(type_expr, 1));
                                                types_resolved_type_set_inner(resolved, elem_type);
                                            }
                                        } else if (!_mv_1173.has_value) {
                                        }
                                    } else if (parser_is_form(type_expr, SLOP_STR("List"))) {
                                        __auto_type _mv_1174 = env_env_lookup_type_direct(env, type_name);
                                        if (_mv_1174.has_value) {
                                            __auto_type resolved = _mv_1174.value;
                                            {
                                                __auto_type elem_type = collect_get_field_type(env, arena, collect_get_type_arg(type_expr, 1));
                                                types_resolved_type_set_inner(resolved, elem_type);
                                            }
                                        } else if (!_mv_1174.has_value) {
                                        }
                                    } else if (parser_is_form(type_expr, SLOP_STR("Option"))) {
                                        __auto_type _mv_1175 = env_env_lookup_type_direct(env, type_name);
                                        if (_mv_1175.has_value) {
                                            __auto_type resolved = _mv_1175.value;
                                            {
                                                __auto_type inner_type = collect_get_field_type(env, arena, collect_get_type_arg(type_expr, 1));
                                                types_resolved_type_set_inner(resolved, inner_type);
                                            }
                                        } else if (!_mv_1175.has_value) {
                                        }
                                    } else {
                                        {
                                            __auto_type alias_name = parser_sexpr_get_symbol_name(type_expr);
                                            if (!(string_eq(alias_name, SLOP_STR("")))) {
                                                __auto_type _mv_1176 = env_env_lookup_type_direct(env, type_name);
                                                if (_mv_1176.has_value) {
                                                    __auto_type resolved = _mv_1176.value;
                                                    {
                                                        __auto_type base_type = collect_get_field_type(env, arena, type_expr);
                                                        types_resolved_type_set_inner(resolved, base_type);
                                                    }
                                                } else if (!_mv_1176.has_value) {
                                                }
                                            }
                                        }
                                    }
                                } else if (!_mv_1168.has_value) {
                                }
                            }
                            break;
                        }
                        default: {
                            break;
                        }
                    }
                } else if (!_mv_1166.has_value) {
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
    __auto_type _mv_1177 = (*record_expr);
    switch (_mv_1177.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1177.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                for (int64_t i = 1; i < len; i++) {
                    __auto_type _mv_1178 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1178.has_value) {
                        __auto_type field_form = _mv_1178.value;
                        __auto_type _mv_1179 = (*field_form);
                        switch (_mv_1179.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type field_lst = _mv_1179.data.lst;
                                {
                                    __auto_type field_items = field_lst.items;
                                    __auto_type _mv_1180 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_1180.has_value) {
                                        __auto_type name_expr = _mv_1180.value;
                                        __auto_type _mv_1181 = (*name_expr);
                                        switch (_mv_1181.tag) {
                                            case types_SExpr_sym:
                                            {
                                                __auto_type name_sym = _mv_1181.data.sym;
                                                __auto_type _mv_1182 = ({ __auto_type _lst = field_items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                                if (_mv_1182.has_value) {
                                                    __auto_type type_expr = _mv_1182.value;
                                                    {
                                                        __auto_type field_name = name_sym.name;
                                                        __auto_type field_type = collect_get_field_type(env, arena, type_expr);
                                                        __auto_type field = types_resolved_field_new(arena, field_name, field_type, (i - 1));
                                                        ({ __auto_type _lst_p = &((*resolved).fields); __auto_type _item = ((*field)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                    }
                                                } else if (!_mv_1182.has_value) {
                                                }
                                                break;
                                            }
                                            default: {
                                                break;
                                            }
                                        }
                                    } else if (!_mv_1180.has_value) {
                                    }
                                }
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_1178.has_value) {
                    }
                }
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
    __auto_type _mv_1183 = (*type_expr);
    switch (_mv_1183.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1183.data.lst;
            __auto_type _mv_1184 = ({ __auto_type _lst = lst.items; size_t _idx = (size_t)idx; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1184.has_value) {
                __auto_type arg = _mv_1184.value;
                return arg;
            } else if (!_mv_1184.has_value) {
                return type_expr;
            }
            SLOP_UNREACHABLE();
        }
        default: {
            return type_expr;
        }
    }
}

types_ResolvedType* collect_get_field_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1185 = (*type_expr);
    switch (_mv_1185.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1185.data.sym;
            {
                __auto_type type_name = sym.name;
                __auto_type _mv_1186 = env_env_lookup_type_direct(env, type_name);
                if (_mv_1186.has_value) {
                    __auto_type t = _mv_1186.value;
                    return t;
                } else if (!_mv_1186.has_value) {
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
                SLOP_UNREACHABLE();
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1185.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type _mv_1187 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1187.has_value) {
                    __auto_type head_expr = _mv_1187.value;
                    {
                        __auto_type head_name = parser_sexpr_get_symbol_name(head_expr);
                        if (string_eq(head_name, SLOP_STR("Option"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                return env_env_make_option_type(env, inner_type);
                            }
                        } else if (string_eq(head_name, SLOP_STR("Ptr"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
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
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type list_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_list, SLOP_STR("List"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_list_t*"));
                                    types_resolved_type_set_inner(list_type, inner_type);
                                    return list_type;
                                }
                            }
                        } else if (string_eq(head_name, SLOP_STR("Set"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type set_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Set"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_map*"));
                                    types_resolved_type_set_inner(set_type, inner_type);
                                    return set_type;
                                }
                            }
                        } else if (string_eq(head_name, SLOP_STR("Map"))) {
                            {
                                __auto_type key_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                __auto_type val_type = (((((int64_t)((items).len)) >= 3)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type map_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_map, SLOP_STR("Map"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_map*"));
                                    types_resolved_type_set_inner(map_type, key_type);
                                    types_resolved_type_set_inner2(map_type, val_type);
                                    return map_type;
                                }
                            }
                        } else if (string_eq(head_name, SLOP_STR("Result"))) {
                            {
                                __auto_type ok_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_unit_type(env)); }) : env_env_get_unit_type(env));
                                __auto_type err_type = (((((int64_t)((items).len)) >= 3)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_unit_type(env)); }) : env_env_get_unit_type(env));
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
                } else if (!_mv_1187.has_value) {
                    return env_env_get_unit_type(env);
                }
                SLOP_UNREACHABLE();
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
            __auto_type _mv_1188 = ({ __auto_type _lst = type_params; size_t _idx = (size_t)i; slop_option_string _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1188.has_value) {
                __auto_type tp = _mv_1188.value;
                if (string_eq(name, tp)) {
                    found = 1;
                }
            } else if (!_mv_1188.has_value) {
            }
        }
        return found;
    }
}

types_ResolvedType* collect_get_field_type_generic(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr, slop_list_string type_params) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1189 = (*type_expr);
    switch (_mv_1189.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1189.data.sym;
            {
                __auto_type type_name = sym.name;
                if (collect_is_type_param(type_name, type_params)) {
                    return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_typevar, type_name, ((slop_option_string){.has_value = false}), type_name);
                } else {
                    __auto_type _mv_1190 = env_env_lookup_type_direct(env, type_name);
                    if (_mv_1190.has_value) {
                        __auto_type t = _mv_1190.value;
                        return t;
                    } else if (!_mv_1190.has_value) {
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
                    SLOP_UNREACHABLE();
                }
            }
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1189.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type _mv_1191 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1191.has_value) {
                    __auto_type head_expr = _mv_1191.value;
                    {
                        __auto_type head_name = parser_sexpr_get_symbol_name(head_expr);
                        if (string_eq(head_name, SLOP_STR("Option"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type_generic(env, arena, inner_expr, type_params); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                return env_env_make_option_type(env, inner_type);
                            }
                        } else if (string_eq(head_name, SLOP_STR("Ptr"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type_generic(env, arena, inner_expr, type_params); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
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
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type_generic(env, arena, inner_expr, type_params); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type list_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_list, SLOP_STR("List"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_list_t*"));
                                    types_resolved_type_set_inner(list_type, inner_type);
                                    return list_type;
                                }
                            }
                        } else if (string_eq(head_name, SLOP_STR("Chan"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type_generic(env, arena, inner_expr, type_params); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type chan_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_chan, SLOP_STR("Chan"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_chan_int*"));
                                    types_resolved_type_set_inner(chan_type, inner_type);
                                    return chan_type;
                                }
                            }
                        } else if (string_eq(head_name, SLOP_STR("Thread"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type_generic(env, arena, inner_expr, type_params); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type thread_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_thread, SLOP_STR("Thread"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_thread_int*"));
                                    types_resolved_type_set_inner(thread_type, inner_type);
                                    return thread_type;
                                }
                            }
                        } else if (string_eq(head_name, SLOP_STR("Result"))) {
                            {
                                __auto_type ok_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type_generic(env, arena, inner_expr, type_params); }) : (env_env_get_unit_type(env)); }) : env_env_get_unit_type(env));
                                __auto_type err_type = (((((int64_t)((items).len)) >= 3)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type_generic(env, arena, inner_expr, type_params); }) : (env_env_get_unit_type(env)); }) : env_env_get_unit_type(env));
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
                } else if (!_mv_1191.has_value) {
                    return env_env_get_unit_type(env);
                }
                SLOP_UNREACHABLE();
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
            __auto_type _mv_1192 = parser_sexpr_list_get(fn_form, i);
            if (_mv_1192.has_value) {
                __auto_type item = _mv_1192.value;
                if (parser_is_form(item, SLOP_STR("@generic"))) {
                    __auto_type _mv_1193 = parser_sexpr_list_get(item, 1);
                    if (_mv_1193.has_value) {
                        __auto_type params_expr = _mv_1193.value;
                        if (parser_sexpr_is_list(params_expr)) {
                            {
                                __auto_type num_params = parser_sexpr_list_len(params_expr);
                                for (int64_t j = 0; j < num_params; j++) {
                                    __auto_type _mv_1194 = parser_sexpr_list_get(params_expr, j);
                                    if (_mv_1194.has_value) {
                                        __auto_type param_expr = _mv_1194.value;
                                        {
                                            __auto_type param_name = parser_sexpr_get_symbol_name(param_expr);
                                            if (!(string_eq(param_name, SLOP_STR("")))) {
                                                ({ __auto_type _lst_p = &(type_params); __auto_type _item = (param_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                            }
                                        }
                                    } else if (!_mv_1194.has_value) {
                                    }
                                }
                            }
                        }
                    } else if (!_mv_1193.has_value) {
                    }
                }
            } else if (!_mv_1192.has_value) {
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
            __auto_type _mv_1195 = parser_sexpr_list_get(fn_form, i);
            if (_mv_1195.has_value) {
                __auto_type item = _mv_1195.value;
                if (parser_is_form(item, SLOP_STR("@spec"))) {
                    if (!(found)) {
                        found_type = collect_extract_spec_return_type_generic(env, item, type_params);
                        found = 1;
                    }
                }
            } else if (!_mv_1195.has_value) {
            }
        }
        return found_type;
    }
}

types_ResolvedType* collect_extract_spec_return_type_generic(env_TypeEnv* env, types_SExpr* spec_form, slop_list_string type_params) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type arena = env_env_arena(env);
        __auto_type _mv_1196 = parser_sexpr_list_get(spec_form, 1);
        if (_mv_1196.has_value) {
            __auto_type spec_body = _mv_1196.value;
            if (parser_sexpr_is_list(spec_body)) {
                {
                    __auto_type len = parser_sexpr_list_len(spec_body);
                    __auto_type _mv_1197 = parser_sexpr_list_get(spec_body, (len - 1));
                    if (_mv_1197.has_value) {
                        __auto_type ret_expr = _mv_1197.value;
                        return collect_get_field_type_generic(env, arena, ret_expr, type_params);
                    } else if (!_mv_1197.has_value) {
                        return env_env_get_unit_type(env);
                    }
                    SLOP_UNREACHABLE();
                }
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (!_mv_1196.has_value) {
            return env_env_get_unit_type(env);
        }
        SLOP_UNREACHABLE();
    }
}

slop_list_types_ResolvedType_ptr collect_collect_fn_spec_params(env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form, slop_list_string type_params) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    {
        __auto_type spec_params = ((slop_list_types_ResolvedType_ptr){ .data = (types_ResolvedType**)slop_arena_alloc(arena, 16 * sizeof(types_ResolvedType*)), .len = 0, .cap = 16 });
        __auto_type len = parser_sexpr_list_len(fn_form);
        for (int64_t i = 3; i < len; i++) {
            __auto_type _mv_1198 = parser_sexpr_list_get(fn_form, i);
            if (_mv_1198.has_value) {
                __auto_type item = _mv_1198.value;
                if (parser_is_form(item, SLOP_STR("@spec"))) {
                    __auto_type _mv_1199 = parser_sexpr_list_get(item, 1);
                    if (_mv_1199.has_value) {
                        __auto_type spec_body = _mv_1199.value;
                        if (parser_sexpr_is_list(spec_body)) {
                            __auto_type _mv_1200 = parser_sexpr_list_get(spec_body, 0);
                            if (_mv_1200.has_value) {
                                __auto_type param_types_expr = _mv_1200.value;
                                if (parser_sexpr_is_list(param_types_expr)) {
                                    {
                                        __auto_type num_ptypes = parser_sexpr_list_len(param_types_expr);
                                        for (int64_t j = 0; j < num_ptypes; j++) {
                                            __auto_type _mv_1201 = parser_sexpr_list_get(param_types_expr, j);
                                            if (_mv_1201.has_value) {
                                                __auto_type ptype_expr = _mv_1201.value;
                                                {
                                                    __auto_type pt = collect_get_field_type_generic(env, arena, ptype_expr, type_params);
                                                    ({ __auto_type _lst_p = &(spec_params); __auto_type _item = (pt); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                }
                                            } else if (!_mv_1201.has_value) {
                                            }
                                        }
                                    }
                                }
                            } else if (!_mv_1200.has_value) {
                            }
                        }
                    } else if (!_mv_1199.has_value) {
                    }
                }
            } else if (!_mv_1198.has_value) {
            }
        }
        return spec_params;
    }
}

void collect_set_module_name_from_form(env_TypeEnv* env, types_SExpr* module_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1202 = parser_sexpr_list_get(module_form, 1);
    if (_mv_1202.has_value) {
        __auto_type name_expr = _mv_1202.value;
        {
            __auto_type mod_name = parser_sexpr_get_symbol_name(name_expr);
            if (!(string_eq(mod_name, SLOP_STR("")))) {
                env_env_set_module(env, (slop_option_string){.has_value = 1, .value = mod_name});
            }
        }
    } else if (!_mv_1202.has_value) {
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
                    __auto_type _mv_1203 = parser_sexpr_list_get(module_form, i);
                    if (_mv_1203.has_value) {
                        __auto_type item = _mv_1203.value;
                        if (parser_is_form(item, SLOP_STR("type"))) {
                            collect_register_type_name(env, arena, item);
                        }
                    } else if (!_mv_1203.has_value) {
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
                    __auto_type _mv_1204 = parser_sexpr_list_get(module_form, i);
                    if (_mv_1204.has_value) {
                        __auto_type item = _mv_1204.value;
                        if (parser_is_form(item, SLOP_STR("type"))) {
                            collect_resolve_type_body(env, arena, item);
                        }
                    } else if (!_mv_1204.has_value) {
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
        __auto_type _mv_1205 = env_env_lookup_type_direct(env, type_name);
        if (_mv_1205.has_value) {
            __auto_type t = _mv_1205.value;
            return (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = t};
        } else if (!_mv_1205.has_value) {
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
        SLOP_UNREACHABLE();
    }
}

uint8_t collect_is_range_type_expr(types_SExpr* type_expr) {
    if (!(parser_sexpr_is_list(type_expr))) {
        return 0;
    } else {
        if (parser_sexpr_list_len(type_expr) < 2) {
            return 0;
        } else {
            __auto_type _mv_1206 = parser_sexpr_list_get(type_expr, 0);
            if (_mv_1206.has_value) {
                __auto_type first_elem = _mv_1206.value;
                {
                    __auto_type base_name = parser_sexpr_get_symbol_name(first_elem);
                    return (string_eq(base_name, SLOP_STR("Int")) || string_eq(base_name, SLOP_STR("Float")));
                }
            } else if (!_mv_1206.has_value) {
                return 0;
            }
            SLOP_UNREACHABLE();
        }
    }
}

types_ResolvedType* collect_get_range_base_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1207 = parser_sexpr_list_get(type_expr, 0);
    if (_mv_1207.has_value) {
        __auto_type first_elem = _mv_1207.value;
        {
            __auto_type base_name = parser_sexpr_get_symbol_name(first_elem);
            if (string_eq(base_name, SLOP_STR("Int"))) {
                return env_env_get_int_type(env);
            } else if (string_eq(base_name, SLOP_STR("Float"))) {
                __auto_type _mv_1208 = env_env_lookup_type_direct(env, SLOP_STR("Float"));
                if (_mv_1208.has_value) {
                    __auto_type t = _mv_1208.value;
                    return t;
                } else if (!_mv_1208.has_value) {
                    return env_env_get_int_type(env);
                }
                SLOP_UNREACHABLE();
            } else {
                return env_env_get_int_type(env);
            }
        }
    } else if (!_mv_1207.has_value) {
        return env_env_get_int_type(env);
    }
    SLOP_UNREACHABLE();
}

slop_string collect_get_type_name_from_expr(types_SExpr* expr) {
    __auto_type _mv_1209 = (*expr);
    switch (_mv_1209.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1209.data.sym;
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
                __auto_type _mv_1210 = parser_sexpr_list_get(union_expr, i);
                if (_mv_1210.has_value) {
                    __auto_type variant_form = _mv_1210.value;
                    collect_collect_single_union_variant(env, arena, resolved, variant_form, variant_idx);
                    variant_idx = (variant_idx + 1);
                } else if (!_mv_1210.has_value) {
                }
            }
        }
    }
}

slop_list_types_ResolvedType_ptr collect_get_variant_payload_types(env_TypeEnv* env, types_SExpr* variant_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((variant_form != NULL)), "(!= variant-form nil)");
    {
        __auto_type arena = env_env_arena(env);
        __auto_type result = ((slop_list_types_ResolvedType_ptr){ .data = (types_ResolvedType**)slop_arena_alloc(arena, 16 * sizeof(types_ResolvedType*)), .len = 0, .cap = 16 });
        __auto_type vlen = parser_sexpr_list_len(variant_form);
        for (int64_t idx = 1; idx < vlen; idx++) {
            __auto_type _mv_1211 = parser_sexpr_list_get(variant_form, idx);
            if (_mv_1211.has_value) {
                __auto_type type_expr = _mv_1211.value;
                ({ __auto_type _lst_p = &(result); __auto_type _item = (collect_get_field_type(env, arena, type_expr)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            } else if (!_mv_1211.has_value) {
            }
        }
        return result;
    }
}

slop_option_types_ResolvedType_ptr collect_get_variant_payload_type(env_TypeEnv* env, types_SExpr* variant_form) {
    if (parser_sexpr_list_len(variant_form) <= 1) {
        return (slop_option_types_ResolvedType_ptr){.has_value = false};
    } else {
        __auto_type _mv_1212 = parser_sexpr_list_get(variant_form, 1);
        if (_mv_1212.has_value) {
            __auto_type type_expr = _mv_1212.value;
            return (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = collect_get_field_type(env, env_env_arena(env), type_expr)};
        } else if (!_mv_1212.has_value) {
            return (slop_option_types_ResolvedType_ptr){.has_value = false};
        }
        SLOP_UNREACHABLE();
    }
}

slop_string collect_checker_get_variant_name(types_SExpr* variant_form) {
    if (parser_sexpr_is_list(variant_form)) {
        if (parser_sexpr_list_len(variant_form) == 0) {
            return SLOP_STR("");
        } else {
            __auto_type _mv_1213 = parser_sexpr_list_get(variant_form, 0);
            if (_mv_1213.has_value) {
                __auto_type name_expr = _mv_1213.value;
                return parser_sexpr_get_symbol_name(name_expr);
            } else if (!_mv_1213.has_value) {
                return SLOP_STR("");
            }
            SLOP_UNREACHABLE();
        }
    } else {
        __auto_type _mv_1214 = (*variant_form);
        switch (_mv_1214.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_1214.data.sym;
                return sym.name;
            }
            default: {
                return SLOP_STR("");
            }
        }
    }
}

uint8_t collect_check_type_expr_recursive(types_SExpr* type_expr, slop_string union_name) {
    SLOP_PRE(((type_expr != NULL)), "(!= type-expr nil)");
    __auto_type _mv_1215 = (*type_expr);
    switch (_mv_1215.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1215.data.sym;
            return string_eq(sym.name, union_name);
        }
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1215.data.lst;
            {
                __auto_type items = lst.items;
                if (((int64_t)((items).len)) < 2) {
                    return 0;
                } else {
                    __auto_type _mv_1216 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1216.has_value) {
                        __auto_type head = _mv_1216.value;
                        __auto_type _mv_1217 = (*head);
                        switch (_mv_1217.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1217.data.sym;
                                if (string_eq(sym.name, SLOP_STR("Option"))) {
                                    __auto_type _mv_1218 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                    if (_mv_1218.has_value) {
                                        __auto_type inner = _mv_1218.value;
                                        return string_eq(parser_sexpr_get_symbol_name(inner), union_name);
                                    } else if (!_mv_1218.has_value) {
                                        return 0;
                                    }
                                    SLOP_UNREACHABLE();
                                } else {
                                    return 0;
                                }
                            }
                            default: {
                                return 0;
                            }
                        }
                    } else if (!_mv_1216.has_value) {
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

uint8_t collect_has_recursive_value_payload(types_SExpr* variant_form, slop_string union_name) {
    SLOP_PRE(((variant_form != NULL)), "(!= variant-form nil)");
    {
        __auto_type vlen = parser_sexpr_list_len(variant_form);
        uint8_t found = 0;
        for (int64_t idx = 1; idx < vlen; idx++) {
            if (!(found)) {
                __auto_type _mv_1219 = parser_sexpr_list_get(variant_form, idx);
                if (_mv_1219.has_value) {
                    __auto_type type_expr = _mv_1219.value;
                    if (collect_check_type_expr_recursive(type_expr, union_name)) {
                        found = 1;
                    }
                } else if (!_mv_1219.has_value) {
                }
            }
        }
        return found;
    }
}

void collect_collect_single_union_variant(env_TypeEnv* env, slop_arena* arena, types_ResolvedType* resolved, types_SExpr* variant_form, int64_t variant_idx) {
    {
        __auto_type vname = collect_checker_get_variant_name(variant_form);
        __auto_type type_name = (*resolved).name;
        __auto_type arena = env_env_arena(env);
        if (!(string_eq(vname, SLOP_STR("")))) {
            if (collect_has_recursive_value_payload(variant_form, type_name)) {
                {
                    __auto_type parts = ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("recursive union variant '")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (vname); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("' in type '")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (type_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR("' would create infinite-size struct; use (Ptr ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (type_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(") or (List ")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (type_name); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    ({ __auto_type _lst_p = &(parts); __auto_type _item = (SLOP_STR(") instead")); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                    env_env_add_error(env, strlib_string_build(arena, parts), parser_sexpr_line(variant_form), parser_sexpr_col(variant_form));
                }
            }
            if (collect_is_reserved_variant_name(vname)) {
                {
                    __auto_type msg = string_concat(arena, SLOP_STR("union variant '"), string_concat(arena, vname, string_concat(arena, SLOP_STR("' in type '"), string_concat(arena, type_name, SLOP_STR("' shadows built-in form")))));
                    env_env_add_warning(env, msg, parser_sexpr_line(variant_form), parser_sexpr_col(variant_form));
                }
            }
            {
                __auto_type payload_type = collect_get_variant_payload_type(env, variant_form);
                __auto_type payload_types = collect_get_variant_payload_types(env, variant_form);
                __auto_type v = types_resolved_variant_new(arena, vname, variant_idx, vname, payload_type, payload_types);
                ({ __auto_type _lst_p = &((*resolved).variants); __auto_type _item = ((*v)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                env_env_register_variant(env, vname, type_name);
            }
        }
    }
}

void collect_collect_enum_variants(env_TypeEnv* env, slop_string enum_name, types_SExpr* enum_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((enum_expr != NULL)), "(!= enum-expr nil)");
    __auto_type _mv_1220 = (*enum_expr);
    switch (_mv_1220.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_1220.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                for (int64_t i = 1; i < len; i++) {
                    __auto_type _mv_1221 = ({ __auto_type _lst = items; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_1221.has_value) {
                        __auto_type variant_expr = _mv_1221.value;
                        __auto_type _mv_1222 = (*variant_expr);
                        switch (_mv_1222.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type sym = _mv_1222.data.sym;
                                env_env_register_variant(env, sym.name, enum_name);
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_1221.has_value) {
                    }
                }
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
            __auto_type _mv_1223 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1223.has_value) {
                __auto_type expr = _mv_1223.value;
                if (parser_is_form(expr, SLOP_STR("const"))) {
                    collect_collect_single_constant(env, arena, expr);
                } else if (parser_is_form(expr, SLOP_STR("module"))) {
                    collect_collect_module_constants(env, expr);
                } else {
                }
            } else if (!_mv_1223.has_value) {
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
                    __auto_type _mv_1224 = parser_sexpr_list_get(module_form, i);
                    if (_mv_1224.has_value) {
                        __auto_type item = _mv_1224.value;
                        if (parser_is_form(item, SLOP_STR("const"))) {
                            collect_collect_single_constant(env, arena, item);
                        }
                    } else if (!_mv_1224.has_value) {
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
        if (parser_sexpr_list_len(const_form) >= 3) {
            __auto_type _mv_1225 = parser_sexpr_list_get(const_form, 1);
            if (_mv_1225.has_value) {
                __auto_type name_expr = _mv_1225.value;
                {
                    __auto_type const_name = parser_sexpr_get_symbol_name(name_expr);
                    if (!(string_eq(const_name, SLOP_STR("")))) {
                        __auto_type _mv_1226 = parser_sexpr_list_get(const_form, 2);
                        if (_mv_1226.has_value) {
                            __auto_type type_expr = _mv_1226.value;
                            {
                                __auto_type const_type = collect_get_const_type(env, arena, type_expr);
                                env_env_register_constant(env, const_name, const_type);
                            }
                        } else if (!_mv_1226.has_value) {
                        }
                    }
                }
            } else if (!_mv_1225.has_value) {
            }
        }
    }
}

types_ResolvedType* collect_get_const_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1227 = (*type_expr);
    switch (_mv_1227.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_1227.data.sym;
            {
                __auto_type type_name = sym.name;
                __auto_type _mv_1228 = env_env_lookup_type_direct(env, type_name);
                if (_mv_1228.has_value) {
                    __auto_type t = _mv_1228.value;
                    return t;
                } else if (!_mv_1228.has_value) {
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
                SLOP_UNREACHABLE();
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
            __auto_type _mv_1229 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1229.has_value) {
                __auto_type expr = _mv_1229.value;
                if (parser_is_form(expr, SLOP_STR("fn"))) {
                    collect_collect_single_function(env, arena, expr);
                } else if (parser_is_form(expr, SLOP_STR("module"))) {
                    collect_collect_module_functions(env, expr);
                } else {
                }
            } else if (!_mv_1229.has_value) {
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
            __auto_type _mv_1230 = parser_sexpr_list_get(module_form, 1);
            if (_mv_1230.has_value) {
                __auto_type name_expr = _mv_1230.value;
                {
                    __auto_type mod_name = parser_sexpr_get_symbol_name(name_expr);
                    if (!(string_eq(mod_name, SLOP_STR("")))) {
                        env_env_set_module(env, (slop_option_string){.has_value = 1, .value = mod_name});
                    }
                }
            } else if (!_mv_1230.has_value) {
            }
            {
                __auto_type len = parser_sexpr_list_len(module_form);
                for (int64_t i = 2; i < len; i++) {
                    __auto_type _mv_1231 = parser_sexpr_list_get(module_form, i);
                    if (_mv_1231.has_value) {
                        __auto_type item = _mv_1231.value;
                        if (parser_is_form(item, SLOP_STR("fn"))) {
                            collect_collect_single_function(env, arena, item);
                        } else if (parser_is_form(item, SLOP_STR("ffi"))) {
                            collect_collect_ffi_functions(env, arena, item);
                        } else if (parser_is_form(item, SLOP_STR("ffi-struct"))) {
                            __auto_type _mv_1232 = parser_sexpr_list_get(item, 2);
                            if (_mv_1232.has_value) {
                                __auto_type name_expr = _mv_1232.value;
                                {
                                    __auto_type struct_name = parser_sexpr_get_symbol_name(name_expr);
                                    if (collect_is_reserved_builtin_name(struct_name)) {
                                        collect_report_reserved_name(env, struct_name, SLOP_STR("foreign struct"), parser_sexpr_line(name_expr), parser_sexpr_col(name_expr));
                                    }
                                }
                            } else if (!_mv_1232.has_value) {
                            }
                        } else {
                        }
                    } else if (!_mv_1231.has_value) {
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
                __auto_type _mv_1233 = parser_sexpr_list_get(ffi_form, i);
                if (_mv_1233.has_value) {
                    __auto_type func_decl = _mv_1233.value;
                    collect_collect_ffi_function(env, arena, func_decl);
                } else if (!_mv_1233.has_value) {
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
            if (decl_len >= 3) {
                __auto_type _mv_1234 = parser_sexpr_list_get(func_decl, 0);
                if (_mv_1234.has_value) {
                    __auto_type name_expr = _mv_1234.value;
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
                                (*sig).is_variadic = collect_ffi_has_variadic(func_decl);
                                if (collect_is_reserved_builtin_name(fn_name)) {
                                    collect_report_reserved_name(env, fn_name, SLOP_STR("foreign function"), parser_sexpr_line(func_decl), parser_sexpr_col(func_decl));
                                }
                                env_env_register_function(env, sig);
                            }
                        }
                    }
                } else if (!_mv_1234.has_value) {
                }
            } else if (decl_len == 2) {
                __auto_type _mv_1235 = parser_sexpr_list_get(func_decl, 0);
                if (_mv_1235.has_value) {
                    __auto_type name_expr = _mv_1235.value;
                    {
                        __auto_type const_name = parser_sexpr_get_symbol_name(name_expr);
                        if (!(string_eq(const_name, SLOP_STR("")))) {
                            __auto_type _mv_1236 = parser_sexpr_list_get(func_decl, 1);
                            if (_mv_1236.has_value) {
                                __auto_type type_expr = _mv_1236.value;
                                {
                                    __auto_type const_type = collect_get_field_type(env, arena, type_expr);
                                    env_env_register_constant(env, const_name, const_type);
                                }
                            } else if (!_mv_1236.has_value) {
                            }
                        }
                    }
                } else if (!_mv_1235.has_value) {
                }
            } else {
            }
        }
    }
}

uint8_t collect_ffi_has_variadic(types_SExpr* func_decl) {
    SLOP_PRE(((func_decl != NULL)), "(!= func-decl nil)");
    {
        __auto_type len = parser_sexpr_list_len(func_decl);
        if (len >= 4) {
            __auto_type _mv_1237 = parser_sexpr_list_get(func_decl, (len - 1));
            if (_mv_1237.has_value) {
                __auto_type last_expr = _mv_1237.value;
                return string_eq(parser_sexpr_get_symbol_name(last_expr), SLOP_STR(":variadic"));
            } else if (!_mv_1237.has_value) {
                return 0;
            }
            SLOP_UNREACHABLE();
        } else {
            return 0;
        }
    }
}

slop_list_types_ParamInfo collect_collect_ffi_params(env_TypeEnv* env, slop_arena* arena, types_SExpr* func_decl) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type params = ((slop_list_types_ParamInfo){ .data = (types_ParamInfo*)slop_arena_alloc(arena, 16 * sizeof(types_ParamInfo)), .len = 0, .cap = 16 });
        __auto_type _mv_1238 = parser_sexpr_list_get(func_decl, 1);
        if (_mv_1238.has_value) {
            __auto_type params_expr = _mv_1238.value;
            if (parser_sexpr_is_list(params_expr)) {
                {
                    __auto_type num_params = parser_sexpr_list_len(params_expr);
                    for (int64_t j = 0; j < num_params; j++) {
                        __auto_type _mv_1239 = parser_sexpr_list_get(params_expr, j);
                        if (_mv_1239.has_value) {
                            __auto_type param_form = _mv_1239.value;
                            if (parser_sexpr_is_list(param_form)) {
                                if (parser_sexpr_list_len(param_form) >= 2) {
                                    __auto_type _mv_1240 = parser_sexpr_list_get(param_form, 0);
                                    if (_mv_1240.has_value) {
                                        __auto_type pname_expr = _mv_1240.value;
                                        {
                                            __auto_type param_name = parser_sexpr_get_symbol_name(pname_expr);
                                            if (!(string_eq(param_name, SLOP_STR("")))) {
                                                __auto_type _mv_1241 = parser_sexpr_list_get(param_form, 1);
                                                if (_mv_1241.has_value) {
                                                    __auto_type ptype_expr = _mv_1241.value;
                                                    {
                                                        __auto_type param_type = collect_get_field_type(env, arena, ptype_expr);
                                                        __auto_type info = types_param_info_new(arena, param_name, param_type);
                                                        ({ __auto_type _lst_p = &(params); __auto_type _item = ((*info)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                    }
                                                } else if (!_mv_1241.has_value) {
                                                }
                                            }
                                        }
                                    } else if (!_mv_1240.has_value) {
                                    }
                                }
                            }
                        } else if (!_mv_1239.has_value) {
                        }
                    }
                }
            }
        } else if (!_mv_1238.has_value) {
        }
        return params;
    }
}

types_ResolvedType* collect_get_ffi_return_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* func_decl) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1242 = parser_sexpr_list_get(func_decl, 2);
    if (_mv_1242.has_value) {
        __auto_type ret_expr = _mv_1242.value;
        return collect_get_field_type(env, arena, ret_expr);
    } else if (!_mv_1242.has_value) {
        return env_env_get_unit_type(env);
    }
    SLOP_UNREACHABLE();
}

void collect_collect_single_function(env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    if (parser_sexpr_is_list(fn_form)) {
        if (parser_sexpr_list_len(fn_form) >= 3) {
            __auto_type _mv_1243 = parser_sexpr_list_get(fn_form, 1);
            if (_mv_1243.has_value) {
                __auto_type name_expr = _mv_1243.value;
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
                            if (collect_is_reserved_builtin_name(fn_name)) {
                                collect_report_reserved_name(env, fn_name, SLOP_STR("function"), parser_sexpr_line(fn_form), parser_sexpr_col(fn_form));
                            }
                            env_env_register_function(env, sig);
                        }
                    }
                }
            } else if (!_mv_1243.has_value) {
            }
        }
    }
}

uint8_t collect_is_reserved_builtin_name(slop_string name) {
    return (string_eq(name, SLOP_STR("is-none")) || string_eq(name, SLOP_STR("is-some")));
}

void collect_report_reserved_name(env_TypeEnv* env, slop_string name, slop_string what, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type arena = env_env_arena(env);
        __auto_type msg = string_concat(arena, SLOP_STR("'"), string_concat(arena, name, string_concat(arena, SLOP_STR("' is a builtin predicate and cannot be redefined as a "), string_concat(arena, what, SLOP_STR(" - rename it, or use match if you want the payload")))));
        env_env_add_error(env, msg, line, col);
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
        if (num_params == 0) {
        } else if (num_params == 2) {
            __auto_type _mv_1244 = ({ __auto_type _lst = params; size_t _idx = (size_t)0; slop_option_types_ParamInfo _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1244.has_value) {
                __auto_type p0 = _mv_1244.value;
                {
                    __auto_type t0 = p0.param_type;
                    if (t0 != NULL) {
                        {
                            __auto_type name0 = (*t0).name;
                            if (!(collect_is_integer_type_name(name0))) {
                                env_env_add_error(env, SLOP_STR("main's first parameter must be an integer type (e.g., Int for argc)"), line, col);
                            }
                        }
                    }
                }
            } else if (!_mv_1244.has_value) {
            }
            __auto_type _mv_1245 = ({ __auto_type _lst = params; size_t _idx = (size_t)1; slop_option_types_ParamInfo _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1245.has_value) {
                __auto_type p1 = _mv_1245.value;
                {
                    __auto_type t1 = p1.param_type;
                    if (t1 != NULL) {
                        if (!(types_resolved_type_is_pointer(t1))) {
                            env_env_add_error(env, SLOP_STR("main's second parameter must be a pointer type (e.g., (Ptr (Ptr U8)) for argv)"), line, col);
                        }
                    }
                }
            } else if (!_mv_1245.has_value) {
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
        __auto_type _mv_1246 = parser_sexpr_list_get(fn_form, 2);
        if (_mv_1246.has_value) {
            __auto_type params_expr = _mv_1246.value;
            if (parser_sexpr_is_list(params_expr)) {
                {
                    __auto_type num_params = parser_sexpr_list_len(params_expr);
                    for (int64_t i = 0; i < num_params; i++) {
                        __auto_type _mv_1247 = parser_sexpr_list_get(params_expr, i);
                        if (_mv_1247.has_value) {
                            __auto_type param_form = _mv_1247.value;
                            if (parser_sexpr_is_list(param_form) && (parser_sexpr_list_len(param_form) >= 2)) {
                                __auto_type _mv_1248 = parser_sexpr_list_get(param_form, 0);
                                if (_mv_1248.has_value) {
                                    __auto_type first_expr = _mv_1248.value;
                                    {
                                        __auto_type first_name = parser_sexpr_get_symbol_name(first_expr);
                                        if ((string_eq(first_name, SLOP_STR("in"))) || (string_eq(first_name, SLOP_STR("out"))) || (string_eq(first_name, SLOP_STR("mut")))) {
                                            if (parser_sexpr_list_len(param_form) >= 3) {
                                                __auto_type _mv_1249 = parser_sexpr_list_get(param_form, 1);
                                                if (_mv_1249.has_value) {
                                                    __auto_type name_expr = _mv_1249.value;
                                                    {
                                                        __auto_type param_name = parser_sexpr_get_symbol_name(name_expr);
                                                        if (!(string_eq(param_name, SLOP_STR("")))) {
                                                            __auto_type _mv_1250 = parser_sexpr_list_get(param_form, 2);
                                                            if (_mv_1250.has_value) {
                                                                __auto_type type_expr = _mv_1250.value;
                                                                {
                                                                    __auto_type param_type = collect_get_field_type(env, arena, type_expr);
                                                                    __auto_type info = types_param_info_new(arena, param_name, param_type);
                                                                    ({ __auto_type _lst_p = &(params); __auto_type _item = ((*info)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                                }
                                                            } else if (!_mv_1250.has_value) {
                                                            }
                                                        }
                                                    }
                                                } else if (!_mv_1249.has_value) {
                                                }
                                            }
                                        } else {
                                            if (!(string_eq(first_name, SLOP_STR("")))) {
                                                __auto_type _mv_1251 = parser_sexpr_list_get(param_form, 1);
                                                if (_mv_1251.has_value) {
                                                    __auto_type type_expr = _mv_1251.value;
                                                    {
                                                        __auto_type param_type = collect_get_field_type(env, arena, type_expr);
                                                        __auto_type info = types_param_info_new(arena, first_name, param_type);
                                                        ({ __auto_type _lst_p = &(params); __auto_type _item = ((*info)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                    }
                                                } else if (!_mv_1251.has_value) {
                                                }
                                            }
                                        }
                                    }
                                } else if (!_mv_1248.has_value) {
                                }
                            }
                        } else if (!_mv_1247.has_value) {
                        }
                    }
                }
            }
        } else if (!_mv_1246.has_value) {
        }
        return params;
    }
}

slop_list_types_ParamInfo collect_collect_fn_params_generic(env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form, slop_list_string type_params) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    {
        __auto_type params = ((slop_list_types_ParamInfo){ .data = (types_ParamInfo*)slop_arena_alloc(arena, 16 * sizeof(types_ParamInfo)), .len = 0, .cap = 16 });
        __auto_type _mv_1252 = parser_sexpr_list_get(fn_form, 2);
        if (_mv_1252.has_value) {
            __auto_type params_expr = _mv_1252.value;
            if (parser_sexpr_is_list(params_expr)) {
                {
                    __auto_type num_params = parser_sexpr_list_len(params_expr);
                    for (int64_t i = 0; i < num_params; i++) {
                        __auto_type _mv_1253 = parser_sexpr_list_get(params_expr, i);
                        if (_mv_1253.has_value) {
                            __auto_type param_form = _mv_1253.value;
                            if (parser_sexpr_is_list(param_form) && (parser_sexpr_list_len(param_form) >= 2)) {
                                __auto_type _mv_1254 = parser_sexpr_list_get(param_form, 0);
                                if (_mv_1254.has_value) {
                                    __auto_type first_expr = _mv_1254.value;
                                    {
                                        __auto_type first_name = parser_sexpr_get_symbol_name(first_expr);
                                        if ((string_eq(first_name, SLOP_STR("in"))) || (string_eq(first_name, SLOP_STR("out"))) || (string_eq(first_name, SLOP_STR("mut")))) {
                                            if (parser_sexpr_list_len(param_form) >= 3) {
                                                __auto_type _mv_1255 = parser_sexpr_list_get(param_form, 1);
                                                if (_mv_1255.has_value) {
                                                    __auto_type name_expr = _mv_1255.value;
                                                    {
                                                        __auto_type param_name = parser_sexpr_get_symbol_name(name_expr);
                                                        if (!(string_eq(param_name, SLOP_STR("")))) {
                                                            __auto_type _mv_1256 = parser_sexpr_list_get(param_form, 2);
                                                            if (_mv_1256.has_value) {
                                                                __auto_type type_expr = _mv_1256.value;
                                                                {
                                                                    __auto_type param_type = collect_get_field_type_generic(env, arena, type_expr, type_params);
                                                                    __auto_type info = types_param_info_new(arena, param_name, param_type);
                                                                    ({ __auto_type _lst_p = &(params); __auto_type _item = ((*info)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                                }
                                                            } else if (!_mv_1256.has_value) {
                                                            }
                                                        }
                                                    }
                                                } else if (!_mv_1255.has_value) {
                                                }
                                            }
                                        } else {
                                            if (!(string_eq(first_name, SLOP_STR("")))) {
                                                __auto_type _mv_1257 = parser_sexpr_list_get(param_form, 1);
                                                if (_mv_1257.has_value) {
                                                    __auto_type type_expr = _mv_1257.value;
                                                    {
                                                        __auto_type param_type = collect_get_field_type_generic(env, arena, type_expr, type_params);
                                                        __auto_type info = types_param_info_new(arena, first_name, param_type);
                                                        ({ __auto_type _lst_p = &(params); __auto_type _item = ((*info)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                    }
                                                } else if (!_mv_1257.has_value) {
                                                }
                                            }
                                        }
                                    }
                                } else if (!_mv_1254.has_value) {
                                }
                            }
                        } else if (!_mv_1253.has_value) {
                        }
                    }
                }
            }
        } else if (!_mv_1252.has_value) {
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
            __auto_type _mv_1258 = parser_sexpr_list_get(fn_form, i);
            if (_mv_1258.has_value) {
                __auto_type item = _mv_1258.value;
                if (parser_is_form(item, SLOP_STR("@spec"))) {
                    if (!(found)) {
                        found_type = collect_checker_extract_spec_return_type(env, item);
                        found = 1;
                    }
                }
            } else if (!_mv_1258.has_value) {
            }
        }
        return found_type;
    }
}

types_ResolvedType* collect_checker_extract_spec_return_type(env_TypeEnv* env, types_SExpr* spec_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type arena = env_env_arena(env);
        __auto_type _mv_1259 = parser_sexpr_list_get(spec_form, 1);
        if (_mv_1259.has_value) {
            __auto_type spec_body = _mv_1259.value;
            if (parser_sexpr_is_list(spec_body)) {
                {
                    __auto_type len = parser_sexpr_list_len(spec_body);
                    __auto_type _mv_1260 = parser_sexpr_list_get(spec_body, (len - 1));
                    if (_mv_1260.has_value) {
                        __auto_type ret_expr = _mv_1260.value;
                        return collect_get_field_type(env, arena, ret_expr);
                    } else if (!_mv_1260.has_value) {
                        return env_env_get_unit_type(env);
                    }
                    SLOP_UNREACHABLE();
                }
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (!_mv_1259.has_value) {
            return env_env_get_unit_type(env);
        }
        SLOP_UNREACHABLE();
    }
}

