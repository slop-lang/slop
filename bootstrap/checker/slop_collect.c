#include "../runtime/slop_runtime.h"
#include "slop_collect.h"

void collect_collect_module(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void collect_collect_types(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void collect_collect_type_def(env_TypeEnv* env, slop_arena* arena, types_SExpr* expr);
void collect_collect_record_fields(env_TypeEnv* env, slop_arena* arena, types_ResolvedType* resolved, types_SExpr* record_expr);
types_SExpr* collect_get_type_arg(types_SExpr* type_expr, int64_t idx);
types_ResolvedType* collect_get_field_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr);
void collect_collect_module_types(env_TypeEnv* env, types_SExpr* module_form);
slop_option_types_ResolvedType_ptr collect_lookup_payload_type(env_TypeEnv* env, slop_string type_name);
uint8_t collect_is_range_type_expr(types_SExpr* type_expr);
types_ResolvedType* collect_get_range_base_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr);
slop_string collect_get_type_name_from_expr(types_SExpr* expr);
uint8_t collect_is_reserved_variant_name(slop_string name);
void collect_collect_union_variants(env_TypeEnv* env, slop_arena* arena, types_ResolvedType* resolved, types_SExpr* union_expr);
slop_option_types_ResolvedType_ptr collect_get_variant_payload_type(env_TypeEnv* env, types_SExpr* variant_form);
slop_string collect_get_variant_name(types_SExpr* variant_form);
void collect_collect_single_union_variant(env_TypeEnv* env, slop_arena* arena, types_ResolvedType* resolved, types_SExpr* variant_form, int64_t variant_idx);
void collect_collect_enum_variants(env_TypeEnv* env, slop_string enum_name, types_SExpr* enum_expr);
void collect_collect_constants(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void collect_collect_module_constants(env_TypeEnv* env, types_SExpr* module_form);
void collect_collect_single_constant(env_TypeEnv* env, slop_arena* arena, types_SExpr* const_form);
types_ResolvedType* collect_get_const_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr);
void collect_collect_functions(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void collect_collect_module_functions(env_TypeEnv* env, types_SExpr* module_form);
void collect_collect_single_function(env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form);
slop_list_types_ParamInfo collect_collect_fn_params(env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form);
types_ResolvedType* collect_find_fn_return_type(env_TypeEnv* env, types_SExpr* fn_form);
types_ResolvedType* collect_extract_spec_return_type(env_TypeEnv* env, types_SExpr* spec_form);

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
            __auto_type _mv_193 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_193.has_value) {
                __auto_type expr = _mv_193.value;
                if (parser_is_form(expr, SLOP_STR("type"))) {
                    collect_collect_type_def(env, arena, expr);
                } else if (parser_is_form(expr, SLOP_STR("module"))) {
                    collect_collect_module_types(env, expr);
                } else {
                }
            } else if (!_mv_193.has_value) {
            }
        }
    }
}

void collect_collect_type_def(env_TypeEnv* env, slop_arena* arena, types_SExpr* expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_194 = (*expr);
    switch (_mv_194.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_194.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type _mv_195 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_195.has_value) {
                    __auto_type name_expr = _mv_195.value;
                    __auto_type _mv_196 = (*name_expr);
                    switch (_mv_196.tag) {
                        case types_SExpr_sym:
                        {
                            __auto_type sym = _mv_196.data.sym;
                            {
                                __auto_type type_name = sym.name;
                                __auto_type _mv_197 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_197.has_value) {
                                    __auto_type type_expr = _mv_197.value;
                                    if (parser_is_form(type_expr, SLOP_STR("enum"))) {
                                        {
                                            __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_enum, type_name, ((slop_option_string){.has_value = false}), type_name);
                                            env_env_register_type(env, resolved);
                                            collect_collect_enum_variants(env, type_name, type_expr);
                                        }
                                    } else if (parser_is_form(type_expr, SLOP_STR("record"))) {
                                        {
                                            __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_record, type_name, ((slop_option_string){.has_value = false}), type_name);
                                            env_env_register_type(env, resolved);
                                            collect_collect_record_fields(env, arena, resolved, type_expr);
                                        }
                                    } else if (parser_is_form(type_expr, SLOP_STR("union"))) {
                                        {
                                            __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_union, type_name, ((slop_option_string){.has_value = false}), type_name);
                                            env_env_register_type(env, resolved);
                                            collect_collect_union_variants(env, arena, resolved, type_expr);
                                        }
                                    } else if (collect_is_range_type_expr(type_expr)) {
                                        {
                                            __auto_type base_type = collect_get_range_base_type(env, arena, type_expr);
                                            __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_range, type_name, ((slop_option_string){.has_value = false}), type_name);
                                            types_resolved_type_set_inner(resolved, base_type);
                                            env_env_register_type(env, resolved);
                                        }
                                    } else if (parser_is_form(type_expr, SLOP_STR("Map"))) {
                                        {
                                            __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_map, type_name, ((slop_option_string){.has_value = false}), SLOP_STR("slop_map*"));
                                            __auto_type key_type = collect_get_field_type(env, arena, collect_get_type_arg(type_expr, 1));
                                            __auto_type val_type = collect_get_field_type(env, arena, collect_get_type_arg(type_expr, 2));
                                            types_resolved_type_set_inner(resolved, key_type);
                                            types_resolved_type_set_inner2(resolved, val_type);
                                            env_env_register_type(env, resolved);
                                        }
                                    } else if (parser_is_form(type_expr, SLOP_STR("Set"))) {
                                        {
                                            __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, type_name, ((slop_option_string){.has_value = false}), SLOP_STR("slop_map*"));
                                            __auto_type elem_type = collect_get_field_type(env, arena, collect_get_type_arg(type_expr, 1));
                                            types_resolved_type_set_inner(resolved, elem_type);
                                            env_env_register_type(env, resolved);
                                        }
                                    } else if (parser_is_form(type_expr, SLOP_STR("List"))) {
                                        {
                                            __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_list, type_name, ((slop_option_string){.has_value = false}), SLOP_STR("slop_list_t*"));
                                            __auto_type elem_type = collect_get_field_type(env, arena, collect_get_type_arg(type_expr, 1));
                                            types_resolved_type_set_inner(resolved, elem_type);
                                            env_env_register_type(env, resolved);
                                        }
                                    } else {
                                        {
                                            __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, type_name, ((slop_option_string){.has_value = false}), type_name);
                                            env_env_register_type(env, resolved);
                                        }
                                    }
                                } else if (!_mv_197.has_value) {
                                    {
                                        __auto_type resolved = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, type_name, ((slop_option_string){.has_value = false}), type_name);
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
                } else if (!_mv_195.has_value) {
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
    __auto_type _mv_198 = (*record_expr);
    switch (_mv_198.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_198.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                ({ for (int64_t i = 1; i < len; i++) { ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type field_form = _mv.value; ({ __auto_type _mv = (*field_form); switch (_mv.tag) { case types_SExpr_lst: { __auto_type field_lst = _mv.data.lst; ({ __auto_type field_items = field_lst.items; ({ __auto_type _mv = ({ __auto_type _lst = field_items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type name_expr = _mv.value; ({ __auto_type _mv = (*name_expr); switch (_mv.tag) { case types_SExpr_sym: { __auto_type name_sym = _mv.data.sym; ({ __auto_type _mv = ({ __auto_type _lst = field_items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type type_expr = _mv.value; ({ __auto_type field_name = name_sym.name; __auto_type field_type = collect_get_field_type(env, arena, type_expr); __auto_type field = types_resolved_field_new(arena, field_name, field_type, (i - 1)); ({ ({ __auto_type _lst_p = &((*resolved).fields); __auto_type _item = ((*field)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); }); }); } else { ({ (void)0; }); } (void)0; }); break; } default: { ({ (void)0; }); break; }  } (void)0; }); } else { ({ (void)0; }); } (void)0; }); }); break; } default: { ({ (void)0; }); break; }  } (void)0; }); } else { ({ (void)0; }); } (void)0; }); } 0; });
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
    __auto_type _mv_199 = (*type_expr);
    switch (_mv_199.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_199.data.lst;
            __auto_type _mv_200 = ({ __auto_type _lst = lst.items; size_t _idx = (size_t)idx; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_200.has_value) {
                __auto_type arg = _mv_200.value;
                return arg;
            } else if (!_mv_200.has_value) {
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
    __auto_type _mv_201 = (*type_expr);
    switch (_mv_201.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_201.data.sym;
            {
                __auto_type type_name = sym.name;
                __auto_type _mv_202 = env_env_lookup_type(env, type_name);
                if (_mv_202.has_value) {
                    __auto_type t = _mv_202.value;
                    return t;
                } else if (!_mv_202.has_value) {
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
            __auto_type lst = _mv_201.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type _mv_203 = ({ __auto_type _lst = items; size_t _idx = (size_t)0; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_203.has_value) {
                    __auto_type head_expr = _mv_203.value;
                    {
                        __auto_type head_name = parser_sexpr_get_symbol_name(head_expr);
                        if (string_eq(head_name, SLOP_STR("Option"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                return env_env_make_option_type(env, inner_type);
                            }
                        } else if (string_eq(head_name, SLOP_STR("Ptr"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
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
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type list_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_list, SLOP_STR("List"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_list_t*"));
                                    types_resolved_type_set_inner(list_type, inner_type);
                                    return list_type;
                                }
                            }
                        } else if (string_eq(head_name, SLOP_STR("Set"))) {
                            {
                                __auto_type inner_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type set_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Set"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_map*"));
                                    types_resolved_type_set_inner(set_type, inner_type);
                                    return set_type;
                                }
                            }
                        } else if (string_eq(head_name, SLOP_STR("Map"))) {
                            {
                                __auto_type key_type = (((((int64_t)((items).len)) >= 2)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                __auto_type val_type = (((((int64_t)((items).len)) >= 3)) ? ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); _mv.has_value ? ({ __auto_type inner_expr = _mv.value; collect_get_field_type(env, arena, inner_expr); }) : (env_env_get_int_type(env)); }) : env_env_get_int_type(env));
                                {
                                    __auto_type map_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_map, SLOP_STR("Map"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_map*"));
                                    types_resolved_type_set_inner(map_type, key_type);
                                    types_resolved_type_set_inner2(map_type, val_type);
                                    return map_type;
                                }
                            }
                        } else {
                            return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, head_name, ((slop_option_string){.has_value = false}), head_name);
                        }
                    }
                } else if (!_mv_203.has_value) {
                    return env_env_get_unit_type(env);
                }
            }
        }
        default: {
            return env_env_get_unit_type(env);
        }
    }
}

void collect_collect_module_types(env_TypeEnv* env, types_SExpr* module_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((module_form != NULL)), "(!= module-form nil)");
    {
        __auto_type arena = env_env_arena(env);
        __auto_type _mv_204 = (*module_form);
        switch (_mv_204.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_204.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type len = ((int64_t)((items).len));
                    ({ for (int64_t i = 2; i < len; i++) { ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type item = _mv.value; ((parser_is_form(item, SLOP_STR("type"))) ? ({ collect_collect_type_def(env, arena, item); 0; }) : ({ (void)0; })); } else { ({ (void)0; }); } (void)0; }); } 0; });
                }
                break;
            }
            default: {
                break;
            }
        }
    }
}

slop_option_types_ResolvedType_ptr collect_lookup_payload_type(env_TypeEnv* env, slop_string type_name) {
    if (string_eq(type_name, SLOP_STR(""))) {
        return (slop_option_types_ResolvedType_ptr){.has_value = false};
    } else {
        __auto_type _mv_205 = env_env_lookup_type(env, type_name);
        if (_mv_205.has_value) {
            __auto_type t = _mv_205.value;
            return (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = t};
        } else if (!_mv_205.has_value) {
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
            __auto_type _mv_206 = parser_sexpr_list_get(type_expr, 0);
            if (_mv_206.has_value) {
                __auto_type first_elem = _mv_206.value;
                {
                    __auto_type base_name = parser_sexpr_get_symbol_name(first_elem);
                    return (string_eq(base_name, SLOP_STR("Int")) || string_eq(base_name, SLOP_STR("Float")));
                }
            } else if (!_mv_206.has_value) {
                return 0;
            }
        }
    }
}

types_ResolvedType* collect_get_range_base_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_207 = parser_sexpr_list_get(type_expr, 0);
    if (_mv_207.has_value) {
        __auto_type first_elem = _mv_207.value;
        {
            __auto_type base_name = parser_sexpr_get_symbol_name(first_elem);
            if (string_eq(base_name, SLOP_STR("Int"))) {
                return env_env_get_int_type(env);
            } else if (string_eq(base_name, SLOP_STR("Float"))) {
                __auto_type _mv_208 = env_env_lookup_type(env, SLOP_STR("Float"));
                if (_mv_208.has_value) {
                    __auto_type t = _mv_208.value;
                    return t;
                } else if (!_mv_208.has_value) {
                    return env_env_get_int_type(env);
                }
            } else {
                return env_env_get_int_type(env);
            }
        }
    } else if (!_mv_207.has_value) {
        return env_env_get_int_type(env);
    }
}

slop_string collect_get_type_name_from_expr(types_SExpr* expr) {
    __auto_type _mv_209 = (*expr);
    switch (_mv_209.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_209.data.sym;
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
            __auto_type variant_idx = 0;
            for (int64_t i = 1; i < len; i++) {
                __auto_type _mv_210 = parser_sexpr_list_get(union_expr, i);
                if (_mv_210.has_value) {
                    __auto_type variant_form = _mv_210.value;
                    collect_collect_single_union_variant(env, arena, resolved, variant_form, variant_idx);
                    variant_idx = (variant_idx + 1);
                } else if (!_mv_210.has_value) {
                }
            }
        }
    }
}

slop_option_types_ResolvedType_ptr collect_get_variant_payload_type(env_TypeEnv* env, types_SExpr* variant_form) {
    if ((parser_sexpr_list_len(variant_form) <= 1)) {
        return (slop_option_types_ResolvedType_ptr){.has_value = false};
    } else {
        __auto_type _mv_211 = parser_sexpr_list_get(variant_form, 1);
        if (_mv_211.has_value) {
            __auto_type type_expr = _mv_211.value;
            return collect_lookup_payload_type(env, parser_sexpr_get_symbol_name(type_expr));
        } else if (!_mv_211.has_value) {
            return (slop_option_types_ResolvedType_ptr){.has_value = false};
        }
    }
}

slop_string collect_get_variant_name(types_SExpr* variant_form) {
    if (parser_sexpr_is_list(variant_form)) {
        if ((parser_sexpr_list_len(variant_form) == 0)) {
            return SLOP_STR("");
        } else {
            __auto_type _mv_212 = parser_sexpr_list_get(variant_form, 0);
            if (_mv_212.has_value) {
                __auto_type name_expr = _mv_212.value;
                return parser_sexpr_get_symbol_name(name_expr);
            } else if (!_mv_212.has_value) {
                return SLOP_STR("");
            }
        }
    } else {
        __auto_type _mv_213 = (*variant_form);
        switch (_mv_213.tag) {
            case types_SExpr_sym:
            {
                __auto_type sym = _mv_213.data.sym;
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
        __auto_type variant_name = collect_get_variant_name(variant_form);
        __auto_type type_name = (*resolved).name;
        __auto_type arena = env_env_arena(env);
        if (!(string_eq(variant_name, SLOP_STR("")))) {
            if (collect_is_reserved_variant_name(variant_name)) {
                {
                    __auto_type msg = string_concat(arena, SLOP_STR("union variant '"), string_concat(arena, variant_name, string_concat(arena, SLOP_STR("' in type '"), string_concat(arena, type_name, SLOP_STR("' shadows built-in form")))));
                    env_env_add_warning(env, msg, parser_sexpr_line(variant_form), parser_sexpr_col(variant_form));
                }
            }
            {
                __auto_type payload_type = collect_get_variant_payload_type(env, variant_form);
                __auto_type variant = types_resolved_variant_new(arena, variant_name, variant_idx, variant_name, payload_type);
                ({ __auto_type _lst_p = &((*resolved).variants); __auto_type _item = ((*variant)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                env_env_register_variant(env, variant_name, type_name);
            }
        }
    }
}

void collect_collect_enum_variants(env_TypeEnv* env, slop_string enum_name, types_SExpr* enum_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((enum_expr != NULL)), "(!= enum-expr nil)");
    __auto_type _mv_214 = (*enum_expr);
    switch (_mv_214.tag) {
        case types_SExpr_lst:
        {
            __auto_type lst = _mv_214.data.lst;
            {
                __auto_type items = lst.items;
                __auto_type len = ((int64_t)((items).len));
                ({ for (int64_t i = 1; i < len; i++) { ({ __auto_type _mv = ({ __auto_type _lst = items; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type variant_expr = _mv.value; ({ __auto_type _mv = (*variant_expr); switch (_mv.tag) { case types_SExpr_sym: { __auto_type sym = _mv.data.sym; ({ env_env_register_variant(env, sym.name, enum_name); }); break; } default: { ({ (void)0; }); break; }  } (void)0; }); } else { ({ (void)0; }); } (void)0; }); } 0; });
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
            __auto_type _mv_215 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_215.has_value) {
                __auto_type expr = _mv_215.value;
                if (parser_is_form(expr, SLOP_STR("const"))) {
                    collect_collect_single_constant(env, arena, expr);
                } else if (parser_is_form(expr, SLOP_STR("module"))) {
                    collect_collect_module_constants(env, expr);
                } else {
                }
            } else if (!_mv_215.has_value) {
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
                    __auto_type _mv_216 = parser_sexpr_list_get(module_form, i);
                    if (_mv_216.has_value) {
                        __auto_type item = _mv_216.value;
                        if (parser_is_form(item, SLOP_STR("const"))) {
                            collect_collect_single_constant(env, arena, item);
                        }
                    } else if (!_mv_216.has_value) {
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
            __auto_type _mv_217 = parser_sexpr_list_get(const_form, 1);
            if (_mv_217.has_value) {
                __auto_type name_expr = _mv_217.value;
                {
                    __auto_type const_name = parser_sexpr_get_symbol_name(name_expr);
                    if (!(string_eq(const_name, SLOP_STR("")))) {
                        __auto_type _mv_218 = parser_sexpr_list_get(const_form, 2);
                        if (_mv_218.has_value) {
                            __auto_type type_expr = _mv_218.value;
                            {
                                __auto_type const_type = collect_get_const_type(env, arena, type_expr);
                                env_env_register_constant(env, const_name, const_type);
                            }
                        } else if (!_mv_218.has_value) {
                        }
                    }
                }
            } else if (!_mv_217.has_value) {
            }
        }
    }
}

types_ResolvedType* collect_get_const_type(env_TypeEnv* env, slop_arena* arena, types_SExpr* type_expr) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_219 = (*type_expr);
    switch (_mv_219.tag) {
        case types_SExpr_sym:
        {
            __auto_type sym = _mv_219.data.sym;
            {
                __auto_type type_name = sym.name;
                __auto_type _mv_220 = env_env_lookup_type(env, type_name);
                if (_mv_220.has_value) {
                    __auto_type t = _mv_220.value;
                    return t;
                } else if (!_mv_220.has_value) {
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
            __auto_type _mv_221 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_221.has_value) {
                __auto_type expr = _mv_221.value;
                if (parser_is_form(expr, SLOP_STR("fn"))) {
                    collect_collect_single_function(env, arena, expr);
                } else if (parser_is_form(expr, SLOP_STR("module"))) {
                    collect_collect_module_functions(env, expr);
                } else {
                }
            } else if (!_mv_221.has_value) {
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
            __auto_type _mv_222 = parser_sexpr_list_get(module_form, 1);
            if (_mv_222.has_value) {
                __auto_type name_expr = _mv_222.value;
                {
                    __auto_type mod_name = parser_sexpr_get_symbol_name(name_expr);
                    if (!(string_eq(mod_name, SLOP_STR("")))) {
                        env_env_set_module(env, (slop_option_string){.has_value = 1, .value = mod_name});
                    }
                }
            } else if (!_mv_222.has_value) {
            }
            {
                __auto_type len = parser_sexpr_list_len(module_form);
                for (int64_t i = 2; i < len; i++) {
                    __auto_type _mv_223 = parser_sexpr_list_get(module_form, i);
                    if (_mv_223.has_value) {
                        __auto_type item = _mv_223.value;
                        if (parser_is_form(item, SLOP_STR("fn"))) {
                            collect_collect_single_function(env, arena, item);
                        }
                    } else if (!_mv_223.has_value) {
                    }
                }
            }
        }
    }
}

void collect_collect_single_function(env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    if (parser_sexpr_is_list(fn_form)) {
        if ((parser_sexpr_list_len(fn_form) >= 3)) {
            __auto_type _mv_224 = parser_sexpr_list_get(fn_form, 1);
            if (_mv_224.has_value) {
                __auto_type name_expr = _mv_224.value;
                {
                    __auto_type fn_name = parser_sexpr_get_symbol_name(name_expr);
                    if (!(string_eq(fn_name, SLOP_STR("")))) {
                        {
                            __auto_type mod_opt = env_env_get_module(env);
                            __auto_type qualified_name = ((mod_opt.has_value) ? string_concat(arena, mod_opt.value, string_concat(arena, SLOP_STR(":"), fn_name)) : fn_name);
                            __auto_type params = collect_collect_fn_params(env, arena, fn_form);
                            __auto_type ret_type = collect_find_fn_return_type(env, fn_form);
                            __auto_type sig = types_fn_signature_new(arena, qualified_name, fn_name, params, ret_type);
                            env_env_register_function(env, sig);
                        }
                    }
                }
            } else if (!_mv_224.has_value) {
            }
        }
    }
}

slop_list_types_ParamInfo collect_collect_fn_params(env_TypeEnv* env, slop_arena* arena, types_SExpr* fn_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((fn_form != NULL)), "(!= fn-form nil)");
    {
        __auto_type params = ((slop_list_types_ParamInfo){ .data = (types_ParamInfo*)slop_arena_alloc(arena, 16 * sizeof(types_ParamInfo)), .len = 0, .cap = 16 });
        __auto_type _mv_225 = parser_sexpr_list_get(fn_form, 2);
        if (_mv_225.has_value) {
            __auto_type params_expr = _mv_225.value;
            if (parser_sexpr_is_list(params_expr)) {
                {
                    __auto_type num_params = parser_sexpr_list_len(params_expr);
                    ({ for (int64_t i = 0; i < num_params; i++) { ({ __auto_type _mv = parser_sexpr_list_get(params_expr, i); if (_mv.has_value) { __auto_type param_form = _mv.value; (((parser_sexpr_is_list(param_form) && (parser_sexpr_list_len(param_form) >= 2))) ? ({ ({ __auto_type _mv = parser_sexpr_list_get(param_form, 0); if (_mv.has_value) { __auto_type first_expr = _mv.value; ({ __auto_type first_name = parser_sexpr_get_symbol_name(first_expr); ((((string_eq(first_name, SLOP_STR("in"))) || (string_eq(first_name, SLOP_STR("out"))) || (string_eq(first_name, SLOP_STR("mut"))))) ? (((parser_sexpr_list_len(param_form) >= 3)) ? ({ ({ __auto_type _mv = parser_sexpr_list_get(param_form, 1); if (_mv.has_value) { __auto_type name_expr = _mv.value; ({ __auto_type param_name = parser_sexpr_get_symbol_name(name_expr); ((!(string_eq(param_name, SLOP_STR("")))) ? ({ ({ __auto_type _mv = parser_sexpr_list_get(param_form, 2); if (_mv.has_value) { __auto_type type_expr = _mv.value; ({ __auto_type param_type = collect_get_field_type(env, arena, type_expr); __auto_type info = types_param_info_new(arena, param_name, param_type); ({ ({ __auto_type _lst_p = &(params); __auto_type _item = ((*info)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); }); }); } else { ({ (void)0; }); } (void)0; }); 0; }) : ({ (void)0; })); }); } else { ({ (void)0; }); } (void)0; }); 0; }) : ({ (void)0; })) : ((!(string_eq(first_name, SLOP_STR("")))) ? ({ ({ __auto_type _mv = parser_sexpr_list_get(param_form, 1); if (_mv.has_value) { __auto_type type_expr = _mv.value; ({ __auto_type param_type = collect_get_field_type(env, arena, type_expr); __auto_type info = types_param_info_new(arena, first_name, param_type); ({ ({ __auto_type _lst_p = &(params); __auto_type _item = ((*info)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; }); }); }); } else { ({ (void)0; }); } (void)0; }); 0; }) : ({ (void)0; }))); }); } else { ({ (void)0; }); } (void)0; }); 0; }) : ({ (void)0; })); } else { ({ (void)0; }); } (void)0; }); } 0; });
                }
            }
        } else if (!_mv_225.has_value) {
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
            __auto_type _mv_226 = parser_sexpr_list_get(fn_form, i);
            if (_mv_226.has_value) {
                __auto_type item = _mv_226.value;
                if (parser_is_form(item, SLOP_STR("@spec"))) {
                    if (!(found)) {
                        found_type = collect_extract_spec_return_type(env, item);
                        found = 1;
                    }
                }
            } else if (!_mv_226.has_value) {
            }
        }
        return found_type;
    }
}

types_ResolvedType* collect_extract_spec_return_type(env_TypeEnv* env, types_SExpr* spec_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type arena = env_env_arena(env);
        __auto_type _mv_227 = parser_sexpr_list_get(spec_form, 1);
        if (_mv_227.has_value) {
            __auto_type spec_body = _mv_227.value;
            if (parser_sexpr_is_list(spec_body)) {
                {
                    __auto_type len = parser_sexpr_list_len(spec_body);
                    __auto_type _mv_228 = parser_sexpr_list_get(spec_body, (len - 1));
                    if (_mv_228.has_value) {
                        __auto_type ret_expr = _mv_228.value;
                        return collect_get_field_type(env, arena, ret_expr);
                    } else if (!_mv_228.has_value) {
                        return env_env_get_unit_type(env);
                    }
                }
            } else {
                return env_env_get_unit_type(env);
            }
        } else if (!_mv_227.has_value) {
            return env_env_get_unit_type(env);
        }
    }
}

