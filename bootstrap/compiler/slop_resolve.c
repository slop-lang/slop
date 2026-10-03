#include "../runtime/slop_runtime.h"
#include "slop_resolve.h"

void resolve_resolve_imports(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void resolve_resolve_import_stmt(env_TypeEnv* env, types_SExpr* import_form);
slop_list_resolve_ImportSite resolve_collect_import_sites(slop_arena* arena, slop_list_types_SExpr_ptr ast);
slop_list_resolve_ImportSite resolve_push_import_sites(slop_arena* arena, slop_list_resolve_ImportSite sites, types_SExpr* import_form);
slop_option_string resolve_resolve_import_target(env_TypeEnv* env, slop_string src, slop_string name);
void resolve_resolve_import_name(env_TypeEnv* env, resolve_ImportSite site);
slop_string resolve_qualified_module_part(slop_arena* arena, slop_string qualified);
void resolve_check_import_shadowing(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
uint8_t resolve_contains_slash(slop_string s);
slop_option_string resolve_resolve_module_file(slop_arena* arena, slop_string module_name, slop_option_string from_file);

void resolve_resolve_imports(env_TypeEnv* env, slop_list_types_SExpr_ptr ast) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type sites = resolve_collect_import_sites(env_env_arena(env), ast);
        __auto_type len = ((int64_t)((sites).len));
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_1058 = ({ __auto_type _lst = sites; size_t _idx = (size_t)i; slop_option_resolve_ImportSite _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1058.has_value) {
                __auto_type site = _mv_1058.value;
                resolve_resolve_import_name(env, site);
            } else if (!_mv_1058.has_value) {
            }
        }
    }
}

void resolve_resolve_import_stmt(env_TypeEnv* env, types_SExpr* import_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((import_form != NULL)), "(!= import-form nil)");
    SLOP_PRE((parser_is_form(import_form, SLOP_STR("import"))), "(is-form import-form \"import\")");
    {
        __auto_type arena = env_env_arena(env);
        __auto_type sites = resolve_push_import_sites(arena, ((slop_list_resolve_ImportSite){ .data = NULL, .len = 0, .cap = 0, .arena = arena }), import_form);
        {
            __auto_type len = ((int64_t)((sites).len));
            for (int64_t i = 0; i < len; i++) {
                __auto_type _mv_1059 = ({ __auto_type _lst = sites; size_t _idx = (size_t)i; slop_option_resolve_ImportSite _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1059.has_value) {
                    __auto_type site = _mv_1059.value;
                    resolve_resolve_import_name(env, site);
                } else if (!_mv_1059.has_value) {
                }
            }
        }
    }
}

slop_list_resolve_ImportSite resolve_collect_import_sites(slop_arena* arena, slop_list_types_SExpr_ptr ast) {
    {
        __auto_type sites = ((slop_list_resolve_ImportSite){ .data = NULL, .len = 0, .cap = 0, .arena = arena });
        __auto_type len = ((int64_t)((ast).len));
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_1060 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1060.has_value) {
                __auto_type expr = _mv_1060.value;
                if (parser_is_form(expr, SLOP_STR("import"))) {
                    sites = resolve_push_import_sites(arena, sites, expr);
                } else if (parser_is_form(expr, SLOP_STR("module"))) {
                    {
                        __auto_type mod_len = parser_sexpr_list_len(expr);
                        for (int64_t j = 2; j < mod_len; j++) {
                            __auto_type _mv_1061 = parser_sexpr_list_get(expr, j);
                            if (_mv_1061.has_value) {
                                __auto_type item = _mv_1061.value;
                                if (parser_is_form(item, SLOP_STR("import"))) {
                                    sites = resolve_push_import_sites(arena, sites, item);
                                }
                            } else if (!_mv_1061.has_value) {
                            }
                        }
                    }
                } else {
                }
            } else if (!_mv_1060.has_value) {
            }
        }
        return sites;
    }
}

slop_list_resolve_ImportSite resolve_push_import_sites(slop_arena* arena, slop_list_resolve_ImportSite sites, types_SExpr* import_form) {
    SLOP_PRE(((import_form != NULL)), "(!= import-form nil)");
    {
        __auto_type result = sites;
        __auto_type _mv_1062 = parser_sexpr_list_get(import_form, 1);
        if (_mv_1062.has_value) {
            __auto_type mod_name_expr = _mv_1062.value;
            __auto_type _mv_1063 = (*mod_name_expr);
            switch (_mv_1063.tag) {
                case types_SExpr_sym:
                {
                    __auto_type mod_sym = _mv_1063.data.sym;
                    __auto_type _mv_1064 = parser_sexpr_list_get(import_form, 2);
                    if (_mv_1064.has_value) {
                        __auto_type names_expr = _mv_1064.value;
                        __auto_type _mv_1065 = (*names_expr);
                        switch (_mv_1065.tag) {
                            case types_SExpr_lst:
                            {
                                __auto_type names_lst = _mv_1065.data.lst;
                                {
                                    __auto_type name_items = names_lst.items;
                                    __auto_type name_len = ((int64_t)((name_items).len));
                                    for (int64_t j = 0; j < name_len; j++) {
                                        __auto_type _mv_1066 = ({ __auto_type _lst = name_items; size_t _idx = (size_t)j; slop_option_types_SExpr_ptr _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                        if (_mv_1066.has_value) {
                                            __auto_type name_expr = _mv_1066.value;
                                            __auto_type _mv_1067 = (*name_expr);
                                            switch (_mv_1067.tag) {
                                                case types_SExpr_sym:
                                                {
                                                    __auto_type name_sym = _mv_1067.data.sym;
                                                    ({ __auto_type _lst_p = &(result); __auto_type _item = ((resolve_ImportSite){mod_sym.name, name_sym.name, name_expr}); if (_lst_p->len >= _lst_p->cap) { _lst_p->data = (__typeof__(_lst_p->data))slop_list_grow_raw(_lst_p->arena, _lst_p->data, &_lst_p->cap, _lst_p->len, sizeof(*_lst_p->data)); } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                                    break;
                                                }
                                                default: {
                                                    break;
                                                }
                                            }
                                        } else if (!_mv_1066.has_value) {
                                        }
                                    }
                                }
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_1064.has_value) {
                    }
                    break;
                }
                default: {
                    break;
                }
            }
        } else if (!_mv_1062.has_value) {
        }
        return result;
    }
}

slop_option_string resolve_resolve_import_target(env_TypeEnv* env, slop_string src, slop_string name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type arena = env_env_arena(env);
        __auto_type qualified = strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 3 * sizeof(slop_string)), .len = 3, .cap = 3, .arena = arena }; _ll.data[0] = src; _ll.data[1] = SLOP_STR(":"); _ll.data[2] = name; _ll; }));
        if ((({ __auto_type _mv = env_env_lookup_type_qualified(env, src, name); _mv.has_value ? ({ __auto_type _ = _mv.value; 1; }) : (0); })) || (({ __auto_type _mv = env_env_lookup_function_direct(env, qualified); _mv.has_value ? ({ __auto_type _ = _mv.value; 1; }) : (0); })) || (env_env_lookup_constant_in_module(env, src, name))) {
            return (slop_option_string){.has_value = 1, .value = qualified};
        } else {
            return env_env_lookup_module_import(env, src, name);
        }
    }
}

void resolve_resolve_import_name(env_TypeEnv* env, resolve_ImportSite site) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type arena = env_env_arena(env);
        __auto_type src = site.source;
        __auto_type local_name = site.name;
        __auto_type name_expr = site.name_expr;
        __auto_type _mv_1068 = resolve_resolve_import_target(env, src, local_name);
        if (_mv_1068.has_value) {
            __auto_type target = _mv_1068.value;
            __auto_type _mv_1069 = env_env_resolve_import(env, local_name);
            if (_mv_1069.has_value) {
                __auto_type prev = _mv_1069.value;
                if (!(string_eq(prev, target))) {
                    env_env_add_error(env, strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 7 * sizeof(slop_string)), .len = 7, .cap = 7, .arena = arena }; _ll.data[0] = SLOP_STR("'"); _ll.data[1] = local_name; _ll.data[2] = SLOP_STR("' is imported from both '"); _ll.data[3] = resolve_qualified_module_part(arena, prev); _ll.data[4] = SLOP_STR("' and '"); _ll.data[5] = src; _ll.data[6] = SLOP_STR("'"); _ll; })), parser_sexpr_line(name_expr), parser_sexpr_col(name_expr));
                }
            } else if (!_mv_1069.has_value) {
            }
            env_env_add_import(env, local_name, target);
        } else if (!_mv_1068.has_value) {
            if (!(resolve_contains_slash(src))) {
                env_env_add_error(env, strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 5 * sizeof(slop_string)), .len = 5, .cap = 5, .arena = arena }; _ll.data[0] = SLOP_STR("module '"); _ll.data[1] = src; _ll.data[2] = SLOP_STR("' does not export '"); _ll.data[3] = local_name; _ll.data[4] = SLOP_STR("'"); _ll; })), parser_sexpr_line(name_expr), parser_sexpr_col(name_expr));
            }
            env_env_add_import(env, local_name, strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 3 * sizeof(slop_string)), .len = 3, .cap = 3, .arena = arena }; _ll.data[0] = src; _ll.data[1] = SLOP_STR(":"); _ll.data[2] = local_name; _ll; })));
        }
    }
}

slop_string resolve_qualified_module_part(slop_arena* arena, slop_string qualified) {
    __auto_type _mv_1070 = strlib_index_of(qualified, SLOP_STR(":"));
    if (_mv_1070.has_value) {
        __auto_type idx = _mv_1070.value;
        return strlib_substring(arena, qualified, 0, idx);
    } else if (!_mv_1070.has_value) {
        return qualified;
    }
    SLOP_UNREACHABLE();
}

void resolve_check_import_shadowing(env_TypeEnv* env, slop_list_types_SExpr_ptr ast) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_1071 = env_env_get_module(env);
    if (_mv_1071.has_value) {
        __auto_type cur = _mv_1071.value;
        {
            __auto_type arena = env_env_arena(env);
            __auto_type sites = resolve_collect_import_sites(arena, ast);
            __auto_type len = ((int64_t)((sites).len));
            for (int64_t i = 0; i < len; i++) {
                __auto_type _mv_1072 = ({ __auto_type _lst = sites; size_t _idx = (size_t)i; slop_option_resolve_ImportSite _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1072.has_value) {
                    __auto_type site = _mv_1072.value;
                    {
                        __auto_type local_name = site.name;
                        __auto_type own = strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 3 * sizeof(slop_string)), .len = 3, .cap = 3, .arena = arena }; _ll.data[0] = cur; _ll.data[1] = SLOP_STR(":"); _ll.data[2] = local_name; _ll; }));
                        __auto_type imported_own = ({ __auto_type _mv = env_env_resolve_import(env, local_name); _mv.has_value ? ({ __auto_type q = _mv.value; string_eq(q, own); }) : (0); });
                        if ((!(imported_own)) && (({ __auto_type _mv = resolve_resolve_import_target(env, site.source, local_name); _mv.has_value ? ({ __auto_type _ = _mv.value; 1; }) : (0); })) && (((({ __auto_type _mv = env_env_lookup_type_qualified(env, cur, local_name); _mv.has_value ? ({ __auto_type _ = _mv.value; 1; }) : (0); })) || (({ __auto_type _mv = env_env_lookup_function_direct(env, own); _mv.has_value ? ({ __auto_type _ = _mv.value; 1; }) : (0); })) || (env_env_lookup_constant_in_module(env, cur, local_name))))) {
                            env_env_add_error(env, strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 7 * sizeof(slop_string)), .len = 7, .cap = 7, .arena = arena }; _ll.data[0] = SLOP_STR("'"); _ll.data[1] = local_name; _ll.data[2] = SLOP_STR("' is defined in module '"); _ll.data[3] = cur; _ll.data[4] = SLOP_STR("' and also imported from '"); _ll.data[5] = site.source; _ll.data[6] = SLOP_STR("'"); _ll; })), parser_sexpr_line(site.name_expr), parser_sexpr_col(site.name_expr));
                        }
                    }
                } else if (!_mv_1072.has_value) {
                }
            }
        }
    } else if (!_mv_1071.has_value) {
    }
}

uint8_t resolve_contains_slash(slop_string s) {
    {
        __auto_type len = ((int64_t)(s.len));
        uint8_t found = 0;
        for (int64_t i = 0; i < len; i++) {
            if (!(found) && (((int64_t)(s.data[i])) == 47)) {
                found = 1;
            }
        }
        return found;
    }
}

slop_option_string resolve_resolve_module_file(slop_arena* arena, slop_string module_name, slop_option_string from_file) {
    if (!(resolve_contains_slash(module_name))) {
        return (slop_option_string){.has_value = false};
    } else {
        __auto_type _mv_1073 = from_file;
        if (_mv_1073.has_value) {
            __auto_type current_path = _mv_1073.value;
            {
                __auto_type dir = path_path_dirname(arena, current_path);
                __auto_type rel_path = string_concat(arena, module_name, SLOP_STR(".slop"));
                __auto_type full_path = path_path_join(arena, dir, rel_path);
                if (file_file_exists(full_path)) {
                    return (slop_option_string){.has_value = 1, .value = full_path};
                } else {
                    return (slop_option_string){.has_value = false};
                }
            }
        } else if (!_mv_1073.has_value) {
            return (slop_option_string){.has_value = false};
        }
        SLOP_UNREACHABLE();
    }
}

