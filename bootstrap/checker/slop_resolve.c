#include "../runtime/slop_runtime.h"
#include "slop_resolve.h"

void resolve_resolve_imports(env_TypeEnv* env, slop_list_types_SExpr_ptr ast);
void resolve_resolve_module_imports(env_TypeEnv* env, types_SExpr* module_form);
void resolve_resolve_import_stmt(env_TypeEnv* env, types_SExpr* import_form);
uint8_t resolve_contains_slash(slop_string s);
slop_option_string resolve_resolve_module_file(slop_arena* arena, slop_string module_name, slop_option_string from_file);

void resolve_resolve_imports(env_TypeEnv* env, slop_list_types_SExpr_ptr ast) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type len = ((int64_t)((ast).len));
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_187 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_187.has_value) {
                __auto_type expr = _mv_187.value;
                if (parser_is_form(expr, SLOP_STR("import"))) {
                    resolve_resolve_import_stmt(env, expr);
                } else if (parser_is_form(expr, SLOP_STR("module"))) {
                    resolve_resolve_module_imports(env, expr);
                } else {
                }
            } else if (!_mv_187.has_value) {
            }
        }
    }
}

void resolve_resolve_module_imports(env_TypeEnv* env, types_SExpr* module_form) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((module_form != NULL)), "(!= module-form nil)");
    if (parser_sexpr_is_list(module_form)) {
        {
            __auto_type len = parser_sexpr_list_len(module_form);
            for (int64_t i = 2; i < len; i++) {
                __auto_type _mv_188 = parser_sexpr_list_get(module_form, i);
                if (_mv_188.has_value) {
                    __auto_type item = _mv_188.value;
                    if (parser_is_form(item, SLOP_STR("import"))) {
                        resolve_resolve_import_stmt(env, item);
                    }
                } else if (!_mv_188.has_value) {
                }
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
        __auto_type _mv_189 = (*import_form);
        switch (_mv_189.tag) {
            case types_SExpr_lst:
            {
                __auto_type lst = _mv_189.data.lst;
                {
                    __auto_type items = lst.items;
                    __auto_type _mv_190 = ({ __auto_type _lst = items; size_t _idx = (size_t)1; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_190.has_value) {
                        __auto_type mod_name_expr = _mv_190.value;
                        __auto_type _mv_191 = (*mod_name_expr);
                        switch (_mv_191.tag) {
                            case types_SExpr_sym:
                            {
                                __auto_type mod_sym = _mv_191.data.sym;
                                __auto_type _mv_192 = ({ __auto_type _lst = items; size_t _idx = (size_t)2; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                                if (_mv_192.has_value) {
                                    __auto_type names_expr = _mv_192.value;
                                    __auto_type _mv_193 = (*names_expr);
                                    switch (_mv_193.tag) {
                                        case types_SExpr_lst:
                                        {
                                            __auto_type names_lst = _mv_193.data.lst;
                                            {
                                                __auto_type name_items = names_lst.items;
                                                __auto_type name_len = ((int64_t)((name_items).len));
                                                ({ for (int64_t j = 0; j < name_len; j++) { ({ __auto_type _mv = ({ __auto_type _lst = name_items; size_t _idx = (size_t)j; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type name_expr = _mv.value; ({ __auto_type _mv = (*name_expr); switch (_mv.tag) { case types_SExpr_sym: { __auto_type name_sym = _mv.data.sym; ({ __auto_type local_name = name_sym.name; __auto_type qualified_name = string_concat(arena, mod_sym.name, string_concat(arena, SLOP_STR(":"), local_name)); ({ env_env_add_import(env, local_name, qualified_name); }); }); break; } default: { ({ (void)0; }); break; }  } (void)0; }); } else { ({ (void)0; }); } (void)0; }); } 0; });
                                            }
                                            break;
                                        }
                                        default: {
                                            break;
                                        }
                                    }
                                } else if (!_mv_192.has_value) {
                                }
                                break;
                            }
                            default: {
                                break;
                            }
                        }
                    } else if (!_mv_190.has_value) {
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

uint8_t resolve_contains_slash(slop_string s) {
    {
        __auto_type len = ((int64_t)(s.len));
        __auto_type found = 0;
        for (int64_t i = 0; i < len; i++) {
            if ((!(found) && (((int64_t)(s.data[i])) == 47))) {
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
        __auto_type _mv_194 = from_file;
        if (_mv_194.has_value) {
            __auto_type current_path = _mv_194.value;
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
        } else if (!_mv_194.has_value) {
            return (slop_option_string){.has_value = false};
        }
    }
}

