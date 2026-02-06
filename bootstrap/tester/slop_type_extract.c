#include "../runtime/slop_runtime.h"
#include "slop_type_extract.h"

type_extract_TypeRegistry type_extract_make_type_registry(slop_arena* arena, slop_string prefix);
type_extract_TypeRegistry type_extract_make_type_registry_with_imports(slop_arena* arena, slop_string prefix, slop_list_type_extract_ImportEntry imports);
void type_extract_registry_add_type(slop_arena* arena, type_extract_TypeRegistry* reg, type_extract_TstTypeEntry* entry);
type_extract_TstTypeEntry* type_extract_type_entry_new(slop_arena* arena, slop_string name, slop_string c_name, type_extract_TstTypeEntryKind kind);
type_extract_TstFieldEntry type_extract_field_entry_new(slop_string name, slop_string type_name);
type_extract_VariantEntry type_extract_variant_entry_new(slop_string name, int64_t index, slop_string payload_type);
type_extract_EnumValueEntry type_extract_enum_value_entry_new(slop_string name, int64_t index);
type_extract_TypeRegistry* type_extract_extract_types_from_ast(slop_arena* arena, slop_list_types_SExpr_ptr ast, slop_string module_prefix);
type_extract_TypeRegistry* type_extract_extract_types_from_ast_with_imports(slop_arena* arena, slop_list_types_SExpr_ptr ast, slop_string module_prefix, slop_list_type_extract_ImportEntry imports);
void type_extract_extract_types_from_module(slop_arena* arena, types_SExpr* module_form, type_extract_TypeRegistry* reg_ptr, slop_string prefix);
void type_extract_extract_type_def(slop_arena* arena, types_SExpr* type_form, type_extract_TypeRegistry* reg_ptr, slop_string prefix);
type_extract_TstTypeEntry* type_extract_extract_record_type(slop_arena* arena, slop_string name, slop_string c_name, types_SExpr* def);
type_extract_TstTypeEntry* type_extract_extract_union_type(slop_arena* arena, slop_string name, slop_string c_name, types_SExpr* def);
type_extract_TstTypeEntry* type_extract_extract_enum_type(slop_arena* arena, slop_string name, slop_string c_name, types_SExpr* def);
slop_option_type_extract_TstTypeEntry_ptr type_extract_registry_lookup(type_extract_TypeRegistry reg, slop_string name);
slop_option_type_extract_TstTypeEntry_ptr type_extract_registry_lookup_variant(type_extract_TypeRegistry reg, slop_string variant_name);
slop_option_type_extract_TstTypeEntry_ptr type_extract_registry_lookup_enum_value(type_extract_TypeRegistry reg, slop_string value_name);
slop_option_string type_extract_registry_lookup_import(type_extract_TypeRegistry reg, slop_string symbol_name);
uint8_t type_extract_registry_is_union(type_extract_TypeRegistry reg, slop_string name);
uint8_t type_extract_registry_is_record(type_extract_TypeRegistry reg, slop_string name);
uint8_t type_extract_registry_is_enum(type_extract_TypeRegistry reg, slop_string name);
slop_option_type_extract_VariantEntry type_extract_registry_get_variant_info(type_extract_TypeRegistry reg, slop_string variant_name);
slop_option_list_type_extract_TstFieldEntry type_extract_registry_get_record_fields(type_extract_TypeRegistry reg, slop_string name);
slop_string type_extract_make_c_type_name(slop_arena* arena, slop_string prefix, slop_string name);
slop_string type_extract_convert_to_c_ident(slop_arena* arena, slop_string name);

type_extract_TypeRegistry type_extract_make_type_registry(slop_arena* arena, slop_string prefix) {
    return (type_extract_TypeRegistry){((slop_list_type_extract_TstTypeEntry_ptr){ .data = (type_extract_TstTypeEntry**)slop_arena_alloc(arena, 16 * sizeof(type_extract_TstTypeEntry*)), .len = 0, .cap = 16 }), prefix, ((slop_list_type_extract_ImportEntry){ .data = (type_extract_ImportEntry*)slop_arena_alloc(arena, 16 * sizeof(type_extract_ImportEntry)), .len = 0, .cap = 16 })};
}

type_extract_TypeRegistry type_extract_make_type_registry_with_imports(slop_arena* arena, slop_string prefix, slop_list_type_extract_ImportEntry imports) {
    return (type_extract_TypeRegistry){((slop_list_type_extract_TstTypeEntry_ptr){ .data = (type_extract_TstTypeEntry**)slop_arena_alloc(arena, 16 * sizeof(type_extract_TstTypeEntry*)), .len = 0, .cap = 16 }), prefix, imports};
}

void type_extract_registry_add_type(slop_arena* arena, type_extract_TypeRegistry* reg, type_extract_TstTypeEntry* entry) {
    ({ __auto_type _lst_p = &((*reg).types); __auto_type _item = (entry); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

type_extract_TstTypeEntry* type_extract_type_entry_new(slop_arena* arena, slop_string name, slop_string c_name, type_extract_TstTypeEntryKind kind) {
    {
        __auto_type entry = ((type_extract_TstTypeEntry*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 128); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        (*entry) = (type_extract_TstTypeEntry){name, c_name, kind, ((slop_list_type_extract_TstFieldEntry){ .data = (type_extract_TstFieldEntry*)slop_arena_alloc(arena, 16 * sizeof(type_extract_TstFieldEntry)), .len = 0, .cap = 16 }), ((slop_list_type_extract_VariantEntry){ .data = (type_extract_VariantEntry*)slop_arena_alloc(arena, 16 * sizeof(type_extract_VariantEntry)), .len = 0, .cap = 16 }), ((slop_list_type_extract_EnumValueEntry){ .data = (type_extract_EnumValueEntry*)slop_arena_alloc(arena, 16 * sizeof(type_extract_EnumValueEntry)), .len = 0, .cap = 16 }), SLOP_STR("")};
        return entry;
    }
}

type_extract_TstFieldEntry type_extract_field_entry_new(slop_string name, slop_string type_name) {
    return (type_extract_TstFieldEntry){name, type_name};
}

type_extract_VariantEntry type_extract_variant_entry_new(slop_string name, int64_t index, slop_string payload_type) {
    return (type_extract_VariantEntry){name, index, payload_type};
}

type_extract_EnumValueEntry type_extract_enum_value_entry_new(slop_string name, int64_t index) {
    return (type_extract_EnumValueEntry){name, index};
}

type_extract_TypeRegistry* type_extract_extract_types_from_ast(slop_arena* arena, slop_list_types_SExpr_ptr ast, slop_string module_prefix) {
    return type_extract_extract_types_from_ast_with_imports(arena, ast, module_prefix, ((slop_list_type_extract_ImportEntry){ .data = (type_extract_ImportEntry*)slop_arena_alloc(arena, 16 * sizeof(type_extract_ImportEntry)), .len = 0, .cap = 16 }));
}

type_extract_TypeRegistry* type_extract_extract_types_from_ast_with_imports(slop_arena* arena, slop_list_types_SExpr_ptr ast, slop_string module_prefix, slop_list_type_extract_ImportEntry imports) {
    {
        __auto_type reg_ptr = ((type_extract_TypeRegistry*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, 128); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        (*reg_ptr) = type_extract_make_type_registry_with_imports(arena, module_prefix, imports);
        {
            __auto_type len = ((int64_t)((ast).len));
            int64_t i = 0;
            while ((i < len)) {
                __auto_type _mv_1410 = ({ __auto_type _lst = ast; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1410.has_value) {
                    __auto_type expr = _mv_1410.value;
                    if (parser_is_form(expr, SLOP_STR("module"))) {
                        type_extract_extract_types_from_module(arena, expr, reg_ptr, module_prefix);
                    }
                    if (parser_is_form(expr, SLOP_STR("type"))) {
                        type_extract_extract_type_def(arena, expr, reg_ptr, module_prefix);
                    }
                } else if (!_mv_1410.has_value) {
                }
                i = (i + 1);
            }
        }
        return reg_ptr;
    }
}

void type_extract_extract_types_from_module(slop_arena* arena, types_SExpr* module_form, type_extract_TypeRegistry* reg_ptr, slop_string prefix) {
    {
        __auto_type len = parser_sexpr_list_len(module_form);
        int64_t i = 2;
        while ((i < len)) {
            __auto_type _mv_1411 = parser_sexpr_list_get(module_form, i);
            if (_mv_1411.has_value) {
                __auto_type form = _mv_1411.value;
                if (parser_is_form(form, SLOP_STR("type"))) {
                    type_extract_extract_type_def(arena, form, reg_ptr, prefix);
                }
            } else if (!_mv_1411.has_value) {
            }
            i = (i + 1);
        }
    }
}

void type_extract_extract_type_def(slop_arena* arena, types_SExpr* type_form, type_extract_TypeRegistry* reg_ptr, slop_string prefix) {
    if ((parser_sexpr_list_len(type_form) >= 3)) {
        __auto_type _mv_1412 = parser_sexpr_list_get(type_form, 1);
        if (_mv_1412.has_value) {
            __auto_type name_expr = _mv_1412.value;
            if (parser_sexpr_is_symbol(name_expr)) {
                {
                    __auto_type type_name = parser_sexpr_get_symbol_name(name_expr);
                    __auto_type c_name = type_extract_make_c_type_name(arena, prefix, type_name);
                    __auto_type _mv_1413 = parser_sexpr_list_get(type_form, 2);
                    if (_mv_1413.has_value) {
                        __auto_type def_expr = _mv_1413.value;
                        if (parser_is_form(def_expr, SLOP_STR("record"))) {
                            {
                                __auto_type entry = type_extract_extract_record_type(arena, type_name, c_name, def_expr);
                                ({ __auto_type _lst_p = &((*reg_ptr).types); __auto_type _item = (entry); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            }
                        } else if (parser_is_form(def_expr, SLOP_STR("union"))) {
                            {
                                __auto_type entry = type_extract_extract_union_type(arena, type_name, c_name, def_expr);
                                ({ __auto_type _lst_p = &((*reg_ptr).types); __auto_type _item = (entry); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            }
                        } else if (parser_is_form(def_expr, SLOP_STR("enum"))) {
                            {
                                __auto_type entry = type_extract_extract_enum_type(arena, type_name, c_name, def_expr);
                                ({ __auto_type _lst_p = &((*reg_ptr).types); __auto_type _item = (entry); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            }
                        } else if (parser_is_form(def_expr, SLOP_STR("Int"))) {
                            {
                                __auto_type entry = type_extract_type_entry_new(arena, type_name, c_name, type_extract_TstTypeEntryKind_te_range);
                                (*entry).inner_type = SLOP_STR("Int");
                                ({ __auto_type _lst_p = &((*reg_ptr).types); __auto_type _item = (entry); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            }
                        } else {
                            {
                                __auto_type entry = type_extract_type_entry_new(arena, type_name, c_name, type_extract_TstTypeEntryKind_te_alias);
                                __auto_type inner = parser_pretty_print(arena, def_expr);
                                (*entry).inner_type = inner;
                                ({ __auto_type _lst_p = &((*reg_ptr).types); __auto_type _item = (entry); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                            }
                        }
                    } else if (!_mv_1413.has_value) {
                    }
                }
            }
        } else if (!_mv_1412.has_value) {
        }
    }
}

type_extract_TstTypeEntry* type_extract_extract_record_type(slop_arena* arena, slop_string name, slop_string c_name, types_SExpr* def) {
    {
        __auto_type entry = type_extract_type_entry_new(arena, name, c_name, type_extract_TstTypeEntryKind_te_record);
        __auto_type len = parser_sexpr_list_len(def);
        int64_t i = 1;
        while ((i < len)) {
            __auto_type _mv_1414 = parser_sexpr_list_get(def, i);
            if (_mv_1414.has_value) {
                __auto_type field_def = _mv_1414.value;
                if ((parser_sexpr_list_len(field_def) >= 2)) {
                    __auto_type _mv_1415 = parser_sexpr_list_get(field_def, 0);
                    if (_mv_1415.has_value) {
                        __auto_type field_name_expr = _mv_1415.value;
                        if (parser_sexpr_is_symbol(field_name_expr)) {
                            {
                                __auto_type field_name = parser_sexpr_get_symbol_name(field_name_expr);
                                __auto_type _mv_1416 = parser_sexpr_list_get(field_def, 1);
                                if (_mv_1416.has_value) {
                                    __auto_type field_type_expr = _mv_1416.value;
                                    {
                                        __auto_type field_type = parser_pretty_print(arena, field_type_expr);
                                        __auto_type fe = type_extract_field_entry_new(field_name, field_type);
                                        ({ __auto_type _lst_p = &((*entry).fields); __auto_type _item = (fe); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    }
                                } else if (!_mv_1416.has_value) {
                                }
                            }
                        }
                    } else if (!_mv_1415.has_value) {
                    }
                }
            } else if (!_mv_1414.has_value) {
            }
            i = (i + 1);
        }
        return entry;
    }
}

type_extract_TstTypeEntry* type_extract_extract_union_type(slop_arena* arena, slop_string name, slop_string c_name, types_SExpr* def) {
    {
        __auto_type entry = type_extract_type_entry_new(arena, name, c_name, type_extract_TstTypeEntryKind_te_union);
        __auto_type len = parser_sexpr_list_len(def);
        int64_t i = 1;
        int64_t idx = 0;
        while ((i < len)) {
            __auto_type _mv_1417 = parser_sexpr_list_get(def, i);
            if (_mv_1417.has_value) {
                __auto_type variant_def = _mv_1417.value;
                {
                    __auto_type vlen = parser_sexpr_list_len(variant_def);
                    if ((vlen >= 1)) {
                        __auto_type _mv_1418 = parser_sexpr_list_get(variant_def, 0);
                        if (_mv_1418.has_value) {
                            __auto_type variant_name_expr = _mv_1418.value;
                            if (parser_sexpr_is_symbol(variant_name_expr)) {
                                {
                                    __auto_type variant_name = parser_sexpr_get_symbol_name(variant_name_expr);
                                    __auto_type payload_type = (((vlen >= 2)) ? ({ __auto_type _mv = parser_sexpr_list_get(variant_def, 1); _mv.has_value ? ({ __auto_type pt_expr = _mv.value; parser_pretty_print(arena, pt_expr); }) : (SLOP_STR("")); }) : SLOP_STR(""));
                                    __auto_type ve = type_extract_variant_entry_new(variant_name, idx, payload_type);
                                    ({ __auto_type _lst_p = &((*entry).variants); __auto_type _item = (ve); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                                    idx = (idx + 1);
                                }
                            }
                        } else if (!_mv_1418.has_value) {
                        }
                    }
                }
            } else if (!_mv_1417.has_value) {
            }
            i = (i + 1);
        }
        return entry;
    }
}

type_extract_TstTypeEntry* type_extract_extract_enum_type(slop_arena* arena, slop_string name, slop_string c_name, types_SExpr* def) {
    {
        __auto_type entry = type_extract_type_entry_new(arena, name, c_name, type_extract_TstTypeEntryKind_te_enum);
        __auto_type len = parser_sexpr_list_len(def);
        int64_t i = 1;
        int64_t idx = 0;
        while ((i < len)) {
            __auto_type _mv_1419 = parser_sexpr_list_get(def, i);
            if (_mv_1419.has_value) {
                __auto_type val_expr = _mv_1419.value;
                if (parser_sexpr_is_symbol(val_expr)) {
                    {
                        __auto_type val_name = parser_sexpr_get_symbol_name(val_expr);
                        __auto_type eve = type_extract_enum_value_entry_new(val_name, idx);
                        ({ __auto_type _lst_p = &((*entry).enum_values); __auto_type _item = (eve); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
                        idx = (idx + 1);
                    }
                }
            } else if (!_mv_1419.has_value) {
            }
            i = (i + 1);
        }
        return entry;
    }
}

slop_option_type_extract_TstTypeEntry_ptr type_extract_registry_lookup(type_extract_TypeRegistry reg, slop_string name) {
    {
        __auto_type types = reg.types;
        __auto_type len = ((int64_t)((types).len));
        int64_t i = 0;
        slop_option_type_extract_TstTypeEntry_ptr found = (slop_option_type_extract_TstTypeEntry_ptr){.has_value = false};
        while (((i < len) && ({ __auto_type _mv = found; _mv.has_value ? (0) : (1); }))) {
            __auto_type _mv_1420 = ({ __auto_type _lst = types; size_t _idx = (size_t)i; slop_option_type_extract_TstTypeEntry_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1420.has_value) {
                __auto_type entry = _mv_1420.value;
                if (string_eq((*entry).name, name)) {
                    found = (slop_option_type_extract_TstTypeEntry_ptr){.has_value = 1, .value = entry};
                }
            } else if (!_mv_1420.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

slop_option_type_extract_TstTypeEntry_ptr type_extract_registry_lookup_variant(type_extract_TypeRegistry reg, slop_string variant_name) {
    {
        __auto_type types = reg.types;
        __auto_type len = ((int64_t)((types).len));
        int64_t i = 0;
        slop_option_type_extract_TstTypeEntry_ptr found = (slop_option_type_extract_TstTypeEntry_ptr){.has_value = false};
        while (((i < len) && ({ __auto_type _mv = found; _mv.has_value ? (0) : (1); }))) {
            __auto_type _mv_1421 = ({ __auto_type _lst = types; size_t _idx = (size_t)i; slop_option_type_extract_TstTypeEntry_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1421.has_value) {
                __auto_type entry = _mv_1421.value;
                if (((*entry).kind == type_extract_TstTypeEntryKind_te_union)) {
                    {
                        __auto_type variants = (*entry).variants;
                        __auto_type vlen = ((int64_t)((variants).len));
                        __auto_type j = 0;
                        __auto_type vfound = 0;
                        while (((j < vlen) && !(vfound))) {
                            __auto_type _mv_1422 = ({ __auto_type _lst = variants; size_t _idx = (size_t)j; slop_option_type_extract_VariantEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1422.has_value) {
                                __auto_type ve = _mv_1422.value;
                                if (string_eq(ve.name, variant_name)) {
                                    vfound = 1;
                                    found = (slop_option_type_extract_TstTypeEntry_ptr){.has_value = 1, .value = entry};
                                }
                            } else if (!_mv_1422.has_value) {
                            }
                            j = (j + 1);
                        }
                    }
                }
            } else if (!_mv_1421.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

slop_option_type_extract_TstTypeEntry_ptr type_extract_registry_lookup_enum_value(type_extract_TypeRegistry reg, slop_string value_name) {
    {
        __auto_type types = reg.types;
        __auto_type len = ((int64_t)((types).len));
        int64_t i = 0;
        slop_option_type_extract_TstTypeEntry_ptr found = (slop_option_type_extract_TstTypeEntry_ptr){.has_value = false};
        while (((i < len) && ({ __auto_type _mv = found; _mv.has_value ? (0) : (1); }))) {
            __auto_type _mv_1423 = ({ __auto_type _lst = types; size_t _idx = (size_t)i; slop_option_type_extract_TstTypeEntry_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1423.has_value) {
                __auto_type entry = _mv_1423.value;
                if (((*entry).kind == type_extract_TstTypeEntryKind_te_enum)) {
                    {
                        __auto_type values = (*entry).enum_values;
                        __auto_type vlen = ((int64_t)((values).len));
                        __auto_type j = 0;
                        __auto_type vfound = 0;
                        while (((j < vlen) && !(vfound))) {
                            __auto_type _mv_1424 = ({ __auto_type _lst = values; size_t _idx = (size_t)j; slop_option_type_extract_EnumValueEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                            if (_mv_1424.has_value) {
                                __auto_type eve = _mv_1424.value;
                                if (string_eq(eve.name, value_name)) {
                                    vfound = 1;
                                    found = (slop_option_type_extract_TstTypeEntry_ptr){.has_value = 1, .value = entry};
                                }
                            } else if (!_mv_1424.has_value) {
                            }
                            j = (j + 1);
                        }
                    }
                }
            } else if (!_mv_1423.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

slop_option_string type_extract_registry_lookup_import(type_extract_TypeRegistry reg, slop_string symbol_name) {
    {
        __auto_type entries = reg.import_entries;
        __auto_type len = ((int64_t)((entries).len));
        int64_t i = 0;
        slop_option_string found = (slop_option_string){.has_value = false};
        while (((i < len) && ({ __auto_type _mv = found; _mv.has_value ? (0) : (1); }))) {
            __auto_type _mv_1425 = ({ __auto_type _lst = entries; size_t _idx = (size_t)i; slop_option_type_extract_ImportEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_1425.has_value) {
                __auto_type entry = _mv_1425.value;
                {
                    __auto_type symbols = entry.symbols;
                    __auto_type slen = ((int64_t)((symbols).len));
                    __auto_type j = 0;
                    while (((j < slen) && ({ __auto_type _mv = found; _mv.has_value ? (0) : (1); }))) {
                        __auto_type _mv_1426 = ({ __auto_type _lst = symbols; size_t _idx = (size_t)j; slop_option_string _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                        if (_mv_1426.has_value) {
                            __auto_type sym = _mv_1426.value;
                            if (string_eq(sym, symbol_name)) {
                                found = (slop_option_string){.has_value = 1, .value = entry.module_name};
                            }
                        } else if (!_mv_1426.has_value) {
                        }
                        j = (j + 1);
                    }
                }
            } else if (!_mv_1425.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

uint8_t type_extract_registry_is_union(type_extract_TypeRegistry reg, slop_string name) {
    __auto_type _mv_1427 = type_extract_registry_lookup(reg, name);
    if (_mv_1427.has_value) {
        __auto_type entry = _mv_1427.value;
        return ((*entry).kind == type_extract_TstTypeEntryKind_te_union);
    } else if (!_mv_1427.has_value) {
        return 0;
    }
}

uint8_t type_extract_registry_is_record(type_extract_TypeRegistry reg, slop_string name) {
    __auto_type _mv_1428 = type_extract_registry_lookup(reg, name);
    if (_mv_1428.has_value) {
        __auto_type entry = _mv_1428.value;
        return ((*entry).kind == type_extract_TstTypeEntryKind_te_record);
    } else if (!_mv_1428.has_value) {
        return 0;
    }
}

uint8_t type_extract_registry_is_enum(type_extract_TypeRegistry reg, slop_string name) {
    __auto_type _mv_1429 = type_extract_registry_lookup(reg, name);
    if (_mv_1429.has_value) {
        __auto_type entry = _mv_1429.value;
        return ((*entry).kind == type_extract_TstTypeEntryKind_te_enum);
    } else if (!_mv_1429.has_value) {
        return 0;
    }
}

slop_option_type_extract_VariantEntry type_extract_registry_get_variant_info(type_extract_TypeRegistry reg, slop_string variant_name) {
    __auto_type _mv_1430 = type_extract_registry_lookup_variant(reg, variant_name);
    if (_mv_1430.has_value) {
        __auto_type entry = _mv_1430.value;
        {
            __auto_type variants = (*entry).variants;
            __auto_type vlen = ((int64_t)((variants).len));
            __auto_type i = 0;
            slop_option_type_extract_VariantEntry found = (slop_option_type_extract_VariantEntry){.has_value = false};
            while (((i < vlen) && ({ __auto_type _mv = found; _mv.has_value ? (0) : (1); }))) {
                __auto_type _mv_1431 = ({ __auto_type _lst = variants; size_t _idx = (size_t)i; slop_option_type_extract_VariantEntry _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_1431.has_value) {
                    __auto_type ve = _mv_1431.value;
                    if (string_eq(ve.name, variant_name)) {
                        found = (slop_option_type_extract_VariantEntry){.has_value = 1, .value = ve};
                    }
                } else if (!_mv_1431.has_value) {
                }
                i = (i + 1);
            }
            return found;
        }
    } else if (!_mv_1430.has_value) {
        return (slop_option_type_extract_VariantEntry){.has_value = false};
    }
}

slop_option_list_type_extract_TstFieldEntry type_extract_registry_get_record_fields(type_extract_TypeRegistry reg, slop_string name) {
    __auto_type _mv_1432 = type_extract_registry_lookup(reg, name);
    if (_mv_1432.has_value) {
        __auto_type entry = _mv_1432.value;
        if (((*entry).kind == type_extract_TstTypeEntryKind_te_record)) {
            return (slop_option_list_type_extract_TstFieldEntry){.has_value = 1, .value = (*entry).fields};
        } else {
            return (slop_option_list_type_extract_TstFieldEntry){.has_value = false};
        }
    } else if (!_mv_1432.has_value) {
        return (slop_option_list_type_extract_TstFieldEntry){.has_value = false};
    }
}

slop_string type_extract_make_c_type_name(slop_arena* arena, slop_string prefix, slop_string name) {
    if ((((int64_t)(prefix.len)) == 0)) {
        return type_extract_convert_to_c_ident(arena, name);
    } else {
        return string_concat(arena, type_extract_convert_to_c_ident(arena, prefix), string_concat(arena, SLOP_STR("_"), type_extract_convert_to_c_ident(arena, name)));
    }
}

slop_string type_extract_convert_to_c_ident(slop_arena* arena, slop_string name) {
    {
        __auto_type len = ((int64_t)(name.len));
        __auto_type buf = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (len + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        int64_t i = 0;
        while ((i < len)) {
            {
                __auto_type c = name.data[i];
                if ((c == 45)) {
                    buf[i] = 95;
                } else {
                    buf[i] = c;
                }
            }
            i = (i + 1);
        }
        buf[len] = 0;
        return (slop_string){.len = name.len, .data = buf};
    }
}

