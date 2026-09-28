#include "../runtime/slop_runtime.h"
#include "slop_types.h"

types_RangeBounds types_range_bounds_new(uint8_t has_min, int64_t min_val, uint8_t has_max, int64_t max_val);
types_RangeBounds types_range_bounds_unbounded(void);
uint8_t types_range_contains(types_RangeBounds bounds, int64_t value);
int64_t types_min(int64_t a, int64_t b);
int64_t types_max(int64_t a, int64_t b);
types_RangeBounds types_range_intersect(types_RangeBounds a, types_RangeBounds b);
types_RangeBounds types_range_union(types_RangeBounds a, types_RangeBounds b);
types_ResolvedVariant* types_resolved_variant_new(slop_arena* arena, slop_string name, int64_t index, slop_string tag_constant, slop_option_types_ResolvedType_ptr payload, slop_list_types_ResolvedType_ptr payload_types);
types_ResolvedField* types_resolved_field_new(slop_arena* arena, slop_string name, types_ResolvedType* field_type, int64_t offset);
types_ResolvedType* types_resolved_type_new(slop_arena* arena, types_ResolvedTypeKind kind, slop_string name, slop_option_string module_name, slop_string c_name);
void types_resolved_type_set_inner(types_ResolvedType* t, types_ResolvedType* inner);
void types_resolved_type_set_inner2(types_ResolvedType* t, types_ResolvedType* inner);
types_ParamInfo* types_param_info_new(slop_arena* arena, slop_string name, types_ResolvedType* param_type);
types_FnSignature* types_fn_signature_new(slop_arena* arena, slop_string name, slop_string c_name, slop_list_types_ParamInfo params, types_ResolvedType* return_type);
types_TypeError types_type_error_new(types_TypeErrorKind kind, slop_string message, int64_t line, int64_t col);
types_Diagnostic types_diagnostic_new(types_DiagnosticLevel level, slop_string message, int64_t line, int64_t col);
uint8_t types_is_primitive_kind(types_ResolvedTypeKind kind);
uint8_t types_is_container_kind(types_ResolvedTypeKind kind);
uint8_t types_resolved_type_is_pointer(types_ResolvedType* t);
uint8_t types_resolved_type_is_union(types_ResolvedType* t);
uint8_t types_resolved_type_is_record(types_ResolvedType* t);
uint8_t types_resolved_type_is_function(types_ResolvedType* t);
slop_option_int types_resolved_type_get_variant_index(types_ResolvedType* t, slop_string name);
slop_option_types_ResolvedType_ptr types_resolved_type_get_variant_payload(types_ResolvedType* t, slop_string name);
slop_list_types_ResolvedType_ptr types_resolved_type_get_variant_payloads(slop_arena* arena, types_ResolvedType* t, slop_string name);
uint8_t types_resolved_type_has_field(types_ResolvedType* t, slop_string name);
slop_option_types_ResolvedType_ptr types_resolved_type_get_field_type(types_ResolvedType* t, slop_string name);
slop_string types_resolved_type_to_slop_string(slop_arena* arena, types_ResolvedType* t);
slop_string types_mutation_error_message(slop_arena* arena, types_MutationKind kind, types_BindingOrigin origin, slop_string name, uint8_t via_field);
slop_string types_param_mode_error_message(slop_arena* arena, slop_string mode, slop_string name);

types_RangeBounds types_range_bounds_new(uint8_t has_min, int64_t min_val, uint8_t has_max, int64_t max_val) {
    return (types_RangeBounds){has_min, has_max, min_val, max_val};
}

types_RangeBounds types_range_bounds_unbounded(void) {
    return (types_RangeBounds){0, 0, 0, 0};
}

uint8_t types_range_contains(types_RangeBounds bounds, int64_t value) {
    return ((!(bounds.has_min) || (value >= bounds.min_val)) && (!(bounds.has_max) || (value <= bounds.max_val)));
}

int64_t types_min(int64_t a, int64_t b) {
    if (a < b) {
        return a;
    } else {
        return b;
    }
}

int64_t types_max(int64_t a, int64_t b) {
    if (a > b) {
        return a;
    } else {
        return b;
    }
}

types_RangeBounds types_range_intersect(types_RangeBounds a, types_RangeBounds b) {
    {
        __auto_type new_has_min = (a.has_min || b.has_min);
        __auto_type new_has_max = (a.has_max || b.has_max);
        __auto_type new_min_val = ((a.has_min) ? ((b.has_min) ? ((a.min_val) > (b.min_val) ? (a.min_val) : (b.min_val)) : a.min_val) : b.min_val);
        __auto_type new_max_val = ((a.has_max) ? ((b.has_max) ? ((a.max_val) < (b.max_val) ? (a.max_val) : (b.max_val)) : a.max_val) : b.max_val);
        return (types_RangeBounds){new_has_min, new_has_max, new_min_val, new_max_val};
    }
}

types_RangeBounds types_range_union(types_RangeBounds a, types_RangeBounds b) {
    {
        __auto_type new_has_min = (a.has_min && b.has_min);
        __auto_type new_has_max = (a.has_max && b.has_max);
        __auto_type new_min_val = (((a.has_min && b.has_min)) ? ((a.min_val) < (b.min_val) ? (a.min_val) : (b.min_val)) : a.min_val);
        __auto_type new_max_val = (((a.has_max && b.has_max)) ? ((a.max_val) > (b.max_val) ? (a.max_val) : (b.max_val)) : a.max_val);
        return (types_RangeBounds){new_has_min, new_has_max, new_min_val, new_max_val};
    }
}

types_ResolvedVariant* types_resolved_variant_new(slop_arena* arena, slop_string name, int64_t index, slop_string tag_constant, slop_option_types_ResolvedType_ptr payload, slop_list_types_ResolvedType_ptr payload_types) {
    {
        __auto_type v = ((types_ResolvedVariant*)(({ __auto_type _alloc = (types_ResolvedVariant*)slop_arena_alloc(arena, sizeof(types_ResolvedVariant)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        (*v) = (types_ResolvedVariant){name, index, tag_constant, payload, payload_types};
        return v;
    }
}

types_ResolvedField* types_resolved_field_new(slop_arena* arena, slop_string name, types_ResolvedType* field_type, int64_t offset) {
    SLOP_PRE(((field_type != NULL)), "(!= field-type nil)");
    {
        __auto_type f = ((types_ResolvedField*)(({ __auto_type _alloc = (types_ResolvedField*)slop_arena_alloc(arena, sizeof(types_ResolvedField)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        (*f) = (types_ResolvedField){name, field_type, offset};
        return f;
    }
}

types_ResolvedType* types_resolved_type_new(slop_arena* arena, types_ResolvedTypeKind kind, slop_string name, slop_option_string module_name, slop_string c_name) {
    {
        __auto_type t = ((types_ResolvedType*)(({ __auto_type _alloc = (types_ResolvedType*)slop_arena_alloc(arena, sizeof(types_ResolvedType)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        (*t) = (types_ResolvedType){kind, name, module_name, c_name, ((slop_list_types_ResolvedVariant){ .data = (types_ResolvedVariant*)slop_arena_alloc(arena, 16 * sizeof(types_ResolvedVariant)), .len = 0, .cap = 16 }), ((slop_list_types_ResolvedField){ .data = (types_ResolvedField*)slop_arena_alloc(arena, 16 * sizeof(types_ResolvedField)), .len = 0, .cap = 16 }), ((slop_option_types_ResolvedType_ptr){.has_value = false}), ((slop_option_types_ResolvedType_ptr){.has_value = false}), ((slop_option_types_RangeBounds){.has_value = false}), 0, 0};
        return t;
    }
}

void types_resolved_type_set_inner(types_ResolvedType* t, types_ResolvedType* inner) {
    SLOP_PRE(((t != NULL)), "(!= t nil)");
    {
        slop_option_types_ResolvedType_ptr inner_opt = (((inner != NULL)) ? (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = inner} : (slop_option_types_ResolvedType_ptr){.has_value = false});
        (*t).inner_type = inner_opt;
    }
}

void types_resolved_type_set_inner2(types_ResolvedType* t, types_ResolvedType* inner) {
    SLOP_PRE(((t != NULL)), "(!= t nil)");
    {
        slop_option_types_ResolvedType_ptr inner_opt = (((inner != NULL)) ? (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = inner} : (slop_option_types_ResolvedType_ptr){.has_value = false});
        (*t).inner_type2 = inner_opt;
    }
}

types_ParamInfo* types_param_info_new(slop_arena* arena, slop_string name, types_ResolvedType* param_type) {
    SLOP_PRE(((param_type != NULL)), "(!= param-type nil)");
    {
        __auto_type p = ((types_ParamInfo*)(({ __auto_type _alloc = (types_ParamInfo*)slop_arena_alloc(arena, sizeof(types_ParamInfo)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        (*p) = (types_ParamInfo){name, param_type};
        return p;
    }
}

types_FnSignature* types_fn_signature_new(slop_arena* arena, slop_string name, slop_string c_name, slop_list_types_ParamInfo params, types_ResolvedType* return_type) {
    SLOP_PRE(((return_type != NULL)), "(!= return-type nil)");
    {
        __auto_type sig = ((types_FnSignature*)(({ __auto_type _alloc = (types_FnSignature*)slop_arena_alloc(arena, sizeof(types_FnSignature)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        (*sig) = (types_FnSignature){name, c_name, params, return_type, 0, 0, ((slop_option_string){.has_value = false}), ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 }), 0};
        return sig;
    }
}

types_TypeError types_type_error_new(types_TypeErrorKind kind, slop_string message, int64_t line, int64_t col) {
    return (types_TypeError){kind, message, line, col};
}

types_Diagnostic types_diagnostic_new(types_DiagnosticLevel level, slop_string message, int64_t line, int64_t col) {
    return (types_Diagnostic){level, message, line, col};
}

uint8_t types_is_primitive_kind(types_ResolvedTypeKind kind) {
    uint8_t _retval = {0};
    _retval = (kind == types_ResolvedTypeKind_rk_primitive);
    SLOP_POST(((_retval == (kind == types_ResolvedTypeKind_rk_primitive))), "(== $result (== kind (quote rk-primitive)))");
    return _retval;
}

uint8_t types_is_container_kind(types_ResolvedTypeKind kind) {
    uint8_t _retval = {0};
    _retval = (((kind == types_ResolvedTypeKind_rk_list)) || ((kind == types_ResolvedTypeKind_rk_ptr)) || ((kind == types_ResolvedTypeKind_rk_option)) || ((kind == types_ResolvedTypeKind_rk_result)) || ((kind == types_ResolvedTypeKind_rk_map)) || ((kind == types_ResolvedTypeKind_rk_array)));
    SLOP_POST(((_retval == (((kind == types_ResolvedTypeKind_rk_list)) || ((kind == types_ResolvedTypeKind_rk_ptr)) || ((kind == types_ResolvedTypeKind_rk_option)) || ((kind == types_ResolvedTypeKind_rk_result)) || ((kind == types_ResolvedTypeKind_rk_map)) || ((kind == types_ResolvedTypeKind_rk_array))))), "(== $result (or (== kind (quote rk-list)) (== kind (quote rk-ptr)) (== kind (quote rk-option)) (== kind (quote rk-result)) (== kind (quote rk-map)) (== kind (quote rk-array))))");
    return _retval;
}

uint8_t types_resolved_type_is_pointer(types_ResolvedType* t) {
    SLOP_PRE(((t != NULL)), "(!= t nil)");
    uint8_t _retval = {0};
    _retval = ((*t).kind == types_ResolvedTypeKind_rk_ptr);
    SLOP_POST(((_retval == ((*t).kind == types_ResolvedTypeKind_rk_ptr))), "(== $result (== (. (deref t) kind) (quote rk-ptr)))");
    return _retval;
}

uint8_t types_resolved_type_is_union(types_ResolvedType* t) {
    SLOP_PRE(((t != NULL)), "(!= t nil)");
    uint8_t _retval = {0};
    _retval = ((*t).kind == types_ResolvedTypeKind_rk_union);
    SLOP_POST(((_retval == ((*t).kind == types_ResolvedTypeKind_rk_union))), "(== $result (== (. (deref t) kind) (quote rk-union)))");
    return _retval;
}

uint8_t types_resolved_type_is_record(types_ResolvedType* t) {
    SLOP_PRE(((t != NULL)), "(!= t nil)");
    uint8_t _retval = {0};
    _retval = ((*t).kind == types_ResolvedTypeKind_rk_record);
    SLOP_POST(((_retval == ((*t).kind == types_ResolvedTypeKind_rk_record))), "(== $result (== (. (deref t) kind) (quote rk-record)))");
    return _retval;
}

uint8_t types_resolved_type_is_function(types_ResolvedType* t) {
    SLOP_PRE(((t != NULL)), "(!= t nil)");
    uint8_t _retval = {0};
    _retval = ((*t).kind == types_ResolvedTypeKind_rk_function);
    SLOP_POST(((_retval == ((*t).kind == types_ResolvedTypeKind_rk_function))), "(== $result (== (. (deref t) kind) (quote rk-function)))");
    return _retval;
}

slop_option_int types_resolved_type_get_variant_index(types_ResolvedType* t, slop_string name) {
    SLOP_PRE(((t != NULL)), "(!= t nil)");
    SLOP_PRE((((*t).kind == types_ResolvedTypeKind_rk_union)), "(== (. (deref t) kind) (quote rk-union))");
    {
        __auto_type variants = (*t).variants;
        __auto_type len = ((int64_t)((variants).len));
        int64_t i = 0;
        uint8_t done = 0;
        slop_option_int found = (slop_option_int){.has_value = false};
        while ((i < len) && !(done)) {
            __auto_type _mv_5 = ({ __auto_type _lst = variants; size_t _idx = (size_t)i; slop_option_types_ResolvedVariant _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_5.has_value) {
                __auto_type v = _mv_5.value;
                if (string_eq(v.name, name)) {
                    done = 1;
                    found = (slop_option_int){.has_value = 1, .value = v.index};
                }
            } else if (!_mv_5.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

slop_option_types_ResolvedType_ptr types_resolved_type_get_variant_payload(types_ResolvedType* t, slop_string name) {
    SLOP_PRE(((t != NULL)), "(!= t nil)");
    if ((*t).kind == types_ResolvedTypeKind_rk_union) {
        {
            __auto_type variants = (*t).variants;
            __auto_type len = ((int64_t)((variants).len));
            int64_t i = 0;
            uint8_t done = 0;
            slop_option_types_ResolvedType_ptr found = (slop_option_types_ResolvedType_ptr){.has_value = false};
            while ((i < len) && !(done)) {
                __auto_type _mv_6 = ({ __auto_type _lst = variants; size_t _idx = (size_t)i; slop_option_types_ResolvedVariant _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_6.has_value) {
                    __auto_type v = _mv_6.value;
                    if (string_eq(v.name, name)) {
                        done = 1;
                        found = v.payload_type;
                    }
                } else if (!_mv_6.has_value) {
                }
                i = (i + 1);
            }
            return found;
        }
    } else {
        return (slop_option_types_ResolvedType_ptr){.has_value = false};
    }
}

slop_list_types_ResolvedType_ptr types_resolved_type_get_variant_payloads(slop_arena* arena, types_ResolvedType* t, slop_string name) {
    SLOP_PRE(((t != NULL)), "(!= t nil)");
    if ((*t).kind == types_ResolvedTypeKind_rk_union) {
        {
            __auto_type variants = (*t).variants;
            __auto_type len = ((int64_t)((variants).len));
            int64_t i = 0;
            uint8_t done = 0;
            slop_list_types_ResolvedType_ptr found = ((slop_list_types_ResolvedType_ptr){ .data = (types_ResolvedType**)slop_arena_alloc(arena, 16 * sizeof(types_ResolvedType*)), .len = 0, .cap = 16 });
            while ((i < len) && !(done)) {
                __auto_type _mv_7 = ({ __auto_type _lst = variants; size_t _idx = (size_t)i; slop_option_types_ResolvedVariant _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_7.has_value) {
                    __auto_type v = _mv_7.value;
                    if (string_eq(v.name, name)) {
                        done = 1;
                        found = v.payload_types;
                    }
                } else if (!_mv_7.has_value) {
                }
                i = (i + 1);
            }
            return found;
        }
    } else {
        return ((slop_list_types_ResolvedType_ptr){ .data = (types_ResolvedType**)slop_arena_alloc(arena, 16 * sizeof(types_ResolvedType*)), .len = 0, .cap = 16 });
    }
}

uint8_t types_resolved_type_has_field(types_ResolvedType* t, slop_string name) {
    SLOP_PRE(((t != NULL)), "(!= t nil)");
    SLOP_PRE((((*t).kind == types_ResolvedTypeKind_rk_record)), "(== (. (deref t) kind) (quote rk-record))");
    {
        __auto_type fields = (*t).fields;
        __auto_type len = ((int64_t)((fields).len));
        int64_t i = 0;
        uint8_t found = 0;
        while ((i < len) && !(found)) {
            __auto_type _mv_8 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_types_ResolvedField _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_8.has_value) {
                __auto_type f = _mv_8.value;
                if (string_eq(f.name, name)) {
                    found = 1;
                }
            } else if (!_mv_8.has_value) {
            }
            i = (i + 1);
        }
        return found;
    }
}

slop_option_types_ResolvedType_ptr types_resolved_type_get_field_type(types_ResolvedType* t, slop_string name) {
    SLOP_PRE(((t != NULL)), "(!= t nil)");
    {
        __auto_type fields = (*t).fields;
        __auto_type len = ((int64_t)((fields).len));
        int64_t i = 0;
        uint8_t found = 0;
        slop_option_types_ResolvedType_ptr result = (slop_option_types_ResolvedType_ptr){.has_value = false};
        while ((i < len) && !(found)) {
            __auto_type _mv_9 = ({ __auto_type _lst = fields; size_t _idx = (size_t)i; slop_option_types_ResolvedField _r = {0}; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_9.has_value) {
                __auto_type f = _mv_9.value;
                if (string_eq(f.name, name)) {
                    found = 1;
                    result = (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = f.field_type};
                }
            } else if (!_mv_9.has_value) {
            }
            i = (i + 1);
        }
        return result;
    }
}

slop_string types_resolved_type_to_slop_string(slop_arena* arena, types_ResolvedType* t) {
    if (t == NULL) {
        return SLOP_STR("Unknown");
    } else {
        {
            __auto_type kind = (*t).kind;
            __auto_type name = (*t).name;
            __auto_type _mv_10 = kind;
            if (_mv_10 == types_ResolvedTypeKind_rk_primitive) {
                return name;
            } else if (_mv_10 == types_ResolvedTypeKind_rk_record) {
                return name;
            } else if (_mv_10 == types_ResolvedTypeKind_rk_enum) {
                return name;
            } else if (_mv_10 == types_ResolvedTypeKind_rk_union) {
                return name;
            } else if (_mv_10 == types_ResolvedTypeKind_rk_function) {
                return name;
            } else if (_mv_10 == types_ResolvedTypeKind_rk_range) {
                return name;
            } else if (_mv_10 == types_ResolvedTypeKind_rk_option) {
                __auto_type _mv_11 = (*t).inner_type;
                if (_mv_11.has_value) {
                    __auto_type inner = _mv_11.value;
                    return string_concat(arena, SLOP_STR("(Option "), string_concat(arena, types_resolved_type_to_slop_string(arena, inner), SLOP_STR(")")));
                } else if (!_mv_11.has_value) {
                    return SLOP_STR("Option");
                }
                SLOP_UNREACHABLE();
            } else if (_mv_10 == types_ResolvedTypeKind_rk_ptr) {
                __auto_type _mv_12 = (*t).inner_type;
                if (_mv_12.has_value) {
                    __auto_type inner = _mv_12.value;
                    return string_concat(arena, SLOP_STR("(Ptr "), string_concat(arena, types_resolved_type_to_slop_string(arena, inner), SLOP_STR(")")));
                } else if (!_mv_12.has_value) {
                    return SLOP_STR("Ptr");
                }
                SLOP_UNREACHABLE();
            } else if (_mv_10 == types_ResolvedTypeKind_rk_list) {
                __auto_type _mv_13 = (*t).inner_type;
                if (_mv_13.has_value) {
                    __auto_type inner = _mv_13.value;
                    return string_concat(arena, SLOP_STR("(List "), string_concat(arena, types_resolved_type_to_slop_string(arena, inner), SLOP_STR(")")));
                } else if (!_mv_13.has_value) {
                    return SLOP_STR("List");
                }
                SLOP_UNREACHABLE();
            } else if (_mv_10 == types_ResolvedTypeKind_rk_map) {
                __auto_type _mv_14 = (*t).inner_type;
                if (_mv_14.has_value) {
                    __auto_type key_type = _mv_14.value;
                    __auto_type _mv_15 = (*t).inner_type2;
                    if (_mv_15.has_value) {
                        __auto_type val_type = _mv_15.value;
                        return string_concat(arena, SLOP_STR("(Map "), string_concat(arena, types_resolved_type_to_slop_string(arena, key_type), string_concat(arena, SLOP_STR(" "), string_concat(arena, types_resolved_type_to_slop_string(arena, val_type), SLOP_STR(")")))));
                    } else if (!_mv_15.has_value) {
                        return string_concat(arena, SLOP_STR("(Map "), string_concat(arena, types_resolved_type_to_slop_string(arena, key_type), SLOP_STR(")")));
                    }
                    SLOP_UNREACHABLE();
                } else if (!_mv_14.has_value) {
                    return SLOP_STR("Map");
                }
                SLOP_UNREACHABLE();
            } else if (_mv_10 == types_ResolvedTypeKind_rk_result) {
                __auto_type _mv_16 = (*t).inner_type;
                if (_mv_16.has_value) {
                    __auto_type ok_type = _mv_16.value;
                    __auto_type _mv_17 = (*t).inner_type2;
                    if (_mv_17.has_value) {
                        __auto_type err_type = _mv_17.value;
                        return string_concat(arena, SLOP_STR("(Result "), string_concat(arena, types_resolved_type_to_slop_string(arena, ok_type), string_concat(arena, SLOP_STR(" "), string_concat(arena, types_resolved_type_to_slop_string(arena, err_type), SLOP_STR(")")))));
                    } else if (!_mv_17.has_value) {
                        return string_concat(arena, SLOP_STR("(Result "), string_concat(arena, types_resolved_type_to_slop_string(arena, ok_type), SLOP_STR(")")));
                    }
                    SLOP_UNREACHABLE();
                } else if (!_mv_16.has_value) {
                    return SLOP_STR("Result");
                }
                SLOP_UNREACHABLE();
            } else if (_mv_10 == types_ResolvedTypeKind_rk_array) {
                __auto_type _mv_18 = (*t).inner_type;
                if (_mv_18.has_value) {
                    __auto_type inner = _mv_18.value;
                    return string_concat(arena, SLOP_STR("(Array "), string_concat(arena, types_resolved_type_to_slop_string(arena, inner), SLOP_STR(")")));
                } else if (!_mv_18.has_value) {
                    return SLOP_STR("Array");
                }
                SLOP_UNREACHABLE();
            } else if (_mv_10 == types_ResolvedTypeKind_rk_typevar) {
                return name;
            } else {
                return name;
            }
        }
    }
}

slop_string types_mutation_error_message(slop_arena* arena, types_MutationKind kind, types_BindingOrigin origin, slop_string name, uint8_t via_field) {
    {
        __auto_type q = strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 3 * sizeof(slop_string)), .len = 3, .cap = 3 }; _ll.data[0] = SLOP_STR("'"); _ll.data[1] = name; _ll.data[2] = SLOP_STR("'"); _ll; }));
        __auto_type _mv_19 = origin;
        if (_mv_19 == types_BindingOrigin_origin_param) {
            __auto_type _mv_20 = kind;
            if (_mv_20 == types_MutationKind_mut_assign) {
                return strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 5 * sizeof(slop_string)), .len = 5, .cap = 5 }; _ll.data[0] = SLOP_STR("cannot assign to parameter "); _ll.data[1] = q; _ll.data[2] = SLOP_STR(" - it is read-only; declare it (mut "); _ll.data[3] = name; _ll.data[4] = SLOP_STR(" T) to modify a local copy, or pass a (Ptr T) to change the caller's value"); _ll; }));
            } else if (_mv_20 == types_MutationKind_mut_field) {
                return strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 5 * sizeof(slop_string)), .len = 5, .cap = 5 }; _ll.data[0] = SLOP_STR("cannot change a field of parameter "); _ll.data[1] = q; _ll.data[2] = SLOP_STR(" - it is read-only; declare it (mut "); _ll.data[3] = name; _ll.data[4] = SLOP_STR(" T) to modify a local copy, or pass a (Ptr T) to change the caller's value"); _ll; }));
            } else {
                {
                    __auto_type verb = (((kind == types_MutationKind_mut_push)) ? SLOP_STR("push to") : SLOP_STR("pop from"));
                    if (via_field) {
                        return strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 7 * sizeof(slop_string)), .len = 7, .cap = 7 }; _ll.data[0] = SLOP_STR("cannot "); _ll.data[1] = verb; _ll.data[2] = SLOP_STR(" a field of parameter "); _ll.data[3] = q; _ll.data[4] = SLOP_STR(" - it is read-only, and a change to a copy is lost to the caller; declare it (mut "); _ll.data[5] = name; _ll.data[6] = SLOP_STR(" T) and return it, or pass a (Ptr T)"); _ll; }));
                    } else {
                        return strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 7 * sizeof(slop_string)), .len = 7, .cap = 7 }; _ll.data[0] = SLOP_STR("cannot "); _ll.data[1] = verb; _ll.data[2] = SLOP_STR(" parameter "); _ll.data[3] = q; _ll.data[4] = SLOP_STR(" - it is read-only, and a change to a copy is lost to the caller; pass a (Ptr (List T)) and use (deref "); _ll.data[5] = name; _ll.data[6] = SLOP_STR("), or return the new list"); _ll; }));
                    }
                }
            }
        } else if (_mv_19 == types_BindingOrigin_origin_local) {
            if (kind == types_MutationKind_mut_assign) {
                return strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 5 * sizeof(slop_string)), .len = 5, .cap = 5 }; _ll.data[0] = SLOP_STR("cannot assign to "); _ll.data[1] = q; _ll.data[2] = SLOP_STR(" - it is immutable; declare it (let ((mut "); _ll.data[3] = name; _ll.data[4] = SLOP_STR(" ...)))"); _ll; }));
            } else {
                return strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 5 * sizeof(slop_string)), .len = 5, .cap = 5 }; _ll.data[0] = SLOP_STR("cannot change a field of "); _ll.data[1] = q; _ll.data[2] = SLOP_STR(" - it is immutable; declare it (let ((mut "); _ll.data[3] = name; _ll.data[4] = SLOP_STR(" ...)))"); _ll; }));
            }
        } else if (_mv_19 == types_BindingOrigin_origin_bound) {
            return strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 5 * sizeof(slop_string)), .len = 5, .cap = 5 }; _ll.data[0] = (((kind == types_MutationKind_mut_assign)) ? SLOP_STR("cannot assign to ") : SLOP_STR("cannot change a field of ")); _ll.data[1] = q; _ll.data[2] = SLOP_STR(" - names bound by for, for-each, match and with-arena are immutable; copy it into (let ((mut "); _ll.data[3] = name; _ll.data[4] = SLOP_STR(" ...)))"); _ll; }));
        } else if (_mv_19 == types_BindingOrigin_origin_const) {
            return strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 2 * sizeof(slop_string)), .len = 2, .cap = 2 }; _ll.data[0] = (((kind == types_MutationKind_mut_assign)) ? SLOP_STR("cannot assign to constant ") : SLOP_STR("cannot change a field of constant ")); _ll.data[1] = q; _ll; }));
        }
        SLOP_UNREACHABLE();
    }
}

slop_string types_param_mode_error_message(slop_arena* arena, slop_string mode, slop_string name) {
    if (string_eq(mode, SLOP_STR("mut"))) {
        return strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 3 * sizeof(slop_string)), .len = 3, .cap = 3 }; _ll.data[0] = SLOP_STR("'mut' is not allowed on parameter '"); _ll.data[1] = name; _ll.data[2] = SLOP_STR("' - a copy of a List, Map or Set shares the caller's storage; use (Ptr (List T)) to change the caller's list"); _ll; }));
    } else if (string_eq(mode, SLOP_STR("out"))) {
        return strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 3 * sizeof(slop_string)), .len = 3, .cap = 3 }; _ll.data[0] = SLOP_STR("'out' parameter '"); _ll.data[1] = name; _ll.data[2] = SLOP_STR("' is not supported - use a (Ptr T) parameter and pass (addr x)"); _ll; }));
    } else {
        return strlib_string_build(arena, ({ slop_list_string _ll = (slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 3 * sizeof(slop_string)), .len = 3, .cap = 3 }; _ll.data[0] = SLOP_STR("unknown parameter mode '"); _ll.data[1] = mode; _ll.data[2] = SLOP_STR("' - write (name Type) or (mut name Type)"); _ll; }));
    }
}

