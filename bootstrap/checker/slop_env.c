#include "../runtime/slop_runtime.h"
#include "slop_env.h"

env_TypeEnv* env_env_new(slop_arena* arena);
slop_arena* env_env_arena(env_TypeEnv* env);
void env_env_push_scope(env_TypeEnv* env);
void env_env_pop_scope(env_TypeEnv* env);
void env_env_bind_var(env_TypeEnv* env, slop_string name, types_ResolvedType* var_type);
slop_option_types_ResolvedType_ptr env_scope_lookup_var(env_Scope* scope_ptr, slop_string name);
slop_option_types_ResolvedType_ptr env_env_lookup_var(env_TypeEnv* env, slop_string name);
void env_env_register_constant(env_TypeEnv* env, slop_string name, types_ResolvedType* const_type);
slop_option_types_ResolvedType_ptr env_env_lookup_constant(env_TypeEnv* env, slop_string name);
void env_env_register_type(env_TypeEnv* env, types_ResolvedType* t);
slop_option_types_ResolvedType_ptr env_env_lookup_type_direct(env_TypeEnv* env, slop_string name);
slop_option_types_ResolvedType_ptr env_env_lookup_type(env_TypeEnv* env, slop_string name);
slop_option_types_ResolvedType_ptr env_env_lookup_type_qualified(env_TypeEnv* env, slop_string module_name, slop_string type_name);
void env_env_register_function(env_TypeEnv* env, types_FnSignature* sig);
slop_option_types_FnSignature_ptr env_env_lookup_function_direct(env_TypeEnv* env, slop_string name);
slop_option_types_FnSignature_ptr env_env_lookup_function(env_TypeEnv* env, slop_string name);
void env_env_add_import(env_TypeEnv* env, slop_string local_name, slop_string qualified_name);
slop_option_string env_env_resolve_import(env_TypeEnv* env, slop_string local_name);
void env_env_register_variant(env_TypeEnv* env, slop_string variant_name, slop_string enum_name);
slop_option_string env_env_lookup_variant(env_TypeEnv* env, slop_string variant_name);
void env_env_check_variant_collisions(env_TypeEnv* env);
void env_env_set_module(env_TypeEnv* env, slop_option_string module_name);
slop_option_string env_env_get_module(env_TypeEnv* env);
types_ResolvedType* env_env_get_int_type(env_TypeEnv* env);
types_ResolvedType* env_env_get_bool_type(env_TypeEnv* env);
types_ResolvedType* env_env_get_string_type(env_TypeEnv* env);
types_ResolvedType* env_env_get_unit_type(env_TypeEnv* env);
types_ResolvedType* env_env_get_arena_type(env_TypeEnv* env);
types_ResolvedType* env_env_get_unknown_type(env_TypeEnv* env);
types_ResolvedType* env_env_make_option_type(env_TypeEnv* env, types_ResolvedType* inner_type);
types_ResolvedType* env_env_make_ptr_type(env_TypeEnv* env, types_ResolvedType* inner_type);
types_ResolvedType* env_env_get_generic_type(env_TypeEnv* env);
types_ResolvedType* env_env_make_result_type(env_TypeEnv* env);
types_ResolvedType* env_env_make_fn_type(env_TypeEnv* env, types_FnSignature* sig);
void env_env_add_warning(env_TypeEnv* env, slop_string message, int64_t line, int64_t col);
void env_env_add_error(env_TypeEnv* env, slop_string message, int64_t line, int64_t col);
slop_list_types_Diagnostic env_env_get_diagnostics(env_TypeEnv* env);
void env_env_clear_diagnostics(env_TypeEnv* env);
void env_env_record_binding(env_TypeEnv* env, slop_string name, int64_t line, int64_t col, slop_string slop_type);
slop_list_env_BindingAnnotation env_env_get_binding_annotations(env_TypeEnv* env);
void env_env_set_current_file(env_TypeEnv* env, slop_option_string file_path);
slop_option_string env_env_get_current_file(env_TypeEnv* env);
void env_env_add_loaded_module(env_TypeEnv* env, slop_string module_path);
uint8_t env_env_is_module_loaded(env_TypeEnv* env, slop_string module_path);

env_TypeEnv* env_env_new(slop_arena* arena) {
    {
        __auto_type int_t = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Int"), ((slop_option_string){.has_value = false}), SLOP_STR("int64_t"));
        __auto_type bool_t = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Bool"), ((slop_option_string){.has_value = false}), SLOP_STR("bool"));
        __auto_type string_t = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("String"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_string_t"));
        __auto_type unit_t = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Unit"), ((slop_option_string){.has_value = false}), SLOP_STR("void"));
        __auto_type arena_t = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Arena"), ((slop_option_string){.has_value = false}), SLOP_STR("slop_arena_t*"));
        __auto_type unknown_t = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("Unknown"), ((slop_option_string){.has_value = false}), SLOP_STR("void"));
        __auto_type env = ((env_TypeEnv*)((uint8_t*)slop_arena_alloc(arena, 256)));
        (*env) = (env_TypeEnv){arena, ((slop_list_types_ResolvedType_ptr){ .data = (types_ResolvedType**)slop_arena_alloc(arena, 16 * sizeof(types_ResolvedType*)), .len = 0, .cap = 16 }), ((slop_list_types_FnSignature_ptr){ .data = (types_FnSignature**)slop_arena_alloc(arena, 16 * sizeof(types_FnSignature*)), .len = 0, .cap = 16 }), ((slop_list_env_ConstBinding){ .data = (env_ConstBinding*)slop_arena_alloc(arena, 16 * sizeof(env_ConstBinding)), .len = 0, .cap = 16 }), ((slop_list_env_ImportEntry){ .data = (env_ImportEntry*)slop_arena_alloc(arena, 16 * sizeof(env_ImportEntry)), .len = 0, .cap = 16 }), ((slop_list_env_VariantMapping){ .data = (env_VariantMapping*)slop_arena_alloc(arena, 16 * sizeof(env_VariantMapping)), .len = 0, .cap = 16 }), ((slop_list_env_Scope_ptr){ .data = (env_Scope**)slop_arena_alloc(arena, 16 * sizeof(env_Scope*)), .len = 0, .cap = 16 }), ((slop_option_string){.has_value = false}), int_t, bool_t, string_t, unit_t, arena_t, unknown_t, ((slop_list_types_Diagnostic){ .data = (types_Diagnostic*)slop_arena_alloc(arena, 16 * sizeof(types_Diagnostic)), .len = 0, .cap = 16 }), ((slop_list_env_BindingAnnotation){ .data = (env_BindingAnnotation*)slop_arena_alloc(arena, 16 * sizeof(env_BindingAnnotation)), .len = 0, .cap = 16 }), ((slop_option_string){.has_value = false}), ((slop_list_string){ .data = (slop_string*)slop_arena_alloc(arena, 16 * sizeof(slop_string)), .len = 0, .cap = 16 })};
        ({ __auto_type _lst_p = &((*env).types); __auto_type _item = (int_t); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
        ({ __auto_type _lst_p = &((*env).types); __auto_type _item = (bool_t); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
        ({ __auto_type _lst_p = &((*env).types); __auto_type _item = (string_t); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
        ({ __auto_type _lst_p = &((*env).types); __auto_type _item = (unit_t); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
        ({ __auto_type _lst_p = &((*env).types); __auto_type _item = (arena_t); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
        {
            __auto_type i8 = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("I8"), ((slop_option_string){.has_value = false}), SLOP_STR("int8_t"));
            __auto_type i16 = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("I16"), ((slop_option_string){.has_value = false}), SLOP_STR("int16_t"));
            __auto_type i32 = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("I32"), ((slop_option_string){.has_value = false}), SLOP_STR("int32_t"));
            __auto_type i64 = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("I64"), ((slop_option_string){.has_value = false}), SLOP_STR("int64_t"));
            __auto_type u8 = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("U8"), ((slop_option_string){.has_value = false}), SLOP_STR("uint8_t"));
            __auto_type u16 = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("U16"), ((slop_option_string){.has_value = false}), SLOP_STR("uint16_t"));
            __auto_type u32 = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("U32"), ((slop_option_string){.has_value = false}), SLOP_STR("uint32_t"));
            __auto_type u64 = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("U64"), ((slop_option_string){.has_value = false}), SLOP_STR("uint64_t"));
            __auto_type f32 = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("F32"), ((slop_option_string){.has_value = false}), SLOP_STR("float"));
            __auto_type f64 = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("F64"), ((slop_option_string){.has_value = false}), SLOP_STR("double"));
            ({ __auto_type _lst_p = &((*env).types); __auto_type _item = (i8); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            ({ __auto_type _lst_p = &((*env).types); __auto_type _item = (i16); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            ({ __auto_type _lst_p = &((*env).types); __auto_type _item = (i32); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            ({ __auto_type _lst_p = &((*env).types); __auto_type _item = (i64); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            ({ __auto_type _lst_p = &((*env).types); __auto_type _item = (u8); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            ({ __auto_type _lst_p = &((*env).types); __auto_type _item = (u16); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            ({ __auto_type _lst_p = &((*env).types); __auto_type _item = (u32); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            ({ __auto_type _lst_p = &((*env).types); __auto_type _item = (u64); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            ({ __auto_type _lst_p = &((*env).types); __auto_type _item = (f32); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
            ({ __auto_type _lst_p = &((*env).types); __auto_type _item = (f64); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
        }
        return env;
    }
}

slop_arena* env_env_arena(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    return (*env).arena;
}

void env_env_push_scope(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type arena = (*env).arena;
        __auto_type scope_ptr = ((env_Scope*)((uint8_t*)slop_arena_alloc(arena, 64)));
        (*scope_ptr) = (env_Scope){((slop_list_env_VarBinding){ .data = (env_VarBinding*)slop_arena_alloc(arena, 16 * sizeof(env_VarBinding)), .len = 0, .cap = 16 })};
        ({ __auto_type _lst_p = &((*env).scopes); __auto_type _item = (scope_ptr); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
    }
}

void env_env_pop_scope(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((((int64_t)(((*env).scopes).len)) > 0)), "(> (list-len (. (deref env) scopes)) 0)");
    {
        __auto_type _ = ({ __auto_type _lst_p = &((*env).scopes); struct { bool has_value; __typeof__(_lst_p->data[0]) value; } _r = {0}; if (_lst_p->len > 0) { _lst_p->len--; _r.has_value = true; _r.value = _lst_p->data[_lst_p->len]; } _r; });
    }
}

void env_env_bind_var(env_TypeEnv* env, slop_string name, types_ResolvedType* var_type) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((var_type != NULL)), "(!= var-type nil)");
    SLOP_PRE(((((int64_t)(((*env).scopes).len)) > 0)), "(> (list-len (. (deref env) scopes)) 0)");
    {
        __auto_type arena = (*env).arena;
        __auto_type scopes = (*env).scopes;
        __auto_type top_idx = (((int64_t)((scopes).len)) - 1);
        __auto_type _mv_18 = ({ __auto_type _lst = scopes; size_t _idx = (size_t)top_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
        if (_mv_18.has_value) {
            __auto_type scope_ptr = _mv_18.value;
            ({ __auto_type _lst_p = &((*scope_ptr).bindings); __auto_type _item = ((env_VarBinding){name, var_type}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
        } else if (!_mv_18.has_value) {
        }
    }
}

slop_option_types_ResolvedType_ptr env_scope_lookup_var(env_Scope* scope_ptr, slop_string name) {
    SLOP_PRE(((scope_ptr != NULL)), "(!= scope-ptr nil)");
    {
        __auto_type bindings = (*scope_ptr).bindings;
        __auto_type num_bindings = ((int64_t)((bindings).len));
        __auto_type found = 0;
        slop_option_types_ResolvedType_ptr result = (slop_option_types_ResolvedType_ptr){.has_value = false};
        for (int64_t j = 0; j < num_bindings; j++) {
            __auto_type _mv_19 = ({ __auto_type _lst = bindings; size_t _idx = (size_t)j; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_19.has_value) {
                __auto_type binding = _mv_19.value;
                if ((!(found) && string_eq(binding.name, name))) {
                    found = 1;
                    result = (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = binding.var_type};
                }
            } else if (!_mv_19.has_value) {
            }
        }
        return result;
    }
}

slop_option_types_ResolvedType_ptr env_env_lookup_var(env_TypeEnv* env, slop_string name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type scopes = (*env).scopes;
        __auto_type num_scopes = ((int64_t)((scopes).len));
        __auto_type found = 0;
        slop_option_types_ResolvedType_ptr result = (slop_option_types_ResolvedType_ptr){.has_value = false};
        for (int64_t i = 0; i < num_scopes; i++) {
            if (!(found)) {
                {
                    __auto_type scope_idx = ((num_scopes) - (1) - (i));
                    __auto_type _mv_20 = ({ __auto_type _lst = scopes; size_t _idx = (size_t)scope_idx; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                    if (_mv_20.has_value) {
                        __auto_type scope_ptr = _mv_20.value;
                        __auto_type _mv_21 = env_scope_lookup_var(scope_ptr, name);
                        if (_mv_21.has_value) {
                            __auto_type var_type = _mv_21.value;
                            found = 1;
                            result = (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = var_type};
                        } else if (!_mv_21.has_value) {
                        }
                    } else if (!_mv_20.has_value) {
                    }
                }
            }
        }
        return result;
    }
}

void env_env_register_constant(env_TypeEnv* env, slop_string name, types_ResolvedType* const_type) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((const_type != NULL)), "(!= const-type nil)");
    ({ __auto_type _lst_p = &((*env).constants); __auto_type _item = ((env_ConstBinding){name, const_type}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(env->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_option_types_ResolvedType_ptr env_env_lookup_constant(env_TypeEnv* env, slop_string name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type constants = (*env).constants;
        __auto_type len = ((int64_t)((constants).len));
        __auto_type found = 0;
        slop_option_types_ResolvedType_ptr result = (slop_option_types_ResolvedType_ptr){.has_value = false};
        for (int64_t i = 0; i < len; i++) {
            if (!(found)) {
                __auto_type _mv_22 = ({ __auto_type _lst = constants; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
                if (_mv_22.has_value) {
                    __auto_type binding = _mv_22.value;
                    if (string_eq(binding.name, name)) {
                        found = 1;
                        result = (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = binding.const_type};
                    }
                } else if (!_mv_22.has_value) {
                }
            }
        }
        return result;
    }
}

void env_env_register_type(env_TypeEnv* env, types_ResolvedType* t) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((t != NULL)), "(!= t nil)");
    ({ __auto_type _lst_p = &((*env).types); __auto_type _item = (t); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(env->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_option_types_ResolvedType_ptr env_env_lookup_type_direct(env_TypeEnv* env, slop_string name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type types = (*env).types;
        __auto_type len = ((int64_t)((types).len));
        __auto_type found = 0;
        slop_option_types_ResolvedType_ptr result = (slop_option_types_ResolvedType_ptr){.has_value = false};
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_23 = ({ __auto_type _lst = types; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_23.has_value) {
                __auto_type t = _mv_23.value;
                if ((!(found) && string_eq((*t).name, name))) {
                    found = 1;
                    result = (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = t};
                }
            } else if (!_mv_23.has_value) {
            }
        }
        return result;
    }
}

slop_option_types_ResolvedType_ptr env_env_lookup_type(env_TypeEnv* env, slop_string name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_24 = env_env_lookup_type_direct(env, name);
    if (_mv_24.has_value) {
        __auto_type t = _mv_24.value;
        return (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = t};
    } else if (!_mv_24.has_value) {
        __auto_type _mv_25 = env_env_resolve_import(env, name);
        if (_mv_25.has_value) {
            __auto_type qualified_name = _mv_25.value;
            return env_env_lookup_type_direct(env, qualified_name);
        } else if (!_mv_25.has_value) {
            return (slop_option_types_ResolvedType_ptr){.has_value = false};
        }
    }
}

slop_option_types_ResolvedType_ptr env_env_lookup_type_qualified(env_TypeEnv* env, slop_string module_name, slop_string type_name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type types = (*env).types;
        __auto_type len = ((int64_t)((types).len));
        __auto_type found = 0;
        slop_option_types_ResolvedType_ptr result = (slop_option_types_ResolvedType_ptr){.has_value = false};
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_26 = ({ __auto_type _lst = types; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_26.has_value) {
                __auto_type t = _mv_26.value;
                if (!(found)) {
                    __auto_type _mv_27 = (*t).module_name;
                    if (_mv_27.has_value) {
                        __auto_type mod = _mv_27.value;
                        if ((string_eq(mod, module_name) && string_eq((*t).name, type_name))) {
                            found = 1;
                            result = (slop_option_types_ResolvedType_ptr){.has_value = 1, .value = t};
                        }
                    } else if (!_mv_27.has_value) {
                    }
                }
            } else if (!_mv_26.has_value) {
            }
        }
        return result;
    }
}

void env_env_register_function(env_TypeEnv* env, types_FnSignature* sig) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((sig != NULL)), "(!= sig nil)");
    ({ __auto_type _lst_p = &((*env).functions); __auto_type _item = (sig); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(env->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_option_types_FnSignature_ptr env_env_lookup_function_direct(env_TypeEnv* env, slop_string name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type functions = (*env).functions;
        __auto_type len = ((int64_t)((functions).len));
        __auto_type found = 0;
        slop_option_types_FnSignature_ptr result = (slop_option_types_FnSignature_ptr){.has_value = false};
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_28 = ({ __auto_type _lst = functions; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_28.has_value) {
                __auto_type sig = _mv_28.value;
                if ((!(found) && string_eq((*sig).name, name))) {
                    found = 1;
                    result = (slop_option_types_FnSignature_ptr){.has_value = 1, .value = sig};
                }
            } else if (!_mv_28.has_value) {
            }
        }
        return result;
    }
}

slop_option_types_FnSignature_ptr env_env_lookup_function(env_TypeEnv* env, slop_string name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    __auto_type _mv_29 = env_env_lookup_function_direct(env, name);
    if (_mv_29.has_value) {
        __auto_type sig = _mv_29.value;
        return (slop_option_types_FnSignature_ptr){.has_value = 1, .value = sig};
    } else if (!_mv_29.has_value) {
        __auto_type _mv_30 = env_env_resolve_import(env, name);
        if (_mv_30.has_value) {
            __auto_type import_qualified = _mv_30.value;
            return env_env_lookup_function_direct(env, import_qualified);
        } else if (!_mv_30.has_value) {
            __auto_type _mv_31 = env_env_get_module(env);
            if (_mv_31.has_value) {
                __auto_type mod = _mv_31.value;
                {
                    __auto_type qualified = string_concat(env_env_arena(env), mod, string_concat(env_env_arena(env), SLOP_STR(":"), name));
                    return env_env_lookup_function_direct(env, qualified);
                }
            } else if (!_mv_31.has_value) {
                return (slop_option_types_FnSignature_ptr){.has_value = false};
            }
        }
    }
}

void env_env_add_import(env_TypeEnv* env, slop_string local_name, slop_string qualified_name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    ({ __auto_type _lst_p = &((*env).imports); __auto_type _item = ((env_ImportEntry){local_name, qualified_name}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(env->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_option_string env_env_resolve_import(env_TypeEnv* env, slop_string local_name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type imports = (*env).imports;
        __auto_type len = ((int64_t)((imports).len));
        __auto_type found = 0;
        slop_option_string result = (slop_option_string){.has_value = false};
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_32 = ({ __auto_type _lst = imports; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_32.has_value) {
                __auto_type entry = _mv_32.value;
                if ((!(found) && string_eq(entry.local, local_name))) {
                    found = 1;
                    result = (slop_option_string){.has_value = 1, .value = entry.qualified};
                }
            } else if (!_mv_32.has_value) {
            }
        }
        return result;
    }
}

void env_env_register_variant(env_TypeEnv* env, slop_string variant_name, slop_string enum_name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    ({ __auto_type _lst_p = &((*env).enum_variants); __auto_type _item = ((env_VariantMapping){variant_name, enum_name}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(env->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_option_string env_env_lookup_variant(env_TypeEnv* env, slop_string variant_name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type variants = (*env).enum_variants;
        __auto_type len = ((int64_t)((variants).len));
        __auto_type found = 0;
        slop_option_string result = (slop_option_string){.has_value = false};
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_33 = ({ __auto_type _lst = variants; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_33.has_value) {
                __auto_type v = _mv_33.value;
                if ((!(found) && string_eq(v.variant_name, variant_name))) {
                    found = 1;
                    result = (slop_option_string){.has_value = 1, .value = v.enum_name};
                }
            } else if (!_mv_33.has_value) {
            }
        }
        return result;
    }
}

void env_env_check_variant_collisions(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type variants = (*env).enum_variants;
        __auto_type len = ((int64_t)((variants).len));
        __auto_type arena = (*env).arena;
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_34 = ({ __auto_type _lst = variants; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_34.has_value) {
                __auto_type v1 = _mv_34.value;
                {
                    __auto_type name1 = v1.variant_name;
                    __auto_type enum1 = v1.enum_name;
                    __auto_type found_collision = 0;
                    slop_string collision_enum = SLOP_STR("");
                    ({ for (int64_t j = (i + 1); j < len; j++) { ({ __auto_type _mv = ({ __auto_type _lst = variants; size_t _idx = (size_t)j; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; }); if (_mv.has_value) { __auto_type v2 = _mv.value; (((!(found_collision) && (string_eq(v2.variant_name, name1) && !(string_eq(v2.enum_name, enum1))))) ? ({ ({ found_collision = 1; (void)0; }); ({ collision_enum = v2.enum_name; (void)0; }); 0; }) : ({ (void)0; })); } else { ({ (void)0; }); } (void)0; }); } 0; });
                    if (found_collision) {
                        {
                            __auto_type msg = string_concat(arena, SLOP_STR("Ambiguous enum variant '"), string_concat(arena, name1, string_concat(arena, SLOP_STR("' exists in multiple types: "), string_concat(arena, enum1, string_concat(arena, SLOP_STR(", "), collision_enum)))));
                            env_env_add_error(env, msg, 0, 0);
                        }
                    }
                }
            } else if (!_mv_34.has_value) {
            }
        }
    }
}

void env_env_set_module(env_TypeEnv* env, slop_option_string module_name) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    (*env).current_module = module_name;
}

slop_option_string env_env_get_module(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    return (*env).current_module;
}

types_ResolvedType* env_env_get_int_type(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    types_ResolvedType* _retval;
    return (*env).int_type;
    SLOP_POST(((_retval != NULL)), "(!= $result nil)");
    return _retval;
}

types_ResolvedType* env_env_get_bool_type(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    types_ResolvedType* _retval;
    return (*env).bool_type;
    SLOP_POST(((_retval != NULL)), "(!= $result nil)");
    return _retval;
}

types_ResolvedType* env_env_get_string_type(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    types_ResolvedType* _retval;
    return (*env).string_type;
    SLOP_POST(((_retval != NULL)), "(!= $result nil)");
    return _retval;
}

types_ResolvedType* env_env_get_unit_type(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    types_ResolvedType* _retval;
    return (*env).unit_type;
    SLOP_POST(((_retval != NULL)), "(!= $result nil)");
    return _retval;
}

types_ResolvedType* env_env_get_arena_type(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    types_ResolvedType* _retval;
    return (*env).arena_type;
    SLOP_POST(((_retval != NULL)), "(!= $result nil)");
    return _retval;
}

types_ResolvedType* env_env_get_unknown_type(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    types_ResolvedType* _retval;
    return (*env).unknown_type;
    SLOP_POST(((_retval != NULL)), "(!= $result nil)");
    return _retval;
}

types_ResolvedType* env_env_make_option_type(env_TypeEnv* env, types_ResolvedType* inner_type) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    types_ResolvedType* _retval;
    {
        __auto_type arena = (*env).arena;
        __auto_type inner_name = (((inner_type != NULL)) ? (*inner_type).name : SLOP_STR("T"));
        __auto_type opt_name = string_concat(arena, SLOP_STR("Option_"), inner_name);
        __auto_type opt_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_option, opt_name, ((slop_option_string){.has_value = false}), opt_name);
        types_resolved_type_set_inner(opt_type, inner_type);
        return opt_type;
    }
    SLOP_POST(((_retval != NULL)), "(!= $result nil)");
    return _retval;
}

types_ResolvedType* env_env_make_ptr_type(env_TypeEnv* env, types_ResolvedType* inner_type) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    types_ResolvedType* _retval;
    {
        __auto_type arena = (*env).arena;
        __auto_type inner_name = (((inner_type != NULL)) ? (*inner_type).name : SLOP_STR("Void"));
        __auto_type ptr_name = string_concat(arena, SLOP_STR("Ptr_"), inner_name);
        __auto_type ptr_type = types_resolved_type_new(arena, types_ResolvedTypeKind_rk_ptr, ptr_name, ((slop_option_string){.has_value = false}), ptr_name);
        types_resolved_type_set_inner(ptr_type, inner_type);
        return ptr_type;
    }
    SLOP_POST(((_retval != NULL)), "(!= $result nil)");
    return _retval;
}

types_ResolvedType* env_env_get_generic_type(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    types_ResolvedType* _retval;
    {
        __auto_type arena = (*env).arena;
        return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_primitive, SLOP_STR("T"), ((slop_option_string){.has_value = false}), SLOP_STR("void*"));
    }
    SLOP_POST(((_retval != NULL)), "(!= $result nil)");
    return _retval;
}

types_ResolvedType* env_env_make_result_type(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    types_ResolvedType* _retval;
    {
        __auto_type arena = (*env).arena;
        return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_result, SLOP_STR("Result"), ((slop_option_string){.has_value = false}), SLOP_STR("Result"));
    }
    SLOP_POST(((_retval != NULL)), "(!= $result nil)");
    return _retval;
}

types_ResolvedType* env_env_make_fn_type(env_TypeEnv* env, types_FnSignature* sig) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    SLOP_PRE(((sig != NULL)), "(!= sig nil)");
    types_ResolvedType* _retval;
    {
        __auto_type arena = (*env).arena;
        __auto_type fn_name = string_concat(arena, SLOP_STR("Fn_"), (*sig).name);
        return types_resolved_type_new(arena, types_ResolvedTypeKind_rk_function, fn_name, ((slop_option_string){.has_value = false}), fn_name);
    }
    SLOP_POST(((_retval != NULL)), "(!= $result nil)");
    return _retval;
}

void env_env_add_warning(env_TypeEnv* env, slop_string message, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    ({ __auto_type _lst_p = &((*env).diagnostics); __auto_type _item = (types_diagnostic_new(types_DiagnosticLevel_diag_warning, message, line, col)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(env->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

void env_env_add_error(env_TypeEnv* env, slop_string message, int64_t line, int64_t col) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    ({ __auto_type _lst_p = &((*env).diagnostics); __auto_type _item = (types_diagnostic_new(types_DiagnosticLevel_diag_error, message, line, col)); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(env->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_list_types_Diagnostic env_env_get_diagnostics(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    return (*env).diagnostics;
}

void env_env_clear_diagnostics(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type arena = (*env).arena;
        (*env).diagnostics = ((slop_list_types_Diagnostic){ .data = (types_Diagnostic*)slop_arena_alloc(arena, 16 * sizeof(types_Diagnostic)), .len = 0, .cap = 16 });
    }
}

void env_env_record_binding(env_TypeEnv* env, slop_string name, int64_t line, int64_t col, slop_string slop_type) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    ({ __auto_type _lst_p = &((*env).binding_annotations); __auto_type _item = ((env_BindingAnnotation){name, line, col, slop_type}); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(env->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

slop_list_env_BindingAnnotation env_env_get_binding_annotations(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    return (*env).binding_annotations;
}

void env_env_set_current_file(env_TypeEnv* env, slop_option_string file_path) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    (*env).current_file = file_path;
}

slop_option_string env_env_get_current_file(env_TypeEnv* env) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    return (*env).current_file;
}

void env_env_add_loaded_module(env_TypeEnv* env, slop_string module_path) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    ({ __auto_type _lst_p = &((*env).loaded_modules); __auto_type _item = (module_path); if (_lst_p->len >= _lst_p->cap) { size_t _new_cap = _lst_p->cap == 0 ? 16 : _lst_p->cap * 2; __typeof__(_lst_p->data) _new_data = (__typeof__(_lst_p->data))slop_arena_alloc(env->arena, _new_cap * sizeof(*_lst_p->data)); if (_lst_p->len > 0) memcpy(_new_data, _lst_p->data, _lst_p->len * sizeof(*_lst_p->data)); _lst_p->data = _new_data; _lst_p->cap = _new_cap; } _lst_p->data[_lst_p->len++] = _item; (void)0; });
}

uint8_t env_env_is_module_loaded(env_TypeEnv* env, slop_string module_path) {
    SLOP_PRE(((env != NULL)), "(!= env nil)");
    {
        __auto_type modules = (*env).loaded_modules;
        __auto_type len = ((int64_t)((modules).len));
        __auto_type found = 0;
        for (int64_t i = 0; i < len; i++) {
            __auto_type _mv_35 = ({ __auto_type _lst = modules; size_t _idx = (size_t)i; struct { bool has_value; __typeof__(_lst.data[0]) value; } _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_35.has_value) {
                __auto_type path = _mv_35.value;
                if ((!(found) && string_eq(path, module_path))) {
                    found = 1;
                }
            } else if (!_mv_35.has_value) {
            }
        }
        return found;
    }
}

