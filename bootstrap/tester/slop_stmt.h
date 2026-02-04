#ifndef SLOP_stmt_H
#define SLOP_stmt_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_types.h"
#include "slop_parser.h"
#include "slop_context.h"
#include "slop_ctype.h"
#include "slop_expr.h"
#include "slop_strlib.h"
#include "slop_match.h"

#ifndef SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
SLOP_LIST_DEFINE(types_SExpr*, slop_list_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

slop_string stmt_sexpr_to_type_string(slop_arena* arena, types_SExpr* expr);
slop_option_string stmt_get_arena_alloc_ptr_type(context_TranspileContext* ctx, types_SExpr* expr);
slop_option_string stmt_extract_sizeof_type_opt(context_TranspileContext* ctx, types_SExpr* expr);
uint8_t stmt_is_stmt_form(types_SExpr* expr);
void stmt_transpile_let(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return);
void stmt_transpile_bindings(context_TranspileContext* ctx, slop_list_types_SExpr_ptr bindings);
void stmt_transpile_single_binding(context_TranspileContext* ctx, types_SExpr* binding);
uint8_t stmt_binding_has_mut(slop_list_types_SExpr_ptr items);
slop_option_types_SExpr_ptr stmt_get_some_value(types_SExpr* expr);
uint8_t stmt_is_none_form(types_SExpr* expr);
void stmt_transpile_if(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return);
void stmt_transpile_when(context_TranspileContext* ctx, types_SExpr* expr);
void stmt_transpile_while(context_TranspileContext* ctx, types_SExpr* expr);
void stmt_transpile_set(context_TranspileContext* ctx, types_SExpr* expr);
slop_option_string stmt_get_var_c_type(context_TranspileContext* ctx, types_SExpr* expr);
uint8_t stmt_is_pointer_target(context_TranspileContext* ctx, types_SExpr* expr);
void stmt_transpile_field_set(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
void stmt_transpile_typed_field_set(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items);
uint8_t stmt_is_deref_expr(types_SExpr* expr);
types_SExpr* stmt_get_deref_inner(types_SExpr* expr);
slop_string stmt_get_symbol_name(slop_arena* arena, types_SExpr* expr);
void stmt_transpile_do(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return);
void stmt_transpile_with_arena(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return);
void stmt_transpile_cond(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return);
void stmt_transpile_cond_body(context_TranspileContext* ctx, slop_list_types_SExpr_ptr items, int64_t start, uint8_t is_return);
void stmt_transpile_for(context_TranspileContext* ctx, types_SExpr* expr);
void stmt_transpile_for_each(context_TranspileContext* ctx, types_SExpr* expr);
void stmt_transpile_stmt(context_TranspileContext* ctx, types_SExpr* expr, uint8_t is_return);
void stmt_emit_typed_return_expr(context_TranspileContext* ctx, types_SExpr* expr);
void stmt_emit_return_with_typed_none(context_TranspileContext* ctx, slop_string code);

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif


#endif
