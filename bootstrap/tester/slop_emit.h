#ifndef SLOP_emit_H
#define SLOP_emit_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_types.h"
#include "slop_context.h"
#include "slop_ctype.h"
#include "slop_strlib.h"

void emit_emit_include(context_TranspileContext* ctx, slop_string header, uint8_t is_system);
void emit_emit_standard_includes(context_TranspileContext* ctx);
void emit_emit_forward_decl(context_TranspileContext* ctx, slop_string return_type, slop_string name, slop_string params);
void emit_emit_var_decl(context_TranspileContext* ctx, slop_string c_type, slop_string name);
void emit_emit_var_decl_init(context_TranspileContext* ctx, slop_string c_type, slop_string name, slop_string init);
void emit_emit_const_decl(context_TranspileContext* ctx, slop_string c_type, slop_string name, slop_string value, uint8_t is_int);
void emit_emit_block_open(context_TranspileContext* ctx);
void emit_emit_block_close(context_TranspileContext* ctx);
void emit_emit_if_open(context_TranspileContext* ctx, slop_string condition);
void emit_emit_else(context_TranspileContext* ctx);
void emit_emit_else_if(context_TranspileContext* ctx, slop_string condition);
void emit_emit_while_open(context_TranspileContext* ctx, slop_string condition);
void emit_emit_for_open(context_TranspileContext* ctx, slop_string init, slop_string cond, slop_string incr);
void emit_emit_typedef(context_TranspileContext* ctx, slop_string c_type, slop_string name);
void emit_emit_struct_open(context_TranspileContext* ctx, slop_string name);
void emit_emit_struct_close(context_TranspileContext* ctx);
void emit_emit_struct_field(context_TranspileContext* ctx, slop_string c_type, slop_string name);
void emit_emit_enum_open(context_TranspileContext* ctx, slop_string name);
void emit_emit_enum_value(context_TranspileContext* ctx, slop_string name, uint8_t is_last);
void emit_emit_enum_close(context_TranspileContext* ctx, slop_string type_name);
void emit_emit_return(context_TranspileContext* ctx, slop_string value);
void emit_emit_assignment(context_TranspileContext* ctx, slop_string lhs, slop_string rhs);
void emit_emit_call(context_TranspileContext* ctx, slop_string fn_name, slop_string args);


#endif
