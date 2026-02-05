#include "../runtime/slop_runtime.h"
#include "slop_emit.h"

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

void emit_emit_include(context_TranspileContext* ctx, slop_string header, uint8_t is_system) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (is_system) {
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("#include <"), header, SLOP_STR(">")));
    } else {
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("#include \""), header, SLOP_STR("\"")));
    }
}

void emit_emit_standard_includes(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit(ctx, SLOP_STR("#include \"slop_runtime.h\""));
    context_ctx_emit(ctx, SLOP_STR("#include <stdint.h>"));
    context_ctx_emit(ctx, SLOP_STR("#include <stdbool.h>"));
    context_ctx_emit(ctx, SLOP_STR(""));
}

void emit_emit_forward_decl(context_TranspileContext* ctx, slop_string return_type, slop_string name, slop_string params) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    {
        __auto_type param_str = ((string_eq(params, SLOP_STR(""))) ? SLOP_STR("void") : params);
        context_ctx_emit(ctx, context_ctx_str5(ctx, return_type, SLOP_STR(" "), name, SLOP_STR("("), context_ctx_str3(ctx, param_str, SLOP_STR(")"), SLOP_STR(";"))));
    }
}

void emit_emit_var_decl(context_TranspileContext* ctx, slop_string c_type, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit(ctx, context_ctx_str4(ctx, c_type, SLOP_STR(" "), name, SLOP_STR(";")));
}

void emit_emit_var_decl_init(context_TranspileContext* ctx, slop_string c_type, slop_string name, slop_string init) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit(ctx, context_ctx_str5(ctx, c_type, SLOP_STR(" "), name, SLOP_STR(" = "), context_ctx_str(ctx, init, SLOP_STR(";"))));
}

void emit_emit_const_decl(context_TranspileContext* ctx, slop_string c_type, slop_string name, slop_string value, uint8_t is_int) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (is_int) {
        context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("#define "), name, SLOP_STR(" ("), context_ctx_str(ctx, value, SLOP_STR(")"))));
    } else {
        context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("static const "), c_type, SLOP_STR(" "), name, context_ctx_str3(ctx, SLOP_STR(" = "), value, SLOP_STR(";"))));
    }
}

void emit_emit_block_open(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit(ctx, SLOP_STR("{"));
    context_ctx_indent(ctx);
}

void emit_emit_block_close(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_dedent(ctx);
    context_ctx_emit(ctx, SLOP_STR("}"));
}

void emit_emit_if_open(context_TranspileContext* ctx, slop_string condition) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("if ("), condition, SLOP_STR(") {")));
    context_ctx_indent(ctx);
}

void emit_emit_else(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_dedent(ctx);
    context_ctx_emit(ctx, SLOP_STR("} else {"));
    context_ctx_indent(ctx);
}

void emit_emit_else_if(context_TranspileContext* ctx, slop_string condition) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_dedent(ctx);
    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("} else if ("), condition, SLOP_STR(") {")));
    context_ctx_indent(ctx);
}

void emit_emit_while_open(context_TranspileContext* ctx, slop_string condition) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("while ("), condition, SLOP_STR(") {")));
    context_ctx_indent(ctx);
}

void emit_emit_for_open(context_TranspileContext* ctx, slop_string init, slop_string cond, slop_string incr) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit(ctx, context_ctx_str5(ctx, SLOP_STR("for ("), init, SLOP_STR("; "), cond, context_ctx_str3(ctx, SLOP_STR("; "), incr, SLOP_STR(") {"))));
    context_ctx_indent(ctx);
}

void emit_emit_typedef(context_TranspileContext* ctx, slop_string c_type, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("typedef "), c_type, SLOP_STR(" "), context_ctx_str(ctx, name, SLOP_STR(";"))));
}

void emit_emit_struct_open(context_TranspileContext* ctx, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("struct "), name, SLOP_STR(" {")));
    context_ctx_indent(ctx);
}

void emit_emit_struct_close(context_TranspileContext* ctx) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_dedent(ctx);
    context_ctx_emit(ctx, SLOP_STR("};"));
}

void emit_emit_struct_field(context_TranspileContext* ctx, slop_string c_type, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit(ctx, context_ctx_str4(ctx, SLOP_STR("    "), c_type, SLOP_STR(" "), context_ctx_str(ctx, name, SLOP_STR(";"))));
}

void emit_emit_enum_open(context_TranspileContext* ctx, slop_string name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit(ctx, SLOP_STR("typedef enum {"));
    context_ctx_indent(ctx);
}

void emit_emit_enum_value(context_TranspileContext* ctx, slop_string name, uint8_t is_last) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (is_last) {
        context_ctx_emit(ctx, context_ctx_str(ctx, SLOP_STR("    "), name));
    } else {
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("    "), name, SLOP_STR(",")));
    }
}

void emit_emit_enum_close(context_TranspileContext* ctx, slop_string type_name) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_dedent(ctx);
    context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("} "), type_name, SLOP_STR(";")));
}

void emit_emit_return(context_TranspileContext* ctx, slop_string value) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    if (string_eq(value, SLOP_STR(""))) {
        context_ctx_emit(ctx, SLOP_STR("return;"));
    } else {
        context_ctx_emit(ctx, context_ctx_str3(ctx, SLOP_STR("return "), value, SLOP_STR(";")));
    }
}

void emit_emit_assignment(context_TranspileContext* ctx, slop_string lhs, slop_string rhs) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit(ctx, context_ctx_str4(ctx, lhs, SLOP_STR(" = "), rhs, SLOP_STR(";")));
}

void emit_emit_call(context_TranspileContext* ctx, slop_string fn_name, slop_string args) {
    SLOP_PRE(((ctx != NULL)), "(!= ctx nil)");
    context_ctx_emit(ctx, context_ctx_str4(ctx, fn_name, SLOP_STR("("), args, SLOP_STR(");")));
}

