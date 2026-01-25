#ifndef SLOP_types_H
#define SLOP_types_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>

typedef struct types_SExprSymbol types_SExprSymbol;
typedef struct types_SExprString types_SExprString;
typedef struct types_SExprNumber types_SExprNumber;
typedef struct types_SExprList types_SExprList;
typedef struct types_SExpr types_SExpr;
typedef struct types_RangeBounds types_RangeBounds;
typedef struct types_FieldDef types_FieldDef;
typedef struct types_VariantDef types_VariantDef;
typedef struct types_TypeDef types_TypeDef;
typedef struct types_ResolvedVariant types_ResolvedVariant;
typedef struct types_ResolvedField types_ResolvedField;
typedef struct types_ResolvedType types_ResolvedType;
typedef struct types_ParamInfo types_ParamInfo;
typedef struct types_FnSignature types_FnSignature;
typedef struct types_TypeError types_TypeError;
typedef struct types_Diagnostic types_Diagnostic;

typedef enum {
    types_TypeKind_kind_primitive,
    types_TypeKind_kind_range,
    types_TypeKind_kind_record,
    types_TypeKind_kind_enum,
    types_TypeKind_kind_union,
    types_TypeKind_kind_alias,
    types_TypeKind_kind_option,
    types_TypeKind_kind_result,
    types_TypeKind_kind_list,
    types_TypeKind_kind_map,
    types_TypeKind_kind_ptr,
    types_TypeKind_kind_array,
    types_TypeKind_kind_function,
    types_TypeKind_kind_ffi
} types_TypeKind;

typedef enum {
    types_ResolvedTypeKind_rk_primitive,
    types_ResolvedTypeKind_rk_range,
    types_ResolvedTypeKind_rk_record,
    types_ResolvedTypeKind_rk_union,
    types_ResolvedTypeKind_rk_enum,
    types_ResolvedTypeKind_rk_list,
    types_ResolvedTypeKind_rk_ptr,
    types_ResolvedTypeKind_rk_option,
    types_ResolvedTypeKind_rk_result,
    types_ResolvedTypeKind_rk_function,
    types_ResolvedTypeKind_rk_array,
    types_ResolvedTypeKind_rk_map
} types_ResolvedTypeKind;

typedef enum {
    types_TypeErrorKind_te_undefined_type,
    types_TypeErrorKind_te_undefined_var,
    types_TypeErrorKind_te_undefined_fn,
    types_TypeErrorKind_te_type_mismatch,
    types_TypeErrorKind_te_arity_mismatch,
    types_TypeErrorKind_te_not_a_function,
    types_TypeErrorKind_te_not_a_record,
    types_TypeErrorKind_te_unknown_field,
    types_TypeErrorKind_te_not_a_union,
    types_TypeErrorKind_te_unknown_variant,
    types_TypeErrorKind_te_non_exhaustive,
    types_TypeErrorKind_te_import_error
} types_TypeErrorKind;

typedef enum {
    types_DiagnosticLevel_diag_warning,
    types_DiagnosticLevel_diag_error
} types_DiagnosticLevel;

#ifndef SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
#define SLOP_LIST_TYPES_SEXPR_PTR_DEFINED
SLOP_LIST_DEFINE(types_SExpr*, slop_list_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
#define SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
SLOP_OPTION_DEFINE(types_ResolvedType*, slop_option_types_ResolvedType_ptr)
#endif

#ifndef SLOP_OPTION_LIST_STRING_DEFINED
#define SLOP_OPTION_LIST_STRING_DEFINED
SLOP_OPTION_DEFINE(slop_list_string, slop_option_list_string)
#endif

struct types_SExprSymbol {
    slop_string name;
    int64_t line;
    int64_t col;
};
typedef struct types_SExprSymbol types_SExprSymbol;

#ifndef SLOP_OPTION_TYPES_SEXPRSYMBOL_DEFINED
#define SLOP_OPTION_TYPES_SEXPRSYMBOL_DEFINED
SLOP_OPTION_DEFINE(types_SExprSymbol, slop_option_types_SExprSymbol)
#endif

struct types_SExprString {
    slop_string value;
    int64_t line;
    int64_t col;
};
typedef struct types_SExprString types_SExprString;

#ifndef SLOP_OPTION_TYPES_SEXPRSTRING_DEFINED
#define SLOP_OPTION_TYPES_SEXPRSTRING_DEFINED
SLOP_OPTION_DEFINE(types_SExprString, slop_option_types_SExprString)
#endif

struct types_SExprNumber {
    int64_t int_value;
    double float_value;
    uint8_t is_float;
    slop_string raw;
    int64_t line;
    int64_t col;
};
typedef struct types_SExprNumber types_SExprNumber;

#ifndef SLOP_OPTION_TYPES_SEXPRNUMBER_DEFINED
#define SLOP_OPTION_TYPES_SEXPRNUMBER_DEFINED
SLOP_OPTION_DEFINE(types_SExprNumber, slop_option_types_SExprNumber)
#endif

struct types_SExprList {
    slop_list_types_SExpr_ptr items;
    int64_t line;
    int64_t col;
};
typedef struct types_SExprList types_SExprList;

#ifndef SLOP_OPTION_TYPES_SEXPRLIST_DEFINED
#define SLOP_OPTION_TYPES_SEXPRLIST_DEFINED
SLOP_OPTION_DEFINE(types_SExprList, slop_option_types_SExprList)
#endif

typedef enum {
    types_SExpr_sym,
    types_SExpr_str,
    types_SExpr_num,
    types_SExpr_lst
} types_SExpr_tag;

struct types_SExpr {
    types_SExpr_tag tag;
    union {
        types_SExprSymbol sym;
        types_SExprString str;
        types_SExprNumber num;
        types_SExprList lst;
    } data;
};
typedef struct types_SExpr types_SExpr;

#ifndef SLOP_OPTION_TYPES_SEXPR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr, slop_option_types_SExpr)
#endif

struct types_RangeBounds {
    uint8_t has_min;
    uint8_t has_max;
    int64_t min_val;
    int64_t max_val;
};
typedef struct types_RangeBounds types_RangeBounds;

#ifndef SLOP_OPTION_TYPES_RANGEBOUNDS_DEFINED
#define SLOP_OPTION_TYPES_RANGEBOUNDS_DEFINED
SLOP_OPTION_DEFINE(types_RangeBounds, slop_option_types_RangeBounds)
#endif

struct types_FieldDef {
    slop_string name;
    types_SExpr* type_expr;
};
typedef struct types_FieldDef types_FieldDef;

#ifndef SLOP_OPTION_TYPES_FIELDDEF_DEFINED
#define SLOP_OPTION_TYPES_FIELDDEF_DEFINED
SLOP_OPTION_DEFINE(types_FieldDef, slop_option_types_FieldDef)
#endif

#ifndef SLOP_LIST_TYPES_FIELDDEF_DEFINED
#define SLOP_LIST_TYPES_FIELDDEF_DEFINED
SLOP_LIST_DEFINE(types_FieldDef, slop_list_types_FieldDef)
#endif

#ifndef SLOP_OPTION_LIST_TYPES_FIELDDEF_DEFINED
#define SLOP_OPTION_LIST_TYPES_FIELDDEF_DEFINED
SLOP_OPTION_DEFINE(slop_list_types_FieldDef, slop_option_list_types_FieldDef)
#endif

struct types_VariantDef {
    slop_string tag;
    slop_option_types_SExpr_ptr payload;
};
typedef struct types_VariantDef types_VariantDef;

#ifndef SLOP_OPTION_TYPES_VARIANTDEF_DEFINED
#define SLOP_OPTION_TYPES_VARIANTDEF_DEFINED
SLOP_OPTION_DEFINE(types_VariantDef, slop_option_types_VariantDef)
#endif

#ifndef SLOP_LIST_TYPES_VARIANTDEF_DEFINED
#define SLOP_LIST_TYPES_VARIANTDEF_DEFINED
SLOP_LIST_DEFINE(types_VariantDef, slop_list_types_VariantDef)
#endif

#ifndef SLOP_OPTION_LIST_TYPES_VARIANTDEF_DEFINED
#define SLOP_OPTION_LIST_TYPES_VARIANTDEF_DEFINED
SLOP_OPTION_DEFINE(slop_list_types_VariantDef, slop_option_list_types_VariantDef)
#endif

struct types_TypeDef {
    slop_string name;
    types_TypeKind kind;
    types_SExpr* source_expr;
    slop_option_types_RangeBounds range;
    slop_option_list_types_FieldDef fields;
    slop_option_list_types_VariantDef variants;
    slop_option_list_string type_params;
};
typedef struct types_TypeDef types_TypeDef;

#ifndef SLOP_OPTION_TYPES_TYPEDEF_DEFINED
#define SLOP_OPTION_TYPES_TYPEDEF_DEFINED
SLOP_OPTION_DEFINE(types_TypeDef, slop_option_types_TypeDef)
#endif

struct types_ResolvedVariant {
    slop_string name;
    int64_t index;
    slop_string tag_constant;
    slop_option_types_ResolvedType_ptr payload_type;
};
typedef struct types_ResolvedVariant types_ResolvedVariant;

#ifndef SLOP_OPTION_TYPES_RESOLVEDVARIANT_DEFINED
#define SLOP_OPTION_TYPES_RESOLVEDVARIANT_DEFINED
SLOP_OPTION_DEFINE(types_ResolvedVariant, slop_option_types_ResolvedVariant)
#endif

#ifndef SLOP_LIST_TYPES_RESOLVEDVARIANT_DEFINED
#define SLOP_LIST_TYPES_RESOLVEDVARIANT_DEFINED
SLOP_LIST_DEFINE(types_ResolvedVariant, slop_list_types_ResolvedVariant)
#endif

struct types_ResolvedField {
    slop_string name;
    types_ResolvedType* field_type;
    int64_t offset;
};
typedef struct types_ResolvedField types_ResolvedField;

#ifndef SLOP_OPTION_TYPES_RESOLVEDFIELD_DEFINED
#define SLOP_OPTION_TYPES_RESOLVEDFIELD_DEFINED
SLOP_OPTION_DEFINE(types_ResolvedField, slop_option_types_ResolvedField)
#endif

#ifndef SLOP_LIST_TYPES_RESOLVEDFIELD_DEFINED
#define SLOP_LIST_TYPES_RESOLVEDFIELD_DEFINED
SLOP_LIST_DEFINE(types_ResolvedField, slop_list_types_ResolvedField)
#endif

struct types_ResolvedType {
    types_ResolvedTypeKind kind;
    slop_string name;
    slop_option_string module_name;
    slop_string c_name;
    slop_list_types_ResolvedVariant variants;
    slop_list_types_ResolvedField fields;
    slop_option_types_ResolvedType_ptr inner_type;
    slop_option_types_ResolvedType_ptr inner_type2;
    slop_option_types_RangeBounds range;
    int64_t source_line;
    int64_t source_col;
};
typedef struct types_ResolvedType types_ResolvedType;

#ifndef SLOP_OPTION_TYPES_RESOLVEDTYPE_DEFINED
#define SLOP_OPTION_TYPES_RESOLVEDTYPE_DEFINED
SLOP_OPTION_DEFINE(types_ResolvedType, slop_option_types_ResolvedType)
#endif

struct types_ParamInfo {
    slop_string name;
    types_ResolvedType* param_type;
};
typedef struct types_ParamInfo types_ParamInfo;

#ifndef SLOP_OPTION_TYPES_PARAMINFO_DEFINED
#define SLOP_OPTION_TYPES_PARAMINFO_DEFINED
SLOP_OPTION_DEFINE(types_ParamInfo, slop_option_types_ParamInfo)
#endif

#ifndef SLOP_LIST_TYPES_PARAMINFO_DEFINED
#define SLOP_LIST_TYPES_PARAMINFO_DEFINED
SLOP_LIST_DEFINE(types_ParamInfo, slop_list_types_ParamInfo)
#endif

struct types_FnSignature {
    slop_string name;
    slop_string c_name;
    slop_list_types_ParamInfo params;
    types_ResolvedType* return_type;
    uint8_t is_pure;
    uint8_t allocates;
    slop_option_string module_name;
};
typedef struct types_FnSignature types_FnSignature;

#ifndef SLOP_OPTION_TYPES_FNSIGNATURE_DEFINED
#define SLOP_OPTION_TYPES_FNSIGNATURE_DEFINED
SLOP_OPTION_DEFINE(types_FnSignature, slop_option_types_FnSignature)
#endif

struct types_TypeError {
    types_TypeErrorKind kind;
    slop_string message;
    int64_t line;
    int64_t col;
};
typedef struct types_TypeError types_TypeError;

#ifndef SLOP_OPTION_TYPES_TYPEERROR_DEFINED
#define SLOP_OPTION_TYPES_TYPEERROR_DEFINED
SLOP_OPTION_DEFINE(types_TypeError, slop_option_types_TypeError)
#endif

struct types_Diagnostic {
    types_DiagnosticLevel level;
    slop_string message;
    int64_t line;
    int64_t col;
};
typedef struct types_Diagnostic types_Diagnostic;

#ifndef SLOP_OPTION_TYPES_DIAGNOSTIC_DEFINED
#define SLOP_OPTION_TYPES_DIAGNOSTIC_DEFINED
SLOP_OPTION_DEFINE(types_Diagnostic, slop_option_types_Diagnostic)
#endif

types_RangeBounds types_range_bounds_new(uint8_t has_min, int64_t min_val, uint8_t has_max, int64_t max_val);
types_RangeBounds types_range_bounds_unbounded(void);
uint8_t types_range_contains(types_RangeBounds bounds, int64_t value);
int64_t types_min(int64_t a, int64_t b);
int64_t types_max(int64_t a, int64_t b);
types_RangeBounds types_range_intersect(types_RangeBounds a, types_RangeBounds b);
types_RangeBounds types_range_union(types_RangeBounds a, types_RangeBounds b);
types_ResolvedVariant* types_resolved_variant_new(slop_arena* arena, slop_string name, int64_t index, slop_string tag_constant, slop_option_types_ResolvedType_ptr payload);
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
uint8_t types_resolved_type_has_field(types_ResolvedType* t, slop_string name);
slop_option_types_ResolvedType_ptr types_resolved_type_get_field_type(types_ResolvedType* t, slop_string name);
slop_string types_resolved_type_to_slop_string(slop_arena* arena, types_ResolvedType* t);

#ifndef SLOP_OPTION_TYPES_SEXPRSYMBOL_DEFINED
#define SLOP_OPTION_TYPES_SEXPRSYMBOL_DEFINED
SLOP_OPTION_DEFINE(types_SExprSymbol, slop_option_types_SExprSymbol)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPRSTRING_DEFINED
#define SLOP_OPTION_TYPES_SEXPRSTRING_DEFINED
SLOP_OPTION_DEFINE(types_SExprString, slop_option_types_SExprString)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPRNUMBER_DEFINED
#define SLOP_OPTION_TYPES_SEXPRNUMBER_DEFINED
SLOP_OPTION_DEFINE(types_SExprNumber, slop_option_types_SExprNumber)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_PTR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr*, slop_option_types_SExpr_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPRLIST_DEFINED
#define SLOP_OPTION_TYPES_SEXPRLIST_DEFINED
SLOP_OPTION_DEFINE(types_SExprList, slop_option_types_SExprList)
#endif

#ifndef SLOP_OPTION_TYPES_SEXPR_DEFINED
#define SLOP_OPTION_TYPES_SEXPR_DEFINED
SLOP_OPTION_DEFINE(types_SExpr, slop_option_types_SExpr)
#endif

#ifndef SLOP_OPTION_TYPES_RANGEBOUNDS_DEFINED
#define SLOP_OPTION_TYPES_RANGEBOUNDS_DEFINED
SLOP_OPTION_DEFINE(types_RangeBounds, slop_option_types_RangeBounds)
#endif

#ifndef SLOP_OPTION_TYPES_FIELDDEF_DEFINED
#define SLOP_OPTION_TYPES_FIELDDEF_DEFINED
SLOP_OPTION_DEFINE(types_FieldDef, slop_option_types_FieldDef)
#endif

#ifndef SLOP_OPTION_TYPES_VARIANTDEF_DEFINED
#define SLOP_OPTION_TYPES_VARIANTDEF_DEFINED
SLOP_OPTION_DEFINE(types_VariantDef, slop_option_types_VariantDef)
#endif

#ifndef SLOP_OPTION_LIST_TYPES_FIELDDEF_DEFINED
#define SLOP_OPTION_LIST_TYPES_FIELDDEF_DEFINED
SLOP_OPTION_DEFINE(slop_list_types_FieldDef, slop_option_list_types_FieldDef)
#endif

#ifndef SLOP_OPTION_LIST_TYPES_VARIANTDEF_DEFINED
#define SLOP_OPTION_LIST_TYPES_VARIANTDEF_DEFINED
SLOP_OPTION_DEFINE(slop_list_types_VariantDef, slop_option_list_types_VariantDef)
#endif

#ifndef SLOP_OPTION_LIST_STRING_DEFINED
#define SLOP_OPTION_LIST_STRING_DEFINED
SLOP_OPTION_DEFINE(slop_list_string, slop_option_list_string)
#endif

#ifndef SLOP_OPTION_TYPES_TYPEDEF_DEFINED
#define SLOP_OPTION_TYPES_TYPEDEF_DEFINED
SLOP_OPTION_DEFINE(types_TypeDef, slop_option_types_TypeDef)
#endif

#ifndef SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
#define SLOP_OPTION_TYPES_RESOLVEDTYPE_PTR_DEFINED
SLOP_OPTION_DEFINE(types_ResolvedType*, slop_option_types_ResolvedType_ptr)
#endif

#ifndef SLOP_OPTION_TYPES_RESOLVEDVARIANT_DEFINED
#define SLOP_OPTION_TYPES_RESOLVEDVARIANT_DEFINED
SLOP_OPTION_DEFINE(types_ResolvedVariant, slop_option_types_ResolvedVariant)
#endif

#ifndef SLOP_OPTION_TYPES_RESOLVEDFIELD_DEFINED
#define SLOP_OPTION_TYPES_RESOLVEDFIELD_DEFINED
SLOP_OPTION_DEFINE(types_ResolvedField, slop_option_types_ResolvedField)
#endif

#ifndef SLOP_OPTION_TYPES_RESOLVEDTYPE_DEFINED
#define SLOP_OPTION_TYPES_RESOLVEDTYPE_DEFINED
SLOP_OPTION_DEFINE(types_ResolvedType, slop_option_types_ResolvedType)
#endif

#ifndef SLOP_OPTION_TYPES_PARAMINFO_DEFINED
#define SLOP_OPTION_TYPES_PARAMINFO_DEFINED
SLOP_OPTION_DEFINE(types_ParamInfo, slop_option_types_ParamInfo)
#endif

#ifndef SLOP_OPTION_TYPES_FNSIGNATURE_DEFINED
#define SLOP_OPTION_TYPES_FNSIGNATURE_DEFINED
SLOP_OPTION_DEFINE(types_FnSignature, slop_option_types_FnSignature)
#endif

#ifndef SLOP_OPTION_TYPES_TYPEERROR_DEFINED
#define SLOP_OPTION_TYPES_TYPEERROR_DEFINED
SLOP_OPTION_DEFINE(types_TypeError, slop_option_types_TypeError)
#endif

#ifndef SLOP_OPTION_TYPES_DIAGNOSTIC_DEFINED
#define SLOP_OPTION_TYPES_DIAGNOSTIC_DEFINED
SLOP_OPTION_DEFINE(types_Diagnostic, slop_option_types_Diagnostic)
#endif


#endif
