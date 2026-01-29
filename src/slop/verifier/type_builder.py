"""
Type registry building from AST.

Functions to extract type definitions and invariants from parsed SLOP AST
without running the full type checker.
"""
from __future__ import annotations

from typing import Dict, List, Optional, TYPE_CHECKING

from slop.parser import SList, Symbol, Number, is_form
from slop.types import (
    Type, PrimitiveType, RangeType, RangeBounds, RecordType, EnumType,
    OptionType, ResultType, PtrType, FnType, UNKNOWN, ListType, ArrayType,
    UnionType,
)

from .registry import TypeInvariantRegistry

if TYPE_CHECKING:
    from slop.parser import SExpr


def build_type_registry_from_ast(ast: List['SExpr']) -> Dict[str, Type]:
    """Extract type definitions from AST without full type checking.

    Mirrors the native type-extract.slop approach for extracting types.
    """
    registry: Dict[str, Type] = {}

    for form in ast:
        if is_form(form, 'module'):
            # Process forms inside module
            for item in form.items[1:]:
                if is_form(item, 'type'):
                    _register_type(item, registry)
        elif is_form(form, 'type'):
            _register_type(form, registry)

    return registry


def build_invariant_registry_from_ast(ast: List['SExpr']) -> TypeInvariantRegistry:
    """Extract type invariants from AST.

    Looks for @invariant annotations in type definitions:
    (type Name (record ...) (@invariant condition))
    """
    registry = TypeInvariantRegistry()

    for form in ast:
        if is_form(form, 'module'):
            for item in form.items[1:]:
                if is_form(item, 'type'):
                    _extract_type_invariants(item, registry)
        elif is_form(form, 'type'):
            _extract_type_invariants(form, registry)

    return registry


def _extract_type_invariants(type_form: SList, registry: TypeInvariantRegistry):
    """Extract @invariant annotations from a type definition"""
    if len(type_form) < 3:
        return

    name = type_form[1].name if isinstance(type_form[1], Symbol) else None
    if not name:
        return

    # Look for @invariant forms after the type body
    for item in type_form.items[3:]:
        if is_form(item, '@invariant') and len(item) >= 2:
            registry.add_invariant(name, item[1])


def _register_type(type_form: SList, registry: Dict[str, Type]):
    """Parse (type Name ...) into registry."""
    if len(type_form) < 3:
        return

    name = type_form[1].name if isinstance(type_form[1], Symbol) else None
    if not name:
        return

    body = type_form[2]

    if is_form(body, 'record'):
        # (type Name (record (field1 T1) (field2 T2) ...))
        fields: Dict[str, Type] = {}
        for field_item in body.items[1:]:
            if isinstance(field_item, SList) and len(field_item) >= 2:
                fname = field_item[0].name if isinstance(field_item[0], Symbol) else None
                if fname:
                    ftype = _parse_type_expr_simple(field_item[1], registry)
                    fields[fname] = ftype
        registry[name] = RecordType(name, fields)

    elif is_form(body, 'enum'):
        # (type Name (enum val1 val2 ...))
        variants = [v.name for v in body.items[1:] if isinstance(v, Symbol)]
        registry[name] = EnumType(name, variants)

    elif is_form(body, 'union'):
        # (type Name (union (tag1 T1) (tag2) ...))
        union_variants: Dict[str, Optional[Type]] = {}
        for variant in body.items[1:]:
            if isinstance(variant, SList) and len(variant) >= 1:
                tag = variant[0].name if isinstance(variant[0], Symbol) else None
                if tag:
                    payload = _parse_type_expr_simple(variant[1], registry) if len(variant) > 1 else None
                    union_variants[tag] = payload
            elif isinstance(variant, Symbol):
                # Tag without payload
                union_variants[variant.name] = None
        registry[name] = UnionType(name, union_variants)

    elif is_form(body, 'Int') or (isinstance(body, SList) and len(body) >= 3):
        # Range type: (type Name (Int min .. max)) or (type Name (Int min ..))
        bounds = _parse_range_bounds(body)
        if bounds:
            registry[name] = RangeType('Int', bounds)

    elif isinstance(body, Symbol):
        # Type alias: (type Name ExistingType)
        aliased = _parse_type_expr_simple(body, registry)
        registry[name] = aliased


def _parse_type_expr_simple(expr: 'SExpr', registry: Dict[str, Type]) -> Type:
    """Parse type expression with minimal context."""
    if isinstance(expr, Symbol):
        name = expr.name
        if name in registry:
            return registry[name]
        # Standard primitive types
        if name in ('Int', 'I8', 'I16', 'I32', 'I64', 'U8', 'U16', 'U32', 'U64',
                    'Float', 'F32', 'F64', 'Bool', 'String', 'Unit', 'Void', 'Arena'):
            return PrimitiveType(name)
        # Unknown type - might be defined later
        return PrimitiveType(name)

    if isinstance(expr, SList) and len(expr) >= 1:
        head = expr[0]
        if isinstance(head, Symbol):
            head_name = head.name

            if head_name == 'Ptr' and len(expr) >= 2:
                inner = _parse_type_expr_simple(expr[1], registry)
                return PtrType(inner)

            if head_name == 'OwnPtr' and len(expr) >= 2:
                inner = _parse_type_expr_simple(expr[1], registry)
                return PtrType(inner, owning=True)

            if head_name == 'OptPtr' and len(expr) >= 2:
                inner = _parse_type_expr_simple(expr[1], registry)
                return PtrType(inner, nullable=True)

            if head_name == 'Option' and len(expr) >= 2:
                inner = _parse_type_expr_simple(expr[1], registry)
                return OptionType(inner)

            if head_name == 'Result' and len(expr) >= 3:
                ok_type = _parse_type_expr_simple(expr[1], registry)
                err_type = _parse_type_expr_simple(expr[2], registry)
                return ResultType(ok_type, err_type)

            if head_name == 'List' and len(expr) >= 2:
                elem = _parse_type_expr_simple(expr[1], registry)
                return ListType(elem)

            if head_name == 'Array' and len(expr) >= 3:
                elem = _parse_type_expr_simple(expr[1], registry)
                size = expr[2].value if isinstance(expr[2], Number) else 0
                return ArrayType(elem, int(size))

            if head_name == 'Fn' and len(expr) >= 4:
                # (Fn (A B) -> R)
                params = expr[1]
                ret = expr[3] if len(expr) > 3 else expr[-1]
                param_types: List[Type] = []
                if isinstance(params, SList):
                    for p in params.items:
                        param_types.append(_parse_type_expr_simple(p, registry))
                ret_type = _parse_type_expr_simple(ret, registry)
                return FnType(tuple(param_types), ret_type)

            # Range type: (Int min .. max)
            if head_name in ('Int', 'I8', 'I16', 'I32', 'I64', 'U8', 'U16', 'U32', 'U64'):
                bounds = _parse_range_bounds(expr)
                if bounds:
                    return RangeType(head_name, bounds)
                return PrimitiveType(head_name)

            # Check registry for parameterized type
            if head_name in registry:
                return registry[head_name]

    return UNKNOWN


def _parse_range_bounds(expr: 'SExpr') -> Optional[RangeBounds]:
    """Parse range bounds from (Int min .. max) or (Int min ..) or (Int .. max)."""
    if not isinstance(expr, SList) or len(expr) < 3:
        return None

    # Expected formats:
    # (Int min .. max) - 4 elements, bounded range
    # (Int min ..)     - 3 elements, lower-bounded only
    # (Int .. max)     - 3 elements, upper-bounded only
    # Find the '..' separator
    dot_idx = -1
    for i, item in enumerate(expr.items):
        if isinstance(item, Symbol) and item.name == '..':
            dot_idx = i
            break

    if dot_idx == -1:
        return None

    min_val: Optional[int] = None
    max_val: Optional[int] = None

    # Parse min value (before ..)
    if dot_idx > 1:
        min_item = expr[dot_idx - 1]
        if isinstance(min_item, Number):
            min_val = int(min_item.value)
        elif isinstance(min_item, Symbol) and min_item.name.lstrip('-').isdigit():
            min_val = int(min_item.name)

    # Parse max value (after ..)
    if dot_idx + 1 < len(expr):
        max_item = expr[dot_idx + 1]
        if isinstance(max_item, Number):
            max_val = int(max_item.value)
        elif isinstance(max_item, Symbol) and max_item.name.lstrip('-').isdigit():
            max_val = int(max_item.name)

    return RangeBounds(min_val, max_val)


__all__ = [
    'build_type_registry_from_ast',
    'build_invariant_registry_from_ast',
    '_parse_type_expr_simple',
    '_parse_range_bounds',
]
