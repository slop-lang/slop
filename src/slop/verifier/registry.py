"""
Function and type invariant registries for verification.

FunctionRegistry tracks function definitions for inlining during verification.
TypeInvariantRegistry tracks @invariant annotations on types.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, TYPE_CHECKING

from slop.parser import SList, Symbol, String, Number, is_form

if TYPE_CHECKING:
    from slop.parser import SExpr


# ============================================================================
# Function Registry
# ============================================================================

@dataclass
class FunctionDef:
    """Definition of a function for inlining purposes"""
    name: str
    params: List[str]  # Parameter names in order
    body: Optional['SExpr']
    is_pure: bool = True
    postconditions: List['SExpr'] = field(default_factory=list)
    properties: List[Tuple[Optional[str], 'SExpr']] = field(default_factory=list)  # @property - (name, expr) tuples


class FunctionRegistry:
    """Registry of functions for inlining during verification.

    Enables inlining of simple accessor functions so postconditions like
    (term-eq (triple-subject $result) subject) can be proven by replacing
    (triple-subject $result) with the actual field access.
    """

    def __init__(self):
        self.functions: Dict[str, FunctionDef] = {}

    def register_from_ast(self, ast: List['SExpr']):
        """Extract function definitions from AST"""
        for form in ast:
            if is_form(form, 'module'):
                for item in form.items[1:]:
                    if is_form(item, 'fn'):
                        self._register_fn(item)
            elif is_form(form, 'fn'):
                self._register_fn(form)

    def _register_fn(self, fn_form: SList):
        """Register a single function"""
        if len(fn_form) < 3:
            return
        name = fn_form[1].name if isinstance(fn_form[1], Symbol) else None
        if not name:
            return

        # Extract parameter names
        params = []
        param_list = fn_form[2] if isinstance(fn_form[2], SList) else SList([])
        for param in param_list:
            if isinstance(param, SList) and len(param) >= 2:
                first = param[0]
                if isinstance(first, Symbol) and first.name in ('in', 'out', 'mut'):
                    # Mode is explicit: (in name Type)
                    param_name = param[1].name if isinstance(param[1], Symbol) else None
                else:
                    # No mode: (name Type)
                    param_name = first.name if isinstance(first, Symbol) else None
                if param_name:
                    params.append(param_name)

        # Extract body, postconditions, properties (skip other annotations and :keywords)
        body = None
        is_pure = False
        postconditions: List['SExpr'] = []
        properties: List[Tuple[Optional[str], 'SExpr']] = []
        annotation_forms = {'@intent', '@spec', '@pre', '@post', '@assume', '@pure',
                           '@alloc', '@example', '@deprecated', '@property',
                           '@generation-mode', '@requires'}

        skip_next_string = False
        for item in fn_form.items[3:]:
            if isinstance(item, Symbol):
                if item.name.startswith(':'):
                    skip_next_string = True  # Next String is property value
                    continue
                # Simple expression as body
                body = item
                skip_next_string = False
            elif isinstance(item, String):
                # Skip string values after :keyword (property values)
                # But allow standalone String as function body
                if skip_next_string:
                    skip_next_string = False
                    continue
                body = item
            elif is_form(item, '@pure'):
                is_pure = True
                skip_next_string = False
                continue
            elif is_form(item, '@post') and len(item) > 1:
                # Extract postcondition
                postconditions.append(item[1])
                skip_next_string = False
                continue
            elif is_form(item, '@property') and len(item) > 1:
                # Extract property (universal assertion)
                # Named: (@property name expr) or Unnamed: (@property expr)
                if isinstance(item[1], Symbol) and len(item) > 2:
                    # Named property: (@property name expr)
                    properties.append((item[1].name, item[2]))
                else:
                    # Unnamed property: (@property expr)
                    properties.append((None, item[1]))
                skip_next_string = False
                continue
            elif isinstance(item, SList) and len(item) > 0:
                head = item[0]
                if isinstance(head, Symbol) and head.name in annotation_forms:
                    skip_next_string = False
                    continue
                body = item
                skip_next_string = False

        self.functions[name] = FunctionDef(name=name, params=params, body=body,
                                           is_pure=is_pure, postconditions=postconditions,
                                           properties=properties)

    def is_simple_accessor(self, name: str) -> bool:
        """Check if function is a simple field accessor: (. param field)"""
        fn = self.functions.get(name)
        if fn and fn.body and is_form(fn.body, '.'):
            return True
        return False

    def get_accessor_info(self, name: str) -> Optional[Tuple[str, str]]:
        """Get (param_name, field_name) for a simple accessor"""
        fn = self.functions.get(name)
        if fn and fn.body and is_form(fn.body, '.') and len(fn.body) >= 3:
            obj = fn.body[1]
            field_item = fn.body[2]
            if isinstance(obj, Symbol) and isinstance(field_item, Symbol):
                return (obj.name, field_item.name)
        return None

    def is_simple_inlinable(self, name: str) -> bool:
        """Check if function is a simple expression that can be inlined.

        Criteria:
        1. Function is marked @pure
        2. Body is a single expression (no control flow)
        3. Not recursive

        Examples of inlinable functions:
        - (fn iri-eq ((a IRI) (b IRI)) (@pure) (string-eq (. a value) (. b value)))
        - (fn blank-eq ((a BlankNode) (b BlankNode)) (@pure) (== (. a id) (. b id)))
        - (fn num-eq ((a Int) (b Int)) (@pure) (== a b))
        """
        fn = self.functions.get(name)
        if not fn or not fn.body or not fn.is_pure:
            return False
        return self._is_simple_expression(fn.body, name)

    def inlines_to_native_equality(self, name: str) -> bool:
        """Check if function inlines to native ==.

        Used by union equality axioms to determine if a helper-eq function
        should be treated as native Z3 equality rather than an uninterpreted function.

        Returns True ONLY for functions that directly use == on parameters:
        - (fn num-eq ((a Int) (b Int)) (@pure) (== a b))

        Does NOT return True for string-eq since that's modeled as an
        uninterpreted function in Z3, not native equality.
        """
        fn = self.functions.get(name)
        if not fn or not fn.body or not fn.is_pure:
            return False

        if not self._is_simple_expression(fn.body, name):
            return False

        # Check if body is (== param1 param2) - ONLY native ==
        body = fn.body
        if not isinstance(body, SList) or len(body) < 3:
            return False

        head = body[0]
        if not isinstance(head, Symbol):
            return False

        # Only native == counts, not string-eq or other comparison functions
        if head.name != '==':
            return False

        # Check if arguments are direct parameter references
        arg1, arg2 = body[1], body[2]
        if isinstance(arg1, Symbol) and isinstance(arg2, Symbol):
            if arg1.name in fn.params and arg2.name in fn.params:
                return True

        return False

    def _is_simple_expression(self, expr: 'SExpr', fn_name: str) -> bool:
        """Check if expression is a simple expression suitable for inlining.

        Returns False for:
        - Control flow: if, cond, match, when, unless
        - Loops: for-each, while
        - Bindings: let, do (multiple expressions)
        - Mutation: set!
        - Recursive calls to fn_name
        """
        if isinstance(expr, (Symbol, Number, String)):
            # Simple values are always inlinable
            return True

        if isinstance(expr, SList) and len(expr) > 0:
            head = expr[0]
            if isinstance(head, Symbol):
                head_name = head.name
                # Reject control flow and complex constructs
                if head_name in ('if', 'cond', 'match', 'when', 'unless',
                                 'for-each', 'while',
                                 'let', 'do', 'set!'):
                    return False
                # Reject recursive calls
                if head_name == fn_name:
                    return False
                # For other function calls, check all arguments are simple
                for arg in expr.items[1:]:
                    if not self._is_simple_expression(arg, fn_name):
                        return False
                return True

        return False


# ============================================================================
# Type Invariant Registry
# ============================================================================

class TypeInvariantRegistry:
    """Registry of type invariants extracted from @invariant annotations"""

    def __init__(self):
        self.invariants: Dict[str, List['SExpr']] = {}  # type_name -> list of invariant expressions

    def add_invariant(self, type_name: str, condition: 'SExpr'):
        """Add an invariant for a type"""
        if type_name not in self.invariants:
            self.invariants[type_name] = []
        self.invariants[type_name].append(condition)

    def get_invariants(self, type_name: str) -> List['SExpr']:
        """Get all invariants for a type"""
        return self.invariants.get(type_name, [])


__all__ = [
    'FunctionDef',
    'FunctionRegistry',
    'TypeInvariantRegistry',
]
