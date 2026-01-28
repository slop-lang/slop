"""
Contract Verifier - Verifies SLOP function contracts using Z3.

This module provides the ContractVerifier class that checks @pre/@post
contracts and @property annotations using Z3 SMT solving.

The ContractVerifier inherits from several mixins that provide specialized
functionality:
- PatternDetectionMixin: Loop pattern detection (filter, map, count, etc.)
- AxiomGenerationMixin: Z3 axiom generation for patterns and constructs
- LoopAnalysisMixin: Loop context analysis and inductive verification
- UnionHandlingMixin: Union type handling and equality axioms
"""
from __future__ import annotations

from typing import Dict, List, Optional, Set, Tuple, Any, TYPE_CHECKING

from slop.parser import SList, Symbol, String, Number, is_form
from slop.types import (
    Type, PrimitiveType, RangeType, RangeBounds, RecordType, EnumType,
    OptionType, ResultType, PtrType, FnType, UNKNOWN, ListType, ArrayType,
    UnionType,
)

from .z3_setup import Z3_AVAILABLE, z3
from .types import MinimalTypeEnv, ImportedDefinitions, SourceLocation
from .results import VerificationResult
from .loop_patterns import (
    FilterPatternInfo, MapPatternInfo, NestedLoopPatternInfo, CountPatternInfo,
    FoldPatternInfo, FindPatternInfo, SetBinding, LoopContext, WhileLoopContext,
    InnerLoopInfo, FieldSource,
)
from .registry import FunctionRegistry, FunctionDef
from .type_builder import _parse_type_expr_simple
from .translator import Z3Translator
from .ssa import SSAContext, SSAVersion
from .wp import WeakestPrecondition
from .invariant_inference import InvariantInferencer, InferredInvariant

# Import mixins
from .pattern_detection import PatternDetectionMixin
from .axiom_generation import AxiomGenerationMixin
from .loop_analysis import LoopAnalysisMixin
from .union_handling import UnionHandlingMixin

if TYPE_CHECKING:
    from slop.parser import SExpr


class ContractVerifier(PatternDetectionMixin, AxiomGenerationMixin, 
                       LoopAnalysisMixin, UnionHandlingMixin):
    """Verifies @pre/@post contracts for functions.
    
    Inherits specialized functionality from mixins:
    - PatternDetectionMixin: Loop pattern detection
    - AxiomGenerationMixin: Z3 axiom generation  
    - LoopAnalysisMixin: Loop analysis and inductive verification
    - UnionHandlingMixin: Union type handling
    """

    def __init__(self, type_env: MinimalTypeEnv, filename: str = "<unknown>",
                 timeout_ms: int = 5000, function_registry: Optional[FunctionRegistry] = None,
                 imported_defs: Optional[ImportedDefinitions] = None):
        if not Z3_AVAILABLE:
            raise RuntimeError("Z3 is not available")
        self.type_env = type_env
        self.filename = filename
        self.timeout_ms = timeout_ms
        self.function_registry = function_registry
        self.imported_defs = imported_defs or ImportedDefinitions()

    def _references_mutable_state(self, expr: SExpr) -> bool:
        """Check if expression references mutable state (deref field access)"""
        if isinstance(expr, SList) and len(expr) >= 2:
            head = expr[0]
            if isinstance(head, Symbol):
                # (. (deref ...) field) pattern
                if head.name == '.' and len(expr) >= 3:
                    inner = expr[1]
                    if isinstance(inner, SList) and len(inner) >= 1:
                        inner_head = inner[0]
                        if isinstance(inner_head, Symbol) and inner_head.name == 'deref':
                            return True
                # Recursively check subexpressions
                for item in expr.items[1:]:
                    if self._references_mutable_state(item):
                        return True
        return False

    def _is_wp_applicable(self, body: SExpr) -> bool:
        """Check if Weakest Precondition calculus should be applied.

        WP is applicable for expressions where backward reasoning helps:
        - let bindings (establish intermediate values)
        - if/cond expressions (multiple paths)
        - match expressions (pattern matching)
        - do blocks (sequential composition)

        WP is NOT applied to:
        - Simple variable references (just returns True)
        - Simple function calls without control flow
        - Loops (require explicit invariants which we handle separately)
        """
        if not isinstance(body, SList) or len(body) == 0:
            return False

        head = body[0]
        if not isinstance(head, Symbol):
            return False

        # Forms where WP adds value
        wp_applicable_forms = {'let', 'if', 'cond', 'match', 'do'}

        if head.name in wp_applicable_forms:
            return True

        # Also check if body contains nested let/if/etc
        for item in body.items[1:]:
            if self._is_wp_applicable(item):
                return True

        return False

    def _needs_array_encoding(self, postconditions: List[SExpr]) -> bool:
        """Check if postconditions require array encoding for lists.

        Returns True if any postcondition:
        - Calls all-triples-have-predicate
        - Uses list-ref
        - Uses forall with list indexing
        """
        for post in postconditions:
            if self._expr_needs_array_encoding(post):
                return True
        return False

    def _expr_needs_array_encoding(self, expr: SExpr) -> bool:
        """Check if an expression needs array encoding."""
        if isinstance(expr, SList) and len(expr) > 0:
            head = expr[0]
            if isinstance(head, Symbol):
                # Check for element-level list operations
                if head.name in ('all-triples-have-predicate', 'list-ref',
                                 'all-elements-satisfy', 'any-element-satisfies'):
                    return True
                # Check for quantifiers that might involve lists
                if head.name in ('forall', 'exists'):
                    # Check if body involves list-ref
                    if len(expr) >= 3 and self._expr_needs_array_encoding(expr[2]):
                        return True
            # Recursively check subexpressions
            for item in expr.items:
                if self._expr_needs_array_encoding(item):
                    return True
        return False

    def _needs_seq_encoding(self, exprs: List[SExpr]) -> bool:
        """Check if expressions require Sequence encoding for lists.

        Returns True if any expression uses collection-bound quantifiers:
        - (forall (elem collection) body) - iterates over all elements
        - (exists (elem collection) body) - checks if any element satisfies

        This is distinct from index-based quantifiers like (forall (i Int) ...).

        Works for both postconditions and properties.
        """
        for expr in exprs:
            if self._expr_needs_seq_encoding(expr):
                return True
        return False

    def _expr_needs_seq_encoding(self, expr: SExpr) -> bool:
        """Check if an expression needs Sequence encoding.

        Detects collection-bound quantifier patterns:
        - (forall (elem coll) body) where coll is a symbol (not (elem Type))
        - (exists (elem coll) body) where coll is a symbol
        - (forall (elem (. obj field)) body) where collection is a field access
        - (exists (elem (. obj field)) body) where collection is a field access
        """
        if isinstance(expr, SList) and len(expr) > 0:
            head = expr[0]
            if isinstance(head, Symbol):
                # Check for collection-bound forall/exists
                if head.name in ('forall', 'exists') and len(expr) >= 3:
                    binding = expr[1]
                    # Collection-bound pattern: (elem collection)
                    if isinstance(binding, SList) and len(binding) == 2:
                        elem = binding[0]
                        coll = binding[1]
                        if isinstance(elem, Symbol):
                            # Case 1: coll is a symbol like $result or items
                            if isinstance(coll, Symbol):
                                coll_name = coll.name
                                if coll_name == '$result' or not coll_name[0].isupper():
                                    return True
                            # Case 2: coll is a field access like (. delta triples)
                            elif isinstance(coll, SList) and is_form(coll, '.'):
                                return True
            # Recursively check subexpressions
            for item in expr.items:
                if self._expr_needs_seq_encoding(item):
                    return True
        return False

    def _references_result_collection(self, exprs: List[SExpr]) -> bool:
        """Check if any expression references $result as a collection in forall/exists."""
        for expr in exprs:
            if self._expr_references_result_collection(expr):
                return True
        return False

    def _expr_references_result_collection(self, expr: SExpr) -> bool:
        """Check if expression references $result as a collection."""
        if isinstance(expr, SList) and len(expr) > 0:
            head = expr[0]
            if isinstance(head, Symbol):
                if head.name in ('forall', 'exists') and len(expr) >= 3:
                    binding = expr[1]
                    if isinstance(binding, SList) and len(binding) == 2:
                        coll = binding[1]
                        if isinstance(coll, Symbol) and coll.name == '$result':
                            return True
            # Recursively check subexpressions
            for item in expr.items:
                if self._expr_references_result_collection(item):
                    return True
        return False

    def _find_eq_function_calls(self, exprs: List[SExpr]) -> set:
        """Find all function calls ending in -eq in expressions"""
        result: set = set()
        for expr in exprs:
            self._collect_eq_calls(expr, result)
        return result

    def _collect_eq_calls(self, expr: SExpr, result: set):
        """Recursively collect function calls ending in -eq"""
        if isinstance(expr, SList) and len(expr) > 0:
            head = expr[0]
            if isinstance(head, Symbol) and head.name.endswith('-eq'):
                result.add(head.name)
            for item in expr.items:
                self._collect_eq_calls(item, result)
        elif isinstance(expr, Symbol):
            # Check for shorthand dot notation like t.field
            pass  # No function calls in plain symbols

    def _find_accessor_calls(self, exprs: List[SExpr]) -> set:
        """Find all function calls that are simple accessors"""
        result: set = set()
        for expr in exprs:
            self._collect_accessor_calls(expr, result)
        return result

    def _collect_accessor_calls(self, expr: SExpr, result: set):
        """Recursively collect function calls that are simple accessors"""
        if isinstance(expr, SList) and len(expr) > 0:
            head = expr[0]
            if isinstance(head, Symbol):
                fn_name = head.name
                if self.function_registry and self.function_registry.is_simple_accessor(fn_name):
                    result.add(fn_name)
            for item in expr.items:
                self._collect_accessor_calls(item, result)

    def _extract_accessor_axioms(self, postconditions: List[SExpr], translator: Z3Translator) -> List:
        """Extract axioms for accessor functions: fn_name(x) == field_name(x)

        For functions that are simple field accessors like (fn graph-size ((g Graph)) (. g size)),
        add universally quantified axiom: ForAll x: fn_graph-size(x) == field_size(x)
        """
        axioms = []

        # Find all accessor function calls in postconditions
        accessor_funcs = self._find_accessor_calls(postconditions)

        for fn_name in accessor_funcs:
            accessor_info = self.function_registry.get_accessor_info(fn_name)
            if accessor_info:
                param_name, field_name = accessor_info

                # Get the function from translator.variables
                func_key = f"fn_{fn_name}_1"
                if func_key not in translator.variables:
                    # Create the function if not yet created
                    func = z3.Function(func_key, z3.IntSort(), z3.IntSort())
                    translator.variables[func_key] = func
                else:
                    func = translator.variables[func_key]

                # Get or create the field accessor function
                field_func_name = f"field_{field_name}"
                if field_func_name not in translator.variables:
                    field_func = z3.Function(field_func_name, z3.IntSort(), z3.IntSort())
                    translator.variables[field_func_name] = field_func
                else:
                    field_func = translator.variables[field_func_name]

                # Add axiom: ForAll x: fn_name(x) == field_name(x)
                x = z3.Int("_accessor_x")
                axioms.append(z3.ForAll([x], func(x) == field_func(x)))

        return axioms

    def _substitute_fields_for_param(self, expr: SExpr, param_name: str, fields: List[str]) -> SExpr:
        """Substitute field names in expr with param_name.field notation.

        For type invariant (== size (list-len triples)) with param 'g' and fields ['size', 'triples'],
        produces (== g.size (list-len g.triples)).
        """
        if isinstance(expr, Symbol):
            name = expr.name
            # Check if this symbol is a field name
            if name in fields:
                # Create shorthand dot notation: param.field
                return Symbol(f"{param_name}.{name}", expr.line, expr.col)
            return expr
        elif isinstance(expr, SList):
            # Recursively substitute in list elements
            new_items = [self._substitute_fields_for_param(item, param_name, fields) for item in expr.items]
            return SList(new_items, expr.line, expr.col)
        else:
            # Number, String, etc. - return unchanged
            return expr

    def _get_record_fields(self, type_name: str) -> List[str]:
        """Get field names for a record type"""
        typ = self.type_env.type_registry.get(type_name)
        if isinstance(typ, RecordType):
            return list(typ.fields.keys())
        return []

    def _collect_parameter_invariants(self, params: SList) -> List[Tuple[str, SExpr]]:
        """Collect type invariants for all parameters, substituted with param names.

        Returns list of (param_name, substituted_invariant) tuples.
        """
        result: List[Tuple[str, SExpr]] = []

        for param in params:
            if isinstance(param, SList) and len(param) >= 2:
                # Handle parameter modes: (name Type) or (in name Type)
                first = param[0]
                if isinstance(first, Symbol) and first.name in ('in', 'out', 'mut'):
                    param_name = param[1].name if isinstance(param[1], Symbol) else None
                    param_type_expr = param[2] if len(param) > 2 else None
                else:
                    param_name = first.name if isinstance(first, Symbol) else None
                    param_type_expr = param[1]

                if param_name and param_type_expr:
                    # Get the type name
                    type_name = None
                    if isinstance(param_type_expr, Symbol):
                        type_name = param_type_expr.name
                    elif isinstance(param_type_expr, SList) and len(param_type_expr) >= 1:
                        # Handle (Ptr Type) or other parameterized types
                        head = param_type_expr[0]
                        if isinstance(head, Symbol) and head.name in ('Ptr', 'OwnPtr', 'OptPtr'):
                            if len(param_type_expr) >= 2 and isinstance(param_type_expr[1], Symbol):
                                type_name = param_type_expr[1].name

                    if type_name:
                        # Get invariants for this type
                        invariants = self.type_env.get_invariants_for_type(type_name)
                        # Get fields for substitution
                        fields = self._get_record_fields(type_name)

                        for inv in invariants:
                            # Substitute field names with param.field
                            subst_inv = self._substitute_fields_for_param(inv, param_name, fields)
                            result.append((param_name, subst_inv))

        return result

    def _extract_call_postcondition_axioms(self, body: SExpr, translator: Z3Translator) -> List:
        """Extract postcondition axioms from function calls bound in let expressions.

        When we see:
            (let ((result (make-delta arena next-iter))) ...)

        And make-delta has:
            (@post {(. $result iteration) == iteration})

        We add the axiom:
            (. result iteration) == next-iter

        This propagates known postconditions from called functions to help verify
        the caller's postconditions.
        """
        axioms = []
        if not self.function_registry:
            return axioms

        # Recursively search for let bindings
        self._collect_call_postconditions(body, translator, axioms)
        return axioms

    def _collect_call_postconditions(self, expr: SExpr, translator: Z3Translator, axioms: List):
        """Recursively collect postcondition axioms from let-bound function calls."""
        if not isinstance(expr, SList) or len(expr) < 1:
            return

        head = expr[0]
        if not isinstance(head, Symbol):
            return

        # Handle direct function call return: body is (fn-name args...)
        # In this case, $result == fn-call result, so we propagate fn's postconditions to $result
        # Check if this is a function call (not a special form)
        special_forms = {'let', 'do', 'if', 'when', 'match', 'for-each', 'while', 'set!',
                         'record-new', 'union-new', 'ok', 'error', 'some', 'none', 'return',
                         'lambda', 'cast', 'deref', 'sizeof', 'arena-alloc', 'with-arena',
                         'list-new', 'list-push', 'list-get', 'quote'}
        if head.name not in special_forms and self.function_registry:
            # This is a function call - check if it has postconditions
            self._process_direct_call_return(expr, translator, axioms)

        # Handle let expressions
        if head.name == 'let' and len(expr) >= 3:
            bindings = expr[1]
            if isinstance(bindings, SList):
                for binding in bindings.items:
                    self._process_let_binding(binding, translator, axioms)
            # Recurse into body expressions
            for body_expr in expr.items[2:]:
                self._collect_call_postconditions(body_expr, translator, axioms)

        # Handle set! expressions: (set! var (fn-call ...))
        elif head.name == 'set!' and len(expr) >= 3:
            var_sym = expr[1]
            value_expr = expr[2]
            if isinstance(var_sym, Symbol) and isinstance(value_expr, SList):
                self._process_set_binding(var_sym.name, value_expr, translator, axioms)

        # Handle do blocks
        elif head.name == 'do':
            for item in expr.items[1:]:
                self._collect_call_postconditions(item, translator, axioms)

        # Handle for-each loops
        elif head.name == 'for-each' and len(expr) >= 3:
            for item in expr.items[2:]:
                self._collect_call_postconditions(item, translator, axioms)

        # Handle if expressions
        elif head.name == 'if':
            for item in expr.items[2:]:
                self._collect_call_postconditions(item, translator, axioms)

        # Handle when expressions
        elif head.name == 'when' and len(expr) >= 3:
            for item in expr.items[2:]:
                self._collect_call_postconditions(item, translator, axioms)

    def _process_let_binding(self, binding: SExpr, translator: Z3Translator, axioms: List):
        """Process a single let binding, extracting postcondition axioms if it's a function call.

        Also handles simple expression bindings like (next-iter (+ x 1)) by adding
        axiom: next-iter == (+ x 1). This enables tracking of computed values.

        Checks both local function definitions and imported function signatures
        for postconditions to enable cross-module postcondition propagation.
        """
        if not isinstance(binding, SList) or len(binding) < 2:
            return

        # Handle both (var value) and (mut var value) patterns
        first = binding[0]
        if isinstance(first, Symbol) and first.name == 'mut' and len(binding) >= 3:
            # (mut var value)
            var_name = binding[1].name if isinstance(binding[1], Symbol) else None
            init_expr = binding[2]
        elif isinstance(first, Symbol):
            # (var value)
            var_name = first.name
            init_expr = binding[1]
        else:
            return

        if not var_name:
            return

        # Handle simple expression bindings (not function calls)
        # Add axiom: var == init_expr
        if not isinstance(init_expr, SList) or len(init_expr) < 1:
            # Simple value binding (number, symbol)
            self._add_binding_axiom(var_name, init_expr, translator, axioms)
            return

        # Check if init_expr is a function call
        fn_head = init_expr[0]
        if not isinstance(fn_head, Symbol):
            return

        fn_name = fn_head.name

        # Check if this is a known operator (not a function call with postconditions)
        # Operators like +, -, *, /, etc. should create binding axioms
        operators = {'+', '-', '*', '/', 'mod', '.', 'and', 'or', 'not',
                     '==', '!=', '<', '<=', '>', '>='}
        if fn_name in operators:
            self._add_binding_axiom(var_name, init_expr, translator, axioms)
            return

        # Check local functions first
        fn_def = self.function_registry.functions.get(fn_name) if self.function_registry else None

        # Get postconditions and params from local definition or imported signature
        postconditions: List[SExpr] = []
        params: List[str] = []

        if fn_def and fn_def.postconditions:
            # Use local function definition
            postconditions = fn_def.postconditions
            params = fn_def.params
        elif self.imported_defs:
            # Fall back to imported function signature
            imported_sig = self.imported_defs.functions.get(fn_name)
            if imported_sig and imported_sig.postconditions:
                postconditions = imported_sig.postconditions
                params = imported_sig.params

        if not postconditions:
            # Handle built-in functions with known semantics
            self._add_builtin_function_axioms(var_name, fn_name, init_expr, translator, axioms)
            return

        # Get the actual arguments to the function call
        call_args = list(init_expr.items[1:])

        # Skip if argument count doesn't match parameter count
        if len(call_args) != len(params):
            return

        # For each postcondition, substitute $result and parameters, then translate
        for post in postconditions:
            subst_post = self._substitute_postcondition(post, var_name, params, call_args)
            z3_axiom = translator.translate_expr(subst_post)
            if z3_axiom is not None:
                axioms.append(z3_axiom)

    def _add_binding_axiom(self, var_name: str, expr: SExpr, translator: Z3Translator, axioms: List):
        """Add axiom: var == expr for simple let bindings.

        This enables tracking of computed values like:
            (let ((next-iter (+ (. delta iteration) 1))) ...)
        Adds axiom: next-iter == (+ (. delta iteration) 1)
        """
        # Declare variable if not already declared
        if var_name not in translator.variables:
            # Infer type from expression - default to Int
            translator.declare_variable(var_name, PrimitiveType('Int'))

        var_z3 = translator.variables.get(var_name)
        if var_z3 is None:
            return

        expr_z3 = translator.translate_expr(expr)
        if expr_z3 is not None:
            # Add axiom: var == expr
            axioms.append(var_z3 == expr_z3)

    def _add_builtin_function_axioms(self, var_name: str, fn_name: str,
                                      call_expr: SList, translator: Z3Translator,
                                      axioms: List):
        """Add axioms for built-in functions with known semantics.

        For make-triple: field_predicate(var) == predicate_arg
        For make-iri: var has value derived from the IRI string
        """
        # Handle make-triple: (make-triple arena subject predicate object)
        if fn_name == 'make-triple' and len(call_expr) >= 4:
            # Declare the variable if needed
            if var_name not in translator.variables:
                translator.declare_variable(var_name, PrimitiveType('Int'))

            var_z3 = translator.variables.get(var_name)
            if var_z3 is None:
                return

            # Get the predicate argument (3rd argument, 0-indexed)
            pred_arg = call_expr[3]
            pred_z3 = translator.translate_expr(pred_arg)

            if pred_z3 is not None:
                # Get or create field_predicate function
                func_name = "field_predicate"
                if func_name not in translator.variables:
                    func = z3.Function(func_name, z3.IntSort(), z3.IntSort())
                    translator.variables[func_name] = func
                else:
                    func = translator.variables[func_name]

                # Axiom: field_predicate(var) == predicate_arg
                axioms.append(func(var_z3) == pred_z3)

        # Handle make-iri: (make-iri arena iri-string)
        elif fn_name == 'make-iri' and len(call_expr) >= 3:
            # Declare the variable if needed
            if var_name not in translator.variables:
                translator.declare_variable(var_name, PrimitiveType('Int'))

            var_z3 = translator.variables.get(var_name)
            if var_z3 is None:
                return

            # Get the IRI argument
            iri_arg = call_expr[2]
            iri_z3 = translator.translate_expr(iri_arg)

            if iri_z3 is not None:
                # Axiom: var == iri_value
                # This connects make-iri result to the IRI constant
                axioms.append(var_z3 == iri_z3)

    def _process_direct_call_return(self, call_expr: SExpr, translator: Z3Translator, axioms: List):
        """Process a function body that is a direct function call return.

        When a function body is just (fn-call args...), the result of fn-call
        becomes $result. We propagate fn-call's postconditions to $result.

        For example:
            (fn reason-with-config ...
              (engine-run arena config input))

        If engine-run has postcondition about iterations <= max-iterations,
        we add that as an axiom for reason-with-config's $result.
        """
        if not isinstance(call_expr, SList) or len(call_expr) < 1:
            return

        head = call_expr[0]
        if not isinstance(head, Symbol):
            return

        fn_name = head.name

        # Look up the called function's postconditions from local registry or imported defs
        postconditions: List[SExpr] = []
        params: List[str] = []

        # Check local functions first
        if self.function_registry:
            fn_def = self.function_registry.functions.get(fn_name)
            if fn_def and fn_def.postconditions:
                postconditions = fn_def.postconditions
                params = fn_def.params

        # Fall back to imported function signature
        if not postconditions and self.imported_defs:
            imported_sig = self.imported_defs.functions.get(fn_name)
            if imported_sig and imported_sig.postconditions:
                postconditions = imported_sig.postconditions
                params = imported_sig.params

        if not postconditions:
            return

        # Get $result variable
        result_var = translator.variables.get('$result')
        if result_var is None:
            return

        # Get the actual arguments to the function call
        args = list(call_expr.items[1:])

        # For each postcondition, substitute $result and parameters, then translate
        # Since this is a direct return, the callee's $result IS our $result
        for post in postconditions:
            # Substitute parameters with actual arguments
            if len(args) == len(params):
                subst_post = self._substitute_postcondition(post, '$result', params, args)
            else:
                subst_post = post
            post_z3 = translator.translate_expr(subst_post)
            if post_z3 is not None:
                axioms.append(post_z3)

    def _process_set_binding(self, var_name: str, call_expr: SExpr, translator: Z3Translator, axioms: List):
        """Process a set! statement, extracting postcondition axioms if it's a function call.

        For (set! result (fn-call args...)), extracts the callee's postconditions
        and adds them as axioms with substituted values.

        SSA-style tracking: When the variable being set is also passed as an argument
        (self-referential pattern like `(set! result (delta-add arena result t))`),
        we create an __old_<varname> Z3 variable to represent the pre-assignment value.
        This ensures postconditions like `{(. $result iteration) == (. d iteration)}`
        correctly relate the NEW result to the OLD value rather than producing tautologies.
        """
        if not isinstance(call_expr, SList) or len(call_expr) < 1:
            return

        fn_head = call_expr[0]
        if not isinstance(fn_head, Symbol):
            return

        fn_name = fn_head.name

        # Check local functions first
        fn_def = self.function_registry.functions.get(fn_name) if self.function_registry else None

        # Get postconditions and params from local definition or imported signature
        postconditions: List[SExpr] = []
        params: List[str] = []

        if fn_def and fn_def.postconditions:
            postconditions = fn_def.postconditions
            params = fn_def.params
        elif self.imported_defs:
            imported_sig = self.imported_defs.functions.get(fn_name)
            if imported_sig and imported_sig.postconditions:
                postconditions = imported_sig.postconditions
                params = imported_sig.params

        if not postconditions:
            return

        # Get the actual arguments to the function call
        call_args = list(call_expr.items[1:])

        # Skip if argument count doesn't match parameter count
        if len(call_args) != len(params):
            return

        # Detect self-referential pattern: when var_name is passed as an argument
        self_ref_params = self._find_self_referential_params(var_name, call_args, params)

        # If self-reference detected and variable exists, create __old_ Z3 variable
        if self_ref_params and var_name in translator.variables:
            old_var_name = f"__old_{var_name}"
            current_var = translator.variables[var_name]

            # Create __old_ variable with same sort as current variable
            if z3.is_bool(current_var):
                old_var = z3.Bool(old_var_name)
            elif z3.is_real(current_var):
                old_var = z3.Real(old_var_name)
            else:
                old_var = z3.Int(old_var_name)

            # Constraint: __old_var equals current value (before the set!)
            translator.constraints.append(old_var == current_var)
            translator.variables[old_var_name] = old_var

        # For each postcondition, substitute $result and parameters, then translate
        for post in postconditions:
            subst_post = self._substitute_postcondition(post, var_name, params, call_args, self_ref_params)
            z3_axiom = translator.translate_expr(subst_post)
            if z3_axiom is not None:
                axioms.append(z3_axiom)

    def _find_self_referential_params(self, var_name: str, call_args: List[SExpr],
                                        params: List[str]) -> Dict[str, str]:
        """Find parameters that received the variable being set.

        For (set! result (fn arena result t)) with params ['arena', 'd', 't']:
        Returns {'d': 'result'} because 'd' received the old value of 'result'.

        This enables SSA-style tracking where:
        - $result refers to the NEW value (after the call)
        - Parameter that received var_name refers to the OLD value (before the call)
        """
        self_refs: Dict[str, str] = {}
        for param, arg in zip(params, call_args):
            if isinstance(arg, Symbol) and arg.name == var_name:
                self_refs[param] = var_name
        return self_refs

    def _substitute_postcondition(self, post: SExpr, result_var: str,
                                  params: List[str], args: List[SExpr],
                                  self_ref_params: Optional[Dict[str, str]] = None) -> SExpr:
        """Substitute $result and parameters in a postcondition.

        Args:
            post: The postcondition expression
            result_var: The name to substitute for $result
            params: Parameter names in the callee
            args: Actual argument expressions from the call site
            self_ref_params: Map of param names to var names for self-referential args.
                             These params will be substituted with __old_<varname> to
                             preserve SSA semantics.

        Returns:
            The substituted postcondition expression
        """
        # Build substitution map
        subst_map: Dict[str, SExpr] = {'$result': Symbol(result_var)}
        for param, arg in zip(params, args):
            if self_ref_params and param in self_ref_params:
                # Parameter received the old value of the variable being set
                # Use __old_<varname> to reference the pre-assignment value
                old_var_name = f"__old_{self_ref_params[param]}"
                subst_map[param] = Symbol(old_var_name)
            else:
                subst_map[param] = arg

        return self._substitute_expr(post, subst_map)

    def _substitute_expr(self, expr: SExpr, subst_map: Dict[str, SExpr]) -> SExpr:
        """Recursively substitute symbols in an expression.

        Special case: In field access (. obj field), don't substitute the field name
        since it's a literal identifier, not a variable reference.
        """
        if isinstance(expr, Symbol):
            name = expr.name
            if name in subst_map:
                return subst_map[name]
            return expr
        elif isinstance(expr, SList):
            # Special handling for field access: (. obj field)
            # Don't substitute the field name (3rd element)
            if len(expr) >= 3:
                head = expr[0]
                if isinstance(head, Symbol) and head.name == '.':
                    # Keep operator, substitute object, preserve field name
                    new_items = [
                        expr[0],  # Keep '.'
                        self._substitute_expr(expr[1], subst_map),  # Substitute object
                        expr[2]  # Keep field name as-is (don't substitute)
                    ]
                    # Handle any additional items (shouldn't be any for '.')
                    new_items.extend(expr.items[3:])
                    return SList(new_items, expr.line, expr.col)

            new_items = [self._substitute_expr(item, subst_map) for item in expr.items]
            return SList(new_items, expr.line, expr.col)
        else:
            # Number, String - return unchanged
            return expr

    def _get_return_expr(self, expr: SExpr) -> SExpr:
        """Get the effective return expression from a body.

        Handles do and let blocks by returning their last expression.
        """
        if is_form(expr, 'do') and len(expr) >= 2:
            return self._get_return_expr(expr.items[-1])
        if is_form(expr, 'let') and len(expr) >= 3:
            # (let (bindings) body1 body2 ... bodyN) -> return value is bodyN
            return self._get_return_expr(expr.items[-1])
        return expr

    def _collect_all_return_exprs(self, expr: SExpr) -> List[SExpr]:
        """Collect ALL return expressions from a function body.

        This includes:
        - Explicit (return ...) expressions
        - The final expression (implicit return)
        - All branches of a match expression (when match is final expression)

        Used to add axioms for all possible return paths.
        """
        returns = []
        self._collect_returns_recursive(expr, returns)

        # Also add the final expression (if not already a return)
        final = self._get_return_expr(expr)
        if not is_form(final, 'return'):
            # If final is a match, collect all branch results
            if is_form(final, 'match') and len(final) >= 3:
                # (match expr ((pattern) body) ...)
                for branch in final.items[2:]:
                    if isinstance(branch, SList) and len(branch) >= 2:
                        branch_body = branch[-1]  # Last item is the body/result
                        branch_result = self._get_return_expr(branch_body)
                        returns.append(branch_result)
            else:
                returns.append(final)

        return returns

    def _collect_returns_recursive(self, expr: SExpr, returns: List[SExpr]) -> None:
        """Recursively collect (return ...) expressions."""
        if not isinstance(expr, SList):
            return

        if is_form(expr, 'return') and len(expr) >= 2:
            returns.append(expr[1])
            return

        # Recurse into subexpressions
        for item in expr.items:
            if isinstance(item, SList):
                self._collect_returns_recursive(item, returns)

    def _is_record_new(self, expr: SExpr) -> bool:
        """Check if expression is a record-new form (handles do blocks)"""
        return_expr = self._get_return_expr(expr)
        return is_form(return_expr, 'record-new')

    def _is_list_new(self, expr: SExpr) -> bool:
        """Check if expression is list-new or contains a result bound to list-new"""
        return_expr = self._get_return_expr(expr)
        if is_form(return_expr, 'list-new'):
            return True

        # Also check for mutable bindings to list-new
        # Pattern: (let ((mut result (list-new ...))) ... result)
        return self._has_list_new_result_binding(expr)

    def _has_list_new_result_binding(self, expr: SExpr) -> bool:
        """Check if expression has a mutable 'result' bound to list-new.

        Looks for pattern: (let ((mut result (list-new ...))) ... result)
        where the final return is the 'result' variable.
        """
        if is_form(expr, 'let') and len(expr) >= 3:
            bindings = expr[1]
            body_exprs = expr.items[2:]

            # Check if final expression is 'result'
            if body_exprs:
                final_expr = self._get_return_expr(body_exprs[-1])
                is_result_return = isinstance(final_expr, Symbol) and final_expr.name == 'result'

                if is_result_return and isinstance(bindings, SList):
                    # Look for (mut result (list-new ...)) binding
                    for binding in bindings.items:
                        if isinstance(binding, SList) and len(binding) >= 3:
                            first = binding[0]
                            if isinstance(first, Symbol) and first.name == 'mut':
                                var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                                init_expr = binding[2]
                                if var_name == 'result' and is_form(init_expr, 'list-new'):
                                    return True

            # Recurse into body expressions
            for body_expr in body_exprs:
                if self._has_list_new_result_binding(body_expr):
                    return True

        # Recurse into do blocks
        if is_form(expr, 'do'):
            for item in expr.items[1:]:
                if self._has_list_new_result_binding(item):
                    return True

        return False

    def _is_conditional_with_record_new(self, expr: SExpr) -> bool:
        """Check if expression is (if cond (record-new ...) else) or (if cond then (record-new ...))"""
        if is_form(expr, 'if') and len(expr) >= 4:
            then_branch = expr[2]
            else_branch = expr[3]
            return self._is_record_new(then_branch) or self._is_record_new(else_branch)
        return False

    def _find_list_push_calls(self, expr: SExpr, result: List[Tuple[SExpr, SExpr]]):
        """Find all (list-push lst item) calls in expression.

        Returns list of [(list_expr, item_expr), ...]
        """
        if isinstance(expr, SList) and len(expr) >= 3:
            head = expr[0]
            if isinstance(head, Symbol) and head.name == 'list-push':
                # Found a list-push: (list-push lst item)
                result.append((expr[1], expr[2]))

            # Recurse into subexpressions
            for item in expr.items:
                self._find_list_push_calls(item, result)

    def _extract_list_axioms(self, body: SExpr, translator: Z3Translator) -> List:
        """Extract axioms for list operations in body.

        For (list-push lst x):
        - After the push, (list-len lst) == original_len + 1

        We model this by creating a "post-push" version of the list length.
        When postconditions reference the list after a push, they see the
        incremented length.

        With array encoding:
        - Track Store axioms for element properties
        - For each push, add: Select(arr, old_len) == pushed_element
        """
        axioms = []

        # Find all list-push calls
        push_calls: List[Tuple[SExpr, SExpr]] = []
        self._find_list_push_calls(body, push_calls)

        for list_expr, item_expr in push_calls:
            # Translate the list expression to get its Z3 representation
            lst_z3 = translator.translate_expr(list_expr)
            if lst_z3 is None:
                continue

            # With array encoding, add Store-based axioms
            if translator.use_array_encoding:
                # Check if this is a known list variable
                if isinstance(list_expr, Symbol):
                    lst_name = list_expr.name
                    if lst_name in translator.list_arrays:
                        arr, length = translator.list_arrays[lst_name]

                        # Translate the pushed item
                        item_z3 = translator.translate_expr(item_expr)
                        if item_z3 is not None:
                            # After push: length increases by 1
                            axioms.append(length >= 1)

                            # Key axiom for element properties:
                            # The pushed element exists somewhere in the array
                            # Using an existential: exists i: 0 <= i < length && arr[i] == item
                            # But for verification, a simpler axiom works:
                            # The element at some valid index has the pushed value's properties

                            # For all-triples-have-predicate, we need to know that every
                            # pushed element has the predicate property. We add the axiom:
                            # field_predicate(item) == expected_value (propagated from make-triple)

                            # Get the predicate accessor
                            pred_func_name = "field_predicate"
                            if pred_func_name not in translator.variables:
                                pred_func = z3.Function(pred_func_name, z3.IntSort(), z3.IntSort())
                                translator.variables[pred_func_name] = pred_func
                            else:
                                pred_func = translator.variables[pred_func_name]

                            # For quantified postcondition verification, we need to add:
                            # All elements at valid indices have the correct property
                            # This is an inductive invariant. For now, we add a simpler axiom:
                            # For each push, the element being pushed has its properties set
                            # (the make-triple axioms handle setting field_predicate)

                            # Bound variable for forall
                            idx = z3.Int(f"_push_idx_{id(item_expr)}")

                            # Key insight: if we push element E to the array,
                            # and E.predicate == P, then after all pushes,
                            # forall i in [0, length): arr[i].predicate == P
                            # IF all pushed elements have the same predicate.

                            # For now, add the axiom that:
                            # forall valid i, field_predicate(Select(arr, i)) comes from pushed elements
                            # This works because all elements are pushed with type-pred
                            continue  # Use fallback axioms for length tracking

            # Fallback: length-based axioms
            # Get or create the field_len function
            func_name = "field_len"
            if func_name not in translator.variables:
                func = z3.Function(func_name, z3.IntSort(), z3.IntSort())
                translator.variables[func_name] = func
            else:
                func = translator.variables[func_name]

            # Create a "pre-push length" variable for tracking
            pre_len_name = f"_list_pre_len_{id(list_expr)}"
            if pre_len_name not in translator.variables:
                pre_len = z3.Int(pre_len_name)
                translator.variables[pre_len_name] = pre_len

                # The pre-push length equals what field_len returns for the list
                axioms.append(pre_len == func(lst_z3))

                # After the push, the length is pre_len + 1
                # We need to constrain future references to this list's length
                # Create a "post-push" marker
                post_len_name = f"_list_post_len_{id(list_expr)}"
                post_len = z3.Int(post_len_name)
                translator.variables[post_len_name] = post_len
                axioms.append(post_len == pre_len + 1)
                axioms.append(post_len >= 1)  # After push, length is at least 1

        # Connect returned list to $result
        # If the function returns a list variable that had push called on it,
        # add axiom: field_len($result) >= number_of_pushes
        result_var = translator.variables.get('$result')
        if result_var is not None and push_calls:
            # Find the return expression
            return_expr = self._get_return_expr(body)
            if isinstance(return_expr, Symbol):
                # Check if this variable had push calls
                for list_expr, _ in push_calls:
                    if isinstance(list_expr, Symbol) and list_expr.name == return_expr.name:
                        # The returned variable is the one we pushed to
                        func_name = "field_len"
                        if func_name in translator.variables:
                            func = translator.variables[func_name]
                            # Count pushes to this list
                            push_count = sum(
                                1 for lst, _ in push_calls
                                if isinstance(lst, Symbol) and lst.name == return_expr.name
                            )
                            # $result is the list after all pushes, so length >= push_count
                            axioms.append(func(result_var) >= push_count)

        return axioms

    def _extract_conditional_record_axioms(self, cond_expr: SList, translator: Z3Translator) -> List:
        """Extract axioms for conditional with record-new in either branch.

        For (if cond (record-new Type (f1 v1) ...) var):
        - Add: cond => field_f1($result) == v1
        - Add: !cond => field_f1($result) == field_f1(var)

        For (if cond var (record-new Type (f1 v1) ...)):
        - Add: !cond => field_f1($result) == v1
        - Add: cond => field_f1($result) == field_f1(var)
        """
        axioms = []
        result_var = translator.variables.get('$result')
        if result_var is None:
            return axioms

        if len(cond_expr) < 4:
            return axioms

        condition = cond_expr[1]
        then_branch = cond_expr[2]
        else_branch = cond_expr[3]

        # Translate the condition
        cond_z3 = translator.translate_expr(condition)
        if cond_z3 is None:
            return axioms

        # Defensive check: ensure condition is Bool before using z3.Not()
        # Some predicates may not be detected as Bool-returning, handle gracefully
        if cond_z3.sort() != z3.BoolSort():
            return axioms

        # Determine which branch has record-new
        record_new_in_then = self._is_record_new(then_branch)
        record_new_in_else = self._is_record_new(else_branch)

        if record_new_in_then:
            record_branch = then_branch
            var_branch = else_branch
            record_cond = cond_z3  # record-new happens when cond is true
        elif record_new_in_else:
            record_branch = else_branch
            var_branch = then_branch
            record_cond = z3.Not(cond_z3)  # record-new happens when cond is false
        else:
            return axioms

        # Extract field values from record-new branch
        field_names = []
        for item in record_branch.items[2:]:  # Skip 'record-new' and Type
            if isinstance(item, SList) and len(item) >= 2:
                field_name = item[0].name if isinstance(item[0], Symbol) else None
                if field_name:
                    field_names.append(field_name)
                    field_value = translator.translate_expr(item[1])
                    if field_value is not None:
                        field_func = translator._translate_field_for_obj(result_var, field_name)
                        # Add: record_cond => field($result) == value
                        axioms.append(z3.Implies(record_cond, field_func == field_value))

        # Handle variable branch: add field equality axioms
        if isinstance(var_branch, Symbol):
            var_z3 = translator.translate_expr(var_branch)
            if var_z3 is not None:
                # For each field, add: !record_cond => field($result) == field(var)
                for field_name in field_names:
                    result_field = translator._translate_field_for_obj(result_var, field_name)
                    var_field = translator._translate_field_for_obj(var_z3, field_name)
                    axioms.append(z3.Implies(z3.Not(record_cond), result_field == var_field))

        # Special case: conditional insert with contains check
        # Pattern: (if (contains coll item) coll (record-new ...add item...))
        # In this case, result contains item in BOTH branches:
        # - Then: coll already contains item (from condition)
        # - Else: we're adding item to coll
        if self._is_contains_condition(condition):
            # Extract the collection and item from the contains check
            contains_coll, contains_item = self._extract_contains_args(condition)
            if contains_coll is not None and contains_item is not None:
                # Check if then branch returns the same collection
                if isinstance(var_branch, Symbol):
                    var_name = var_branch.name
                    coll_name = contains_coll.name if isinstance(contains_coll, Symbol) else None
                    if var_name == coll_name:
                        # Pattern matches! Add axiom: (contains $result item)
                        item_z3 = translator.translate_expr(contains_item)
                        if item_z3 is not None:
                            # Find the contains function used in the condition
                            contains_func_name = self._get_contains_func_name(condition)
                            if contains_func_name:
                                func_key = f"fn_{contains_func_name}_2"
                                if func_key not in translator.variables:
                                    contains_func = z3.Function(func_key, z3.IntSort(), z3.IntSort(), z3.BoolSort())
                                    translator.variables[func_key] = contains_func
                                else:
                                    contains_func = translator.variables[func_key]
                                # Result contains the item unconditionally
                                axioms.append(contains_func(result_var, item_z3))

        return axioms

    def _is_contains_condition(self, condition: SExpr) -> bool:
        """Check if condition is a contains-type predicate call"""
        if isinstance(condition, SList) and len(condition) >= 1:
            head = condition[0]
            if isinstance(head, Symbol):
                name = head.name
                return 'contains' in name or name.endswith('-has')
        return False

    def _extract_contains_args(self, condition: SExpr) -> Tuple[Optional[SExpr], Optional[SExpr]]:
        """Extract (collection, item) from (contains coll item) or (type-contains coll item)"""
        if isinstance(condition, SList) and len(condition) >= 3:
            return (condition[1], condition[2])
        return (None, None)

    def _get_contains_func_name(self, condition: SExpr) -> Optional[str]:
        """Get the function name from a contains condition"""
        if isinstance(condition, SList) and len(condition) >= 1:
            head = condition[0]
            if isinstance(head, Symbol):
                return head.name
        return None

    def _extract_match_exhaustiveness_constraints(
        self, postconditions: List[SExpr], translator: Z3Translator
    ) -> List:
        """Extract exhaustiveness constraints for match postconditions.

        For a match like:
            (match $result ((none) true) ((some report) cond))

        Add constraint: union_tag($result) == none_tag OR union_tag($result) == some_tag

        This prevents Z3 from finding counterexamples with invalid tag values
        that don't correspond to any constructor.
        """
        constraints = []
        result_var = translator.variables.get('$result')
        if result_var is None:
            return constraints

        for post in postconditions:
            if is_form(post, 'match') and len(post) >= 3:
                scrutinee = post[1]
                # Only process match on $result
                if not (isinstance(scrutinee, Symbol) and scrutinee.name == '$result'):
                    continue

                # Get or create union_tag function
                tag_func_name = "union_tag"
                if tag_func_name not in translator.variables:
                    tag_func = z3.Function(tag_func_name, z3.IntSort(), z3.IntSort())
                    translator.variables[tag_func_name] = tag_func
                else:
                    tag_func = translator.variables[tag_func_name]

                tag_value = tag_func(result_var)

                # Collect all tag indices from the match patterns
                tag_conditions = []
                for clause in post.items[2:]:
                    if not isinstance(clause, SList) or len(clause) < 1:
                        continue

                    pattern = clause[0]

                    # Extract tag name from pattern
                    tag_name = None
                    if isinstance(pattern, Symbol):
                        if pattern.name == '_':
                            # Wildcard - match is already exhaustive, no constraint needed
                            tag_conditions = []
                            break
                        tag_name = pattern.name
                    elif isinstance(pattern, SList) and len(pattern) >= 1:
                        tag_elem = pattern[0]
                        if isinstance(tag_elem, Symbol):
                            tag_name = tag_elem.name.lstrip("'")
                        elif is_form(tag_elem, 'quote') and len(tag_elem) >= 2:
                            inner = tag_elem[1]
                            tag_name = inner.name if isinstance(inner, Symbol) else None

                    if tag_name:
                        # Get tag index using same calculation as _translate_match
                        tag_idx = translator.enum_values.get(
                            tag_name,
                            translator.enum_values.get(f"'{tag_name}", hash(tag_name) % 256)
                        )
                        tag_conditions.append(tag_value == z3.IntVal(tag_idx))

                # Add disjunction constraint: tag must be one of the pattern tags
                if tag_conditions:
                    constraints.append(z3.Or(*tag_conditions))

        return constraints

    def _extract_record_field_axioms(self, record_new: SList, translator: Z3Translator) -> List:
        """Extract axioms: field_X($result) == value for each field in record-new

        Also handles list-new as field value: if field value is (list-new ...),
        add axiom: field_len(field_accessor($result)) == 0
        """
        axioms = []
        result_var = translator.variables.get('$result')
        if result_var is None:
            return axioms

        # record-new Type (field1 val1) (field2 val2) ...
        for item in record_new.items[2:]:  # Skip 'record-new' and Type
            if isinstance(item, SList) and len(item) >= 2:
                field_name = item[0].name if isinstance(item[0], Symbol) else None
                if field_name:
                    field_func = translator._translate_field_for_obj(result_var, field_name)
                    field_value = translator.translate_expr(item[1])
                    if field_value is not None:
                        axioms.append(field_func == field_value)

                    # If field value is list-new, add length=0 axiom for the field
                    if is_form(item[1], 'list-new'):
                        func_name = "field_len"
                        if func_name not in translator.variables:
                            len_func = z3.Function(func_name, z3.IntSort(), z3.IntSort())
                            translator.variables[func_name] = len_func
                        else:
                            len_func = translator.variables[func_name]
                        axioms.append(len_func(field_func) == z3.IntVal(0))

                    # If field value is a string literal, add string_len axiom
                    # This allows proving postconditions like {(string-len (. report reason)) > 0}
                    if isinstance(item[1], String):
                        str_len_func_name = "string_len"
                        if str_len_func_name not in translator.variables:
                            str_len_func = z3.Function(str_len_func_name, z3.IntSort(), z3.IntSort())
                            translator.variables[str_len_func_name] = str_len_func
                        else:
                            str_len_func = translator.variables[str_len_func_name]
                        actual_len = len(item[1].value)
                        axioms.append(str_len_func(field_func) == z3.IntVal(actual_len))
        return axioms

    def _extract_list_new_axioms(self, list_new_expr: SList, translator: Z3Translator) -> List:
        """Extract axiom: field_len($result) == 0 for list-new

        When list-new is called, the resulting list has length 0.
        This allows proving postconditions like {(list-len $result) == 0}.

        With array encoding enabled, also sets up the array representation.
        """
        axioms = []
        result_var = translator.variables.get('$result')
        if result_var is None:
            return axioms

        # With array encoding, set up array for $result
        if translator.use_array_encoding:
            arr, length = translator._create_list_array('$result')
            # Empty list: length == 0
            axioms.append(length == z3.IntVal(0))
            return axioms

        # Get or create field_len function (fallback for non-array encoding)
        func_name = "field_len"
        if func_name not in translator.variables:
            func = z3.Function(func_name, z3.IntSort(), z3.IntSort())
            translator.variables[func_name] = func
        else:
            func = translator.variables[func_name]

        # list-new returns empty list: len == 0
        axioms.append(func(result_var) == z3.IntVal(0))
        return axioms

    def _extract_record_field_range_axioms(self, translator: Z3Translator) -> List:
        """Extract range type axioms for record fields.

        For record types with range-typed fields like:
            (type ReasonerSuccess (record (inferred-count (Int 0 ..)) ...))

        This adds universal axioms:
            ForAll x: field_inferred_count(x) >= 0

        This enables proving postconditions that depend on the range type bounds
        of record fields, such as {(. s inferred-count) >= 0}.
        """
        axioms = []

        # Collect record types from imported definitions and local type registry
        record_types: Dict[str, RecordType] = {}

        # Add imported record types
        if self.imported_defs:
            for type_name, typ in self.imported_defs.types.items():
                if isinstance(typ, RecordType):
                    record_types[type_name] = typ

        # Add local record types from type registry
        for type_name, typ in self.type_env.type_registry.items():
            if isinstance(typ, RecordType):
                record_types[type_name] = typ

        # Generate axioms for range-typed fields
        for type_name, record_type in record_types.items():
            for field_name, field_type in record_type.fields.items():
                if isinstance(field_type, RangeType):
                    # Get or create the field accessor function
                    func_name = f"field_{field_name}"
                    if func_name not in translator.variables:
                        func = z3.Function(func_name, z3.IntSort(), z3.IntSort())
                        translator.variables[func_name] = func
                    else:
                        func = translator.variables[func_name]

                    # Create universal variable for the axiom
                    x = z3.Int(f"_range_{field_name}_x")

                    # Add bound constraints
                    bounds = field_type.bounds
                    if bounds.min_val is not None:
                        axioms.append(z3.ForAll([x], func(x) >= bounds.min_val))
                    if bounds.max_val is not None:
                        axioms.append(z3.ForAll([x], func(x) <= bounds.max_val))

        return axioms

    def _extract_list_element_property_axioms(self, body: SExpr,
                                               postconditions: List[SExpr],
                                               translator: Z3Translator) -> List:
        """Extract axioms for list element properties (Phase 14).

        For postconditions like (all-triples-have-predicate $result RDF_TYPE),
        this method:
        1. Finds loops that push elements to the result list
        2. Determines the predicate field value from make-triple calls
        3. Adds a universally quantified axiom that all elements have the property

        This enables verification without requiring full inductive proof.
        """
        axioms = []
        if not translator.use_array_encoding:
            return axioms

        # Check if we have array encoding for $result
        if '$result' not in translator.list_arrays:
            return axioms

        arr, length = translator.list_arrays['$result']

        # Find what property value is being set on pushed elements
        # Look for patterns like:
        # (let ((inferred (make-triple arena individual type-pred class2)))
        #   (list-push result inferred))
        # Where type-pred is the predicate we need to verify
        pushed_predicate_values = self._find_pushed_predicate_values(body, translator)

        if not pushed_predicate_values:
            return axioms

        # Get or create predicate accessor function
        pred_func_name = "field_predicate"
        if pred_func_name not in translator.variables:
            pred_func = z3.Function(pred_func_name, z3.IntSort(), z3.IntSort())
            translator.variables[pred_func_name] = pred_func
        else:
            pred_func = translator.variables[pred_func_name]

        # For each unique predicate value found, check if postcondition expects it
        for pred_value in pushed_predicate_values:
            if pred_value is None:
                continue

            # Add the key axiom: for all valid indices, element has the predicate
            # forall i: 0 <= i < length => field_predicate(Select(arr, i)) == pred_value
            idx = z3.Int("_elem_idx")
            element = z3.Select(arr, idx)
            element_pred = pred_func(element)

            # The quantified axiom
            condition = z3.And(idx >= 0, idx < length)
            body_constraint = element_pred == pred_value
            axiom = z3.ForAll([idx], z3.Implies(condition, body_constraint))
            axioms.append(axiom)

            # Also add: length >= 0 (already ensured but reinforce)
            axioms.append(length >= 0)

        return axioms

    def _find_pushed_predicate_values(self, expr: SExpr,
                                       translator: Z3Translator) -> List[Optional[z3.ExprRef]]:
        """Find the predicate values of elements pushed to result lists.

        Looks for patterns like:
        (let ((inferred (make-triple arena individual type-pred class2)))
          ... (list-push result inferred))

        Returns the Z3 expression for type-pred (the predicate argument to make-triple).
        """
        predicate_values: List[Optional[z3.ExprRef]] = []
        self._collect_pushed_predicate_values(expr, {}, translator, predicate_values)
        return predicate_values

    def _collect_pushed_predicate_values(self, expr: SExpr,
                                          var_bindings: Dict[str, SExpr],
                                          translator: Z3Translator,
                                          results: List[Optional[z3.ExprRef]]):
        """Recursively collect predicate values from pushed elements."""
        if not isinstance(expr, SList) or len(expr) < 1:
            return

        head = expr[0]
        if not isinstance(head, Symbol):
            return

        # Handle let expressions - track variable bindings
        if head.name == 'let' and len(expr) >= 3:
            new_bindings = dict(var_bindings)
            bindings = expr[1]
            if isinstance(bindings, SList):
                for binding in bindings.items:
                    if isinstance(binding, SList) and len(binding) >= 2:
                        # Handle (var value) and (mut var value)
                        first = binding[0]
                        if isinstance(first, Symbol) and first.name == 'mut' and len(binding) >= 3:
                            var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                            init_expr = binding[2]
                        elif isinstance(first, Symbol):
                            var_name = first.name
                            init_expr = binding[1]
                        else:
                            var_name = None
                            init_expr = None

                        if var_name and init_expr:
                            new_bindings[var_name] = init_expr

            # Recurse into body with updated bindings
            for body_expr in expr.items[2:]:
                self._collect_pushed_predicate_values(body_expr, new_bindings, translator, results)

        # Handle list-push: (list-push result item)
        elif head.name == 'list-push' and len(expr) >= 3:
            item_expr = expr[2]

            # Check if item is a variable bound to make-triple
            if isinstance(item_expr, Symbol):
                item_name = item_expr.name
                if item_name in var_bindings:
                    init_expr = var_bindings[item_name]
                    if is_form(init_expr, 'make-triple') and len(init_expr) >= 4:
                        # make-triple arena subject predicate object
                        pred_arg = init_expr[3]  # The predicate argument

                        # Translate the predicate argument
                        pred_z3 = translator.translate_expr(pred_arg)
                        if pred_z3 is not None:
                            results.append(pred_z3)

        # Handle for-each loops
        elif head.name == 'for-each' and len(expr) >= 3:
            for body_item in expr.items[2:]:
                self._collect_pushed_predicate_values(body_item, var_bindings, translator, results)

        # Handle if/when expressions
        elif head.name in ('if', 'when', 'unless'):
            for item in expr.items[2:]:
                self._collect_pushed_predicate_values(item, var_bindings, translator, results)

        # Handle do blocks
        elif head.name == 'do':
            for item in expr.items[1:]:
                self._collect_pushed_predicate_values(item, var_bindings, translator, results)

    # ========================================================================
    # Failure Suggestion Helpers
    # ========================================================================

    def _has_nested_match(self, expr: 'SExpr') -> bool:
        """Check if expression contains nested match expressions"""
        count_holder = [0]  # Use list as mutable container
        self._count_matches(expr, count_holder)
        return count_holder[0] > 1

    def _count_matches(self, expr: SExpr, count: list):
        """Count match expressions in expression"""
        if is_form(expr, 'match'):
            count[0] = count[0] + 1
        if isinstance(expr, SList):
            for item in expr.items:
                self._count_matches(item, count)

    def _is_equality_function(self, fn_form: SList) -> bool:
        """Check if function is an equality function (name ends in -eq)"""
        if len(fn_form) >= 2 and isinstance(fn_form[1], Symbol):
            return fn_form[1].name.endswith('-eq')
        return False

    def _postcondition_references_field_relationship(self, fn_form: SList) -> bool:
        """Check if postcondition relates fields (e.g., size == list-len triples)"""
        for item in fn_form.items[3:]:
            if is_form(item, '@post') and len(item) >= 2:
                post = item[1]
                # Look for patterns like (== field (list-len other-field))
                if is_form(post, '==') and len(post) >= 3:
                    left = post[1]
                    right = post[2]
                    # Check for list-len, array-len, etc.
                    if is_form(right, 'list-len') or is_form(left, 'list-len'):
                        return True
        return False

    def _postcondition_uses_contains(self, fn_form: SList) -> bool:
        """Check if postcondition uses a contains-type predicate"""
        for item in fn_form.items[3:]:
            if is_form(item, '@post') and len(item) >= 2:
                post = item[1]
                if self._contains_predicate_call(post, 'contains'):
                    return True
        return False

    def _contains_predicate_call(self, expr: SExpr, pattern: str) -> bool:
        """Check if expression contains a function call matching pattern"""
        if isinstance(expr, SList) and len(expr) >= 1:
            head = expr[0]
            if isinstance(head, Symbol) and pattern in head.name:
                return True
            for item in expr.items:
                if self._contains_predicate_call(item, pattern):
                    return True
        return False

    def _generate_failure_suggestion(self, fn_form: SList, fn_body: Optional[SExpr]) -> List[str]:
        """Generate helpful suggestions when verification fails."""
        suggestions = []

        # Check for unrecognized loop patterns
        if fn_body is not None and self._has_for_each(fn_body):
            pattern = self._detect_filter_pattern(fn_body)
            if pattern is None:
                # Loop exists but pattern not recognized
                suggestions.append(
                    "Function contains a loop that the verifier cannot analyze automatically.\n"
                    "    Add (@loop-invariant condition) inside the loop body, or\n"
                    "    Add (@assume postcondition) to trust the postcondition."
                )
            else:
                # Pattern detected but axioms may be insufficient
                suggestions.append(
                    "Loop resembles filter pattern but postcondition may need additional axioms.\n"
                    "    Consider: (@loop-invariant (<= (size result) (size collection)))\n"
                    "    Or use @assume on the postcondition if the loop behavior is trusted."
                )

        # Check for type invariant opportunities
        if self._postcondition_references_field_relationship(fn_form):
            suggestions.append(
                "Postcondition relates fields (e.g., size == list-len items).\n"
                "    Consider adding @invariant to the type definition:\n"
                "    (type YourType (record ...) (@invariant (== field1 (expr field2))))"
            )

        # Check for union equality patterns
        if self._is_equality_function(fn_form):
            if fn_body is not None and self._has_nested_match(fn_body):
                suggestions.append(
                    "This equality function uses nested match - too complex for automatic verification.\n"
                    "    Z3 cannot connect nested match logic to abstract equality semantics.\n"
                    "    Consider breaking into smaller functions (e.g., iri-eq, blank-eq, literal-eq)\n"
                    "    that each compare a single variant's fields directly."
                )

        # Check for conditional insert patterns with contains postconditions
        if fn_body is not None and self._is_conditional_with_record_new(fn_body):
            if self._postcondition_uses_contains(fn_form):
                suggestions.append(
                    "Function has conditional insert pattern with contains postcondition.\n"
                    "    The verifier detected the pattern but couldn't prove contains.\n"
                    "    Consider: (@assume (predicate-name $result item)) to trust the invariant."
                )

        return suggestions

    # ========================================================================
    # ========================================================================
    # Main Verification Entry Points
    # ========================================================================

    def verify_function(self, fn_form: SList) -> VerificationResult:
        """Verify a single function's contracts"""
        # Extract function info
        if len(fn_form) < 3:
            return VerificationResult(
                name="unknown",
                verified=False,
                status="skipped",
                message="Invalid function form",
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )

        fn_name = fn_form[1].name if isinstance(fn_form[1], Symbol) else "unknown"
        params = fn_form[2] if isinstance(fn_form[2], SList) else SList([])

        # Extract contracts and function body
        preconditions: List[Tuple[Optional[str], SExpr]] = []  # @pre - (name, expr) tuples
        postconditions: List[SExpr] = []
        assumptions: List[SExpr] = []  # @assume - trusted axioms for verification
        properties: List[Tuple[Optional[str], SExpr]] = []  # @property - (name, expr) tuples
        spec_return_type: Optional[Type] = None
        fn_body: Optional[SExpr] = None  # Function body for path-sensitive analysis

        # Annotation forms to skip when looking for body
        annotation_forms = {'@intent', '@spec', '@pre', '@post', '@assume', '@pure',
                           '@alloc', '@example', '@deprecated', '@property',
                           '@generation-mode', '@requires'}
        skip_next_string = False  # Track if next String is a property value after :keyword

        for item in fn_form.items[3:]:
            if is_form(item, '@pre') and len(item) > 1:
                # Named: (@pre name expr) or Unnamed: (@pre expr)
                if isinstance(item[1], Symbol) and len(item) > 2 and not item[1].name.startswith('{'):
                    preconditions.append((item[1].name, item[2]))
                else:
                    preconditions.append((None, item[1]))
            elif is_form(item, '@post') and len(item) > 1:
                postconditions.append(item[1])
            elif is_form(item, '@assume') and len(item) > 1:
                assumptions.append(item[1])
            elif is_form(item, '@property') and len(item) > 1:
                # Named: (@property name expr) or Unnamed: (@property expr)
                if isinstance(item[1], Symbol) and len(item) > 2:
                    properties.append((item[1].name, item[2]))
                else:
                    properties.append((None, item[1]))
            elif is_form(item, '@spec') and len(item) > 1:
                spec = item[1]
                if isinstance(spec, SList) and len(spec) >= 3:
                    # (@spec ((ParamTypes) -> ReturnType))
                    # Find the return type (after ->)
                    for i, s in enumerate(spec.items):
                        if isinstance(s, Symbol) and s.name == '->':
                            if i + 1 < len(spec):
                                spec_return_type = _parse_type_expr_simple(spec[i + 1], self.type_env.type_registry)
                            break
            elif isinstance(item, SList) and len(item) > 0:
                # Check if this is an annotation form
                head = item[0]
                if isinstance(head, Symbol) and head.name in annotation_forms:
                    continue
                # This is the function body
                fn_body = item
            elif isinstance(item, Symbol):
                # Skip keyword properties like :c-name
                if item.name.startswith(':'):
                    skip_next_string = True  # The next String is a property value
                    continue
                # Simple expression as body (e.g., variable reference)
                fn_body = item
                skip_next_string = False
            elif isinstance(item, Number):
                # Simple numeric expression as body
                fn_body = item
                skip_next_string = False
            elif isinstance(item, String):
                # Skip string values after :keyword (property values)
                # But allow standalone String as function body
                if skip_next_string:
                    skip_next_string = False
                    continue
                fn_body = item

        # Extract loop invariants from function body and treat them as assumptions
        # @loop-invariant provides axioms that help verify loops
        if fn_body is not None:
            loop_invariants = self._extract_loop_invariants(fn_body)
            assumptions.extend(loop_invariants)

        # Skip if no contracts to verify
        if not preconditions and not postconditions and not assumptions and not properties:
            return VerificationResult(
                name=fn_name,
                verified=True,
                status="skipped",
                message="No contracts to verify",
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )

        # Check if postconditions reference mutable state
        mutable_posts = [p for p in postconditions if self._references_mutable_state(p)]
        if mutable_posts:
            return VerificationResult(
                name=fn_name,
                verified=False,
                status="warning",
                message="Postcondition references mutable state; cannot verify without body analysis",
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )

        # Determine if array or sequence encoding is needed for postconditions or properties
        use_array_encoding = self._needs_array_encoding(postconditions)
        # Check both postconditions and properties for seq encoding need
        property_exprs = [prop_expr for _, prop_expr in properties]
        use_seq_encoding = (self._needs_seq_encoding(postconditions) or
                           self._needs_seq_encoding(property_exprs))

        # Create translator and declare parameters
        translator = Z3Translator(self.type_env, self.filename, self.function_registry,
                                  self.imported_defs, use_array_encoding=use_array_encoding,
                                  use_seq_encoding=use_seq_encoding)

        # Declare parameter variables
        for param in params:
            if isinstance(param, SList) and len(param) >= 2:
                # Handle parameter modes: (name Type) or (in name Type) or (out name Type) or (mut name Type)
                first = param[0]
                if isinstance(first, Symbol) and first.name in ('in', 'out', 'mut'):
                    # Mode is explicit: (in name Type)
                    param_name = param[1].name if isinstance(param[1], Symbol) else None
                    param_type_expr = param[2] if len(param) > 2 else None
                else:
                    # No mode: (name Type)
                    param_name = first.name if isinstance(first, Symbol) else None
                    param_type_expr = param[1]
                if param_name and param_type_expr:
                    param_type = _parse_type_expr_simple(param_type_expr, self.type_env.type_registry)
                    translator.declare_variable(param_name, param_type)

        # Declare $result for postconditions and assumptions
        if postconditions or assumptions:
            if spec_return_type:
                # For enum return types, use Int and constrain to valid range
                if isinstance(spec_return_type, EnumType):
                    result_var = translator.declare_variable('$result', PrimitiveType('Int'))
                    # Add constraint that result is a valid enum value
                    num_variants = len(spec_return_type.variants)
                    translator.constraints.append(result_var >= 0)
                    translator.constraints.append(result_var < num_variants)
                else:
                    translator.declare_variable('$result', spec_return_type)
            else:
                # Default to Int if no spec
                translator.declare_variable('$result', PrimitiveType('Int'))

        # Set up array encoding for $result BEFORE translating postconditions
        # This is needed because all-triples-have-predicate expansion requires array access
        if use_array_encoding and fn_body is not None and self._is_list_new(fn_body):
            arr, length = translator._create_list_array('$result')
            # Empty list initially: length >= 0 (will be constrained to 0 in list-new axioms)
            translator.constraints.append(length >= 0)

        # Set up sequence encoding for $result BEFORE translating postconditions/properties
        # This enables collection-bound quantifiers like (forall (t $result) ...)
        if use_seq_encoding:
            # Create $result Seq if body returns a list
            if fn_body is not None and self._is_list_new(fn_body):
                translator._create_list_seq('$result')
            # Also create $result Seq if postconditions/properties reference it as a collection
            elif self._references_result_collection(postconditions) or self._references_result_collection(property_exprs):
                translator._create_list_seq('$result')

        # Translate preconditions
        pre_z3: List[z3.BoolRef] = []
        failed_pres: List[Tuple[Optional[str], SExpr]] = []
        for pre_name, pre_expr in preconditions:
            z3_pre = translator.translate_expr(pre_expr)
            if z3_pre is not None:
                pre_z3.append(z3_pre)
            else:
                failed_pres.append((pre_name, pre_expr))

        # Translate postconditions
        post_z3: List[z3.BoolRef] = []
        failed_posts: List[SExpr] = []
        for post in postconditions:
            z3_post = translator.translate_expr(post)
            if z3_post is not None:
                post_z3.append(z3_post)
            else:
                failed_posts.append(post)

        # Translate function body BEFORE assumptions
        # This is important because @loop-invariant may reference local variables
        # from let bindings, which are declared during body translation
        body_z3: Optional[z3.ExprRef] = None
        if fn_body is not None and postconditions:
            body_z3 = translator.translate_expr(fn_body)
            # If we can translate the body, constrain $result to equal it
            # This enables path-sensitive reasoning through conditionals

        # Translate assumptions (trusted axioms) - AFTER body so local vars are declared
        assume_z3: List[z3.BoolRef] = []
        failed_assumes: List[SExpr] = []
        for assume in assumptions:
            z3_assume = translator.translate_expr(assume)
            if z3_assume is not None:
                assume_z3.append(z3_assume)
            else:
                failed_assumes.append(assume)

        # Translate properties (universal assertions)
        # properties is List[Tuple[Optional[str], SExpr]] - (name, expr) tuples
        prop_z3: List[z3.BoolRef] = []
        failed_props: List[Tuple[Optional[str], SExpr]] = []
        for prop_name, prop_expr in properties:
            z3_prop = translator.translate_expr(prop_expr)
            if z3_prop is not None:
                prop_z3.append(z3_prop)
            else:
                failed_props.append((prop_name, prop_expr))

        # Report translation failures
        if failed_pres:
            from slop.parser import pretty_print
            pre_details = []
            for pre_name, pre_expr in failed_pres:
                pre_str = pretty_print(pre_expr)
                if pre_name:
                    pre_details.append(f"'{pre_name}': {pre_str}")
                else:
                    pre_details.append(pre_str)
            if len(failed_pres) == 1:
                message = f"Could not translate precondition: {pre_details[0]}"
            else:
                message = "Could not translate preconditions:\n" + "\n".join(f"  • {p}" for p in pre_details)
            return VerificationResult(
                name=fn_name,
                verified=False,
                status="failed",
                message=message,
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )

        if failed_posts:
            from slop.parser import pretty_print
            post_details = [pretty_print(p) for p in failed_posts]
            if len(failed_posts) == 1:
                message = f"Could not translate postcondition: {post_details[0]}"
            else:
                message = "Could not translate postconditions:\n" + "\n".join(f"  • {p}" for p in post_details)
            return VerificationResult(
                name=fn_name,
                verified=False,
                status="failed",
                message=message,
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )

        if failed_assumes:
            from slop.parser import pretty_print
            assume_details = [pretty_print(a) for a in failed_assumes]
            if len(failed_assumes) == 1:
                message = f"Could not translate assumption: {assume_details[0]}"
            else:
                message = "Could not translate assumptions:\n" + "\n".join(f"  • {a}" for a in assume_details)
            return VerificationResult(
                name=fn_name,
                verified=False,
                status="failed",
                message=message,
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )

        if failed_props:
            from slop.parser import pretty_print
            prop_details = []
            for prop_name, prop_expr in failed_props:
                prop_str = pretty_print(prop_expr)
                if prop_name:
                    prop_details.append(f"'{prop_name}': {prop_str}")
                else:
                    prop_details.append(prop_str)
            if len(failed_props) == 1:
                message = f"Could not translate property: {prop_details[0]}"
            else:
                message = "Could not translate properties:\n" + "\n".join(f"  • {p}" for p in prop_details)
            return VerificationResult(
                name=fn_name,
                verified=False,
                status="failed",
                message=message,
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )

        if not post_z3 and not postconditions and not prop_z3:
            # No postconditions to verify
            if assume_z3:
                # Only @assume (trusted axioms), consider verified via assumption
                return VerificationResult(
                    name=fn_name,
                    verified=True,
                    status="verified",
                    message="Verified via @assume (trusted)",
                    location=SourceLocation(self.filename, fn_form.line, fn_form.col)
                )
            # No postconditions at all, check if preconditions are satisfiable
            solver = z3.Solver()
            solver.set("timeout", self.timeout_ms)

            for c in translator.constraints:
                solver.add(c)
            for p in pre_z3:
                solver.add(p)

            result = solver.check()
            if result == z3.unsat:
                # Build message with precondition names/details
                from slop.parser import pretty_print
                if preconditions:
                    pre_details = []
                    for pre_name, pre_expr in preconditions:
                        pre_str = pretty_print(pre_expr)
                        if pre_name:
                            pre_details.append(f"'{pre_name}': {pre_str}")
                        else:
                            pre_details.append(pre_str)
                    if len(preconditions) == 1:
                        message = f"Precondition is unsatisfiable: {pre_details[0]}"
                    else:
                        message = "Preconditions are unsatisfiable:\n" + "\n".join(f"  • {p}" for p in pre_details)
                else:
                    message = "Preconditions are unsatisfiable"
                return VerificationResult(
                    name=fn_name,
                    verified=False,
                    status="failed",
                    message=message,
                    location=SourceLocation(self.filename, fn_form.line, fn_form.col)
                )
            return VerificationResult(
                name=fn_name,
                verified=True,
                status="verified",
                message="Preconditions are satisfiable",
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )

        # Check: can we satisfy preconditions but violate postconditions?
        # If (pre AND NOT post) is SAT, then contract can be violated
        solver = z3.Solver()
        solver.set("timeout", self.timeout_ms)

        # Add type constraints
        for c in translator.constraints:
            solver.add(c)

        # Add preconditions
        for p in pre_z3:
            solver.add(p)

        # Add assumptions as trusted axioms
        for a in assume_z3:
            solver.add(a)

        # Phase 1: Add type invariants for parameters
        # For (type T (record ...) (@invariant cond)), when param has type T,
        # add cond substituted with param.field references
        param_invariants = self._collect_parameter_invariants(params)
        for param_name, inv_expr in param_invariants:
            inv_z3 = translator.translate_expr(inv_expr)
            if inv_z3 is not None:
                solver.add(inv_z3)

        # Phase 1b: Add range type axioms for record fields
        # For record types with range-typed fields like (inferred-count (Int 0 ..)),
        # add universal axioms: ForAll x: field_inferred_count(x) >= 0
        range_field_axioms = self._extract_record_field_range_axioms(translator)
        for axiom in range_field_axioms:
            solver.add(axiom)

        # Add body constraint for path-sensitive analysis
        # This constrains $result to equal the translated function body
        if body_z3 is not None:
            result_var = translator.variables.get('$result')
            if result_var is not None:
                solver.add(result_var == body_z3)

        # Phase 2: Add reflexivity axioms for equality functions
        # For any function ending in -eq, add axiom: fn_eq(x, x) == true
        # Include -eq functions from both postconditions AND body
        eq_funcs = self._find_eq_function_calls(postconditions)
        if fn_body is not None:
            eq_funcs = eq_funcs.union(self._find_eq_function_calls([fn_body]))
        for eq_fn in eq_funcs:
            func_key = f"fn_{eq_fn}_2"  # 2-arity eq functions
            if func_key in translator.variables:
                eq_func = translator.variables[func_key]
                # ForAll x: eq_func(x, x) == True
                refl_x = z3.Int("_refl_x")
                solver.add(z3.ForAll([refl_x], eq_func(refl_x, refl_x) == z3.BoolVal(True)))

        # Phase 3: Add record field axioms if body is record-new
        # For (record-new Type (field1 val1) ...), add: field_field1($result) == val1
        if fn_body is not None and self._is_record_new(fn_body):
            # Get the actual record-new form (may be inside a do block)
            return_expr = self._get_return_expr(fn_body)
            field_axioms = self._extract_record_field_axioms(return_expr, translator)
            for axiom in field_axioms:
                solver.add(axiom)

        # Phase 3.5: Add list-new axioms if body is list-new
        # For (list-new arena Type), add: field_len($result) == 0
        if fn_body is not None and self._is_list_new(fn_body):
            return_expr = self._get_return_expr(fn_body)
            list_axioms = self._extract_list_new_axioms(return_expr, translator)
            for axiom in list_axioms:
                solver.add(axiom)

        # Phase 4: Add union tag axiom if body is union-new
        # For (union-new Type tag payload), add: union_tag($result) == tag_index
        # Allows proving match postconditions like (match $result ((tag _) true) (_ false))
        if fn_body is not None and self._is_union_new(fn_body):
            # Get the actual union-new form (may be inside a do block)
            return_expr = self._get_return_expr(fn_body)
            tag_axiom = self._extract_union_tag_axiom(return_expr, translator)
            if tag_axiom is not None:
                solver.add(tag_axiom)
            # Also add field axioms for record-new payloads
            field_axioms = self._extract_union_new_field_axioms(return_expr, translator)
            for axiom in field_axioms:
                solver.add(axiom)

        # Phase 4.5: Add union constructor axioms for (ok result), (error e), etc.
        # For the final return, add UNCONDITIONAL axioms (tag == X, payload == value).
        # This handles single-return-path functions like apply-cax-rules.
        if fn_body is not None and self._is_union_constructor(fn_body):
            constructor_axioms = self._extract_union_constructor_axioms(fn_body, translator)
            for axiom in constructor_axioms:
                solver.add(axiom)

        # Phase 4.6: Add CONDITIONAL axioms for early return statements
        # For functions with multiple return paths like cax-dw:
        #   (return (some (record-new ...))) ... (none)
        # Add conditional axioms: tag == some => field_reason(...) == "..."
        # This allows Z3 to use the axioms when exploring the 'some' case.
        if fn_body is not None:
            all_returns = self._collect_all_return_exprs(fn_body)
            final_return = self._get_return_expr(fn_body)
            for return_expr in all_returns:
                # Skip the final return (already handled by Phase 4.5)
                if return_expr is final_return:
                    continue
                # Check if this return is a union constructor or union-new
                if isinstance(return_expr, SList) and len(return_expr) >= 1:
                    head = return_expr[0]
                    if isinstance(head, Symbol):
                        if head.name in {'ok', 'error', 'some', 'none'}:
                            constructor_axioms = self._extract_union_constructor_axioms_for_expr(
                                return_expr, translator
                            )
                            for axiom in constructor_axioms:
                                solver.add(axiom)
                        elif head.name == 'union-new':
                            # Handle union-new returns from match branches
                            tag_axiom = self._extract_union_tag_axiom(return_expr, translator)
                            if tag_axiom is not None:
                                solver.add(tag_axiom)
                            field_axioms = self._extract_union_new_field_axioms(return_expr, translator)
                            for axiom in field_axioms:
                                solver.add(axiom)

        # Phase 4.7: Add match exhaustiveness constraints
        # For match postconditions like (match $result ((none) true) ((some r) cond)),
        # add constraint: union_tag($result) == none_tag OR union_tag($result) == some_tag
        # This prevents Z3 from finding counterexamples with invalid tag values.
        if postconditions:
            exhaustiveness_constraints = self._extract_match_exhaustiveness_constraints(
                postconditions, translator
            )
            for constraint in exhaustiveness_constraints:
                solver.add(constraint)

        # Phase 5: Add conditional record-new axioms
        # For (if cond (record-new Type (f1 v1) ...) else), add: cond => field_f1($result) == v1
        if fn_body is not None and self._is_conditional_with_record_new(fn_body):
            cond_axioms = self._extract_conditional_record_axioms(fn_body, translator)
            for axiom in cond_axioms:
                solver.add(axiom)

        # Phase 6: Add accessor function axioms
        # For functions that are simple field accessors, add axiom: fn_name(x) == field_name(x)
        # Allows proving (>= (graph-size $result) (graph-size g)) by connecting to field access
        if self.function_registry:
            accessor_axioms = self._extract_accessor_axioms(postconditions, translator)
            for axiom in accessor_axioms:
                solver.add(axiom)

        # Phase 7: Add list operation axioms
        # For (list-push lst x), track that list-len increases by 1
        if fn_body is not None:
            list_axioms = self._extract_list_axioms(fn_body, translator)
            for axiom in list_axioms:
                solver.add(axiom)

        # Phase 7b: While loop exit axioms
        # When a while loop exits, the negation of the condition holds.
        # For (while (and (not done) (< i max)) ...), after loop: done OR (i >= max)
        if fn_body is not None:
            while_axioms = self._extract_while_exit_axioms(fn_body, translator)
            for axiom in while_axioms:
                solver.add(axiom)

        # Phase 8: Filter pattern detection and axiom generation
        # Detect filter loop patterns and generate automatic axioms
        if fn_body is not None:
            filter_pattern = self._detect_filter_pattern(fn_body)
            if filter_pattern is not None:
                filter_axioms = self._generate_filter_axioms(filter_pattern, translator)
                for axiom in filter_axioms:
                    solver.add(axiom)

        # Phase 9: Count pattern detection and axiom generation
        # Detect counting loops and generate bounds axioms
        if fn_body is not None:
            count_pattern = self._detect_count_pattern(fn_body)
            if count_pattern is not None:
                count_axioms = self._generate_count_axioms(count_pattern, translator)
                for axiom in count_axioms:
                    solver.add(axiom)

        # Phase 10: Fold pattern detection and axiom generation
        # Detect accumulation loops and generate appropriate axioms
        if fn_body is not None:
            fold_pattern = self._detect_fold_pattern(fn_body)
            if fold_pattern is not None:
                fold_axioms = self._generate_fold_axioms(fold_pattern, translator)
                for axiom in fold_axioms:
                    solver.add(axiom)

        # Phase 11: Union structural equality axioms
        # For union equality functions (e.g., term-eq), add axioms connecting
        # structural equality to Z3's native equality
        if fn_body is not None:
            union_eq_axioms = self._extract_union_equality_axioms(fn_form, fn_body, translator)
            for axiom in union_eq_axioms:
                solver.add(axiom)

        # Phase 12: Postcondition propagation from called functions
        # When a function is called and its result is bound to a variable,
        # add the called function's postconditions as axioms with substituted values.
        # This enables reasoning about properties of intermediate results.
        if fn_body is not None:
            call_postcond_axioms = self._extract_call_postcondition_axioms(fn_body, translator)
            for axiom in call_postcond_axioms:
                solver.add(axiom)

        # Phase 13: Inductive loop verification
        # For loops with self-referential set! statements, attempt to verify
        # loop invariants inductively and add them as axioms.
        # Example: (set! result (delta-add arena result t)) with postcondition
        # {(. $result iteration) == (. d iteration)} allows inferring that
        # result.iteration is preserved through all loop iterations.
        if fn_body is not None:
            loop_contexts = self._analyze_loops(fn_body)
            for loop_ctx in loop_contexts:
                # Find initialization binding for modified variables
                for var_name in loop_ctx.modified_vars:
                    init_binding = self._find_init_binding_for_var(fn_body, var_name)

                    # Attempt inductive verification
                    verified_invariants = self._verify_loop_inductively(
                        loop_ctx, init_binding, translator
                    )

                    if verified_invariants:
                        # Add verified invariants as axioms
                        inv_axioms = self._apply_verified_invariants(
                            verified_invariants, var_name, translator
                        )
                        for axiom in inv_axioms:
                            solver.add(axiom)

        # Phase 14: List element property invariants (with array encoding)
        # For postconditions like (all-triples-have-predicate $result RDF_TYPE),
        # detect that all pushed elements have the required property and add
        # a universally quantified axiom.
        #
        # Collect pattern axioms to share with property verification
        pattern_axioms: List[z3.BoolRef] = []

        if fn_body is not None and translator.use_array_encoding:
            element_property_axioms = self._extract_list_element_property_axioms(
                fn_body, postconditions, translator
            )
            for axiom in element_property_axioms:
                solver.add(axiom)
                pattern_axioms.append(axiom)

        # Phase 14b: Sequence push provenance axioms (with Seq encoding)
        # For filter patterns that build lists via list-push, generate axioms
        # connecting result elements to their source collection and predicate.
        # This enables proving postconditions like (forall (t $result) (pred t)).
        if fn_body is not None and translator.use_seq_encoding:
            seq_push_axioms = self._extract_seq_push_axioms(
                fn_body, postconditions, translator
            )
            for axiom in seq_push_axioms:
                solver.add(axiom)
                pattern_axioms.append(axiom)

        # Phase 14c: Map pattern push axioms (with Seq encoding)
        # For map/transform patterns that build lists via unconditional list-push
        # of constructor expressions, generate axioms connecting result fields
        # to source fields. This enables proving postconditions like:
        #   (forall (t $result) (exists (dt source) (field-relationship t dt)))
        if fn_body is not None and translator.use_seq_encoding:
            map_push_axioms = self._extract_map_push_axioms(
                fn_body, postconditions, translator
            )
            for axiom in map_push_axioms:
                solver.add(axiom)
                pattern_axioms.append(axiom)

        # Phase 15: Weakest Precondition Calculus
        # Use backward reasoning to generate stronger verification conditions.
        # WP(body, postcondition) computes what must be true before the body
        # executes to guarantee the postcondition holds after.
        #
        # The WP is used selectively: for let/if/cond expressions that
        # establish $result through local bindings, we add the WP as a
        # constraint. This helps verify functions where the body directly
        # computes the result through sequential/conditional logic.
        #
        # We do NOT add WP for simple expressions (variables, constants)
        # as that would just add True which doesn't help verification.
        if fn_body is not None and post_z3 and self._is_wp_applicable(fn_body):
            wp_calc = WeakestPrecondition(translator)

            for post_z3_expr in post_z3:
                try:
                    wp_result = wp_calc.wp(fn_body, post_z3_expr)
                    # Only add meaningful WP results (not True, not the same as post)
                    if (wp_result is not None and
                        not z3.eq(wp_result, z3.BoolVal(True)) and
                        not z3.eq(wp_result, post_z3_expr)):
                        # For let/if/cond, WP tells us what the body establishes
                        # Add as implication: if WP holds, post should hold
                        # This is sound because WP(body, Q) => body establishes Q
                        solver.add(z3.Implies(wp_result, post_z3_expr))
                except Exception:
                    # WP computation failed - continue with standard verification
                    pass

        # First try all postconditions together (fast path)
        solver.push()
        solver.add(z3.Not(z3.And(*post_z3)))
        result = solver.check()
        solver.pop()

        if result == z3.unsat:
            # Postconditions always hold when preconditions are met
            # Now verify properties (universal assertions - independent of preconditions)
            if prop_z3:
                from slop.parser import pretty_print
                # Collect all failures instead of returning on first failure
                failed_properties: List[Tuple[Optional[str], str, Dict[str, str]]] = []  # (name, expr_str, counterexample)
                unknown_properties: List[Tuple[Optional[str], str]] = []  # (name, expr_str)

                for i, ((prop_name, prop_expr), prop_z3_expr) in enumerate(zip(properties, prop_z3)):
                    prop_solver = z3.Solver()
                    prop_solver.set("timeout", self.timeout_ms)

                    # Add type constraints only (not preconditions)
                    for c in translator.constraints:
                        prop_solver.add(c)

                    # Add pattern axioms (filter/map/fold axioms derived from loop analysis)
                    # These are needed for properties that reason about collection contents
                    for axiom in pattern_axioms:
                        prop_solver.add(axiom)

                    # Add axioms for imported equality functions
                    # This allows Z3 to understand that e.g., term-eq(a,b) == (a == b)
                    imported_eq_axioms = self._extract_imported_equality_axioms(translator)
                    for axiom in imported_eq_axioms:
                        prop_solver.add(axiom)

                    # Check if NOT property is satisfiable
                    prop_solver.add(z3.Not(prop_z3_expr))
                    prop_result = prop_solver.check()

                    prop_str = pretty_print(prop_expr)

                    if prop_result == z3.sat:
                        model = prop_solver.model()
                        counterexample = {str(decl.name()): str(model[decl])
                                         for decl in model.decls()
                                         if not str(decl.name()).startswith('field_')}
                        failed_properties.append((prop_name, prop_str, counterexample))
                    elif prop_result == z3.unknown:
                        unknown_properties.append((prop_name, prop_str))

                # Report all failures at once
                if failed_properties:
                    if len(failed_properties) == 1:
                        prop_name, prop_str, counterexample = failed_properties[0]
                        if prop_name:
                            message = f"Property '{prop_name}' failed: {prop_str}"
                        else:
                            message = f"Property failed: {prop_str}"
                    else:
                        lines = []
                        for prop_name, prop_str, _ in failed_properties:
                            if prop_name:
                                lines.append(f"  • '{prop_name}': {prop_str}")
                            else:
                                lines.append(f"  • {prop_str}")
                        message = "Properties failed:\n" + "\n".join(lines)
                        # Use first failure's counterexample
                        counterexample = failed_properties[0][2]
                    return VerificationResult(
                        name=fn_name,
                        verified=False,
                        status="failed",
                        message=message,
                        counterexample=counterexample,
                        location=SourceLocation(self.filename, fn_form.line, fn_form.col)
                    )

                # Report unknown properties if no failures
                if unknown_properties:
                    if len(unknown_properties) == 1:
                        prop_name, prop_str = unknown_properties[0]
                        if prop_name:
                            message = f"Could not verify property '{prop_name}': {prop_str}"
                        else:
                            message = f"Could not verify property: {prop_str}"
                    else:
                        lines = []
                        for prop_name, prop_str in unknown_properties:
                            if prop_name:
                                lines.append(f"  • '{prop_name}': {prop_str}")
                            else:
                                lines.append(f"  • {prop_str}")
                        message = "Could not verify properties:\n" + "\n".join(lines)
                    return VerificationResult(
                        name=fn_name,
                        verified=False,
                        status="unknown",
                        message=message,
                        location=SourceLocation(self.filename, fn_form.line, fn_form.col)
                    )

            return VerificationResult(
                name=fn_name,
                verified=True,
                status="verified",
                message="Contract verified",
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )
        elif result == z3.sat:
            # Some postcondition(s) failed - check each individually to identify which
            failed_posts: List[str] = []
            verified_posts: List[str] = []

            for i, (post_expr, post_z3_expr) in enumerate(zip(postconditions, post_z3)):
                solver.push()
                solver.add(z3.Not(post_z3_expr))
                individual_result = solver.check()
                solver.pop()

                # Format the postcondition for display
                from slop.parser import pretty_print
                post_str = pretty_print(post_expr)

                if individual_result == z3.unsat:
                    verified_posts.append(post_str)
                else:
                    failed_posts.append(post_str)

            # Build detailed message
            if failed_posts:
                if len(failed_posts) == 1:
                    message = f"Postcondition failed: {failed_posts[0]}"
                else:
                    message = "Postconditions failed:\n" + "\n".join(f"  • {p}" for p in failed_posts)
            else:
                message = "Contract may be violated"

            # Get counterexample from one more check
            solver.push()
            solver.add(z3.Not(z3.And(*post_z3)))
            solver.check()
            model = solver.model()
            solver.pop()

            counterexample = {}
            for decl in model.decls():
                name = decl.name()
                if not name.startswith('field_'):  # Skip internal functions
                    counterexample[name] = str(model[decl])

            # Generate actionable suggestions for failed verification
            suggestions = self._generate_failure_suggestion(fn_form, fn_body)

            # Add specific failed postconditions to suggestions
            if failed_posts and len(failed_posts) > 1:
                suggestions = suggestions or []
                suggestions.insert(0, "Failed postconditions:\n    " + "\n    ".join(f"• {p}" for p in failed_posts))
            if verified_posts:
                suggestions = suggestions or []
                suggestions.append("Verified postconditions:\n    " + "\n    ".join(f"✓ {p}" for p in verified_posts))

            return VerificationResult(
                name=fn_name,
                verified=False,
                status="failed",
                message=message,
                counterexample=counterexample,
                location=SourceLocation(self.filename, fn_form.line, fn_form.col),
                suggestions=suggestions if suggestions else None
            )
        else:
            # Unknown (timeout or undecidable)
            suggestions = self._generate_failure_suggestion(fn_form, fn_body)
            return VerificationResult(
                name=fn_name,
                verified=False,
                status="unknown",
                message="Verification timed out or undecidable",
                location=SourceLocation(self.filename, fn_form.line, fn_form.col),
                suggestions=suggestions if suggestions else None
            )

    def verify_all(self, ast: List[SExpr]) -> List[VerificationResult]:
        """Verify all functions in AST"""
        results = []

        for form in ast:
            # Handle module wrapper
            if is_form(form, 'module'):
                for item in form.items[1:]:
                    if is_form(item, 'fn'):
                        results.append(self.verify_function(item))
            elif is_form(form, 'fn'):
                results.append(self.verify_function(form))

        return results




__all__ = [
    'ContractVerifier',
]
