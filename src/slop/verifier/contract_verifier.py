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
from .translator import Z3Translator, _str_hash
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

    def _ensure_bool(self, expr: z3.ExprRef) -> z3.BoolRef:
        """Coerce a Z3 expression to boolean if it's not already boolean.

        Non-boolean expressions (Int, etc.) are converted using != 0 semantics.
        """
        if z3.is_bool(expr):
            return expr
        # Coerce non-boolean to boolean (non-zero = true)
        return expr != 0

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

    # ── String operation axiom generation ──────────────────────────────────

    def _generate_string_operation_axioms(
        self, fn_body: SExpr, postconditions: List[SExpr], translator: Z3Translator
    ) -> List:
        """Generate semantic axioms connecting string-concat, starts-with, string-len.

        Without these axioms, Z3 treats these as uninterpreted functions with no
        relationships, making it impossible to verify postconditions like
        (starts-with $result "?") when the body is (string-concat arena "?" name).

        Axioms generated:
        1. starts-with(concat(arena, a, b), a) — result starts with first operand
        2. string-len(concat(arena, a, b)) == string-len(a) + string-len(b)
        3. string-len(a) > 0 → string-len(concat(arena, a, b)) > 0
        4. For string literal pairs where a.startswith(b): starts-with(hash_a, hash_b)
        5. Transitivity: starts-with(a, prefix) → starts-with(concat(arena, a, ...), prefix)
        """
        axioms: list = []

        # Collect all string-concat calls from body
        concat_calls: List[SList] = []
        self._collect_string_concat_calls(fn_body, concat_calls)

        if not concat_calls and not self._postconditions_use_string_ops(postconditions):
            return axioms

        # Get or create the starts-with function (2 args: string, prefix → Int)
        sw_key = "fn_starts-with_2"
        if sw_key not in translator.variables:
            sw_func = z3.Function(sw_key, z3.IntSort(), z3.IntSort(), z3.IntSort())
            translator.variables[sw_key] = sw_func
        else:
            sw_func = translator.variables[sw_key]

        # Get or create the string-len function
        sl_key = "string_len"
        if sl_key not in translator.variables:
            sl_func = z3.Function(sl_key, z3.IntSort(), z3.IntSort())
            translator.variables[sl_key] = sl_func
        else:
            sl_func = translator.variables[sl_key]

        # For each string-concat call, add ground axioms
        for concat_call in concat_calls:
            if len(concat_call) < 4:
                continue

            first_arg = concat_call[2]   # a in (string-concat arena a b)
            second_arg = concat_call[3]  # b

            concat_z3 = translator.translate_expr(concat_call)
            first_z3 = translator.translate_expr(first_arg)
            second_z3 = translator.translate_expr(second_arg)

            if concat_z3 is None or first_z3 is None:
                continue

            # Axiom 1: starts-with(concat(arena, a, b), a) is truthy
            sw_result = sw_func(concat_z3, first_z3)
            if z3.is_bool(sw_result):
                axioms.append(sw_result)
            else:
                axioms.append(sw_result != 0)

            # Axiom 2: string-len(concat) == string-len(a) + string-len(b)
            if second_z3 is not None:
                axioms.append(
                    sl_func(concat_z3) == sl_func(first_z3) + sl_func(second_z3)
                )

            # Axiom 3: string-len(a) > 0 → string-len(concat) > 0
            axioms.append(z3.Implies(sl_func(first_z3) > 0, sl_func(concat_z3) > 0))

            # Also: string-len(b) > 0 → string-len(concat) > 0
            if second_z3 is not None:
                axioms.append(z3.Implies(sl_func(second_z3) > 0, sl_func(concat_z3) > 0))

        # Collect all string literals from body and postconditions
        body_literals: List[str] = []
        self._collect_string_literals(fn_body, body_literals)
        post_literals: List[str] = []
        for post in postconditions:
            self._collect_string_literals(post, post_literals)
        all_literals = list(set(body_literals + post_literals))

        # Axiom 4: For all pairs of string literals where a.startswith(b)
        for i, lit_a in enumerate(all_literals):
            for j, lit_b in enumerate(all_literals):
                if i != j and lit_a.startswith(lit_b) and lit_b:
                    hash_a = _str_hash(lit_a)
                    hash_b = _str_hash(lit_b)
                    sw_result = sw_func(z3.IntVal(hash_a), z3.IntVal(hash_b))
                    if z3.is_bool(sw_result):
                        axioms.append(sw_result)
                    else:
                        axioms.append(sw_result != 0)

        # Axiom 5: Transitivity — starts-with(a, prefix) → starts-with(concat(arena, a, ...), prefix)
        # For each concat call and each prefix used in postcondition starts-with calls
        post_prefixes = self._extract_starts_with_prefix_z3(postconditions, translator)
        for concat_call in concat_calls:
            if len(concat_call) < 4:
                continue
            first_arg = concat_call[2]
            first_z3 = translator.translate_expr(first_arg)
            concat_z3 = translator.translate_expr(concat_call)
            if first_z3 is None or concat_z3 is None:
                continue
            for prefix_z3 in post_prefixes:
                sw_first = sw_func(first_z3, prefix_z3)
                sw_concat = sw_func(concat_z3, prefix_z3)
                if z3.is_bool(sw_first):
                    axioms.append(z3.Implies(sw_first, sw_concat))
                else:
                    axioms.append(z3.Implies(sw_first != 0, sw_concat != 0))

        return axioms

    def _collect_string_concat_calls(self, expr: SExpr, result: List):
        """Recursively collect all (string-concat ...) call expressions from AST."""
        if not isinstance(expr, SList) or len(expr) == 0:
            return
        head = expr[0]
        if isinstance(head, Symbol) and head.name == 'string-concat' and len(expr) >= 4:
            result.append(expr)
        # Recurse into subexpressions
        for item in expr.items:
            if isinstance(item, SList):
                self._collect_string_concat_calls(item, result)

    def _collect_string_literals(self, expr: SExpr, result: List[str]):
        """Recursively collect all string literal values from AST."""
        if isinstance(expr, String):
            result.append(expr.value)
        elif isinstance(expr, SList):
            for item in expr.items:
                self._collect_string_literals(item, result)

    def _postconditions_use_string_ops(self, postconditions: List[SExpr]) -> bool:
        """Check if any postcondition uses starts-with or string-len."""
        for post in postconditions:
            if self._uses_string_op(post):
                return True
        return False

    def _uses_string_op(self, expr: SExpr) -> bool:
        """Check if expression uses starts-with or string-len."""
        if isinstance(expr, SList) and len(expr) > 0:
            head = expr[0]
            if isinstance(head, Symbol) and head.name in ('starts-with', 'string-len'):
                return True
            for item in expr.items:
                if self._uses_string_op(item):
                    return True
        return False

    def _extract_starts_with_prefix_z3(
        self, postconditions: List[SExpr], translator: Z3Translator
    ) -> List:
        """Extract Z3 translations of prefix arguments from (starts-with ... prefix) in postconditions."""
        prefixes: list = []
        for post in postconditions:
            self._collect_starts_with_prefixes(post, prefixes, translator)
        return prefixes

    def _collect_starts_with_prefixes(
        self, expr: SExpr, result: list, translator: Z3Translator
    ):
        """Recursively find (starts-with X prefix) calls and collect translated prefix values."""
        if isinstance(expr, SList) and len(expr) >= 3:
            head = expr[0]
            if isinstance(head, Symbol) and head.name == 'starts-with':
                prefix_z3 = translator.translate_expr(expr[2])
                if prefix_z3 is not None:
                    result.append(prefix_z3)
                return
            for item in expr.items:
                self._collect_starts_with_prefixes(item, result, translator)
        elif isinstance(expr, SList):
            for item in expr.items:
                self._collect_starts_with_prefixes(item, result, translator)

    # ── End string operation axioms ─────────────────────────────────────

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

        # Handle match expressions - recurse into arm bodies
        # This enables postcondition propagation for dispatch functions like:
        #   (match t ((term-iri iri) (serialize-iri arena iri prefixes)) ...)
        # where each arm's result IS $result
        elif head.name == 'match' and len(expr) >= 3:
            for clause in expr.items[2:]:
                if isinstance(clause, SList) and len(clause) >= 2:
                    arm_body = clause[-1]
                    self._collect_call_postconditions(arm_body, translator, axioms)

        # Handle cond expressions - recurse into branch bodies
        elif head.name == 'cond':
            for clause in expr.items[1:]:
                if isinstance(clause, SList) and len(clause) >= 2:
                    arm_body = clause[-1]
                    self._collect_call_postconditions(arm_body, translator, axioms)

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

        # Evaluated where the binding is, but this runs long after the body was
        # translated, when every name holds its final version. If the
        # initializer mentions a name a loop or an assignment replaced, that is
        # not necessarily the value the binding was given (issue #116).
        #
        # Conservative in one direction: a binding made *after* the loop should
        # use the post version, and is skipped too. Telling the two apart needs
        # the program point, which this pass does not have.
        if self._mentions_loop_versioned(init_expr, translator):
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

    def _mentions_loop_versioned(self, expr: SExpr, translator: Z3Translator) -> bool:
        """True if `expr` names a variable some loop reassigned."""
        if isinstance(expr, Symbol):
            return translator.is_loop_versioned(expr.name)
        if isinstance(expr, SList):
            return any(self._mentions_loop_versioned(item, translator)
                       for item in expr.items)
        return False

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

        # The constant the name held before any loop reassigned it: this is the
        # binding's *initial* value, and after a loop `variables` holds the
        # version the loop produced instead (issue #116).
        var_z3 = translator.initial_variable(var_name)
        if var_z3 is None:
            return

        # This runs long after the body was translated, so re-translating the
        # initializer reads whatever version of each name is current. If it
        # mentions one a loop reassigned, the value it produces is not the one
        # the binding was given.
        if self._mentions_loop_versioned(expr, translator):
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

    def _desugar_callback_iterations(self, expr: SExpr) -> SExpr:
        """Rewrite callback-taking function calls as for-each loops (verifier-internal).

        Transforms:
            (fn-with-callback arg1 ... (fn ((var Type)) body))
        Into:
            (for-each (var (fn-with-callback arg1 ...)) body)

        The virtual collection (fn-with-callback arg1 ...) gets its @callback-assume
        axioms rewritten as collection postconditions by axiom generation.
        """
        if not isinstance(expr, SList) or len(expr) < 1:
            return expr

        # Recursively desugar children first
        new_items = [self._desugar_callback_iterations(item) for item in expr.items]

        head = new_items[0]
        if isinstance(head, Symbol):
            # Check if this is a call to a function with @callback-assume
            sig = self.imported_defs.functions.get(head.name)
            if sig and sig.callback_assumptions:
                # Find the callback argument (last arg that is a lambda)
                last_arg = new_items[-1] if len(new_items) > 1 else None
                if (isinstance(last_arg, SList) and len(last_arg) >= 3 and
                    isinstance(last_arg[0], Symbol) and last_arg[0].name == 'fn'):
                    # Extract lambda params and body
                    lambda_params = last_arg[1]  # ((var Type))
                    lambda_body = last_arg.items[2:]  # body expressions

                    # Get the loop variable from lambda params
                    loop_var = None
                    if isinstance(lambda_params, SList) and len(lambda_params) >= 1:
                        first_param = lambda_params[0]
                        if isinstance(first_param, SList) and len(first_param) >= 1:
                            if isinstance(first_param[0], Symbol):
                                loop_var = first_param[0].name
                        elif isinstance(first_param, Symbol):
                            loop_var = first_param.name

                    if loop_var:
                        # Build the virtual collection: (fn-name arg1 ... argN-1)
                        # (everything except the callback argument)
                        virtual_coll = SList(new_items[:-1])
                        if hasattr(expr, 'line'):
                            virtual_coll.line = expr.line
                            virtual_coll.col = expr.col

                        # Build binding: (var virtual-coll)
                        binding = SList([Symbol(loop_var), virtual_coll])

                        # Build body (wrap in do if multiple exprs)
                        if len(lambda_body) == 1:
                            body = lambda_body[0]
                        else:
                            body = SList([Symbol('for-each')] + list(lambda_body))
                            # Actually wrap in do
                            body = SList([Symbol('do')] + list(lambda_body))

                        # Build for-each: (for-each (var virtual-coll) body)
                        result = SList([Symbol('for-each'), binding, body])
                        if hasattr(expr, 'line'):
                            result.line = expr.line
                            result.col = expr.col
                        return result

        # No desugaring needed, return with recursively processed children
        result = SList(new_items)
        if hasattr(expr, 'line'):
            result.line = expr.line
            result.col = expr.col
        return result

    @staticmethod
    def _z3_exprs_match_ignoring_patterns(a, b) -> bool:
        """Check if two Z3 expressions are structurally equal ignoring :pattern annotations.

        ForAll quantifiers get different :pattern (trigger) hints from the axiom generator
        vs the translator, but the semantic content is identical. This strips :pattern
        from the sexpr representation before comparing.
        """
        def strip_patterns(sexpr: str) -> str:
            result = []
            i = 0
            while i < len(sexpr):
                # Look for :pattern
                if sexpr[i:i+8] == ':pattern':
                    # Skip whitespace before :pattern
                    while result and result[-1] in ' \n\t':
                        result.pop()
                    # Skip :pattern
                    i += 8
                    # Skip whitespace after :pattern
                    while i < len(sexpr) and sexpr[i] in ' \n\t':
                        i += 1
                    # Skip the balanced parenthesized pattern list
                    if i < len(sexpr) and sexpr[i] == '(':
                        depth = 1
                        i += 1
                        while i < len(sexpr) and depth > 0:
                            if sexpr[i] == '(':
                                depth += 1
                            elif sexpr[i] == ')':
                                depth -= 1
                            i += 1
                else:
                    result.append(sexpr[i])
                    i += 1
            return ''.join(result)
        return strip_patterns(a.sexpr()) == strip_patterns(b.sexpr())

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

    @staticmethod
    def _contains_quantifier(expr) -> bool:
        """True if `expr` has a ForAll or Exists anywhere inside it."""
        stack = [expr]
        while stack:
            node = stack.pop()
            if z3.is_quantifier(node):
                return True
            if z3.is_app(node):
                stack.extend(node.children())
        return False

    def _axioms_are_contradictory(self, assertions) -> bool:
        """True unless this axiom set is shown satisfiable, so a proof from it holds.

        Showing satisfiability is the expensive direction - Z3 has to produce a
        model, and with quantified sequence axioms it often cannot inside the
        timeout. Answering "cannot tell" with "fine, accept the proof" would
        make the guard optional exactly where it is hardest, so instead: when
        the full set is undecided, retry on the ground fragment. Dropping
        assertions can only make a set easier to satisfy, so a satisfiable
        ground subset is not proof of anything - but it is cheap, and in
        practice it settles.

        Ground-satisfiable-but-quantifier-undecided is where the line falls: the
        proof is accepted, on the grounds that every contradiction seen here has
        been ground (two conflicting claims about one length) and that
        unsatisfiability is the direction Z3 answers quickly. An undecided
        ground fragment gets no such benefit and the proof is withheld.
        """
        assertions = list(assertions)
        solver = z3.Solver()
        solver.set("timeout", self.timeout_ms)
        for a in assertions:
            solver.add(a)
        outcome = solver.check()
        if outcome != z3.unknown:
            return outcome == z3.unsat

        ground = [a for a in assertions if not self._contains_quantifier(a)]
        if len(ground) == len(assertions):
            # Nothing was dropped, so there is no cheaper question left to ask.
            return True
        ground_solver = z3.Solver()
        ground_solver.set("timeout", self.timeout_ms)
        for a in ground:
            ground_solver.add(a)
        # An undecided ground fragment leaves the whole question open, and the
        # guard exists so that an unestablished proof is not reported as one.
        return ground_solver.check() != z3.sat

    def _inconsistent_context_result(
        self, solver, translator, fn_name, fn_form,
        pre_z3, preconditions, invariant_z3, range_field_axioms, assume_z3,
        type_constraint_count, pre_constraint_count,
        assume_constraint_start, assume_constraint_end, body_equality,
        result_length_axioms, constraint_terms,
    ):
        """A result to report when the axioms contradict each other, else None.

        Issue #115. Every contract is discharged by asking whether
        (axioms AND NOT contract) is satisfiable, so if the axioms alone are
        unsatisfiable that answers "no" for any contract and it reports verified
        having proved nothing.

        Only worth asking once a contract has come back proved: a counterexample
        is itself a model of the axioms, so a sat result has already shown them
        consistent.

        Four things can make the context unsat and they are not the same
        problem, so the layers are added one at a time and the first one that
        tips it over names the cause. Three of them are the author's contract;
        only what survives all three is ours.
        """
        if not self._axioms_are_contradictory(solver.assertions()):
            return None

        layer = z3.Solver()
        layer.set("timeout", self.timeout_ms)
        for c in constraint_terms[:type_constraint_count]:
            layer.add(c)

        if layer.check() == z3.unsat:
            # Unsat before any @pre was added: the parameter or result types
            # themselves admit no value, e.g. an empty range (Int 5 .. 3).
            return VerificationResult(
                name=fn_name,
                verified=False,
                status="failed",
                message=(
                    "Parameter or result types admit no value: their constraints "
                    "cannot all hold, so the function can never be called. An "
                    "empty range type such as (Int 5 .. 3) does this."
                ),
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )

        # The assumptions are held back to the end, so that a contradiction
        # they introduce is distinguishable from one already present without
        # them - @assume is trusted, so one that the body refutes is the
        # author's error rather than ours.
        assumption_assertions = (
            list(constraint_terms[assume_constraint_start:assume_constraint_end])
            + list(assume_z3)
        )

        def _is_assumption(assertion) -> bool:
            return any(z3.eq(assertion, a) for a in assumption_assertions)

        # Everything else the main solver holds. Enumerating the kinds of axiom
        # by hand does not work - Phase 3's record fields, Phase 4's union tags,
        # the sequence identities and the rest are added straight to the solver -
        # so take them from the solver itself. Re-adding assertions already in
        # an earlier layer is harmless.
        generated_axioms = [a for a in solver.assertions() if not _is_assumption(a)]

        authored = [
            (
                self._unsatisfiable_precondition_message(preconditions),
                list(constraint_terms[type_constraint_count:pre_constraint_count])
                + list(pre_z3),
            ),
            (
                "Type invariants are contradictory: no value of the parameter "
                "types can satisfy them together with the preconditions, so the "
                "function has no legal input.",
                invariant_z3 + range_field_axioms,
            ),
            (
                "A contract or body expression cannot be well-defined: the side "
                "conditions from translating them cannot all hold. A division by "
                "a zero denominator or a value outside its range type does this.",
                list(constraint_terms[pre_constraint_count:assume_constraint_start])
                + list(constraint_terms[assume_constraint_end:]),
            ),
            (
                "The body cannot produce a value of the declared return type: "
                "what it computes and what the type admits have no overlap. A "
                "literal outside a range return type does this.",
                list(body_equality) + list(result_length_axioms),
            ),
            (
                "Verification context is inconsistent: the axioms generated for this "
                "function contradict each other, so nothing can be proved from them. "
                "This is a verifier defect, not a problem with the contract - please "
                "report it with the function body.",
                generated_axioms,
            ),
            (
                "An assumption contradicts the function: @assume is trusted, so "
                "one that the body or the contract already refutes would "
                "discharge any postcondition. Check it against the body.",
                assumption_assertions,
            ),
        ]
        for message, extra in authored:
            for a in extra:
                layer.add(a)
            outcome = layer.check()
            if outcome == z3.unsat:
                # Only the verifier's own layer is our fault; the rest are the
                # author's, and a contract that cannot hold is a failure.
                ours = message.startswith("Verification context is inconsistent")
                return VerificationResult(
                    name=fn_name,
                    verified=False,
                    status="unknown" if ours else "failed",
                    message=message,
                    location=SourceLocation(self.filename, fn_form.line, fn_form.col)
                )
            if outcome == z3.unknown:
                # This layer may be the culprit. Adding the next one and
                # blaming whichever check happens to come back unsat would name
                # the wrong cause, which is the one thing this loop exists to
                # avoid.
                return VerificationResult(
                    name=fn_name,
                    verified=False,
                    status="unknown",
                    message=(
                        "The axioms for this function contradict each other, but which "
                        "part is responsible could not be determined within the timeout. "
                        "Raise the timeout to get a specific diagnosis."
                    ),
                    location=SourceLocation(self.filename, fn_form.line, fn_form.col)
                )

        # Unreachable in principle - the last layer holds everything the main
        # solver does, and that is unsat by hypothesis - but a layer's check can
        # come back undecided, and saying so beats asserting a cause.
        return VerificationResult(
            name=fn_name,
            verified=False,
            status="unknown",
            message=(
                "Verification context is inconsistent: the axioms generated for this "
                "function contradict each other, so nothing can be proved from them. "
                "This is a verifier defect, not a problem with the contract - please "
                "report it with the function body."
            ),
            location=SourceLocation(self.filename, fn_form.line, fn_form.col)
        )

    def _unsatisfiable_precondition_message(
        self, preconditions: List[Tuple[Optional[str], SExpr]]
    ) -> str:
        """Message for a @pre set that no input can satisfy, naming each one."""
        from slop.parser import pretty_print
        if not preconditions:
            return "Preconditions are unsatisfiable"
        details = []
        for pre_name, pre_expr in preconditions:
            pre_str = pretty_print(pre_expr)
            details.append(f"'{pre_name}': {pre_str}" if pre_name else pre_str)
        if len(details) == 1:
            return f"Precondition is unsatisfiable: {details[0]}"
        return "Preconditions are unsatisfiable:\n" + "\n".join(f"  • {d}" for d in details)

    def _propagate_properties_as_loop_invariants(
        self, fn_body: SExpr, properties: List[Tuple[Optional[str], SExpr]]
    ) -> List[SExpr]:
        """Auto-propagate @property annotations as @loop-invariant assumptions.

        When a function has @property but no explicit @loop-invariant on any loop,
        the property body is used as the loop invariant at every for-each nesting
        level, with $result substituted for the mutable result variable name.

        For example, given:
            (@property soundness (forall (t $result) (exists (dt source) ...)))

        And body:
            (let ((mut result (list-new arena T)))
              (for-each (x items) (list-push result ...))
              result)

        Generates the assumption:
            (forall (t result) (exists (dt source) ...))

        This eliminates the need for manually writing identical @loop-invariant
        annotations at every nesting level.
        """
        # Find the mutable result variable from the return expression
        return_expr = self._get_return_expr(fn_body)
        if not isinstance(return_expr, Symbol):
            return []

        result_var_name = return_expr.name

        # Check that this is actually a mutable variable returned from a let
        # (basic sanity check - the pattern is (let ((mut result ...)) ... result))
        if not self._has_for_each_loop(fn_body):
            return []

        propagated: List[SExpr] = []
        for _, prop_expr in properties:
            # Substitute $result with the actual mutable variable name
            substituted = self._substitute_result_var(prop_expr, result_var_name)
            propagated.append(substituted)

        return propagated

    def _substitute_result_var(self, expr: SExpr, var_name: str) -> SExpr:
        """Substitute $result with var_name in an expression."""
        if isinstance(expr, Symbol):
            if expr.name == '$result':
                return Symbol(var_name, expr.line, expr.col)
            return expr
        if isinstance(expr, SList):
            new_items = [self._substitute_result_var(item, var_name) for item in expr.items]
            return SList(new_items, expr.line, expr.col)
        return expr

    def _has_for_each_loop(self, expr: SExpr) -> bool:
        """Check if expression contains a for-each loop."""
        if isinstance(expr, SList) and len(expr) >= 1:
            head = expr[0]
            if isinstance(head, Symbol) and head.name == 'for-each':
                return True
            for item in expr.items:
                if self._has_for_each_loop(item):
                    return True
        return False

    def _body_has_list_push_to_result(self, fn_body: SExpr) -> bool:
        """Check if function body has list-push to the mutable result variable.

        Finds the result variable from the let body's return expression,
        then checks if any code path contains a list-push targeting it.
        """
        if not is_form(fn_body, 'let') or len(fn_body) < 3:
            return False

        # Find the result variable name from the return expression
        return_expr = self._get_return_expr(fn_body)
        if not isinstance(return_expr, Symbol):
            return False
        result_var = return_expr.name

        # Check if the body contains list-push targeting that variable
        return self._has_list_push_to_var(fn_body.items[2:], result_var)

    def _has_list_push_to_var(self, stmts: list, var_name: str) -> bool:
        """Recursively check if any statement pushes to the named variable."""
        for stmt in stmts:
            if not isinstance(stmt, SList):
                continue
            if is_form(stmt, 'list-push') and len(stmt) >= 2:
                target = stmt[1]
                if isinstance(target, Symbol) and target.name == var_name:
                    return True
            # Recurse into all subforms
            for item in stmt.items:
                if isinstance(item, SList):
                    if self._has_list_push_to_var([item], var_name):
                        return True
        return False

    def _count_list_push_to_result(self, fn_body: SExpr) -> int:
        """Count total number of list-push sites targeting the result variable."""
        if not is_form(fn_body, 'let') or len(fn_body) < 3:
            return 0
        return_expr = self._get_return_expr(fn_body)
        if not isinstance(return_expr, Symbol):
            return 0
        result_var = return_expr.name
        return self._count_push_to_var(fn_body.items[2:], result_var)

    def _count_push_to_var(self, stmts: list, var_name: str) -> int:
        """Recursively count list-push sites targeting the named variable."""
        count = 0
        for stmt in stmts:
            if not isinstance(stmt, SList):
                continue
            if is_form(stmt, 'list-push') and len(stmt) >= 2:
                target = stmt[1]
                if isinstance(target, Symbol) and target.name == var_name:
                    count += 1
            # Recurse into all subforms (except the list-push head itself)
            for item in stmt.items:
                if isinstance(item, SList):
                    count += self._count_push_to_var([item], var_name)
        return count

    def _count_pattern_covered_pushes(self, fn_body: SExpr) -> int:
        """Count push sites that are inside a detected pattern.

        A push is "covered" if it's inside a for-each loop that was detected
        as part of a filter, map, or nested loop pattern. This is a heuristic:
        we count push sites that are inside for-each loops that are direct
        children of the outer let (or inside match-some branches of those).
        """
        if not is_form(fn_body, 'let') or len(fn_body) < 3:
            return 0
        return_expr = self._get_return_expr(fn_body)
        if not isinstance(return_expr, Symbol):
            return 0
        result_var = return_expr.name

        # Count pushes inside for-each loops (the pattern-detected region)
        body_exprs = fn_body.items[2:]
        return self._count_pushes_in_patterns(body_exprs, result_var)

    def _count_pushes_in_patterns(self, stmts: list, result_var: str) -> int:
        """Count push sites inside for-each loops (which patterns would detect).

        Recurses into let, when, do, and match forms to find for-each loops,
        then counts all pushes to result_var inside those loops.
        """
        count = 0
        for stmt in stmts:
            if not isinstance(stmt, SList):
                continue
            if is_form(stmt, 'for-each') and len(stmt) >= 3:
                # Pushes inside for-each are pattern-covered
                count += self._count_push_to_var(stmt.items[2:], result_var)
            elif is_form(stmt, 'match') and len(stmt) >= 3:
                for clause in stmt.items[2:]:
                    if isinstance(clause, SList) and len(clause) >= 2:
                        count += self._count_pushes_in_patterns(clause.items[1:], result_var)
            elif is_form(stmt, 'let') and len(stmt) >= 3:
                count += self._count_pushes_in_patterns(stmt.items[2:], result_var)
            elif is_form(stmt, 'when') and len(stmt) >= 3:
                count += self._count_pushes_in_patterns(stmt.items[2:], result_var)
            elif is_form(stmt, 'do') and len(stmt) >= 2:
                count += self._count_pushes_in_patterns(stmt.items[1:], result_var)
        return count

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
        """Check if expression has a mutable variable bound to list-new that is returned.

        Looks for pattern: (let ((mut VAR (list-new ...))) ... VAR)
        where the final return is the same variable.
        """
        if is_form(expr, 'let') and len(expr) >= 3:
            bindings = expr[1]
            body_exprs = expr.items[2:]

            # Check if final expression is a symbol (potential result variable)
            if body_exprs:
                final_expr = self._get_return_expr(body_exprs[-1])
                if isinstance(final_expr, Symbol) and isinstance(bindings, SList):
                    return_name = final_expr.name

                    # Look for (mut return_name (list-new ...)) binding
                    for binding in bindings.items:
                        if isinstance(binding, SList) and len(binding) >= 3:
                            first = binding[0]
                            if isinstance(first, Symbol) and first.name == 'mut':
                                var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                                init_expr = binding[2]
                                if var_name == return_name and is_form(init_expr, 'list-new'):
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
        """True for an `if` or `cond` with a record-new in at least one branch.

        `cond` counts: it is the same shape, and a function that assembles its
        result differently under three conditions rather than two should not
        lose its field axioms for it.
        """
        if is_form(expr, 'if') and len(expr) >= 3:
            return any(self._is_record_new(branch) for branch in expr.items[2:])
        if is_form(expr, 'cond') and len(expr) >= 2:
            return any(self._is_record_new(clause[-1])
                       for clause in expr.items[1:]
                       if isinstance(clause, SList) and len(clause) >= 2)
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

    def _extract_list_axioms(self, body: SExpr, translator: Z3Translator,
                             all_body_exprs: Optional[List] = None) -> List:
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

        # Find all list-push calls across all body expressions
        # (handles multi-statement bodies where push is in an earlier expression)
        push_calls: List[Tuple[SExpr, SExpr]] = []
        if all_body_exprs and len(all_body_exprs) > 1:
            for expr in all_body_exprs:
                self._find_list_push_calls(expr, push_calls)
        else:
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
                            # A push only raises the lower bound if it is
                            # actually taken: one guarded by a when/if or sitting
                            # in a match arm may not be, and one inside a loop
                            # over an empty collection runs zero times. An
                            # unconditional `length >= 1` here was the same
                            # unsound shape as issue #115.
                            taken = self._unconditional_push_count(body, lst_name)
                            if taken >= 1:
                                axioms.append(length >= taken)

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

            # Fallback: nothing sound to say about this list's length here.
            #
            # This used to introduce a fresh _list_pre_len_N with
            #   pre_len == field_len(lst); post_len == pre_len + 1; post_len >= 1
            # Nothing ever read post_len, and pre_len was fresh, so the three
            # together said only field_len(lst) >= 0 - which the translator
            # already asserts. The length of the *returned* list is derived
            # from its push sites by _result_length_axioms, which is the only
            # place that knows which pushes are conditional or in a loop.
            #
            # A push through an alias, e.g. (list-push (. c items) x), cannot be
            # expressed at all while field_len is a function of the handle: the
            # pushed-to list keeps its identity, so its pre- and post-lengths
            # would have to be two values of one term.
            pass

        # Nothing is asserted here about the length of the returned list.
        #
        # Two axioms used to be, and both were unsound (issue #115):
        #
        #   field_len($result) >= push_count
        #     wrong whenever a push is conditional or inside a loop that may
        #     run zero times, and it contradicted the flat field_len == 0 that
        #     Phase 3.5 derived from the (mut r (list-new ...)) binding.
        #     _result_length_axioms now derives one bound from the push sites.
        #
        #   field_len(field_X($result)) == field_len(push_target) + push_count
        #     emitted when a record field held the pushed-to list. It fired
        #     only when the field value *was* the push target, and in exactly
        #     that case Phase 3 has already asserted
        #     field_X($result) == push_target - so the pair reads X == X + 1.
        #     push mutates the list in place; with field_len a function of the
        #     handle there is no second term to carry the pre-push length.

        return axioms

    def _result_sequence_equality(self, fn_body: SExpr,
                                  translator: Z3Translator) -> List:
        """Equate $result's Seq with the returned local's, when they must agree.

        Under Seq encoding the two get separate constants, so a @loop-invariant
        stated about the local proves nothing about the result unless they are
        tied together.

        Withheld when the body contains an explicit (return ...):
        _get_return_expr only sees the trailing expression, and equating
        $result with it would claim the other exit cannot happen.
        """
        if self._contains_any_form(fn_body, ('return',)):
            return []
        ret_expr = self._get_return_expr(fn_body)
        if not isinstance(ret_expr, Symbol):
            return []
        result_seq = translator.list_seqs.get('$result')
        ret_seq = translator.list_seqs.get(ret_expr.name)
        if result_seq is None or ret_seq is None or z3.eq(result_seq, ret_seq):
            return []
        return [result_seq == ret_seq]

    def _unconditional_push_count(self, body: SExpr, list_name: str) -> int:
        """How many pushes to `list_name` are certain to happen exactly once.

        Sites under a when/if guard or inside a match arm may not run, and
        sites inside a loop run an unknown number of times, so neither
        contributes to a lower bound on the length.
        """
        return sum(
            1 for site in self._collect_push_sites([body], list_name)
            if site.loop_depth == 0 and not site.guard_conditions and not site.conditional
        )

    def _extract_conditional_record_axioms(self, cond_expr: SList, translator: Z3Translator,
                                           fn_body: Optional[SExpr] = None,
                                           param_names: Optional[Set[str]] = None,
                                           reached_guard=None) -> List:
        """Axioms for a conditional whose branches build or pass along a record.

        Each branch contributes its own facts under its own guard. A branch that
        constructs a record goes through _extract_record_field_axioms, so it
        picks up everything a record-new says - the length of a `list-new`
        field, a nested record, a string length, a union tag - rather than only
        the field-equals-value line this used to reimplement (issue #70). A
        branch that yields something else carries that value's fields across
        under the same guard.
        """
        axioms = []
        result_var = translator.variables.get('$result')
        if result_var is None:
            return axioms
        if fn_body is None:
            fn_body = cond_expr

        branches = self._branch_conditions(cond_expr, translator)
        if branches is None:
            return axioms

        # Every constructor about to be described, so a list stored in one of
        # them still counts as read-only; a record built anywhere else is a way
        # to reach the list again.
        result_forms: Tuple[int, ...] = ()
        for _, branch in branches:
            if self._is_record_new(branch):
                result_forms += self._nested_record_forms(self._get_return_expr(branch))
        bindings = self._tail_bindings(fn_body, param_names, result_forms=result_forms)
        # A branch-local name may shadow an enclosing binding, which shares its
        # Z3 constant. Sibling arms do not: their axioms carry mutually
        # exclusive guards.
        enclosing_names = set(param_names or ()) | self._tail_binding_names(fn_body)

        field_names: List[str] = []
        passthrough: List = []

        for guard, branch in branches:
            if self._is_record_new(branch):
                record_new = self._get_return_expr(branch)
                # An arm may bind its own locals before constructing.
                branch_bindings = dict(bindings)
                branch_bindings.update(self._tail_bindings(
                    branch, enclosing_names, stability_body=fn_body,
                    result_forms=result_forms))
                for item in record_new.items[2:]:
                    if isinstance(item, SList) and len(item) >= 2 and isinstance(item[0], Symbol):
                        if item[0].name not in field_names:
                            field_names.append(item[0].name)
                axioms.extend(self._extract_record_field_axioms(
                    record_new, translator, base_accessor=result_var,
                    path_cond=self._conjoin(reached_guard, guard),
                    bindings=branch_bindings))
            else:
                passthrough.append((guard, branch))

        # A branch that yields an existing record: under its guard the result is
        # that value, so the fields the other branches name agree with it.
        for guard, branch in passthrough:
            branch_z3 = translator.translate_expr(branch)
            if branch_z3 is None:
                continue
            for field_name in field_names:
                axioms.append(z3.Implies(
                    self._conjoin(reached_guard, guard),
                    translator._translate_field_for_obj(result_var, field_name)
                    == translator._translate_field_for_obj(branch_z3, field_name)))

        if not (is_form(cond_expr, 'if') and len(cond_expr) >= 4):
            return axioms

        condition = cond_expr[1]
        then_branch = cond_expr[2]
        else_branch = cond_expr[3]
        var_branch = else_branch if self._is_record_new(then_branch) else then_branch

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

    def _aliases_of(self, body: SExpr, name: str) -> List[str]:
        """Names bound directly to `name`, which therefore denote the same list."""
        aliases: List[str] = []

        def walk(node):
            if not isinstance(node, SList):
                return
            if is_form(node, 'let') and len(node) >= 2 and isinstance(node[1], SList):
                for binding in node[1].items:
                    if isinstance(binding, SList) and len(binding) >= 2:
                        value = binding[-1]
                        if isinstance(value, Symbol) and value.name == name:
                            bound = self._binding_name(binding)
                            if bound and bound != name:
                                aliases.append(bound)
            for item in node.items:
                walk(item)

        walk(body)
        return aliases

    def _binding_is_stable(self, body: SExpr, name: str,
                           result_forms: Tuple[int, ...] = (),
                           seen: Optional[Set[str]] = None) -> bool:
        """True if `name` is only read in this body, never changed.

        Following a name back to its initializer is only valid while nothing has
        changed what it holds. `list-push` and `list-pop` mutate the list in
        place, `set!` replaces it outright, and handing it to a function lets
        the callee do either - so only the handful of positions that are known
        to be reads keep a binding resolvable.

        A read is not always harmless. `(let ((a e)) (list-push a it))` mutates
        the same list through another name, so every alias has to be stable too
        - that is what `seen` follows. And storing the list in a record hands
        out another way to reach it: `(list-push (. box xs) it)` never mentions
        `e`. So a record field counts as a read only inside `result_forms`, the
        constructors whose fields are being described here, which nothing in the
        function can reach through afterwards.
        """
        if seen is None:
            seen = set()
        if name in seen:
            return True
        seen.add(name)

        for alias in self._aliases_of(body, name):
            if not self._binding_is_stable(body, alias, result_forms, seen):
                return False

        def walk(node, parent_head, index, in_pair) -> bool:
            if isinstance(node, Symbol):
                if node.name != name:
                    return True
                if parent_head in ('list-len', 'list-get') and index == 1:
                    return True
                if parent_head == 'mut' and index == 1:
                    return True
                # A let binding or a field of a constructor being described
                # here: the name is bound, or read as a value that nothing goes
                # on to reach through.
                if in_pair:
                    return True
                return False

            if not isinstance(node, SList):
                return True

            head = node[0].name if len(node) and isinstance(node[0], Symbol) else None
            # An intermediate record is a way to reach the list again, so only
            # the constructors whose fields are being described count as reads.
            is_result_record = is_form(node, 'record-new') and id(node) in result_forms
            is_let_bindings = parent_head == 'let' and index == 1
            for i, item in enumerate(node.items):
                in_child_pair = (is_result_record and i >= 2) or is_let_bindings
                if in_child_pair and isinstance(item, SList):
                    # A pair's head is a name, not a call, so its children are
                    # walked with no parent head of their own.
                    for j, sub in enumerate(item.items):
                        if not walk(sub, None, j, True):
                            return False
                    continue
                if not walk(item, head, i, False):
                    return False
            return True

        return walk(body, None, -1, False)

    def _nested_record_forms(self, expr: SExpr) -> Tuple[int, ...]:
        """Every record-new inside `expr`, itself included.

        A constructor nested in the one being returned is part of the same
        value: it is built inline and nothing in the function can reach through
        it afterwards, so a list stored there is as safe as one stored directly.
        """
        forms: List[int] = []

        def walk(node):
            if not isinstance(node, SList) or len(node) < 1:
                return
            if is_form(node, 'record-new'):
                forms.append(id(node))
                # Only the field values, not everything underneath: a
                # constructor handed to a call, as in
                # (ys (touch (record-new Box (xs e)))), is an argument that
                # callee may mutate through, not part of the value returned.
                for item in node.items[2:]:
                    if isinstance(item, SList) and len(item) >= 2:
                        walk(item[-1])
                return
            head = node[0]
            if isinstance(head, Symbol) and head.name in {'some', 'ok', 'error'} and len(node) >= 2:
                walk(node[1])

        walk(expr)
        return tuple(forms)

    def _early_exits(self, body: SExpr, translator: Z3Translator):
        """[(guard, value)] for each `(return v)` that can run before the tail.

        `_get_return_expr` sees only the trailing expression, so a function with
        an early return has exits it does not know about - and `$result == body`
        was asserted for the trailing one unconditionally, which proves whatever
        that form yields regardless of which path ran.

        Recognises a bare `(return v)`, `(when C ... (return v))` and
        `(if C (return v) ...)` among the statements leading up to the tail.

        Runs before the body is translated, so a guard reads the versions in
        scope at the top - which is what a guard before the first loop means.
        A guard naming a `let`-bound local has nothing to read yet and becomes
        an unconstrained Bool, which leaves that exit looking possible when it
        may not be; the conservative direction, and the price of not having
        program points here.
        Guards are cumulative: a later exit only runs if the earlier tests all
        failed. Returns None if a `return` turns up in a shape this cannot
        guard, which tells the caller to withhold rather than guess.
        """
        exits: List = []
        earlier: List = []
        failed = False
        # Guards are read as they stood at the top of the body. That is what a
        # guard before the first loop or assignment means; past one, the name it
        # tests may have changed and there is no program point here to say
        # which version it meant, so the whole modelling is given up.
        reassigned = False

        def returned_value(stmts):
            """The value a statement list returns directly, if that is all of it.

            `(when c (if d (return 1) 0) (return 2))` returns 1 when d holds, so
            taking the direct `(return 2)` as the whole story would model the
            wrong value for part of the path. A nested return anywhere means the
            shape is not one this can guard.
            """
            direct = None
            found = False
            for stmt in stmts:
                if is_form(stmt, 'return'):
                    if found:
                        return None, False
                    direct = stmt[1] if len(stmt) >= 2 else None
                    found = True
                    continue
                if self._contains_any_form(stmt, ('return',)):
                    return None, False
            return direct, found

        def note(guard_term, value, guard_expr):
            nonlocal failed
            if reassigned and self._mentions_loop_versioned(guard_expr, translator):
                failed = True
                return
            guard = z3.And(guard_term, *[z3.Not(t) for t in earlier]) if earlier else guard_term
            exits.append((guard, value, guard_expr))
            earlier.append(guard_term)

        def scan(stmts):
            nonlocal failed, reassigned
            for stmt in stmts:
                if not isinstance(stmt, SList):
                    continue
                if (is_form(stmt, 'while') or is_form(stmt, 'for-each')
                        or is_form(stmt, 'set!')):
                    reassigned = True
                    # A return inside a loop or an assigned value still has no
                    # single condition to negate.
                    if self._contains_any_form(stmt, ('return',)):
                        failed = True
                        return
                    continue
                if is_form(stmt, 'return'):
                    note(z3.BoolVal(True), stmt[1] if len(stmt) >= 2 else None, stmt)
                    return
                if is_form(stmt, 'when') and len(stmt) >= 3:
                    value, found = returned_value(stmt.items[2:])
                    if found:
                        note(self._condition_term(stmt[1], translator), value, stmt[1])
                        continue
                elif is_form(stmt, 'if') and len(stmt) >= 3:
                    then_value, then_found = returned_value([stmt[2]])
                    if then_found:
                        note(self._condition_term(stmt[1], translator), then_value, stmt[1])
                        if len(stmt) >= 4 and not self._contains_any_form(stmt[3], ('return',)):
                            continue
                        if len(stmt) < 4:
                            continue
                if self._contains_any_form(stmt, ('return',)):
                    failed = True
                    return

        node = body
        while True:
            if is_form(node, 'let') and len(node) >= 3:
                # A binding initializer can return too, and there is no obvious
                # guard for one that does.
                if self._contains_any_form(node[1], ('return',)):
                    return None
                scan(node.items[2:-1])
                node = node.items[-1]
                if failed:
                    return None
            elif is_form(node, 'do') and len(node) >= 2:
                scan(node.items[1:-1])
                node = node.items[-1]
            else:
                break
            if failed:
                return None
        if failed:
            return None
        if self._contains_any_form(node, ('return',)):
            return None
        return exits

    def _tail_binding_names(self, body: SExpr) -> Set[str]:
        """Every name bound along the tail of `body`, kept or not."""
        names: Set[str] = set()
        node = body
        while True:
            if is_form(node, 'let') and len(node) >= 3:
                if isinstance(node[1], SList):
                    for binding in node[1].items:
                        if isinstance(binding, SList) and len(binding) >= 2:
                            name = self._binding_name(binding)
                            if name:
                                names.add(name)
                node = node.items[-1]
            elif is_form(node, 'do') and len(node) >= 2:
                node = node.items[-1]
            else:
                return names

    def _tail_bindings(self, body: SExpr,
                       param_names: Optional[Set[str]] = None,
                       stability_body: Optional[SExpr] = None,
                       result_forms: Tuple[int, ...] = ()) -> Dict[str, Tuple[SExpr, Dict]]:
        """The `let` bindings in scope where the body yields its value.

        Follows the tail - the last form of each nested do/let - so a field
        written as `(xs e)` can be resolved back to what `e` was bound to. Each
        entry carries the environment as it stood at its own binding, because a
        later `let` may rebind a name an earlier initializer referred to: with
        one flattened map, `(let ((x zs)) (let ((y x)) (let ((x (list-new ...)))`
        would resolve `y` to the inner empty list rather than to `zs`.

        A name that anything mutates is dropped rather than recorded, as is one
        that shadows another binding or a parameter. `param_names` carries those
        names - for a branch it also carries whatever the enclosing scopes bind,
        since the translator shares one constant with them. Sibling branches are
        not enclosing scopes: their facts are guarded by mutually exclusive
        conditions and cannot reach each other.
        """
        if param_names is None:
            param_names = set()
        if stability_body is None:
            stability_body = body
        bindings: Dict[str, Tuple[SExpr, Dict]] = {}
        # The translator gives every binding of a name one Z3 constant, so a
        # fact derived from one initializer would be asserted about the other
        # value too. That only matters for bindings whose scopes overlap: one
        # further down this same tail, or a parameter. Two disjoint `let`s in a
        # `do`, like two sibling branches, cannot see each other.
        seen: Set[str] = set()
        dropped: Set[str] = set()
        node = body
        while True:
            if is_form(node, 'let') and len(node) >= 3:
                if isinstance(node[1], SList):
                    for binding in node[1].items:
                        if not (isinstance(binding, SList) and len(binding) >= 2):
                            continue
                        name = self._binding_name(binding)
                        if not name or name in dropped:
                            continue
                        if name in seen or name in param_names:
                            dropped.add(name)
                            bindings.pop(name, None)
                            continue
                        seen.add(name)
                        if not self._binding_is_stable(stability_body, name, result_forms):
                            dropped.add(name)
                            bindings.pop(name, None)
                            continue
                        bindings[name] = (binding[-1], dict(bindings))
                node = node.items[-1]
            elif is_form(node, 'do') and len(node) >= 2:
                node = node.items[-1]
            else:
                return bindings

    def _resolve_binding(self, expr: SExpr, bindings: Dict[str, Tuple[SExpr, Dict]]) -> SExpr:
        """Follow a symbol through the bindings in scope, to its initializer.

        Each step continues in the environment that binding was made in, so a
        name rebound later does not reach back into an earlier initializer.
        """
        seen = set()
        node, env = expr, bindings
        while isinstance(node, Symbol) and node.name in env and node.name not in seen:
            seen.add(node.name)
            node, env = env[node.name]
        return node

    def _condition_term(self, cond_expr: SExpr, translator: Z3Translator):
        """A Bool term for a branch condition, opaque or not.

        An `if` on a function call translates to an Int, and refusing to model
        the branch at all then loses every fact that holds in *both* arms -
        which is the usual reason to write one. A fresh Bool keeps the branch
        structure without claiming to know which way the test goes.
        """
        translated = translator.translate_expr(cond_expr)
        if translated is not None and translated.sort() == z3.BoolSort():
            return translated
        # FreshBool rather than a name of our own choosing: `_path_1` is a legal
        # SLOP identifier, and colliding with a parameter of that name would tie
        # the branch to an unrelated input.
        return z3.FreshBool('_path')

    def _branch_conditions(self, expr: SExpr, translator: Z3Translator):
        """[(guard, branch)] for an `if` or `cond`, or None if it is neither.

        A `cond` clause runs when its own test holds *and* no earlier one did,
        so each guard carries the negation of the tests above it. Taking the
        test alone would claim a later clause runs when an earlier one already
        matched.
        """
        if is_form(expr, 'if') and len(expr) >= 3:
            guard = self._condition_term(expr[1], translator)
            branches = [(guard, expr[2])]
            if len(expr) >= 4:
                branches.append((z3.Not(guard), expr[3]))
            return branches

        if is_form(expr, 'cond') and len(expr) >= 2:
            branches = []
            earlier: List = []
            for clause in expr.items[1:]:
                if not isinstance(clause, SList) or len(clause) < 2:
                    return None
                test = clause[0]
                body = clause[-1]
                if isinstance(test, Symbol) and test.name == 'else':
                    guard = z3.And(*[z3.Not(t) for t in earlier]) if earlier else z3.BoolVal(True)
                    branches.append((guard, body))
                    break
                term = self._condition_term(test, translator)
                guard = z3.And(term, *[z3.Not(t) for t in earlier]) if earlier else term
                branches.append((guard, body))
                earlier.append(term)
            return branches or None

        return None

    @staticmethod
    def _conjoin(path_cond, guard):
        """path_cond AND guard, with None standing for "no condition"."""
        if path_cond is None:
            return guard
        if guard is None:
            return path_cond
        return z3.And(path_cond, guard)

    def _record_value_axioms(self, field_func, value: SExpr, translator: Z3Translator,
                             bindings: Dict[str, Tuple[SExpr, Dict]], path_cond) -> List:
        """What is known about a record field, from the shape of its value.

        Recurses through `if`/`cond` in the value itself, conjoining each
        branch's guard, so `(xs (if c (list-new ...) (list-new ...)))` still
        yields a length for both arms. A symbol is followed to what it was bound
        to, which is what makes `(xs e)` work when `e` is a local empty list.
        """
        # Resolve first: a field written as `(xs e)` where `e` was bound to an
        # `if` is still a branch, and dispatching on the unresolved symbol would
        # miss it.
        resolved = self._resolve_binding(value, bindings)

        branches = self._branch_conditions(resolved, translator)
        if branches is not None:
            axioms = []
            for guard, branch in branches:
                axioms.extend(self._record_value_axioms(
                    field_func, branch, translator, bindings,
                    self._conjoin(path_cond, guard)))
            return axioms

        axioms = []

        def add(axiom):
            axioms.append(axiom if path_cond is None else z3.Implies(path_cond, axiom))

        # A freshly created list is empty. Reaching it through a binding counts:
        # a syntactic test for (list-new ...) misses (xs e), and that shape is
        # not rare.
        if is_form(resolved, 'list-new'):
            add(self._length_accessor(translator)(field_func) == z3.IntVal(0))

        if is_form(resolved, 'record-new'):
            axioms.extend(self._extract_record_field_axioms(
                resolved, translator, base_accessor=field_func,
                path_cond=path_cond, bindings=bindings))

        if isinstance(resolved, String):
            str_len_func_name = "string_len"
            if str_len_func_name not in translator.variables:
                str_len_func = z3.Function(str_len_func_name, z3.IntSort(), z3.IntSort())
                translator.variables[str_len_func_name] = str_len_func
            else:
                str_len_func = translator.variables[str_len_func_name]
            add(str_len_func(field_func) == z3.IntVal(len(resolved.value)))

        # Option/Result constructors: tag, and payload where there is one.
        if isinstance(resolved, SList) and len(resolved) >= 1:
            head = resolved[0]
            if isinstance(head, Symbol) and head.name in {'some', 'none', 'ok', 'error'}:
                constructor = head.name
                # Tag index mapping (matches translator.py lines 54-92)
                tag_idx = {'none': 0, 'some': 1, 'ok': 0, 'error': 1}.get(constructor, 0)
                if "union_tag" not in translator.variables:
                    tag_func = z3.Function("union_tag", z3.IntSort(), z3.IntSort())
                    translator.variables["union_tag"] = tag_func
                else:
                    tag_func = translator.variables["union_tag"]
                add(tag_func(field_func) == z3.IntVal(tag_idx))

                if len(resolved) >= 2 and constructor != 'none':
                    payload = translator.translate_expr(resolved[1])
                    if payload is not None:
                        payload_func_name = f"union_payload_{constructor}"
                        if payload_func_name not in translator.variables:
                            payload_func = z3.Function(
                                payload_func_name, z3.IntSort(), z3.IntSort())
                            translator.variables[payload_func_name] = payload_func
                        else:
                            payload_func = translator.variables[payload_func_name]
                        add(payload_func(field_func) == payload)

                        if is_form(resolved[1], 'record-new'):
                            axioms.extend(self._extract_record_field_axioms(
                                resolved[1], translator,
                                base_accessor=payload_func(field_func),
                                path_cond=path_cond, bindings=bindings))
        return axioms

    @staticmethod
    def _length_accessor(translator: Z3Translator):
        """The field_len function, created if this is its first use."""
        func = translator.variables.get("field_len")
        if func is None:
            func = z3.Function("field_len", z3.IntSort(), z3.IntSort())
            translator.variables["field_len"] = func
        return func

    def _extract_record_field_axioms(self, record_new: SList, translator: Z3Translator,
                                      base_accessor: Optional[z3.ExprRef] = None,
                                      path_cond=None,
                                      bindings: Optional[Dict[str, Tuple[SExpr, Dict]]] = None) -> List:
        """Axioms for each field of a record-new: its value, and what that implies.

        `path_cond` guards every axiom, for a record built on one branch of a
        conditional. `bindings` are the let bindings in scope, used to follow a
        field value written as a local name.

        Args:
            record_new: The record-new expression
            translator: The Z3 translator
            base_accessor: The Z3 accessor for the base object (default: $result)
            path_cond: Bool term this record is conditional on, or None
            bindings: let bindings in scope at the record-new
        """
        axioms = []
        if base_accessor is None:
            base_accessor = translator.variables.get('$result')
        if base_accessor is None:
            return axioms
        if bindings is None:
            bindings = {}

        # record-new Type (field1 val1) (field2 val2) ...
        for item in record_new.items[2:]:  # Skip 'record-new' and Type
            if isinstance(item, SList) and len(item) >= 2:
                field_name = item[0].name if isinstance(item[0], Symbol) else None
                if not field_name:
                    continue
                field_func = translator._translate_field_for_obj(base_accessor, field_name)
                field_value = translator.translate_expr(item[1])
                if field_value is not None:
                    equality = field_func == field_value
                    axioms.append(equality if path_cond is None
                                  else z3.Implies(path_cond, equality))
                axioms.extend(self._record_value_axioms(
                    field_func, item[1], translator, bindings, path_cond))
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
        all_body_exprs: List[SExpr] = []  # All body expressions (for multi-statement bodies)

        # Annotation forms to skip when looking for body
        annotation_forms = {'@intent', '@spec', '@pre', '@post', '@assume', '@pure',
                           '@alloc', '@example', '@deprecated', '@property',
                           '@generation-mode', '@requires', '@callback-assume'}
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
                all_body_exprs.append(item)
            elif isinstance(item, Symbol):
                # Skip keyword properties like :c-name
                if item.name.startswith(':'):
                    skip_next_string = True  # The next String is a property value
                    continue
                # Simple expression as body (e.g., variable reference)
                fn_body = item
                all_body_exprs.append(item)
                skip_next_string = False
            elif isinstance(item, Number):
                # Simple numeric expression as body
                fn_body = item
                all_body_exprs.append(item)
                skip_next_string = False
            elif isinstance(item, String):
                # Skip string values after :keyword (property values)
                # But allow standalone String as function body
                if skip_next_string:
                    skip_next_string = False
                    continue
                fn_body = item
                all_body_exprs.append(item)

        # Desugar callback-taking function calls to for-each loops (verifier-internal)
        if fn_body is not None:
            fn_body = self._desugar_callback_iterations(fn_body)

        # Extract loop invariants from function body and treat them as assumptions
        # @loop-invariant provides axioms that help verify loops
        if fn_body is not None:
            loop_invariants = self._extract_loop_invariants(fn_body)
            if loop_invariants:
                assumptions.extend(loop_invariants)
            elif properties:
                # Auto-propagate @property as @loop-invariant when no explicit
                # invariants exist. The @property body (with $result substituted
                # for the mutable result variable) serves as the invariant at
                # every loop nesting level.
                propagated = self._propagate_properties_as_loop_invariants(
                    fn_body, properties
                )
                assumptions.extend(propagated)

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
        declared_param_names: Set[str] = set()
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
                if param_name:
                    declared_param_names.add(param_name)
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

        # Everything in translator.constraints up to here comes from declaring
        # the parameters and $result. Each later phase appends its own side
        # conditions - a division adds a non-zero denominator, a range type adds
        # its bounds - so the diagnosis below can only attribute a contradiction
        # correctly if it knows where each phase's constraints begin.
        type_constraint_count = len(translator.constraints)

        # Translate preconditions
        pre_z3: List[z3.BoolRef] = []
        failed_pres: List[Tuple[Optional[str], SExpr]] = []
        for pre_name, pre_expr in preconditions:
            z3_pre = translator.translate_expr(pre_expr)
            if z3_pre is not None:
                pre_z3.append(self._ensure_bool(z3_pre))
            else:
                failed_pres.append((pre_name, pre_expr))

        pre_constraint_count = len(translator.constraints)

        # Translate function body BEFORE assumptions
        # This is important because @loop-invariant may reference local variables
        # from let bindings, which are declared during body translation

        body_z3: Optional[z3.ExprRef] = None
        body_constraint_start = len(translator.constraints)
        if fn_body is not None:
            # Which loops run whenever the body does. Without this every loop is
            # taken as conditional and contributes no facts. The last form is
            # fn_body rather than all_body_exprs[-1]: the same form, but
            # _desugar_callback_iterations rebuilt it, and this is keyed on
            # node identity.
            for form in (list(all_body_exprs[:-1]) + [fn_body]
                         if all_body_exprs else [fn_body]):
                translator.note_body(form)
        if fn_body is not None and postconditions:
            body_z3 = translator.translate_expr(fn_body)
        body_constraint_end = len(translator.constraints)

        # Postconditions are translated after the body, not before it: a @post
        # speaks about the state the function ends in, so a mutable parameter
        # in one means the value it was left with. @pre keeps the versions from
        # before the body, which is what it is about.
        # Translate postconditions
        post_z3: List[z3.BoolRef] = []
        failed_posts: List[SExpr] = []
        for post in postconditions:
            z3_post = translator.translate_expr(post)
            if z3_post is not None:
                post_z3.append(self._ensure_bool(z3_post))
            else:
                failed_posts.append(post)


        # _get_return_expr picks the trailing form. An explicit (return ...)
        # elsewhere is another exit, and what it yields is just as much $result,
        # so nothing the trailing constructor says describes the result alone.
        # A multi-form body keeps only its last expression in fn_body, so the
        # earlier forms have to be looked at too - both for that check and for
        # the bindings a constructor's fields may refer to.
        # The last element is fn_body rather than all_body_exprs[-1]: those are
        # the same form, but fn_body has been through
        # _desugar_callback_iterations and the other has not, and the two trees
        # share no nodes. Anything keyed on node identity - which constructor
        # is the returned one - has to see the same tree it was taken from.
        combined_body = fn_body
        if fn_body is not None and all_body_exprs and len(all_body_exprs) > 1:
            combined_body = SList(
                [Symbol('do')] + list(all_body_exprs[:-1]) + [fn_body],
                fn_body.line, fn_body.col)
        # Exits other than the trailing form. `reached` is the condition under
        # which control actually gets there; None means it always does, and a
        # `return` in a shape _early_exits cannot guard leaves early_exits None,
        # in which case nothing is claimed about the result at all.
        with translator.initial_versions():
            early_exits = (self._early_exits(combined_body, translator)
                           if combined_body is not None else [])
        body_has_one_exit = early_exits is not None
        reached_guard = None
        if early_exits:
            reached_guard = z3.And(*[z3.Not(guard) for guard, _, _ in early_exits])

            # If we can translate the body, constrain $result to equal it
            # This enables path-sensitive reasoning through conditionals

        # Translate assumptions (trusted axioms) - AFTER body so local vars are declared
        assume_constraint_start = len(translator.constraints)
        assume_z3: List[z3.BoolRef] = []
        failed_assumes: List[SExpr] = []
        for assume in assumptions:
            z3_assume = translator.translate_expr(assume)
            if z3_assume is not None:
                assume_z3.append(self._ensure_bool(z3_assume))
            else:
                failed_assumes.append(assume)
        assume_constraint_end = len(translator.constraints)

        # Translate properties (universal assertions)
        # properties is List[Tuple[Optional[str], SExpr]] - (name, expr) tuples
        prop_z3: List[z3.BoolRef] = []
        failed_props: List[Tuple[Optional[str], SExpr]] = []
        for prop_name, prop_expr in properties:
            z3_prop = translator.translate_expr(prop_expr)
            if z3_prop is not None:
                prop_z3.append(self._ensure_bool(z3_prop))
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
                return VerificationResult(
                    name=fn_name,
                    verified=False,
                    status="failed",
                    message=self._unsatisfiable_precondition_message(preconditions),
                    location=SourceLocation(self.filename, fn_form.line, fn_form.col)
                )
            return VerificationResult(
                name=fn_name,
                verified=True,
                status="verified",
                message="Preconditions are satisfiable",
                location=SourceLocation(self.filename, fn_form.line, fn_form.col)
            )


        # Contracts have been translated by now - a @loop-invariant is about the
        # value the loop leaves behind, so it wants the final version. The
        # pattern phases below re-translate expressions from anywhere in the
        # body instead, where a name with more than one version has no single
        # value to give, so from here it stops answering.
        translator.freeze_versions()

        # The tail's own side conditions - a non-zero divisor, a string length -
        # only hold because the tail ran. An early return bypasses it, so they
        # travel under the same guard as everything else derived from it.
        constraint_terms = list(translator.constraints)
        if reached_guard is not None:
            for i in range(body_constraint_start, min(body_constraint_end,
                                                      len(constraint_terms))):
                constraint_terms[i] = z3.Implies(reached_guard, constraint_terms[i])

        # Check: can we satisfy preconditions but violate postconditions?
        # If (pre AND NOT post) is SAT, then contract can be violated
        solver = z3.Solver()
        solver.set("timeout", self.timeout_ms)

        # Add type constraints
        for c in constraint_terms:
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
        invariant_z3: List[z3.BoolRef] = []
        for param_name, inv_expr in param_invariants:
            inv_z3 = translator.translate_expr(inv_expr)
            if inv_z3 is not None:
                inv_bool = self._ensure_bool(inv_z3)
                solver.add(inv_bool)
                invariant_z3.append(inv_bool)

        # Phase 1b: Add range type axioms for record fields
        # For record types with range-typed fields like (inferred-count (Int 0 ..)),
        # add universal axioms: ForAll x: field_inferred_count(x) >= 0
        range_field_axioms = self._extract_record_field_range_axioms(translator)
        for axiom in range_field_axioms:
            solver.add(axiom)


        # Add body constraint for path-sensitive analysis
        # This constrains $result to equal the translated function body
        body_equality: List[z3.BoolRef] = []
        # early_exits is None when the body returns somewhere this cannot guard,
        # or when a guard turned out to name something later reassigned. Either
        # way the trailing form is not the only thing $result can be, so it is
        # not equated with it at all.
        if body_z3 is not None and early_exits is not None:
            result_var = translator.variables.get('$result')
            if result_var is not None:
                # Only on the path that reaches the trailing form. Asserting it
                # unconditionally proved whatever that form yields even for a
                # call that took an earlier (return ...).
                equality = (result_var == body_z3 if reached_guard is None
                            else z3.Implies(reached_guard, result_var == body_z3))
                body_equality.append(equality)
                solver.add(equality)

        # What each early exit yields is $result on its own path.
        if early_exits:
            result_var = translator.variables.get('$result')
            if result_var is not None:
                for guard, value, _ in early_exits:
                    if value is None:
                        continue
                    # Translating a value can append side conditions - a
                    # non-zero allocation, a non-zero divisor, a string's length
                    # - and everything in translator.constraints was copied to
                    # the solver before this point, so the new ones have to be
                    # carried over. Under this exit's guard, though: they hold
                    # because this path ran, and `(when flag (return (/ n n)))`
                    # would otherwise assert n != 0 for the path that did not.
                    before = len(translator.constraints)
                    value_z3 = translator.translate_expr(value)
                    for constraint in translator.constraints[before:]:
                        guarded_constraint = z3.Implies(guard, constraint)
                        solver.add(guarded_constraint)
                        # constraint_terms is what the inconsistency diagnosis
                        # replays; a condition only the solver knows about would
                        # come out as a verifier defect.
                        constraint_terms.append(guarded_constraint)
                    if value_z3 is None or value_z3.sort() != result_var.sort():
                        continue
                    exit_equality = z3.Implies(guard, result_var == value_z3)
                    body_equality.append(exit_equality)
                    solver.add(exit_equality)

                    # A record returned early needs its fields too: the
                    # equality alone ties $result to a fresh identifier that
                    # nothing else says anything about.
                    exit_form = self._get_return_expr(value)
                    if is_form(exit_form, 'record-new'):
                        for axiom in self._extract_record_field_axioms(
                                exit_form, translator, base_accessor=result_var,
                                path_cond=guard,
                                bindings=self._tail_bindings(
                                    combined_body, declared_param_names,
                                    result_forms=self._nested_record_forms(exit_form))):
                            solver.add(axiom)

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

        if fn_body is not None and body_has_one_exit and self._is_record_new(fn_body):
            # Get the actual record-new form (may be inside a do block)
            return_expr = self._get_return_expr(fn_body)
            field_axioms = self._extract_record_field_axioms(
                return_expr, translator,
                path_cond=reached_guard,
                bindings=self._tail_bindings(
                    combined_body, declared_param_names,
                    result_forms=self._nested_record_forms(return_expr)))
            for axiom in field_axioms:
                solver.add(axiom)

        # Phase 3.5: Length of a returned list, derived from its push sites.
        result_length_axioms: List[z3.BoolRef] = []
        # This used to assert a flat field_len($result) == 0 whenever the body
        # bound a list with (mut r (list-new ...)), ignoring every push, which
        # contradicted the push-count axiom in Phase 7 - issue #115.
        if fn_body is not None:
            if translator.use_array_encoding and self._is_list_new(fn_body):
                # Array encoding needs the representation to exist; the length
                # claim itself comes from _result_length_axioms below.
                translator._create_list_array('$result')
            # combined_body, not fn_body: a multi-form body keeps only its last
            # expression there, and a push in an earlier form would be
            # invisible to the push scan.
            result_length_axioms = self._result_length_axioms(combined_body, translator)
            for axiom in result_length_axioms:
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

        # Phase 4.8: Union tag axiom from set!-deref-union-new pattern
        # For (set! (deref var) (union-new Type tag payload)) where var is the return value,
        # add: union_tag($result) == tag_index
        # This handles constructors like xml-element, xml-text, etc. that allocate,
        # set via deref, then return the pointer.
        if fn_body is not None:
            return_expr = self._get_return_expr(fn_body)
            if isinstance(return_expr, Symbol):
                union_new_form = self._find_set_deref_union_new(fn_body, return_expr.name)
                if union_new_form is not None:
                    tag_axiom = self._extract_union_tag_axiom(union_new_form, translator)
                    if tag_axiom is not None:
                        solver.add(tag_axiom)

        # Phase 5: Add conditional record-new axioms
        # For (if cond (record-new Type (f1 v1) ...) else), add: cond => field_f1($result) == v1
        # Use _get_return_expr to handle let/do wrappers
        if fn_body is not None and body_has_one_exit:
            return_expr = self._get_return_expr(fn_body)
            if self._is_conditional_with_record_new(return_expr):
                cond_axioms = self._extract_conditional_record_axioms(
                    return_expr, translator, combined_body, declared_param_names,
                    reached_guard)
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
            list_axioms = self._extract_list_axioms(fn_body, translator, all_body_exprs)
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
                # combined_body, not fn_body: an early return in a form before
                # the trailing one is another exit, and this bound is asserted
                # about $result on every path.
                count_axioms = self._generate_count_axioms(
                    count_pattern, translator, combined_body)
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

        # Phase 12b: String operation axioms
        # Add semantic connections between string-concat, starts-with, and string-len.
        # Without these, Z3 treats them as uninterpreted functions with no relationships.
        if fn_body is not None and postconditions:
            string_axioms = self._generate_string_operation_axioms(fn_body, postconditions, translator)
            for axiom in string_axioms:
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

        # Phase 13b: Exists-search pattern axioms
        # Detect (let ((mut found false)) (for-each (v coll) (when pred (set! found true)))
        #   (if found branch-a branch-b))
        # and generate: union_tag($result) == found_tag ↔ ∃v ∈ coll: pred(v)
        exists_search_axioms: List[z3.BoolRef] = []
        if fn_body is not None:
            exists_pattern = self._detect_exists_search_pattern(fn_body)
            if exists_pattern is not None:
                exists_search_axioms = self._generate_exists_search_axioms(exists_pattern, translator)
                for axiom in exists_search_axioms:
                    solver.add(axiom)

        # Phase 13c: Emptiness-universality axioms for nested conditional push
        # Detect nested for-each with conditional push via enum match and generate:
        #   Length($result) == 0 ↔ ForAll v,o: condition(v,o)
        emptiness_axioms: List[z3.BoolRef] = []
        if fn_body is not None:
            cond_push_pattern = self._detect_conditional_push_pattern(fn_body)
            if cond_push_pattern is not None:
                emptiness_axioms = self._generate_emptiness_universality_axioms(
                    cond_push_pattern, translator
                )
                for axiom in emptiness_axioms:
                    solver.add(axiom)

        # Phase 14: List element property invariants (with array encoding)
        # For postconditions like (all-triples-have-predicate $result RDF_TYPE),
        # detect that all pushed elements have the required property and add
        # a universally quantified axiom.
        #
        # Collect pattern axioms to share with property verification
        pattern_axioms: List[z3.BoolRef] = []

        # Include exists-search and emptiness axioms in pattern_axioms
        # so the vacuous truth safety net doesn't override them
        pattern_axioms.extend(exists_search_axioms)
        pattern_axioms.extend(emptiness_axioms)

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

        # Phase 14d: Structural push-site axioms
        # For functions where loop patterns aren't detected (while loops,
        # deeply nested callbacks), analyze push sites directly to generate
        # axioms from constant fields in constructors and guard conditions.
        has_only_structural_axioms = False
        structural_axiom_list: List[z3.BoolRef] = []
        if fn_body is not None and translator.use_seq_encoding:
            if not pattern_axioms and self._body_has_list_push_to_result(fn_body):
                return_expr = self._get_return_expr(fn_body)
                if isinstance(return_expr, Symbol):
                    result_var_name = return_expr.name
                    push_sites = self._collect_push_sites(
                        [fn_body], result_var_name
                    )
                    if push_sites:
                        # Extract function parameter names
                        fn_param_names = []
                        for param in params:
                            if isinstance(param, SList) and len(param) >= 2:
                                first = param[0]
                                if isinstance(first, Symbol) and first.name in ('in', 'out', 'mut'):
                                    if isinstance(param[1], Symbol):
                                        fn_param_names.append(param[1].name)
                                elif isinstance(first, Symbol):
                                    fn_param_names.append(first.name)

                        structural_axiom_list = self._generate_structural_push_axioms(
                            push_sites, translator, fn_param_names
                        )
                        for axiom in structural_axiom_list:
                            solver.add(axiom)
                            pattern_axioms.append(axiom)
                        if structural_axiom_list:
                            has_only_structural_axioms = True

        # Phase 14e: Vacuous truth safety net
        # Detect functions with list-push to result but either:
        # (a) no push axioms generated (result is unconstrained), or
        # (b) push axioms exist but there are extra push sites outside the
        #     detected pattern that the axioms don't model (unsound axiom).
        has_unaxiomatized_pushes = False
        if fn_body is not None and translator.use_seq_encoding:
            if self._body_has_list_push_to_result(fn_body):
                if not pattern_axioms:
                    # Case (a): no axioms at all
                    has_unaxiomatized_pushes = True
                else:
                    # Case (b): check if ALL push sites are inside detected patterns
                    # Count total push sites vs. pattern-covered push sites
                    total_pushes = self._count_list_push_to_result(fn_body)
                    pattern_pushes = self._count_pattern_covered_pushes(fn_body)
                    if total_pushes > pattern_pushes:
                        has_unaxiomatized_pushes = True

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

        # Under Seq encoding the returned local and $result get separate Seq
        # constants, so a fact about one is invisible to the other. The property
        # solver below already equates them; the postcondition solver needs it
        # too, or a @loop-invariant stated about the local proves nothing about
        # the result.
        if fn_body is not None and translator.use_seq_encoding:
            for equality in self._result_sequence_equality(fn_body, translator):
                solver.add(equality)

        # First try all postconditions together (fast path)
        solver.push()
        solver.add(z3.Not(z3.And(*post_z3)))
        result = solver.check()
        solver.pop()

        if result == z3.unsat:
            # Proved - but check the axioms were consistent before believing it.
            inconsistent = self._inconsistent_context_result(
                solver, translator, fn_name, fn_form,
                pre_z3, preconditions, invariant_z3, range_field_axioms, assume_z3,
                type_constraint_count, pre_constraint_count,
                assume_constraint_start, assume_constraint_end, body_equality,
                result_length_axioms, constraint_terms,
            )
            if inconsistent is not None:
                return inconsistent

            # Postconditions always hold when preconditions are met
            # Now verify properties (universal assertions - independent of preconditions)
            if prop_z3:
                from slop.parser import pretty_print
                # Collect all failures instead of returning on first failure
                failed_properties: List[Tuple[Optional[str], str, Dict[str, str]]] = []  # (name, expr_str, counterexample)
                unknown_properties: List[Tuple[Optional[str], str, str]] = []  # (name, expr_str, reason)

                for i, ((prop_name, prop_expr), prop_z3_expr) in enumerate(zip(properties, prop_z3)):
                    prop_solver = z3.Solver()
                    prop_solver.set("timeout", self.timeout_ms)

                    # Add type constraints only (not preconditions)
                    for c in translator.constraints:
                        prop_solver.add(c)

                    # Add assumptions (including loop invariants) as trusted axioms
                    for a in assume_z3:
                        prop_solver.add(a)

                    # Equate $result sequence with the actual return variable's sequence
                    # Loop invariants reference the local variable (e.g., 'result'),
                    # while properties reference '$result' - these are different Z3 seqs
                    if fn_body is not None and translator.use_seq_encoding:
                        for equality in self._result_sequence_equality(fn_body, translator):
                            prop_solver.add(equality)

                    # Add pattern axioms (filter/map/fold axioms derived from loop analysis)
                    # These are needed for properties that reason about collection contents
                    for axiom in pattern_axioms:
                        prop_solver.add(axiom)

                    # Add exists-search axioms (from Phase 13b)
                    for axiom in exists_search_axioms:
                        prop_solver.add(axiom)

                    # Add emptiness-universality axioms (from Phase 13c)
                    # If an axiom structurally matches the property, short-circuit:
                    # the pattern analysis already proves this property.
                    emptiness_verified = False
                    for axiom in emptiness_axioms:
                        prop_solver.add(axiom)
                        # Compare ignoring :pattern annotations (quantifier triggers
                        # differ between axiom and translator but semantics are the same)
                        if self._z3_exprs_match_ignoring_patterns(axiom, prop_z3_expr):
                            emptiness_verified = True

                    # Add axioms for imported equality functions
                    # This allows Z3 to understand that e.g., term-eq(a,b) == (a == b)
                    imported_eq_axioms = self._extract_imported_equality_axioms(translator)
                    for axiom in imported_eq_axioms:
                        prop_solver.add(axiom)

                    # Add universal axioms from imported function postconditions
                    # This enables verifying relational properties that involve multiple
                    # calls to the same function (e.g., filtered vs unfiltered results)
                    imported_postcond_axioms = self._extract_imported_postcondition_axioms(translator)
                    for axiom in imported_postcond_axioms:
                        prop_solver.add(axiom)

                    # Add body constraint to connect $result to function body
                    if body_z3 is not None:
                        result_var = translator.variables.get('$result')
                        if result_var is not None:
                            prop_solver.add(result_var == body_z3)

                    prop_str = pretty_print(prop_expr)

                    # Vacuity guard (issue #115). The property solver carries a
                    # different axiom subset from the postcondition solver, so it
                    # needs its own consistency check.
                    #
                    # Ahead of the emptiness short-circuit below: that path
                    # reports verified without consulting Z3 at all, so a
                    # property matching an emptiness axiom would otherwise be the
                    # one thing that can still pass on a contradictory context.
                    # Everything asserted so far is the axiom set; Not(prop)
                    # goes on next. Kept aside so the consistency check below
                    # can be run on the axioms alone without disturbing the
                    # solver, whose stack the structural-vacuity branch reuses.
                    prop_axioms = list(prop_solver.assertions())


                    if emptiness_verified:
                        if self._axioms_are_contradictory(prop_axioms):
                            unknown_properties.append((prop_name, prop_str,
                                "verification context is inconsistent (verifier defect)"))
                        continue

                    # Check if NOT property is satisfiable
                    prop_solver.add(z3.Not(prop_z3_expr))

                    prop_result = prop_solver.check()

                    if prop_result == z3.unsat:
                        # Asked only of a proof: a sat result is itself a model
                        # of the axioms, so it has already shown them consistent.
                        if self._axioms_are_contradictory(prop_axioms):
                            unknown_properties.append((prop_name, prop_str,
                                "verification context is inconsistent (verifier defect)"))
                            continue

                    if prop_result == z3.sat:
                        model = prop_solver.model()
                        counterexample = {str(decl.name()): str(model[decl])
                                         for decl in model.decls()
                                         if not str(decl.name()).startswith('field_')}
                        failed_properties.append((prop_name, prop_str, counterexample))
                    elif prop_result == z3.unsat and has_unaxiomatized_pushes:
                        # Z3 says "verified" but result was unconstrained — vacuous truth.
                        # Check if this property quantifies over $result (forall over result).
                        prop_str_check = pretty_print(prop_expr)
                        if '$result' in prop_str_check:
                            unknown_properties.append((prop_name, prop_str,
                                "no push axioms for list-push body (vacuous)"))
                    elif prop_result == z3.unsat and has_only_structural_axioms:
                        # Z3 says "verified" with structural push axioms only.
                        # Check for vacuous truth: re-verify with Length($result) > 0.
                        # If the property only holds because the sequence is empty,
                        # it's not actually provable from the structural axioms.
                        prop_str_check = pretty_print(prop_expr)
                        if '$result' in prop_str_check:
                            result_seq = translator.list_seqs.get('$result')
                            if result_seq is not None:
                                prop_solver.push()
                                prop_solver.add(z3.Length(result_seq) > 0)
                                nonempty_result = prop_solver.check()
                                prop_solver.pop()
                                if nonempty_result != z3.unsat:
                                    # Property not provable for non-empty result —
                                    # either fails (sat) or times out (unknown)
                                    unknown_properties.append((prop_name, prop_str,
                                        "structural axioms insufficient (not provable for non-empty result)"))
                    elif prop_result == z3.unknown:
                        reason = prop_solver.reason_unknown()
                        unknown_properties.append((prop_name, prop_str, reason))

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
                    # Check if any are timeouts
                    has_timeout = any(reason == "timeout" for _, _, reason in unknown_properties)
                    status = "timeout" if has_timeout else "unknown"

                    if len(unknown_properties) == 1:
                        prop_name, prop_str, reason = unknown_properties[0]
                        reason_suffix = f" ({reason})" if reason else ""
                        if prop_name:
                            message = f"Could not verify property '{prop_name}'{reason_suffix}: {prop_str}"
                        else:
                            message = f"Could not verify property{reason_suffix}: {prop_str}"
                    else:
                        lines = []
                        for prop_name, prop_str, reason in unknown_properties:
                            reason_suffix = f" ({reason})" if reason else ""
                            if prop_name:
                                lines.append(f"  • '{prop_name}'{reason_suffix}: {prop_str}")
                            else:
                                lines.append(f"  • {prop_str}{reason_suffix}")
                        message = "Could not verify properties:\n" + "\n".join(lines)
                    return VerificationResult(
                        name=fn_name,
                        verified=False,
                        status=status,
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

            # Get counterexample from one more check.
            #
            # The same query said sat above, but this is a fresh solve on a
            # solver that has since learned from other checks, and it can time
            # out where the first did not. Asking an unknown solver for its
            # model raises, which took down the whole file rather than one
            # function - so a failure that cannot be illustrated is reported
            # without an illustration.
            solver.push()
            solver.add(z3.Not(z3.And(*post_z3)))
            counterexample_result = solver.check()
            model = solver.model() if counterexample_result == z3.sat else None
            solver.pop()

            counterexample = {}
            if model is not None:
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
                counterexample=counterexample or None,
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
