"""
Loop invariant inference from function postconditions.

Automatically derives loop invariants by analyzing postconditions of
functions called within loops.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple, TYPE_CHECKING

from slop.parser import SList, Symbol, Number, is_form

if TYPE_CHECKING:
    from slop.parser import SExpr
    from .registry import FunctionRegistry
    from .types import ImportedDefinitions
    from .loop_patterns import LoopContext


@dataclass
class InferredInvariant:
    """A loop invariant automatically inferred from function postconditions.

    Invariants are inferred by analyzing postconditions of functions called
    in set! statements within loops. For example:

    - `{(. $result field) == (. param field)}` -> field preserved
    - `{(. $result field) >= (. param field)}` -> field monotonically increasing
    - `{(list-len (. $result list)) >= ...}` -> list grows or stays same

    These inferred invariants enable automatic verification of loops without
    requiring explicit @loop-invariant annotations.
    """
    variable: str  # The loop variable this invariant applies to
    property_expr: 'SExpr'  # The invariant expression (using variable name, not $result)
    source: str  # Where this was inferred from: "initialization", "preservation", "postcondition"
    confidence: float = 1.0  # Confidence level (1.0 = certain, lower = heuristic)
    original_postcondition: Optional['SExpr'] = None  # The postcondition it was derived from


class InvariantInferencer:
    """Infers loop invariants from function postconditions.

    Analyzes postconditions of functions called within loops to automatically
    derive loop invariants. This enables verification of loops without
    requiring manual @loop-invariant annotations.

    Inference patterns:
    1. Field preservation: (. $result field) == (. param field)
       -> Invariant: field value unchanged through iterations

    2. Monotonic increase: (. $result field) >= (. param field)
       -> Invariant: field monotonically increasing

    3. List growth: (list-len (. $result list)) >= (list-len (. param list))
       -> Invariant: list grows or stays same size

    4. Non-negative: (>= $result 0) or (>= (. $result field) 0)
       -> Invariant: value stays non-negative
    """

    def __init__(self, function_registry: Optional['FunctionRegistry'] = None,
                 imported_defs: Optional['ImportedDefinitions'] = None):
        self.function_registry = function_registry
        self.imported_defs = imported_defs

    def infer_from_loop(self, loop_ctx: 'LoopContext') -> List[InferredInvariant]:
        """Infer invariants for a loop from its set! statements.

        For each self-referential set! in the loop, analyzes the called
        function's postconditions to derive invariants.
        """
        invariants: List[InferredInvariant] = []

        for binding in loop_ctx.set_bindings:
            if not binding.is_self_ref:
                continue

            # Get postconditions for the function being called
            postconditions = self._get_postconditions(binding.fn_name)
            if not postconditions:
                continue

            # Analyze each postcondition for invariant patterns
            for post in postconditions:
                inferred = self._infer_from_postcondition(
                    post, binding.var_name, binding.self_ref_params
                )
                invariants.extend(inferred)

        return invariants

    def _get_postconditions(self, fn_name: str) -> List['SExpr']:
        """Get postconditions for a function from registry or imports."""
        if self.function_registry:
            fn_def = self.function_registry.functions.get(fn_name)
            if fn_def and fn_def.postconditions:
                return fn_def.postconditions

        if self.imported_defs:
            imported_sig = self.imported_defs.functions.get(fn_name)
            if imported_sig and imported_sig.postconditions:
                return imported_sig.postconditions

        return []

    def _infer_from_postcondition(self, post: 'SExpr', var_name: str,
                                   self_ref_params: Dict[str, str]) -> List[InferredInvariant]:
        """Infer invariants from a single postcondition.

        Looks for patterns that relate $result to parameters that received
        the old value of the variable (self-referential parameters).
        """
        invariants: List[InferredInvariant] = []

        # Find which parameter names map to our variable
        param_names = [p for p, v in self_ref_params.items() if v == var_name]
        if not param_names:
            return invariants

        # Pattern 1: Field preservation - (== (. $result field) (. param field))
        preserved = self._check_field_preservation(post, param_names)
        if preserved:
            field_name, _ = preserved
            # Create invariant: the field value is preserved
            invariant_expr = self._make_field_preserved_invariant(var_name, field_name)
            invariants.append(InferredInvariant(
                variable=var_name,
                property_expr=invariant_expr,
                source="preservation",
                confidence=1.0,
                original_postcondition=post
            ))

        # Pattern 2: Monotonic increase - (>= (. $result field) (. param field))
        monotonic = self._check_monotonic_increase(post, param_names)
        if monotonic:
            field_name, _ = monotonic
            # This gives us: field is non-decreasing, but we need initial value
            # For now, just note that it's monotonic (used with initialization)
            pass

        # Pattern 3: Non-negative result - (>= $result 0) or (>= (. $result field) 0)
        nonneg = self._check_nonnegative(post)
        if nonneg:
            invariants.append(InferredInvariant(
                variable=var_name,
                property_expr=nonneg,
                source="postcondition",
                confidence=1.0,
                original_postcondition=post
            ))

        # Pattern 4: List length preservation/growth
        list_pattern = self._check_list_length_pattern(post, param_names)
        if list_pattern:
            invariants.append(InferredInvariant(
                variable=var_name,
                property_expr=list_pattern,
                source="preservation",
                confidence=0.9,
                original_postcondition=post
            ))

        return invariants

    def _check_field_preservation(self, post: 'SExpr',
                                   param_names: List[str]) -> Optional[Tuple[str, str]]:
        """Check if postcondition preserves a field value.

        Looks for: (== (. $result field) (. param field))
        Returns: (field_name, param_name) if found, None otherwise
        """
        if not isinstance(post, SList) or len(post) < 3:
            return None

        head = post[0]
        if not isinstance(head, Symbol) or head.name != '==':
            return None

        lhs, rhs = post[1], post[2]

        # Check if LHS is (. $result field)
        lhs_field = self._extract_result_field(lhs)
        if not lhs_field:
            return None

        # Check if RHS is (. param field) where param is in param_names
        rhs_info = self._extract_param_field(rhs, param_names)
        if not rhs_info:
            return None

        rhs_field, param_name = rhs_info

        # Fields must match
        if lhs_field != rhs_field:
            return None

        return (lhs_field, param_name)

    def _check_monotonic_increase(self, post: 'SExpr',
                                   param_names: List[str]) -> Optional[Tuple[str, str]]:
        """Check if postcondition shows monotonic increase.

        Looks for: (>= (. $result field) (. param field))
        Returns: (field_name, param_name) if found, None otherwise
        """
        if not isinstance(post, SList) or len(post) < 3:
            return None

        head = post[0]
        if not isinstance(head, Symbol) or head.name != '>=':
            return None

        lhs, rhs = post[1], post[2]

        lhs_field = self._extract_result_field(lhs)
        if not lhs_field:
            return None

        rhs_info = self._extract_param_field(rhs, param_names)
        if not rhs_info:
            return None

        rhs_field, param_name = rhs_info

        if lhs_field != rhs_field:
            return None

        return (lhs_field, param_name)

    def _check_nonnegative(self, post: 'SExpr') -> Optional['SExpr']:
        """Check if postcondition asserts non-negativity.

        Looks for: (>= $result 0) or (>= (. $result field) 0)
        Returns: The invariant expression with var substituted, or None
        """
        if not isinstance(post, SList) or len(post) < 3:
            return None

        head = post[0]
        if not isinstance(head, Symbol) or head.name != '>=':
            return None

        lhs, rhs = post[1], post[2]

        # Check RHS is 0
        if not isinstance(rhs, Number) or rhs.value != 0:
            return None

        # Check LHS involves $result
        if isinstance(lhs, Symbol) and lhs.name == '$result':
            return post  # Return as-is, will be substituted later
        elif self._extract_result_field(lhs):
            return post

        return None

    def _check_list_length_pattern(self, post: 'SExpr',
                                    param_names: List[str]) -> Optional['SExpr']:
        """Check for list length preservation/growth patterns.

        Looks for: (>= (list-len (. $result list)) (list-len (. param list)))
        """
        if not isinstance(post, SList) or len(post) < 3:
            return None

        head = post[0]
        if not isinstance(head, Symbol) or head.name != '>=':
            return None

        lhs, rhs = post[1], post[2]

        # Check if LHS is (list-len (. $result field))
        if not is_form(lhs, 'list-len') or len(lhs) < 2:
            return None

        lhs_inner = lhs[1]
        if not self._extract_result_field(lhs_inner):
            return None

        # Check if RHS is (list-len (. param field))
        if not is_form(rhs, 'list-len') or len(rhs) < 2:
            return None

        rhs_inner = rhs[1]
        if not self._extract_param_field(rhs_inner, param_names):
            return None

        return post

    def _extract_result_field(self, expr: 'SExpr') -> Optional[str]:
        """Extract field name from (. $result field) expression."""
        if not isinstance(expr, SList) or len(expr) < 3:
            return None

        head = expr[0]
        if not isinstance(head, Symbol) or head.name != '.':
            return None

        obj = expr[1]
        if not isinstance(obj, Symbol) or obj.name != '$result':
            return None

        field = expr[2]
        if isinstance(field, Symbol):
            return field.name

        return None

    def _extract_param_field(self, expr: 'SExpr',
                              param_names: List[str]) -> Optional[Tuple[str, str]]:
        """Extract (field_name, param_name) from (. param field) expression."""
        if not isinstance(expr, SList) or len(expr) < 3:
            return None

        head = expr[0]
        if not isinstance(head, Symbol) or head.name != '.':
            return None

        obj = expr[1]
        if not isinstance(obj, Symbol) or obj.name not in param_names:
            return None

        field = expr[2]
        if isinstance(field, Symbol):
            return (field.name, obj.name)

        return None

    def _make_field_preserved_invariant(self, var_name: str, field_name: str) -> 'SExpr':
        """Create invariant expression for field preservation.

        Creates: (== (. <var> <field>) (. <var>@0 <field>))
        This says: current field value equals initial field value
        """
        # We'll use __init_<var> to refer to initial value
        init_var = f"__init_{var_name}"
        return SList([
            Symbol('=='),
            SList([Symbol('.'), Symbol(var_name), Symbol(field_name)]),
            SList([Symbol('.'), Symbol(init_var), Symbol(field_name)])
        ])


__all__ = [
    'InferredInvariant',
    'InvariantInferencer',
]
