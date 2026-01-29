"""
Range Verifier - Verifies range type safety through operations.

This module provides the RangeVerifier class that checks range type
bounds are preserved through arithmetic operations.
"""
from __future__ import annotations

from typing import List, Optional, TYPE_CHECKING

from slop.parser import SList, Symbol, is_form

from .z3_setup import Z3_AVAILABLE, z3
from .types import MinimalTypeEnv
from .results import VerificationResult

if TYPE_CHECKING:
    from slop.parser import SExpr


class RangeVerifier:
    """Verifies range type safety through operations"""

    def __init__(self, type_env: MinimalTypeEnv, filename: str = "<unknown>", timeout_ms: int = 5000):
        if not Z3_AVAILABLE:
            raise RuntimeError("Z3 is not available")
        self.type_env = type_env
        self.filename = filename
        self.timeout_ms = timeout_ms

    def verify_range_safety(self, ast: List['SExpr']) -> List[VerificationResult]:
        """Verify range safety for all range type operations in AST"""
        results = []

        for form in ast:
            if is_form(form, 'module'):
                for item in form.items[1:]:
                    if is_form(item, 'fn'):
                        results.extend(self._verify_function_ranges(item))
            elif is_form(form, 'fn'):
                results.extend(self._verify_function_ranges(form))

        return results

    def _verify_function_ranges(self, fn_form: SList) -> List[VerificationResult]:
        """Verify range safety within a function"""
        results = []

        fn_name = fn_form[1].name if len(fn_form) > 1 and isinstance(fn_form[1], Symbol) else "unknown"

        # For this basic implementation, we check @pre conditions with range types
        # A full implementation would track all assignments

        # Extract preconditions that involve range comparisons
        for item in fn_form.items[3:]:
            if is_form(item, '@pre') and len(item) > 1:
                pre = item[1]
                # Check if this involves a range comparison that could fail
                result = self._verify_range_condition(fn_name, pre, fn_form)
                if result:
                    results.append(result)

        return results

    def _verify_range_condition(self, fn_name: str, cond: 'SExpr', fn_form: SList) -> Optional[VerificationResult]:
        """Verify a range-related condition"""
        # This is a simplified check - a full implementation would analyze
        # arithmetic through the function body

        if not isinstance(cond, SList) or len(cond) < 3:
            return None

        head = cond[0]
        if not isinstance(head, Symbol):
            return None

        op = head.name
        if op not in ('>=', '<=', '>', '<'):
            return None

        # Check if comparing against a literal that's within expected ranges
        # This is a basic check - full verification would require symbolic execution

        return None  # Placeholder for more sophisticated range verification


__all__ = [
    'RangeVerifier',
]
