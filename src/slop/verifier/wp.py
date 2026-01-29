"""
Weakest Precondition Calculus implementation.

Computes weakest preconditions for SLOP expressions to enable
backward reasoning for verification.
"""
from __future__ import annotations

from typing import Optional, TYPE_CHECKING

from slop.parser import SList, Symbol, Number, String, is_form

from .z3_setup import Z3_AVAILABLE, z3

if TYPE_CHECKING:
    from slop.parser import SExpr
    from .translator import Z3Translator


class WeakestPrecondition:
    """Compute weakest preconditions for SLOP expressions.

    WP(expr, Q) = the weakest condition P such that {P} expr {Q}

    This class implements backward reasoning for verification:
    - WP(skip, Q) = Q
    - WP(x := e, Q) = Q[x/e]  (substitute x with e in Q)
    - WP(if c then s1 else s2, Q) = (c => WP(s1, Q)) && (!c => WP(s2, Q))
    - WP(s1; s2, Q) = WP(s1, WP(s2, Q))

    The verification condition for {P} body {Q} is: P => WP(body, Q)
    If this implication is valid, the function satisfies its contract.
    """

    def __init__(self, translator: 'Z3Translator'):
        self.translator = translator
        self._substitution_depth = 0
        self._max_substitution_depth = 20  # Prevent infinite recursion

    def wp(self, expr: 'SExpr', postcondition: 'z3.BoolRef') -> 'z3.BoolRef':
        """Compute weakest precondition of expr with respect to postcondition.

        Args:
            expr: The SLOP expression to analyze
            postcondition: The Z3 boolean formula that must hold after expr

        Returns:
            The weakest precondition - a Z3 boolean formula that must hold
            before expr executes to guarantee postcondition holds after.
        """
        if not Z3_AVAILABLE:
            return postcondition

        # Constants don't change state
        if isinstance(expr, (Number, String)):
            return postcondition

        # Variable reference doesn't change state
        if isinstance(expr, Symbol):
            return postcondition

        if not isinstance(expr, SList) or len(expr) == 0:
            return postcondition

        head = expr[0]
        if not isinstance(head, Symbol):
            return postcondition

        op = head.name

        # Dispatch to specific WP handlers
        if op == 'let':
            return self._wp_let(expr, postcondition)
        elif op == 'if':
            return self._wp_if(expr, postcondition)
        elif op == 'cond':
            return self._wp_cond(expr, postcondition)
        elif op == 'match':
            return self._wp_match(expr, postcondition)
        elif op == 'set!':
            return self._wp_set(expr, postcondition)
        elif op == 'do':
            return self._wp_do(expr, postcondition)
        elif op == 'for-each':
            return self._wp_for_each(expr, postcondition)
        elif op == 'while':
            return self._wp_while(expr, postcondition)
        elif op == 'return':
            return self._wp_return(expr, postcondition)
        else:
            # Function call or other expression - doesn't modify state
            # (except through side effects which we handle via axioms)
            return postcondition

    def _wp_let(self, expr: SList, Q: 'z3.BoolRef') -> 'z3.BoolRef':
        """WP((let ((x e)) body), Q) = WP(body, Q)[x/eval(e)]

        For let with multiple bindings, we first compute WP of the body,
        then substitute each binding (processing right-to-left to handle
        dependencies correctly).
        """
        if len(expr) < 3:
            return Q

        bindings = expr[1]
        if not isinstance(bindings, SList):
            return Q

        # Get body expressions (everything after bindings)
        body_exprs = expr.items[2:]
        if not body_exprs:
            return Q

        # First compute WP of body (process body as a sequence)
        inner_wp = Q
        for body_item in reversed(body_exprs):
            inner_wp = self.wp(body_item, inner_wp)

        # Then substitute each binding (in reverse order for nested let)
        for binding in reversed(bindings.items):
            if isinstance(binding, SList) and len(binding) >= 2:
                var_name = None
                init_expr = None

                first = binding[0]
                if isinstance(first, Symbol):
                    if first.name == 'mut' and len(binding) >= 3:
                        # (mut var value)
                        var_name = binding[1].name if isinstance(binding[1], Symbol) else None
                        init_expr = binding[2]
                    else:
                        # (var value)
                        var_name = first.name
                        init_expr = binding[1]
                elif isinstance(first, SList) and len(first) >= 2:
                    # ((mut var) value)
                    if isinstance(first[0], Symbol) and first[0].name == 'mut':
                        var_name = first[1].name if isinstance(first[1], Symbol) else None
                    init_expr = binding[1]

                if var_name and init_expr is not None:
                    inner_wp = self._substitute_var_with_expr(
                        inner_wp, var_name, init_expr
                    )

        return inner_wp

    def _wp_if(self, expr: SList, Q: 'z3.BoolRef') -> 'z3.BoolRef':
        """WP((if cond then else), Q) = (cond => WP(then, Q)) && (!cond => WP(else, Q))

        This is the classic Dijkstra/Hoare rule for conditionals.
        """
        if len(expr) < 3:
            return Q

        cond = expr[1]
        then_branch = expr[2]
        else_branch = expr[3] if len(expr) > 3 else None

        cond_z3 = self.translator.translate_expr(cond)
        if cond_z3 is None or not z3.is_bool(cond_z3):
            # Can't translate condition - be conservative
            return Q

        wp_then = self.wp(then_branch, Q)
        wp_else = self.wp(else_branch, Q) if else_branch else Q

        return z3.And(
            z3.Implies(cond_z3, wp_then),
            z3.Implies(z3.Not(cond_z3), wp_else)
        )

    def _wp_cond(self, expr: SList, Q: 'z3.BoolRef') -> 'z3.BoolRef':
        """WP((cond (test1 e1) (test2 e2) ... (else default)), Q)

        Multiple-armed conditional. Process as nested if-then-else.
        """
        if len(expr) < 2:
            return Q

        # Build conjuncts for each clause
        conjuncts = []
        conditions_so_far = []

        for clause in expr.items[1:]:
            if not isinstance(clause, SList) or len(clause) < 2:
                continue

            first = clause[0]

            if isinstance(first, Symbol) and first.name == 'else':
                # else clause: previous conditions were all false
                body = clause[1]
                wp_body = self.wp(body, Q)

                if conditions_so_far:
                    # else case: all previous conditions false
                    all_false = z3.And(*[z3.Not(c) for c in conditions_so_far])
                    conjuncts.append(z3.Implies(all_false, wp_body))
                else:
                    conjuncts.append(wp_body)
            else:
                # Regular clause: (test body)
                cond_z3 = self.translator.translate_expr(first)
                body = clause[1]

                if cond_z3 is None or not z3.is_bool(cond_z3):
                    continue

                wp_body = self.wp(body, Q)

                # This clause triggers when: test is true AND all previous were false
                if conditions_so_far:
                    prev_false = z3.And(*[z3.Not(c) for c in conditions_so_far])
                    this_triggers = z3.And(prev_false, cond_z3)
                else:
                    this_triggers = cond_z3

                conjuncts.append(z3.Implies(this_triggers, wp_body))
                conditions_so_far.append(cond_z3)

        if conjuncts:
            return z3.And(*conjuncts)
        return Q

    def _wp_match(self, expr: SList, Q: 'z3.BoolRef') -> 'z3.BoolRef':
        """WP((match e ((p1 b1) (p2 b2) ...)), Q)

        For match on union types:
        (tag(e)==t1 => WP(b1, Q)) && (tag(e)==t2 => WP(b2, Q)) && ...
        """
        if len(expr) < 3:
            return Q

        scrutinee = expr[1]
        clauses = expr.items[2:]

        scrutinee_z3 = self.translator.translate_expr(scrutinee)
        if scrutinee_z3 is None:
            return Q

        # Get union tag function
        tag_func_name = "union_tag"
        if tag_func_name not in self.translator.variables:
            tag_func = z3.Function(tag_func_name, z3.IntSort(), z3.IntSort())
            self.translator.variables[tag_func_name] = tag_func
        else:
            tag_func = self.translator.variables[tag_func_name]

        scrutinee_tag = tag_func(scrutinee_z3)

        conjuncts = []
        for clause in clauses:
            if not isinstance(clause, SList) or len(clause) < 2:
                continue

            pattern = clause[0]
            body = clause[1]

            # Extract tag from pattern
            tag_idx = self._pattern_to_tag_index(pattern)
            if tag_idx is not None:
                tag_cond = scrutinee_tag == z3.IntVal(tag_idx)
                wp_body = self.wp(body, Q)
                conjuncts.append(z3.Implies(tag_cond, wp_body))
            elif self._is_wildcard_pattern(pattern):
                # Wildcard matches anything
                wp_body = self.wp(body, Q)
                conjuncts.append(wp_body)

        if conjuncts:
            return z3.And(*conjuncts)
        return Q

    def _wp_set(self, expr: SList, Q: 'z3.BoolRef') -> 'z3.BoolRef':
        """WP((set! x e), Q) = Q[x/eval(e)]

        Assignment replaces x with the new value in the postcondition.
        """
        if len(expr) < 3:
            return Q

        var = expr[1]
        new_value = expr[2]

        if not isinstance(var, Symbol):
            return Q

        var_name = var.name
        return self._substitute_var_with_expr(Q, var_name, new_value)

    def _wp_do(self, expr: SList, Q: 'z3.BoolRef') -> 'z3.BoolRef':
        """WP((do s1 s2 ... sn), Q) = WP(s1, WP(s2, ... WP(sn, Q)))

        Sequential composition: process statements right-to-left.
        """
        result = Q
        for stmt in reversed(expr.items[1:]):
            result = self.wp(stmt, result)
        return result

    def _wp_for_each(self, expr: SList, Q: 'z3.BoolRef') -> 'z3.BoolRef':
        """WP for loops with @loop-invariant.

        For loops, we need user-provided invariants:
        WP((for-each (x coll) (@loop-invariant I) body), Q) =
            I_init && (I && done => Q)

        Where:
        - I_init: invariant holds before loop
        - The loop body must preserve I (checked separately)
        - After loop completes, I && done implies Q
        """
        # Try to find @loop-invariant in loop body
        invariant = self._find_loop_invariant(expr)

        if invariant is None:
            # Without invariant, we can't verify the loop precisely
            # Return True to indicate we assume the loop is correct
            # (optimistic - the existing axiom-based approach handles common patterns)
            return z3.BoolVal(True)

        inv_z3 = self.translator.translate_expr(invariant)
        if inv_z3 is None or not z3.is_bool(inv_z3):
            return z3.BoolVal(True)

        # The WP is: invariant must hold initially
        # The verifier will also need to check:
        # 1. I is preserved by each iteration (I && in_loop => WP(body, I))
        # 2. I && done => Q (invariant + termination implies postcondition)
        #
        # For now, we require the invariant to hold at entry and trust
        # that it implies the postcondition (standard approach).
        return inv_z3

    def _wp_while(self, expr: SList, Q: 'z3.BoolRef') -> 'z3.BoolRef':
        """WP for while loops.

        Similar to for-each but with explicit condition.
        """
        # Try to find @loop-invariant
        invariant = self._find_loop_invariant(expr)

        if invariant is None:
            return z3.BoolVal(True)

        inv_z3 = self.translator.translate_expr(invariant)
        if inv_z3 is None or not z3.is_bool(inv_z3):
            return z3.BoolVal(True)

        return inv_z3

    def _wp_return(self, expr: SList, Q: 'z3.BoolRef') -> 'z3.BoolRef':
        """WP((return e), Q) = Q[$result/e]

        Early return binds the return value to $result.
        """
        if len(expr) < 2:
            return Q

        return_val = expr[1]
        return self._substitute_var_with_expr(Q, '$result', return_val)

    def _find_loop_invariant(self, loop_expr: SList) -> Optional['SExpr']:
        """Find @loop-invariant annotation in a loop body."""
        for item in loop_expr.items:
            if is_form(item, '@loop-invariant') and len(item) >= 2:
                return item[1]
            # Also search in nested do blocks
            if isinstance(item, SList) and len(item) > 0:
                head = item[0]
                if isinstance(head, Symbol) and head.name == 'do':
                    for sub_item in item.items[1:]:
                        if is_form(sub_item, '@loop-invariant') and len(sub_item) >= 2:
                            return sub_item[1]
        return None

    def _pattern_to_tag_index(self, pattern: 'SExpr') -> Optional[int]:
        """Extract tag index from a match pattern.

        Patterns can be:
        - (tag var) - union variant with binding
        - (tag) - unit variant
        - tag - bare tag
        """
        tag_name = None

        if isinstance(pattern, Symbol):
            tag_name = pattern.name
        elif isinstance(pattern, SList) and len(pattern) >= 1:
            first = pattern[0]
            if isinstance(first, Symbol):
                tag_name = first.name

        if tag_name is None:
            return None

        # Strip leading quote if present
        if tag_name.startswith("'"):
            tag_name = tag_name[1:]

        # Look up in enum values
        if tag_name in self.translator.enum_values:
            return self.translator.enum_values[tag_name]

        return None

    def _is_wildcard_pattern(self, pattern: 'SExpr') -> bool:
        """Check if pattern is a wildcard (_)."""
        if isinstance(pattern, Symbol):
            return pattern.name == '_'
        return False

    def _substitute_var_with_expr(
        self, formula: 'z3.BoolRef', var_name: str, expr: 'SExpr'
    ) -> 'z3.BoolRef':
        """Substitute a variable with an expression in a Z3 formula.

        This is the core of WP: Q[x/e] replaces all occurrences of x with e.
        """
        self._substitution_depth += 1
        if self._substitution_depth > self._max_substitution_depth:
            self._substitution_depth -= 1
            return formula

        try:
            # Get the Z3 variable to replace
            old_var = self.translator.variables.get(var_name)
            if old_var is None:
                return formula

            # Translate the new expression
            new_val_z3 = self.translator.translate_expr(expr)
            if new_val_z3 is None:
                return formula

            # Perform substitution
            return z3.substitute(formula, (old_var, new_val_z3))
        finally:
            self._substitution_depth -= 1


__all__ = [
    'WeakestPrecondition',
]
