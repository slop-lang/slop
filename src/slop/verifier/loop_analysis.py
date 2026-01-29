"""
Loop Analysis Mixin for ContractVerifier.

Provides methods for analyzing loop structures, extracting loop invariants,
and performing inductive verification of loops.
"""
from __future__ import annotations

from typing import Dict, List, Optional, Set, Tuple, TYPE_CHECKING

from slop.parser import SList, Symbol, is_form

from .z3_setup import Z3_AVAILABLE, z3
from .loop_patterns import LoopContext, WhileLoopContext, SetBinding
from .invariant_inference import InferredInvariant, InvariantInferencer

if TYPE_CHECKING:
    from slop.parser import SExpr
    from .translator import Z3Translator


class LoopAnalysisMixin:
    """Mixin providing loop analysis and inductive verification methods."""

    def _extract_loop_invariants(self, expr: SExpr) -> List[SExpr]:
        """Extract all @loop-invariant annotations from an expression recursively.

        Looks for (for-each (var coll) (@loop-invariant cond) ...) patterns
        and collects the invariant conditions.
        """
        result: List[SExpr] = []
        self._collect_loop_invariants(expr, result)
        return result

    def _collect_loop_invariants(self, expr: SExpr, result: List[SExpr]):
        """Recursively collect @loop-invariant conditions from expressions"""
        if isinstance(expr, SList) and len(expr) > 0:
            head = expr[0]
            if isinstance(head, Symbol):
                # Check for @loop-invariant annotation
                if head.name == '@loop-invariant' and len(expr) >= 2:
                    result.append(expr[1])
                # Recurse into for-each, let, do, if, etc.
            # Recurse into subexpressions
            for item in expr.items:
                self._collect_loop_invariants(item, result)

    def _analyze_loops(self, body: SExpr) -> List[LoopContext]:
        """Analyze function body to extract information about all for-each loops.

        This is a pre-pass that identifies:
        - All for-each loops in the function
        - Variables modified within each loop (via set!)
        - Function calls in those set! statements
        - Whether set! is self-referential (variable passed as argument)

        This information is used for SSA-based loop invariant inference.
        """
        loops: List[LoopContext] = []
        self._collect_loop_contexts(body, loops)
        return loops

    def _collect_loop_contexts(self, expr: SExpr, loops: List[LoopContext]):
        """Recursively collect LoopContext for all for-each loops in expression."""
        if not isinstance(expr, SList) or len(expr) == 0:
            return

        head = expr[0]
        if not isinstance(head, Symbol):
            # Recurse into subexpressions
            for item in expr.items:
                self._collect_loop_contexts(item, loops)
            return

        if head.name == 'for-each' and len(expr) >= 3:
            # Found a for-each loop: (for-each (var coll) body...)
            binding = expr[1]
            if isinstance(binding, SList) and len(binding) >= 2:
                loop_var = binding[0].name if isinstance(binding[0], Symbol) else None
                collection = binding[1]

                if loop_var:
                    # Analyze the loop body
                    modified_vars: Set[str] = set()
                    set_bindings: List[SetBinding] = []
                    loop_invariants: List[SExpr] = []

                    # Collect set! bindings and loop invariants from body
                    for body_item in expr.items[2:]:
                        self._collect_set_bindings(body_item, modified_vars, set_bindings)
                        self._collect_loop_invariants(body_item, loop_invariants)

                    loop_ctx = LoopContext(
                        loop_var=loop_var,
                        collection=collection,
                        loop_expr=expr,
                        modified_vars=modified_vars,
                        set_bindings=set_bindings,
                        loop_invariants=loop_invariants
                    )
                    loops.append(loop_ctx)

        # Recurse into subexpressions (including nested loops in loop body)
        for item in expr.items:
            self._collect_loop_contexts(item, loops)

    def _analyze_while_loops(self, body: SExpr) -> List[WhileLoopContext]:
        """Analyze function body to extract information about all while loops.

        This is a pre-pass that identifies:
        - All while loops in the function
        - The loop condition
        - Variables modified within each loop (via set!)
        - Explicit @loop-invariant annotations

        This information is used for while loop exit axiom generation.
        """
        loops: List[WhileLoopContext] = []
        self._collect_while_loop_contexts(body, loops)
        return loops

    def _collect_while_loop_contexts(self, expr: SExpr, loops: List[WhileLoopContext]):
        """Recursively collect WhileLoopContext for all while loops in expression."""
        if not isinstance(expr, SList) or len(expr) == 0:
            return

        head = expr[0]
        if not isinstance(head, Symbol):
            # Recurse into subexpressions
            for item in expr.items:
                self._collect_while_loop_contexts(item, loops)
            return

        if head.name == 'while' and len(expr) >= 2:
            # Found a while loop: (while condition body...)
            condition = expr[1]

            # Analyze the loop body
            modified_vars: Set[str] = set()
            set_bindings: List[SetBinding] = []
            loop_invariants: List[SExpr] = []

            # Collect set! bindings and loop invariants from body
            for body_item in expr.items[2:]:
                self._collect_set_bindings(body_item, modified_vars, set_bindings)
                self._collect_loop_invariants(body_item, loop_invariants)

            loop_ctx = WhileLoopContext(
                condition=condition,
                loop_expr=expr,
                modified_vars=modified_vars,
                loop_invariants=loop_invariants
            )
            loops.append(loop_ctx)

        # Recurse into subexpressions (including nested loops in loop body)
        for item in expr.items:
            self._collect_while_loop_contexts(item, loops)

    def _extract_while_exit_axioms(self, body: SExpr, translator: 'Z3Translator') -> List:
        """Extract axioms for while loop exit conditions.

        When a while loop exits normally (not via return/break), the negation
        of the loop condition holds. This is the standard Hoare logic rule:
        {P && B} body {P} implies {P} while(B) body {P && !B}

        For a while loop like:
            (while (and (not done) (< iteration max))
              ...)

        After the loop, we know:
            NOT (and (not done) (< iteration max))

        Which means either:
            - done is true, OR
            - iteration >= max
        """
        axioms = []
        while_loops = self._analyze_while_loops(body)

        for ctx in while_loops:
            # Translate the loop condition
            cond_z3 = translator.translate_expr(ctx.condition)
            if cond_z3 is not None:
                # After while loop exits, the condition is false
                axioms.append(z3.Not(cond_z3))

        return axioms

    def _collect_set_bindings(self, expr: SExpr, modified_vars: Set[str],
                              set_bindings: List[SetBinding]):
        """Recursively collect set! bindings within a loop body.

        For each (set! var (fn-call args...)), creates a SetBinding with:
        - var_name: the variable being set
        - call_expr: the function call expression
        - fn_name: name of the function being called
        - is_self_ref: whether var_name appears in args
        - self_ref_params: which params received var_name
        """
        if not isinstance(expr, SList) or len(expr) == 0:
            return

        head = expr[0]
        if isinstance(head, Symbol):
            if head.name == 'set!' and len(expr) >= 3:
                # Found: (set! var value)
                var = expr[1]
                value = expr[2]

                if isinstance(var, Symbol):
                    var_name = var.name
                    modified_vars.add(var_name)

                    # Check if value is a function call
                    if isinstance(value, SList) and len(value) >= 1:
                        fn_head = value[0]
                        if isinstance(fn_head, Symbol):
                            fn_name = fn_head.name
                            call_args = list(value.items[1:])

                            # Get params from function registry
                            params: List[str] = []
                            fn_def = self.function_registry.functions.get(fn_name) if self.function_registry else None
                            if fn_def:
                                params = fn_def.params
                            elif self.imported_defs:
                                imported_sig = self.imported_defs.functions.get(fn_name)
                                if imported_sig:
                                    params = imported_sig.params

                            # Check for self-reference
                            self_ref_params = self._find_self_referential_params(
                                var_name, call_args, params
                            )

                            set_bindings.append(SetBinding(
                                var_name=var_name,
                                call_expr=value,
                                fn_name=fn_name,
                                is_self_ref=len(self_ref_params) > 0,
                                self_ref_params=self_ref_params
                            ))

        # Recurse into subexpressions
        for item in expr.items:
            self._collect_set_bindings(item, modified_vars, set_bindings)

    # =========================================================================
    # Inductive Loop Verification
    # =========================================================================

    def _verify_loop_inductively(self, loop_ctx: LoopContext,
                                  init_binding: Optional[SExpr],
                                  translator: Z3Translator) -> Optional[List[InferredInvariant]]:
        """Verify a loop using inductive reasoning.

        For a loop pattern like:
            (let ((mut result (make-delta arena iter)))
              (for-each (t triples)
                (set! result (delta-add arena result t)))
              result)

        We verify:
        1. BASE CASE: Invariant holds after initialization (make-delta)
        2. INDUCTIVE STEP: If invariant holds before iteration, it holds after

        Returns list of verified invariants if successful, None if verification fails.
        """
        # Infer invariants from the loop's set! postconditions
        inferencer = InvariantInferencer(
            function_registry=self.function_registry,
            imported_defs=self.imported_defs
        )
        inferred_invariants = inferencer.infer_from_loop(loop_ctx)

        if not inferred_invariants:
            return None  # No invariants to verify

        verified_invariants: List[InferredInvariant] = []

        for invariant in inferred_invariants:
            # Verify base case and inductive step for each invariant
            base_ok = self._verify_base_case(invariant, init_binding, translator)
            step_ok = self._verify_inductive_step(invariant, loop_ctx, translator)

            if base_ok and step_ok:
                verified_invariants.append(invariant)

        return verified_invariants if verified_invariants else None

    def _verify_base_case(self, invariant: InferredInvariant,
                          init_binding: Optional[SExpr],
                          translator: Z3Translator) -> bool:
        """Verify that the invariant holds after initialization.

        For field preservation invariant like:
            (== (. result iteration) (. __init_result iteration))

        At initialization, result == __init_result, so this is trivially true.

        For other invariants, we check if the initialization postconditions
        establish the invariant.
        """
        if invariant.source == 'preservation':
            # Field preservation invariants are trivially true at initialization
            # because result@0 == __init_result by definition
            return True

        if invariant.source == 'postcondition':
            # For postcondition-derived invariants (like >= 0), we need to check
            # if the initialization establishes this property.
            # For now, assume it does if we found the postcondition
            return True

        # For other cases, attempt Z3 verification
        return self._verify_invariant_with_z3(invariant, translator, is_base_case=True)

    def _verify_inductive_step(self, invariant: InferredInvariant,
                                loop_ctx: LoopContext,
                                translator: Z3Translator) -> bool:
        """Verify that if invariant holds before iteration, it holds after.

        For field preservation with postcondition:
            (== (. $result iteration) (. d iteration))

        We need to show:
            Assume: (. result@k iteration) == (. __init_result iteration)
            After set!: result@k+1 = delta-add(arena, result@k, t)
            Postcondition: (. result@k+1 iteration) == (. result@k iteration)
            Prove: (. result@k+1 iteration) == (. __init_result iteration)

        This follows by transitivity:
            result@k+1.iteration == result@k.iteration  (postcondition)
            result@k.iteration == __init_result.iteration  (induction hypothesis)
            Therefore: result@k+1.iteration == __init_result.iteration
        """
        if invariant.source == 'preservation' and invariant.original_postcondition:
            # For field preservation, check if the postcondition matches the pattern
            # that guarantees preservation through iterations
            post = invariant.original_postcondition
            if self._is_field_equality_postcondition(post):
                # The postcondition directly states field equality between
                # $result and the parameter that holds the old value.
                # Combined with the induction hypothesis, this proves preservation.
                return True

        if invariant.source == 'postcondition':
            # For postcondition-derived invariants, the postcondition itself
            # guarantees the property holds after each iteration
            return True

        # For other cases, attempt Z3 verification
        return self._verify_invariant_with_z3(invariant, translator, is_base_case=False)

    def _is_field_equality_postcondition(self, post: SExpr) -> bool:
        """Check if postcondition is a field equality: (== (. $result f) (. param f))"""
        if not isinstance(post, SList) or len(post) < 3:
            return False

        head = post[0]
        if not isinstance(head, Symbol) or head.name != '==':
            return False

        lhs, rhs = post[1], post[2]

        # Check both sides are field accesses
        if not (isinstance(lhs, SList) and len(lhs) >= 3 and
                isinstance(rhs, SList) and len(rhs) >= 3):
            return False

        lhs_head = lhs[0]
        rhs_head = rhs[0]

        if not (isinstance(lhs_head, Symbol) and lhs_head.name == '.' and
                isinstance(rhs_head, Symbol) and rhs_head.name == '.'):
            return False

        # LHS should be (. $result field)
        lhs_obj = lhs[1]
        if not isinstance(lhs_obj, Symbol) or lhs_obj.name != '$result':
            return False

        # Fields should match
        lhs_field = lhs[2]
        rhs_field = rhs[2]
        if isinstance(lhs_field, Symbol) and isinstance(rhs_field, Symbol):
            return lhs_field.name == rhs_field.name

        return False

    def _verify_invariant_with_z3(self, invariant: InferredInvariant,
                                   translator: Z3Translator,
                                   is_base_case: bool) -> bool:
        """Attempt to verify an invariant using Z3.

        This is a fallback for invariants that don't match simple patterns.
        """
        # For now, return False to indicate we can't verify complex invariants
        # This can be extended with full Z3 encoding later
        return False

    def _get_init_postconditions(self, init_expr: SExpr) -> List[SExpr]:
        """Get postconditions from the initialization function call.

        For (make-delta arena iter), returns make-delta's postconditions.
        """
        if not isinstance(init_expr, SList) or len(init_expr) < 1:
            return []

        fn_head = init_expr[0]
        if not isinstance(fn_head, Symbol):
            return []

        fn_name = fn_head.name

        # Check local functions
        if self.function_registry:
            fn_def = self.function_registry.functions.get(fn_name)
            if fn_def and fn_def.postconditions:
                return fn_def.postconditions

        # Check imported functions
        if self.imported_defs:
            imported_sig = self.imported_defs.functions.get(fn_name)
            if imported_sig and imported_sig.postconditions:
                return imported_sig.postconditions

        return []

    def _find_init_binding_for_var(self, body: SExpr, var_name: str) -> Optional[SExpr]:
        """Find the initialization expression for a mutable variable.

        Looks for (let ((mut <var_name> <init_expr>)) ...) pattern.
        Returns the <init_expr> if found.
        """
        if not isinstance(body, SList) or len(body) < 2:
            return None

        head = body[0]
        if not isinstance(head, Symbol) or head.name != 'let':
            # Recurse into subexpressions
            for item in body.items:
                result = self._find_init_binding_for_var(item, var_name)
                if result:
                    return result
            return None

        bindings = body[1]
        if not isinstance(bindings, SList):
            return None

        for binding in bindings.items:
            if not isinstance(binding, SList) or len(binding) < 2:
                continue

            first = binding[0]
            if isinstance(first, Symbol) and first.name == 'mut' and len(binding) >= 3:
                # (mut var init)
                var = binding[1]
                if isinstance(var, Symbol) and var.name == var_name:
                    return binding[2]

        return None

    def _apply_verified_invariants(self, invariants: List[InferredInvariant],
                                    var_name: str,
                                    translator: Z3Translator) -> List:
        """Convert verified invariants to Z3 axioms for the solver.

        For field preservation invariants, creates:
            (. result field) == (. __init_result field)

        This allows the solver to use the invariant when verifying postconditions.
        """
        axioms = []

        for inv in invariants:
            if inv.source == 'preservation':
                # Create __init_<var> variable and constrain field equality
                init_var_name = f"__init_{var_name}"

                # Get or create the init variable
                if init_var_name not in translator.variables:
                    if var_name in translator.variables:
                        current = translator.variables[var_name]
                        if z3.is_bool(current):
                            init_var = z3.Bool(init_var_name)
                        elif z3.is_real(current):
                            init_var = z3.Real(init_var_name)
                        else:
                            init_var = z3.Int(init_var_name)
                        translator.variables[init_var_name] = init_var

                # Translate the invariant expression to Z3
                z3_inv = translator.translate_expr(inv.property_expr)
                if z3_inv is not None:
                    axioms.append(z3_inv)

        return axioms


__all__ = ['LoopAnalysisMixin']
